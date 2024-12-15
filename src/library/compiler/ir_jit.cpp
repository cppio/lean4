#include <xbyak/xbyak.h>
#include "library/compiler/ir.h"
#include "library/compiler/ir_jit.h"
#include "runtime/option_ref.h"

namespace lean {
namespace ir {

static lean_external_class * g_jit_code_external_class;

static void jit_code_finalize(void * code) {
    delete static_cast<Xbyak::CodeGenerator *>(code);
}

static void jit_code_foreach(void *, object *) {}

class JitCompiler {
    Xbyak::CodeGenerator & c;
    environment const & env;
    array_ref<decl> const & decls;
    std::vector<Xbyak::Label> labels;

    void compile(decl const & decl);
    void compile_expr(expr const & expr, type t);
    void compile_body(fn_body const & body);

    usize max_var;
    std::vector<Xbyak::Label> jps;
    std::vector<array_ref<param>> jp_params;

public:
    JitCompiler(Xbyak::CodeGenerator & code, environment const & env, array_ref<decl> const & decls) : c(code), env(env), decls(decls), labels(decls.size()) {
        for (size_t i = 0; i < decls.size(); ++i) {
            c.L(labels[i]);
            compile(decls[i]);
        }
        c.readyRE();
    }

    void * getLabel(usize i) {
        return const_cast<void *>(static_cast<void const *>(labels[i].getAddress()));
    }
};

static array_ref<object_ref> jit_compile(environment const & env, array_ref<decl> const & decls) {
    if (decls.size() == 0) return array_ref<object_ref>();
    for (auto const & decl : decls) {
        if (decl_tag(decl) != decl_kind::Fun) throw exception("cannot compile extern");
        if (decl_params(decl).size() > 16) throw exception("too many parameters");
    }

    auto code = std::make_unique<Xbyak::CodeGenerator>(Xbyak::DEFAULT_MAX_CODE_SIZE, Xbyak::AutoGrow);
    JitCompiler compiler(*code, env, decls);

    object_ref code_obj(lean_alloc_external(g_jit_code_external_class, code.release()));

    object * compiled_decls = alloc_array(decls.size(), decls.size());
    for (size_t i = 0; i < decls.size(); ++i) {
        object * compiled_decl = alloc_cnstr(0, 2, 0);
        cnstr_set(compiled_decl, 0, code_obj.to_obj_arg());
        cnstr_set(compiled_decl, 1, alloc_closure(compiler.getLabel(i), std::max(decl_params(decls[i]).size(), 1UL), 0));
        array_set(compiled_decls, i, compiled_decl);
    }
    return array_ref<object_ref>(compiled_decls);
}

extern "C" LEAN_EXPORT obj_res lean_jit_compile(b_obj_arg env, b_obj_arg decls) {
    try {
        return mk_cnstr(1, jit_compile(TO_REF(environment, env), TO_REF(array_ref<decl>, decls))).steal();
    } catch (exception & ex) {
        return mk_cnstr(0, string_ref(ex.what())).steal();
    }
}

extern "C" LEAN_EXPORT obj_res lean_jit_eval(b_obj_arg compiled_decl) {
    object * res = cnstr_get(compiled_decl, 1);
    inc_ref(res);
    return res;
}

extern "C" obj_res lean_ir_decl_max_var_id(obj_arg decl);
extern "C" obj_res lean_ir_decl_max_jp_id(obj_arg decl);

static Xbyak::Address var_oper(var_id const & var) {
    using namespace Xbyak::util;
    return ptr [rbp - 8 * (var.get_small_value() + 1)];
}

void JitCompiler::compile(decl const & decl) {
    using namespace Xbyak::util;

    max_var = nat(lean_ir_decl_max_var_id(decl.to_obj_arg())).get_small_value();

    usize max_jp = nat(lean_ir_decl_max_jp_id(decl.to_obj_arg())).get_small_value() + 1;
    jps.clear();
    jps.resize(max_jp);
    jp_params.clear();
    jp_params.resize(max_jp);

    c.push(rbp);
    c.mov(rbp, rsp);
    c.sub(rsp, max_var * 8);

    usize arg_idx = 0;
    for (param const & param : decl_params(decl)) {
        auto target = var_oper(param_var(param));
        switch (arg_idx) {
        case 0: c.mov(target, rdi); break;
        case 1: c.mov(target, rsi); break;
        case 2: c.mov(target, rdx); break;
        case 3: c.mov(target, rcx); break;
        case 4: c.mov(target, r8); break;
        case 5: c.mov(target, r9); break;
        default:
            c.mov(rax, ptr [rbp + 8 * (arg_idx - 4)]);
            c.mov(target, rax);
        }
        ++arg_idx;
    }

    compile_body(decl_fun_body(decl));
}

extern "C" obj_res lean_jit_lookup(obj_arg env, obj_arg name);

void * get_jit_compiled_symbol(environment const & env, name const & name) {
    auto opt_compiled_decl = option_ref<object_ref>(lean_jit_lookup(env.to_obj_arg(), name.to_obj_arg()));
    if (opt_compiled_decl) {
        return lean_closure_fun(cnstr_get(opt_compiled_decl.get_val().raw(), 1));
    } else {
        return nullptr;
    }
}

void * lookup_symbol_in_cur_exe(char const * sym);
string_ref name_mangle(name const & n, string_ref const & pre);
option_ref<decl> find_ir_decl(environment const & env, name const & n);

static void * resolve_symbol(environment const & env, name const & name) {
    if (auto sym = get_jit_compiled_symbol(env, name)) {
        return sym;
    }

    string_ref prefix("l_");
    string_ref mangled = name_mangle(name, prefix);
    if (auto sym = lookup_symbol_in_cur_exe(mangled.data())) {
        return sym;
    }

    return nullptr;
}

static void * resolve_symbol_boxed(name const & name) {
    string_ref prefix("l_");
    string_ref suffix("___boxed");
    string_ref mangled(string_append(name_mangle(name, prefix).steal(), suffix.raw()));
    return lookup_symbol_in_cur_exe(mangled.data());
}

void JitCompiler::compile_expr(expr const & expr, type t) {
    using namespace Xbyak::util;

    switch (expr_tag(expr)) {
    case expr_kind::Ctor: {
        ctor_info const & info = expr_ctor_info(expr);
        usize tag = ctor_info_tag(info).get_small_value();
        usize ctor_size = ctor_info_size(info).get_small_value();
        usize ctor_usize = ctor_info_usize(info).get_small_value();
        usize ctor_ssize = ctor_info_ssize(info).get_small_value();
        if (!ctor_size && !ctor_usize && !ctor_ssize) {
            c.mov(eax, 1);
        } else {
            unsigned sz = lean_align(sizeof(lean_ctor_object) + sizeof(void *) * (ctor_size + ctor_usize) + ctor_ssize, LEAN_OBJECT_SIZE_DELTA);
            c.mov(edi, sz);
            c.mov(esi, lean_get_slot_idx(sz));
            c.mov(rax, reinterpret_cast<usize>(lean_alloc_small));
            c.call(rax);
            c.mov(dword [rax], 1);
            c.mov(dword [rax + 4], (tag << 24) | (ctor_size << 16));
            usize idx = 0;
            for (arg const & arg : expr_ctor_args(expr)) {
                auto target = qword [rax + 8 * (idx + 1)];
                if (arg_is_irrelevant(arg)) {
                    c.mov(target, 1);
                } else {
                    c.mov(rcx, var_oper(arg_var_id(arg)));
                    c.mov(target, rcx);
                }
                ++idx;
            }
        }
        break;
    }
    case expr_kind::Reset: {
        Xbyak::Label st, end;
        c.mov(rdi, var_oper(expr_reset_obj(expr)));
        c.mov(eax, ptr [rdi]);
        c.cmp(eax, 1);
        c.jg(st);
        c.jz(end);
        c.mov(rax, reinterpret_cast<usize>(lean_dec_ref_cold));
        c.call(rax);
        c.jmp(end);
        c.L(st);
        c.dec(eax);
        c.mov(ptr [rdi], eax);
        c.L(end);
        c.mov(eax, 1);
        break;
    }
    case expr_kind::Reuse: {
        ctor_info const & info = expr_reuse_ctor(expr);
        usize tag = ctor_info_tag(info).get_small_value();
        usize ctor_size = ctor_info_size(info).get_small_value();
        usize ctor_usize = ctor_info_usize(info).get_small_value();
        usize ctor_ssize = ctor_info_ssize(info).get_small_value();
        unsigned sz = lean_align(sizeof(lean_ctor_object) + sizeof(void *) * (ctor_size + ctor_usize) + ctor_ssize, LEAN_OBJECT_SIZE_DELTA);
        c.mov(edi, sz);
        c.mov(esi, lean_get_slot_idx(sz));
        c.mov(rax, reinterpret_cast<usize>(lean_alloc_small));
        c.call(rax);
        c.mov(dword [rax], 1);
        c.mov(dword [rax + 4], (tag << 24) | (ctor_size << 16));
        usize idx = 0;
        for (arg const & arg : expr_reuse_args(expr)) {
            auto target = qword [rax + 8 * (idx + 1)];
            if (arg_is_irrelevant(arg)) {
                c.mov(target, 1);
            } else {
                c.mov(rcx, var_oper(arg_var_id(arg)));
                c.mov(target, rcx);
            }
            ++idx;
        }
        break;
    }
    case expr_kind::Proj:
        c.mov(rax, var_oper(expr_proj_obj(expr)));
        c.mov(rax, ptr [rax + 8 * (expr_proj_idx(expr).get_small_value() + 1)]);
        break;
    case expr_kind::UProj:
        c.mov(rax, var_oper(expr_uproj_obj(expr)));
        c.mov(rax, ptr [rax + 8 * (expr_uproj_idx(expr).get_small_value() + 1)]);
        break;
    case expr_kind::SProj: {
        c.mov(rax, var_oper(expr_sproj_obj(expr)));
        usize offset = 8 * (expr_sproj_idx(expr).get_small_value() + 1) + expr_sproj_offset(expr).get_small_value();
        switch (t) {
        case type::Float:
            throw exception("float not supported");
            break;
        case type::UInt8:
            c.movzx(eax, byte [rax + offset]);
            break;
        case type::UInt16:
            c.movzx(eax, word [rax + offset]);
            break;
        case type::UInt32:
            c.mov(eax, ptr [rax + offset]);
            break;
        case type::UInt64:
            c.mov(rax, ptr [rax + offset]);
            break;
        case type::USize:
        case type::Irrelevant:
        case type::Object:
        case type::TObject:
            throw exception("invalid type");
        }
        break;
    }
    case expr_kind::FAp: {
        name const & fun = expr_fap_fun(expr);
        auto const & args = expr_fap_args(expr);
        auto addr = resolve_symbol(env, fun);
        usize idx = 0;
        if (!addr) {
            for (decl const & decl : decls) {
                if (decl_fun_id(decl) == fun) {
                    break;
                }
                ++idx;
            }
        }
        if (idx < decls.size()) {
            for (usize i = 0; i < args.size() && i < 6; ++i) {
                Xbyak::Reg32 reg32;
                Xbyak::Reg64 reg64;
                switch (i) {
                case 0: reg32 = edi; reg64 = rdi; break;
                case 1: reg32 = esi; reg64 = rsi; break;
                case 2: reg32 = edx; reg64 = rdx; break;
                case 3: reg32 = ecx; reg64 = rcx; break;
                case 4: reg32 = r8d; reg64 = r8; break;
                case 5: reg32 = r9d; reg64 = r9; break;
                }
                if (arg_is_irrelevant(args[i])) {
                    c.mov(reg32, 1);
                } else {
                    c.mov(reg64, var_oper(arg_var_id(args[i])));
                }
            }
            for (usize i = args.size(); i-- > 6; ) {
                if (arg_is_irrelevant(args[i])) {
                    c.push(1);
                } else {
                    c.mov(rax, var_oper(arg_var_id(args[i])));
                    c.push(rax);
                }
            }
            if (addr) {
                c.mov(rax, reinterpret_cast<usize>(addr));
                c.call(rax);
            } else {
                c.call(labels[idx]);
            }
            if (args.size() > 6) {
                c.add(rsp, 8 * (args.size() - 6));
            }
        } else {
            addr = resolve_symbol_boxed(fun);
            if (!addr) {
                throw exception(sstream() << "cannot find compiled implementation of " << fun);
            }
            auto ir_decl = find_ir_decl(env, fun);
            if (!ir_decl) {
                throw exception("cannot find decl");
            }
            decl decl = ir_decl.get_val();
            for (usize i = args.size(); i-- > 0; ) {
                if (arg_is_irrelevant(args[i])) {
                    c.push(1);
                } else {
                    var_id const & var = arg_var_id(args[i]);
                    param const & param = decl_params(decl)[i];
                    switch (param_type(param)) {
                    case type::Float:
                        throw exception("float not supported");
                        break;
                    case type::UInt8:
                    case type::UInt16:
                    case type::UInt32:
                        c.mov(rax, var_oper(var));
                        c.lea(rax, ptr [rax + rax + 1]);
                        break;
                    case type::UInt64:
                    case type::USize: {
                        unsigned sz = lean_align(sizeof(lean_ctor_object) + sizeof(void *), LEAN_OBJECT_SIZE_DELTA);
                        c.mov(edi, sz);
                        c.mov(esi, lean_get_slot_idx(sz));
                        c.mov(rax, reinterpret_cast<usize>(lean_alloc_small));
                        c.call(rax);
                        c.mov(qword [rax], 1);
                        c.mov(rcx, var_oper(var));
                        c.mov(ptr [rax + 8], rcx);
                        break;
                    }
                    case type::Irrelevant:
                    case type::Object:
                    case type::TObject:
                        if (param_borrow(param)) {
                            Xbyak::Label st, end;
                            c.mov(rdi, var_oper(var));
                            c.test(dil, 1);
                            c.jnz(end);
                            c.mov(eax, ptr [rdi]);
                            c.test(eax, eax);
                            c.jg(st);
                            c.jz(end);
                            c.mov(rax, reinterpret_cast<usize>(lean_inc_ref_cold));
                            c.call(rax);
                            c.jmp(end);
                            c.L(st);
                            c.inc(eax);
                            c.mov(ptr [rdi], eax);
                            c.L(end);
                        }
                        c.mov(rax, var_oper(var));
                        break;
                    }
                    c.push(rax);
                }
            }
            c.pop(rdi);
            if (args.size() > 1) c.pop(rsi);
            if (args.size() > 2) c.pop(rdx);
            if (args.size() > 3) c.pop(rcx);
            if (args.size() > 4) c.pop(r8);
            if (args.size() > 5) c.pop(r9);
            c.mov(rax, reinterpret_cast<usize>(addr));
            c.call(rax);
            if (args.size() > 6) {
                c.add(rsp, 8 * (args.size() - 6));
            }
            switch (decl_type(decl)) {
            case type::Float:
                throw exception("float not supported");
                break;
            case type::UInt8:
            case type::UInt16:
            case type::UInt32:
                c.shr(rax, 1);
                break;
            case type::UInt64:
            case type::USize: {
                Xbyak::Label st, end;
                c.push(qword [rax + 8]);
                c.mov(rdi, rax);
                c.mov(eax, ptr [rdi]);
                c.cmp(eax, 1);
                c.jg(st);
                c.jz(end);
                c.mov(rax, reinterpret_cast<usize>(lean_dec_ref_cold));
                c.call(rax);
                c.jmp(end);
                c.L(st);
                c.dec(eax);
                c.mov(ptr [rdi], eax);
                c.L(end);
                c.pop(rax);
                break;
            }
            default:
                break;
            }
        }
        break;
    }
    case expr_kind::PAp: {
        name const & fun = expr_pap_fun(expr);
        auto const & args = expr_pap_args(expr);

        auto addr = resolve_symbol(env, fun);
        usize decl_idx = 0;
        if (!addr) {
            for (decl const & decl : decls) {
                if (decl_fun_id(decl) == fun) {
                    break;
                }
                ++decl_idx;
            }
        }
        if (decl_idx == decls.size()) {
            throw exception(sstream() << "cannot find compiled implementation of " << fun);
        }

        auto ir_decl = find_ir_decl(env, fun);
        if (!ir_decl) {
            throw exception("cannot find decl");
        }
        decl decl = ir_decl.get_val();

        unsigned sz = lean_align(sizeof(lean_closure_object) + sizeof(void *) * args.size(), LEAN_OBJECT_SIZE_DELTA);
        c.mov(edi, sz);
        c.mov(esi, lean_get_slot_idx(sz));
        c.mov(rax, reinterpret_cast<usize>(lean_alloc_small));
        c.call(rax);
        c.mov(dword [rax], 1);
        c.mov(dword [rax + 4], LeanClosure << 24);
        if (addr) {
            c.mov(rcx, reinterpret_cast<usize>(addr));
        } else {
            c.mov(rcx, labels[decl_idx]);
        }
        c.mov(qword [rax + 8], rcx);
        c.mov(qword [rax + 16], (args.size() << 16) | decl_params(decl).size());

        usize idx = 0;
        for (arg const & arg : expr_pap_args(expr)) {
            auto target = qword [rax + 8 * (idx + 3)];
            if (arg_is_irrelevant(arg)) {
                c.mov(target, 1);
            } else {
                c.mov(rcx, var_oper(arg_var_id(arg)));
                c.mov(target, rcx);
            }
            ++idx;
        }
        break;
    }
    case expr_kind::Ap: {
        c.mov(rdi, var_oper(expr_ap_fun(expr)));
        auto const & args = expr_ap_args(expr);
        for (usize i = 0; i < args.size() && i < 5; ++i) {
            Xbyak::Reg32 reg32;
            Xbyak::Reg64 reg64;
            switch (i + 1) {
            case 1: reg32 = esi; reg64 = rsi; break;
            case 2: reg32 = edx; reg64 = rdx; break;
            case 3: reg32 = ecx; reg64 = rcx; break;
            case 4: reg32 = r8d; reg64 = r8; break;
            case 5: reg32 = r9d; reg64 = r9; break;
            }
            if (arg_is_irrelevant(args[i])) {
                c.mov(reg32, 1);
            } else {
                c.mov(reg64, var_oper(arg_var_id(args[i])));
            }
        }
        for (usize i = args.size(); i-- > 5; ) {
            if (arg_is_irrelevant(args[i])) {
                c.push(1);
            } else {
                c.mov(rax, var_oper(arg_var_id(args[i])));
                c.push(rax);
            }
        }
        switch (args.size()) {
        case 1: c.mov(rax, reinterpret_cast<usize>(lean_apply_1)); break;
        case 2: c.mov(rax, reinterpret_cast<usize>(lean_apply_2)); break;
        case 3: c.mov(rax, reinterpret_cast<usize>(lean_apply_3)); break;
        case 4: c.mov(rax, reinterpret_cast<usize>(lean_apply_4)); break;
        case 5: c.mov(rax, reinterpret_cast<usize>(lean_apply_5)); break;
        case 6: c.mov(rax, reinterpret_cast<usize>(lean_apply_6)); break;
        case 7: c.mov(rax, reinterpret_cast<usize>(lean_apply_7)); break;
        case 8: c.mov(rax, reinterpret_cast<usize>(lean_apply_8)); break;
        case 9: c.mov(rax, reinterpret_cast<usize>(lean_apply_9)); break;
        case 10: c.mov(rax, reinterpret_cast<usize>(lean_apply_10)); break;
        case 11: c.mov(rax, reinterpret_cast<usize>(lean_apply_11)); break;
        case 12: c.mov(rax, reinterpret_cast<usize>(lean_apply_12)); break;
        case 13: c.mov(rax, reinterpret_cast<usize>(lean_apply_13)); break;
        case 14: c.mov(rax, reinterpret_cast<usize>(lean_apply_14)); break;
        case 15: c.mov(rax, reinterpret_cast<usize>(lean_apply_15)); break;
        case 16: c.mov(rax, reinterpret_cast<usize>(lean_apply_16)); break;
        default:
            throw exception("too many arguments");
        }
        c.call(rax);
        if (args.size() > 5) {
            c.add(rsp, 8 * (args.size() - 5));
        }
        break;
    }
    case expr_kind::Box:
        switch (expr_box_type(expr)) {
        case type::Float:
            throw exception("float not supported");
            break;
        case type::UInt8:
        case type::UInt16:
        case type::UInt32:
            c.mov(rax, var_oper(expr_box_obj(expr)));
            c.lea(rax, ptr [rax + rax + 1]);
            break;
        case type::UInt64:
        case type::USize: {
            unsigned sz = lean_align(sizeof(lean_ctor_object) + sizeof(void *), LEAN_OBJECT_SIZE_DELTA);
            c.mov(edi, sz);
            c.mov(esi, lean_get_slot_idx(sz));
            c.mov(rax, reinterpret_cast<usize>(lean_alloc_small));
            c.call(rax);
            c.mov(qword [rax], 1);
            c.mov(rcx, var_oper(expr_box_obj(expr)));
            c.mov(ptr [rax + 8], rcx);
            break;
        }
        case type::Irrelevant:
        case type::Object:
        case type::TObject:
            c.mov(rax, var_oper(expr_box_obj(expr)));
            break;
        }
        break;
    case expr_kind::Unbox:
        c.mov(rax, var_oper(expr_unbox_obj(expr)));
        switch (t) {
        case type::Float:
            throw exception("float not supported");
            break;
        case type::UInt8:
        case type::UInt16:
        case type::UInt32:
            c.shr(rax, 1);
            break;
        case type::UInt64:
        case type::USize:
            c.mov(rax, ptr [rax + 8]);
            break;
        case type::Irrelevant:
        case type::Object:
        case type::TObject:
            throw exception("invalid type");
        }
        break;
    case expr_kind::Lit: {
        lit_val const & lit = expr_lit_val(expr);
        switch (lit_val_tag(lit)) {
        case lit_val_kind::Num: {
            nat const & num = lit_val_num(lit);
            switch (t) {
            case type::Float:
                throw exception("float not supported");
                break;
            case type::UInt8:
            case type::UInt16:
            case type::UInt32:
            case type::UInt64:
            case type::USize:
                c.mov(rax, uint64_of_nat(num.raw()));
                break;
            case type::Irrelevant:
                throw exception("invalid type");
            case type::Object:
            case type::TObject:
                c.mov(rax, reinterpret_cast<usize>(num.raw()));
                break;
            }
            break;
        }
        case lit_val_kind::Str:
            c.mov(rax, reinterpret_cast<usize>(lit_val_str(lit).raw()));
            break;
        }
        break;
    }
    case expr_kind::IsShared:
        c.mov(rax, var_oper(expr_is_shared_obj(expr)));
        c.cmp(dword [rax], 1);
        c.setne(al);
        c.movzx(eax, al);
        break;
    case expr_kind::IsTaggedPtr:
        c.test(var_oper(expr_is_tagged_ptr_obj(expr)), 1);
        c.setz(al);
        c.movzx(eax, al);
        break;
    }
}

void JitCompiler::compile_body(fn_body const & body) {
    using namespace Xbyak::util;

    switch (fn_body_tag(body)) {
    case fn_body_kind::VDecl:
        compile_expr(fn_body_vdecl_expr(body), fn_body_vdecl_type(body));
        c.mov(var_oper(fn_body_vdecl_var(body)), rax);
        compile_body(fn_body_vdecl_cont(body));
        break;
    case fn_body_kind::JDecl: {
        usize id = fn_body_jdecl_id(body).get_small_value();
        jp_params[id] = fn_body_jdecl_params(body);
        compile_body(fn_body_jdecl_cont(body));
        c.L(jps[fn_body_jdecl_id(body).get_small_value()]);
        compile_body(fn_body_jdecl_body(body));
        break;
    }
    case fn_body_kind::Set: {
        arg const & arg = fn_body_set_arg(body);
        c.mov(rax, var_oper(fn_body_set_var(body)));
        auto target = qword [rax + 8 * (1 + fn_body_set_idx(body).get_small_value())];
        if (arg_is_irrelevant(arg)) {
            c.mov(target, 1);
        } else {
            c.mov(rcx, var_oper(arg_var_id(arg)));
            c.mov(target, rcx);
        }
        compile_body(fn_body_set_cont(body));
        break;
    }
    case fn_body_kind::SetTag:
        c.mov(rax, var_oper(fn_body_set_tag_var(body)));
        c.mov(byte [rax + 7], fn_body_set_tag_cidx(body).get_small_value());
        compile_body(fn_body_set_tag_cont(body));
        break;
    case fn_body_kind::USet:
        c.mov(rax, var_oper(fn_body_uset_target(body)));
        c.mov(rcx, var_oper(fn_body_uset_source(body)));
        c.mov(ptr [rax + 8 * (1 + fn_body_uset_idx(body).get_small_value())], rcx);
        compile_body(fn_body_uset_cont(body));
        break;
    case fn_body_kind::SSet: {
        usize offset = 8 * (fn_body_sset_idx(body).get_small_value() + 1) + fn_body_sset_offset(body).get_small_value();
        c.mov(rax, var_oper(fn_body_sset_target(body)));
        c.mov(rcx, var_oper(fn_body_sset_source(body)));
        switch (fn_body_sset_type(body)) {
        case type::Float:
            throw exception("float not supported");
            break;
        case type::UInt8:
            c.mov(ptr [rax + offset], cl);
            break;
        case type::UInt16:
            c.mov(ptr [rax + offset], cx);
            break;
        case type::UInt32:
            c.mov(ptr [rax + offset], ecx);
            break;
        case type::UInt64:
            c.mov(ptr [rax + offset], rcx);
            break;
        case type::USize:
        case type::Irrelevant:
        case type::Object:
        case type::TObject:
            throw exception("invalid type");
        }
        compile_body(fn_body_sset_cont(body));
        break;
    }
    case fn_body_kind::Inc: {
        Xbyak::Label st, end;
        usize val = fn_body_inc_val(body).get_small_value();
        c.mov(rdi, var_oper(fn_body_inc_var(body)));
        if (fn_body_inc_maybe_scalar(body)) {
            c.test(dil, 1);
            c.jnz(end);
        }
        c.mov(eax, ptr [rdi]);
        c.test(eax, eax);
        c.jg(st);
        c.jz(end);
        if (val != 1) {
            c.mov(rsi, val);
            c.mov(rax, reinterpret_cast<usize>(lean_inc_ref_n_cold));
        } else {
            c.mov(rax, reinterpret_cast<usize>(lean_inc_ref_cold));
        }
        c.call(rax);
        c.jmp(end);
        c.L(st);
        if (val != 1) {
            c.add(eax, val);
        } else {
            c.inc(eax);
        }
        c.mov(ptr [rdi], eax);
        c.L(end);
        compile_body(fn_body_inc_cont(body));
        break;
    }
    case fn_body_kind::Dec: {
        Xbyak::Label st, end;
        usize val = fn_body_dec_val(body).get_small_value();
        c.mov(rdi, var_oper(fn_body_dec_var(body)));
        if (fn_body_dec_maybe_scalar(body)) {
            c.test(dil, 1);
            c.jnz(end);
        }
        c.mov(eax, ptr [rdi]);
        c.cmp(eax, val);
        c.jg(st);
        c.jz(end);
        c.mov(rax, reinterpret_cast<usize>(lean_dec_ref_cold));
        c.call(rax);
        for (usize i = 1; i < val; ++i) {
            c.mov(rdi, var_oper(fn_body_dec_var(body)));
            c.mov(rax, reinterpret_cast<usize>(lean_dec_ref_cold));
            c.call(rax);
        }
        c.jmp(end);
        c.L(st);
        if (val != 1) {
            c.sub(eax, val);
        } else {
            c.dec(eax);
        }
        c.mov(ptr [rdi], eax);
        c.L(end);
        compile_body(fn_body_dec_cont(body));
        break;
    }
    case fn_body_kind::Del:
        c.mov(rdi, var_oper(fn_body_del_var(body)));
        c.mov(rax, reinterpret_cast<usize>(lean_free_object));
        compile_body(fn_body_del_cont(body));
        break;
    case fn_body_kind::MData:
        compile_body(fn_body_mdata_cont(body));
        break;
    case fn_body_kind::Case: {
        c.mov(rax, var_oper(fn_body_case_var(body)));
        switch (fn_body_case_var_type(body)) {
        case type::Irrelevant:
        case type::Object:
        case type::TObject: {
            Xbyak::Label scalar, end;
            c.test(al, 1);
            c.jnz(scalar);
            c.movzx(eax, byte [rax + 7]);
            c.jmp(end);
            c.L(scalar);
            c.shr(rax, 1);
            c.L(end);
            break;
        }
        default:
            break;
        }

        std::vector<Xbyak::Label> alt_labels(fn_body_case_alts(body).size());
        std::vector<optional<usize>> alts;
        optional<usize> default_alt;
        usize idx = 0;
        for (alt const & alt : fn_body_case_alts(body)) {
            switch (alt_core_tag(alt)) {
            case alt_core_kind::Ctor: {
                usize tag = ctor_info_tag(alt_core_ctor_info(alt)).get_small_value();
                if (tag >= alts.size()) alts.resize(tag + 1);
                if (!alts[tag]) alts[tag] = idx;
                break;
            }
            case alt_core_kind::Default:
                if (!default_alt) default_alt = idx;
                break;
            }
            ++idx;
        }

        if (default_alt) {
            c.cmp(eax, alts.size());
            c.jae(alt_labels[*default_alt], Xbyak::CodeGenerator::T_NEAR);
        }
        c.lea(rcx, ptr [rip + 3]);
        c.jmp(ptr [rcx + 8 * rax]);
        for (auto alt : alts) {
            if (alt) c.putL(alt_labels[*alt]);
            else if (default_alt) c.putL(alt_labels[*default_alt]);
            else c.dq(0);
        }
        idx = 0;
        for (alt const & alt : fn_body_case_alts(body)) {
            c.L(alt_labels[idx++]);
            switch (alt_core_tag(alt)) {
            case alt_core_kind::Ctor: {
                compile_body(alt_core_ctor_cont(alt));
                break;
            }
            case alt_core_kind::Default:
                compile_body(alt_core_default_cont(alt));
                break;
            }
        }
        break;
    }
    case fn_body_kind::Ret: {
        arg const & arg = fn_body_ret_arg(body);
        if (arg_is_irrelevant(arg)) {
            c.mov(eax, 1);
        } else {
            c.mov(rax, var_oper(arg_var_id(arg)));
        }
        c.add(rsp, max_var * 8);
        c.pop(rbp);
        c.ret();
        break;
    }
    case fn_body_kind::Jmp: {
        usize id = fn_body_jmp_jp(body).get_small_value();
        auto const & params = jp_params[id];
        usize idx = 0;
        for (arg const & arg : fn_body_jmp_args(body)) {
            auto target = var_oper(param_var(params[idx]));
            if (arg_is_irrelevant(arg)) {
                c.mov(target, 1);
            } else {
                c.mov(rax, var_oper(arg_var_id(arg)));
                c.mov(target, rax);
            }
            ++idx;
        }
        c.jmp(jps[id], Xbyak::CodeGenerator::T_NEAR);
        break;
    }
    case fn_body_kind::Unreachable:
        c.ud2();
        break;
    }
}

}

void initialize_ir_jit() {
    ir::g_jit_code_external_class = lean_register_external_class(ir::jit_code_finalize, ir::jit_code_foreach);
}

void finalize_ir_jit() {}

}
