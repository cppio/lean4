// Lean compiler output
// Module: Lean.Elab.Declaration
// Imports: Init Lean.Util.CollectLevelParams Lean.Elab.Definition Lean.Elab.Inductive Lean.Elab.Structure
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_Lean_Elab_Command_elabDeclaration(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__2;
extern lean_object* l_Lean_Parser_Command_abbrev___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabConstant___closed__4;
lean_object* l_unreachable_x21___rarg(lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__8;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__6;
lean_object* l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__4;
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__10;
lean_object* l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__2;
lean_object* l___private_Lean_Elab_Declaration_2__checkValidCtorModifier(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__9;
lean_object* l_Lean_Elab_Command_elabConstant___closed__2;
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Elab_Command_elabExample(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabAbbrev(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withDeclId___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabExample___closed__1;
lean_object* l_Lean_Elab_Command_elabConstant___closed__1;
lean_object* l_Lean_Elab_Command_elabInductiveCore(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__6;
lean_object* l___private_Lean_Elab_Declaration_4__classInductiveSyntaxToView(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
extern lean_object* l_Lean_Parser_Command_section___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Command_6__mkTermContext(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandDeclSig(lean_object*);
lean_object* l_Lean_Elab_Command_elabExample___closed__2;
extern lean_object* l_Lean_Parser_Command_declaration___elambda__1___closed__2;
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration(lean_object*);
extern lean_object* l_Lean_Parser_Command_mutual___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Command_3__setState(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_8__splitMutualPreamble___boxed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_Term_mkForallUsedOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__6;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__5;
lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual(lean_object*);
extern lean_object* l_Lean_Parser_Command_mutual___elambda__1___closed__1;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__3;
extern lean_object* l_Lean_Parser_Command_example___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__6;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_section___elambda__1___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__1;
lean_object* l_Lean_Elab_Command_applyVisibility(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__8;
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_check___elambda__1___closed__2;
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__3;
extern lean_object* l_Lean_Parser_Command_classInductive___elambda__1___closed__2;
extern lean_object* l_Lean_mkTermIdFromIdent___closed__2;
lean_object* l_Lean_Elab_Command_elabInstance___closed__4;
lean_object* l_Lean_Elab_Command_mkDeclName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__5;
lean_object* l_Lean_Elab_Command_expandOptDeclSig___boxed(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__3;
lean_object* l_Lean_Elab_Term_levelMVarToParam(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_7__isMutualPreambleCommand___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__11;
lean_object* l_Lean_Elab_Command_elabAxiom(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__7;
lean_object* l_Lean_Elab_Command_elabInstance___closed__1;
extern lean_object* l_Lean_Parser_Command_set__option___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_elabInstance___closed__2;
lean_object* l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__7;
lean_object* l___private_Lean_Elab_Declaration_8__splitMutualPreamble(lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_Declaration_5__isMutualInductive___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__8;
extern lean_object* l_Lean_Parser_Command_def___elambda__1___closed__2;
extern lean_object* l_Lean_Parser_Command_declValSimple___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__1;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabConstant(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__1;
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandOptDeclSig(lean_object*);
lean_object* l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__7;
lean_object* l_Lean_Elab_Command_elabClassInductive(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
lean_object* l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__3;
lean_object* l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__7;
lean_object* l_Lean_Elab_Command_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_Declaration_5__isMutualInductive___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__5;
extern lean_object* l_Lean_Parser_Command_instance___elambda__1___closed__1;
extern lean_object* l_Lean_Parser_Command_variable___elambda__1___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_6__elabMutualInductive___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__10;
extern lean_object* l_Lean_Parser_Command_open___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_elabMutual___closed__2;
lean_object* l_Lean_Elab_Command_elabTheorem(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDef(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerClassAttr___closed__2;
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_sortDeclLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInstance___closed__5;
lean_object* l___private_Lean_Elab_Command_2__getState(lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_Declaration_5__isMutualInductive(lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_Elab_Command_elabClassInductive___closed__1;
extern lean_object* l_Lean_Parser_Command_instance___elambda__1___closed__2;
extern lean_object* l_Lean_mkReducibilityAttrs___closed__4;
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_universe___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__2;
lean_object* l___private_Lean_Elab_Declaration_3__inductiveSyntaxToView(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_8__letBindRhss___main___closed__11;
lean_object* l_Lean_Elab_Command_elabAbbrev___closed__3;
lean_object* l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__12;
lean_object* lean_environment_main_module(lean_object*);
extern lean_object* l_Lean_Parser_Command_end___elambda__1___closed__1;
lean_object* l_Lean_Elab_Command_elabMutual(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInstance(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_7__mkTermState(lean_object*);
extern lean_object* l_Lean_Parser_Command_axiom___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l_Lean_Elab_Command_getMainModule(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInstance___closed__3;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_5__isMutualInductive___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_elabAbbrev___closed__2;
extern lean_object* l_Lean_Elab_Command_Attribute_inhabited;
lean_object* l_Lean_Elab_Command_Modifiers_addAttribute(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabMutual___closed__3;
lean_object* l___private_Lean_Elab_Declaration_6__elabMutualInductive(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_structure___elambda__1___closed__2;
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_Lean_Elab_Command_elabConstant___closed__6;
uint8_t l___private_Lean_Elab_Declaration_7__isMutualPreambleCommand(lean_object*);
extern lean_object* l_Lean_Elab_Command_mkDef___lambda__1___closed__5;
extern lean_object* l_Lean_Parser_Command_inductive___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Command_9__getVarDecls(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__4;
lean_object* l_Lean_Elab_Command_getEnv(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_universes___elambda__1___closed__2;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__1;
extern lean_object* l_Lean_mkOptionalNode___closed__1;
lean_object* l_Lean_Elab_Command_getLevelNames(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabModifiers(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__11;
lean_object* l___private_Lean_Elab_Declaration_8__splitMutualPreamble___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDefLike(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandDeclSig___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_elabDeclaration___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__12;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__4;
uint8_t l_Lean_Elab_Command_Modifiers_isProtected(lean_object*);
extern lean_object* l_Lean_Parser_Command_variables___elambda__1___closed__2;
uint8_t l_Lean_Elab_Command_Modifiers_isPrivate(lean_object*);
lean_object* l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__9;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDeclaration___closed__2;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabConstant___closed__5;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInductive(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_8__splitMutualPreamble___main___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDeclaration___closed__1;
lean_object* l_Lean_Elab_Command_elabDeclaration___closed__3;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__2;
lean_object* l_Lean_Elab_Command_elabConstant___closed__3;
lean_object* l_Lean_Elab_Command_elabAbbrev___closed__1;
lean_object* l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__9;
lean_object* l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__8;
lean_object* l_Lean_Elab_Command_elabAbbrev___closed__4;
lean_object* l_Lean_CollectLevelParams_main___main(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
lean_object* l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual___closed__1;
lean_object* l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__5;
extern lean_object* l_Lean_Parser_Command_constant___elambda__1___closed__2;
extern lean_object* l_Lean_Parser_Command_theorem___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__4;
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_declId___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_elabMutual___closed__1;
lean_object* l_Lean_Elab_Command_expandOptDeclSig(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_isNone(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Syntax_getArg(x_5, x_2);
lean_dec(x_5);
x_8 = l_Lean_Syntax_getArg(x_7, x_4);
lean_dec(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
lean_object* l_Lean_Elab_Command_expandOptDeclSig___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_expandOptDeclSig(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_expandDeclSig(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArg(x_5, x_4);
lean_dec(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_expandDeclSig___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_expandDeclSig(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabAbbrev___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inline");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabAbbrev___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabAbbrev___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabAbbrev___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabAbbrev___closed__2;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabAbbrev___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkReducibilityAttrs___closed__4;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabAbbrev(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_5 = lean_unsigned_to_nat(2u);
x_6 = l_Lean_Syntax_getArg(x_2, x_5);
x_7 = l_Lean_Elab_Command_expandOptDeclSig(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Elab_Command_elabAbbrev___closed__3;
x_11 = l_Lean_Elab_Command_Modifiers_addAttribute(x_1, x_10);
x_12 = l_Lean_Elab_Command_elabAbbrev___closed__4;
x_13 = l_Lean_Elab_Command_Modifiers_addAttribute(x_11, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_2, x_14);
x_16 = lean_unsigned_to_nat(3u);
x_17 = l_Lean_Syntax_getArg(x_2, x_16);
x_18 = 4;
x_19 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 3, x_8);
lean_ctor_set(x_19, 4, x_9);
lean_ctor_set(x_19, 5, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*6, x_18);
x_20 = l_Lean_Elab_Command_elabDefLike(x_19, x_3, x_4);
return x_20;
}
}
lean_object* l_Lean_Elab_Command_elabDef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_5 = lean_unsigned_to_nat(2u);
x_6 = l_Lean_Syntax_getArg(x_2, x_5);
x_7 = l_Lean_Elab_Command_expandOptDeclSig(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_2, x_10);
x_12 = lean_unsigned_to_nat(3u);
x_13 = l_Lean_Syntax_getArg(x_2, x_12);
x_14 = 0;
x_15 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_1);
lean_ctor_set(x_15, 2, x_11);
lean_ctor_set(x_15, 3, x_8);
lean_ctor_set(x_15, 4, x_9);
lean_ctor_set(x_15, 5, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*6, x_14);
x_16 = l_Lean_Elab_Command_elabDefLike(x_15, x_3, x_4);
return x_16;
}
}
lean_object* l_Lean_Elab_Command_elabTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_unsigned_to_nat(2u);
x_6 = l_Lean_Syntax_getArg(x_2, x_5);
x_7 = l_Lean_Elab_Command_expandDeclSig(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_2, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_9);
x_13 = lean_unsigned_to_nat(3u);
x_14 = l_Lean_Syntax_getArg(x_2, x_13);
x_15 = 1;
x_16 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_1);
lean_ctor_set(x_16, 2, x_11);
lean_ctor_set(x_16, 3, x_8);
lean_ctor_set(x_16, 4, x_12);
lean_ctor_set(x_16, 5, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*6, x_15);
x_17 = l_Lean_Elab_Command_elabDefLike(x_16, x_3, x_4);
return x_17;
}
}
lean_object* _init_l_Lean_Elab_Command_elabConstant___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("arbitrary");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabConstant___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabConstant___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabConstant___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabConstant___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabConstant___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Command_elabConstant___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabConstant___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabConstant___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabConstant___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabConstant___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabConstant___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabConstant(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_unsigned_to_nat(2u);
x_6 = l_Lean_Syntax_getArg(x_2, x_5);
x_7 = l_Lean_Elab_Command_expandDeclSig(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Syntax_getArg(x_2, x_10);
x_12 = l_Lean_Syntax_getOptional_x3f(x_11);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Lean_Elab_Command_getCurrMacroScope(x_3, x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_3);
x_16 = l_Lean_Elab_Command_getMainModule(x_3, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Elab_Command_elabConstant___closed__4;
x_20 = l_Lean_addMacroScope(x_17, x_19, x_14);
x_21 = l_Lean_SourceInfo_inhabited___closed__1;
x_22 = l_Lean_Elab_Command_elabConstant___closed__3;
x_23 = l_Lean_Elab_Command_elabConstant___closed__6;
x_24 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_20);
lean_ctor_set(x_24, 3, x_23);
x_25 = l_Array_empty___closed__1;
x_26 = lean_array_push(x_25, x_24);
x_27 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_28 = lean_array_push(x_26, x_27);
x_29 = l_Lean_mkTermIdFromIdent___closed__2;
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_array_push(x_25, x_30);
x_32 = l___private_Lean_Elab_Quotation_8__letBindRhss___main___closed__11;
x_33 = lean_array_push(x_31, x_32);
x_34 = l_Lean_mkAppStx___closed__8;
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__3;
x_37 = l_Lean_mkAtomFrom(x_2, x_36);
x_38 = l_Lean_mkAppStx___closed__9;
x_39 = lean_array_push(x_38, x_37);
x_40 = lean_array_push(x_39, x_35);
x_41 = l_Lean_Parser_Command_declValSimple___elambda__1___closed__2;
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_unsigned_to_nat(1u);
x_44 = l_Lean_Syntax_getArg(x_2, x_43);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_9);
x_46 = 3;
x_47 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_47, 0, x_2);
lean_ctor_set(x_47, 1, x_1);
lean_ctor_set(x_47, 2, x_44);
lean_ctor_set(x_47, 3, x_8);
lean_ctor_set(x_47, 4, x_45);
lean_ctor_set(x_47, 5, x_42);
lean_ctor_set_uint8(x_47, sizeof(void*)*6, x_46);
x_48 = l_Lean_Elab_Command_elabDefLike(x_47, x_3, x_18);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_16);
if (x_49 == 0)
{
return x_16;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_16, 0);
x_51 = lean_ctor_get(x_16, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_16);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_12);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_12, 0);
x_55 = lean_unsigned_to_nat(1u);
x_56 = l_Lean_Syntax_getArg(x_2, x_55);
lean_ctor_set(x_12, 0, x_9);
x_57 = 3;
x_58 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_58, 0, x_2);
lean_ctor_set(x_58, 1, x_1);
lean_ctor_set(x_58, 2, x_56);
lean_ctor_set(x_58, 3, x_8);
lean_ctor_set(x_58, 4, x_12);
lean_ctor_set(x_58, 5, x_54);
lean_ctor_set_uint8(x_58, sizeof(void*)*6, x_57);
x_59 = l_Lean_Elab_Command_elabDefLike(x_58, x_3, x_4);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_12, 0);
lean_inc(x_60);
lean_dec(x_12);
x_61 = lean_unsigned_to_nat(1u);
x_62 = l_Lean_Syntax_getArg(x_2, x_61);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_9);
x_64 = 3;
x_65 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_65, 0, x_2);
lean_ctor_set(x_65, 1, x_1);
lean_ctor_set(x_65, 2, x_62);
lean_ctor_set(x_65, 3, x_8);
lean_ctor_set(x_65, 4, x_63);
lean_ctor_set(x_65, 5, x_60);
lean_ctor_set_uint8(x_65, sizeof(void*)*6, x_64);
x_66 = l_Lean_Elab_Command_elabDefLike(x_65, x_3, x_4);
return x_66;
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_elabInstance___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Command_instance___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabInstance___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabInstance___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabInstance___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("not implemented yet");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabInstance___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabInstance___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabInstance___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabInstance___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_unsigned_to_nat(2u);
x_6 = l_Lean_Syntax_getArg(x_2, x_5);
x_7 = l_Lean_Elab_Command_expandDeclSig(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Elab_Command_elabInstance___closed__2;
x_11 = l_Lean_Elab_Command_Modifiers_addAttribute(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_2, x_12);
x_14 = l_Lean_Syntax_getOptional_x3f(x_13);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
x_15 = l_Lean_Elab_Command_elabInstance___closed__5;
x_16 = l_Lean_Elab_Command_throwError___rarg(x_2, x_15, x_3, x_4);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_14, 0, x_9);
x_23 = lean_unsigned_to_nat(3u);
x_24 = l_Lean_Syntax_getArg(x_2, x_23);
x_25 = 0;
x_26 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_11);
lean_ctor_set(x_26, 2, x_22);
lean_ctor_set(x_26, 3, x_8);
lean_ctor_set(x_26, 4, x_14);
lean_ctor_set(x_26, 5, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*6, x_25);
x_27 = l_Lean_Elab_Command_elabDefLike(x_26, x_3, x_4);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_9);
x_30 = lean_unsigned_to_nat(3u);
x_31 = l_Lean_Syntax_getArg(x_2, x_30);
x_32 = 0;
x_33 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_11);
lean_ctor_set(x_33, 2, x_28);
lean_ctor_set(x_33, 3, x_8);
lean_ctor_set(x_33, 4, x_29);
lean_ctor_set(x_33, 5, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*6, x_32);
x_34 = l_Lean_Elab_Command_elabDefLike(x_33, x_3, x_4);
return x_34;
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_elabExample___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_example");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabExample___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabExample___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabExample(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_2, x_5);
x_7 = l_Lean_Elab_Command_expandDeclSig(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Elab_Command_elabExample___closed__2;
x_11 = l_Lean_mkIdentFrom(x_2, x_10);
x_12 = l_Lean_mkAppStx___closed__9;
x_13 = lean_array_push(x_12, x_11);
x_14 = l_Lean_mkOptionalNode___closed__1;
x_15 = lean_array_push(x_13, x_14);
x_16 = l_Lean_Parser_Command_declId___elambda__1___closed__2;
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_9);
x_19 = lean_unsigned_to_nat(2u);
x_20 = l_Lean_Syntax_getArg(x_2, x_19);
x_21 = 2;
x_22 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_1);
lean_ctor_set(x_22, 2, x_17);
lean_ctor_set(x_22, 3, x_8);
lean_ctor_set(x_22, 4, x_18);
lean_ctor_set(x_22, 5, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*6, x_21);
x_23 = l_Lean_Elab_Command_elabDefLike(x_22, x_3, x_4);
return x_23;
}
}
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_1);
x_11 = l_Lean_Elab_Term_elabType(x_1, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 0;
x_15 = lean_box(0);
lean_inc(x_9);
x_16 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_14, x_15, x_9, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_9);
x_18 = l_Lean_Elab_Term_instantiateMVars(x_1, x_12, x_9, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_9);
x_21 = l_Lean_Elab_Term_mkForall(x_1, x_8, x_19, x_9, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_9);
x_24 = l_Lean_Elab_Term_mkForallUsedOnly(x_1, x_2, x_22, x_9, x_23);
lean_dec(x_1);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_unsigned_to_nat(1u);
lean_inc(x_9);
x_29 = l_Lean_Elab_Term_levelMVarToParam(x_27, x_28, x_9, x_26);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Elab_Command_mkDef___lambda__1___closed__5;
lean_inc(x_33);
x_35 = l_Lean_CollectLevelParams_main___main(x_33, x_34);
x_36 = lean_ctor_get(x_35, 2);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_Elab_Command_sortDeclLevelParams(x_3, x_4, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_33);
lean_free_object(x_29);
lean_dec(x_6);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = l_Lean_Elab_Term_throwError___rarg(x_5, x_40, x_9, x_32);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_9);
x_42 = lean_ctor_get(x_37, 0);
lean_inc(x_42);
lean_dec(x_37);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_6);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_33);
x_44 = lean_ctor_get_uint8(x_7, sizeof(void*)*2 + 3);
x_45 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_44);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_29, 0, x_46);
return x_29;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_29, 0);
x_48 = lean_ctor_get(x_29, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_29);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_Elab_Command_mkDef___lambda__1___closed__5;
lean_inc(x_49);
x_51 = l_Lean_CollectLevelParams_main___main(x_49, x_50);
x_52 = lean_ctor_get(x_51, 2);
lean_inc(x_52);
lean_dec(x_51);
x_53 = l_Lean_Elab_Command_sortDeclLevelParams(x_3, x_4, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_49);
lean_dec(x_6);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = l_Lean_Elab_Term_throwError___rarg(x_5, x_56, x_9, x_48);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_9);
x_58 = lean_ctor_get(x_53, 0);
lean_inc(x_58);
lean_dec(x_53);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_6);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_49);
x_60 = lean_ctor_get_uint8(x_7, sizeof(void*)*2 + 3);
x_61 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_60);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_48);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_64 = !lean_is_exclusive(x_24);
if (x_64 == 0)
{
return x_24;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_24, 0);
x_66 = lean_ctor_get(x_24, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_24);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_21);
if (x_68 == 0)
{
return x_21;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_21, 0);
x_70 = lean_ctor_get(x_21, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_21);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_16);
if (x_72 == 0)
{
return x_16;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_16, 0);
x_74 = lean_ctor_get(x_16, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_16);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_11);
if (x_76 == 0)
{
return x_11;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_11, 0);
x_78 = lean_ctor_get(x_11, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_11);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Syntax_getArgs(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lambda__1___boxed), 10, 7);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_8);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
lean_closure_set(x_12, 4, x_5);
lean_closure_set(x_12, 5, x_6);
lean_closure_set(x_12, 6, x_7);
x_13 = l_Lean_Elab_Term_elabBinders___rarg(x_11, x_12, x_9, x_10);
lean_dec(x_11);
return x_13;
}
}
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
x_10 = l_Lean_Elab_Command_mkDeclName(x_1, x_2, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
x_33 = 2;
x_34 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc(x_11);
x_35 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_3, x_11, x_33, x_13, x_34, x_8, x_12);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
lean_inc(x_8);
x_37 = l_Lean_Elab_Command_getLevelNames(x_8, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_11);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_11);
lean_inc(x_11);
lean_inc(x_3);
x_41 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lambda__2___boxed), 10, 7);
lean_closure_set(x_41, 0, x_4);
lean_closure_set(x_41, 1, x_5);
lean_closure_set(x_41, 2, x_6);
lean_closure_set(x_41, 3, x_38);
lean_closure_set(x_41, 4, x_3);
lean_closure_set(x_41, 5, x_11);
lean_closure_set(x_41, 6, x_2);
lean_inc(x_8);
x_42 = l___private_Lean_Elab_Command_2__getState(x_8, x_39);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l___private_Lean_Elab_Command_9__getVarDecls(x_43);
lean_dec(x_43);
lean_inc(x_8);
x_46 = l___private_Lean_Elab_Command_2__getState(x_8, x_44);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l___private_Lean_Elab_Command_6__mkTermContext(x_8, x_47, x_40);
x_50 = l___private_Lean_Elab_Command_7__mkTermState(x_47);
lean_dec(x_47);
x_51 = l_Lean_Elab_Term_elabBinders___rarg(x_45, x_41, x_49, x_50);
lean_dec(x_45);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_8);
x_54 = l___private_Lean_Elab_Command_2__getState(x_8, x_48);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_ctor_get(x_53, 2);
lean_inc(x_59);
lean_dec(x_53);
x_60 = !lean_is_exclusive(x_56);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_56, 1);
lean_dec(x_61);
x_62 = lean_ctor_get(x_56, 0);
lean_dec(x_62);
lean_ctor_set(x_56, 1, x_59);
lean_ctor_set(x_56, 0, x_58);
lean_inc(x_8);
x_63 = l___private_Lean_Elab_Command_3__setState(x_56, x_8, x_57);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_14 = x_52;
x_15 = x_64;
goto block_32;
}
else
{
uint8_t x_65; 
lean_dec(x_52);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
return x_63;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_63, 0);
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_63);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_56, 2);
x_70 = lean_ctor_get(x_56, 3);
x_71 = lean_ctor_get(x_56, 4);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_56);
x_72 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_72, 0, x_58);
lean_ctor_set(x_72, 1, x_59);
lean_ctor_set(x_72, 2, x_69);
lean_ctor_set(x_72, 3, x_70);
lean_ctor_set(x_72, 4, x_71);
lean_inc(x_8);
x_73 = l___private_Lean_Elab_Command_3__setState(x_72, x_8, x_57);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_14 = x_52;
x_15 = x_74;
goto block_32;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_52);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_77 = x_73;
} else {
 lean_dec_ref(x_73);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_79 = !lean_is_exclusive(x_54);
if (x_79 == 0)
{
return x_54;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_54, 0);
x_81 = lean_ctor_get(x_54, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_54);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_51, 0);
lean_inc(x_83);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
x_84 = lean_ctor_get(x_51, 1);
lean_inc(x_84);
lean_dec(x_51);
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
lean_dec(x_83);
lean_inc(x_8);
x_86 = l___private_Lean_Elab_Command_2__getState(x_8, x_48);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_87 = lean_ctor_get(x_84, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = lean_ctor_get(x_87, 0);
lean_inc(x_90);
lean_dec(x_87);
x_91 = lean_ctor_get(x_84, 2);
lean_inc(x_91);
lean_dec(x_84);
x_92 = !lean_is_exclusive(x_88);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_88, 1);
lean_dec(x_93);
x_94 = lean_ctor_get(x_88, 0);
lean_dec(x_94);
lean_ctor_set(x_88, 1, x_91);
lean_ctor_set(x_88, 0, x_90);
x_95 = l___private_Lean_Elab_Command_3__setState(x_88, x_8, x_89);
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_95, 0);
lean_dec(x_97);
lean_ctor_set_tag(x_95, 1);
lean_ctor_set(x_95, 0, x_85);
return x_95;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_85);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
else
{
uint8_t x_100; 
lean_dec(x_85);
x_100 = !lean_is_exclusive(x_95);
if (x_100 == 0)
{
return x_95;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_95, 0);
x_102 = lean_ctor_get(x_95, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_95);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_ctor_get(x_88, 2);
x_105 = lean_ctor_get(x_88, 3);
x_106 = lean_ctor_get(x_88, 4);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_88);
x_107 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_107, 0, x_90);
lean_ctor_set(x_107, 1, x_91);
lean_ctor_set(x_107, 2, x_104);
lean_ctor_set(x_107, 3, x_105);
lean_ctor_set(x_107, 4, x_106);
x_108 = l___private_Lean_Elab_Command_3__setState(x_107, x_8, x_89);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_110 = x_108;
} else {
 lean_dec_ref(x_108);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
 lean_ctor_set_tag(x_111, 1);
}
lean_ctor_set(x_111, 0, x_85);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_85);
x_112 = lean_ctor_get(x_108, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_108, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_114 = x_108;
} else {
 lean_dec_ref(x_108);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_8);
x_116 = !lean_is_exclusive(x_86);
if (x_116 == 0)
{
return x_86;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_86, 0);
x_118 = lean_ctor_get(x_86, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_86);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_51);
x_120 = l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
x_121 = l_unreachable_x21___rarg(x_120);
lean_inc(x_8);
x_122 = lean_apply_2(x_121, x_8, x_48);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_14 = x_123;
x_15 = x_124;
goto block_32;
}
else
{
uint8_t x_125; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_125 = !lean_is_exclusive(x_122);
if (x_125 == 0)
{
return x_122;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_122, 0);
x_127 = lean_ctor_get(x_122, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_122);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_45);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_129 = !lean_is_exclusive(x_46);
if (x_129 == 0)
{
return x_46;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_46, 0);
x_131 = lean_ctor_get(x_46, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_46);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_133 = !lean_is_exclusive(x_42);
if (x_133 == 0)
{
return x_42;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_42, 0);
x_135 = lean_ctor_get(x_42, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_42);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_137 = !lean_is_exclusive(x_37);
if (x_137 == 0)
{
return x_37;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_37, 0);
x_139 = lean_ctor_get(x_37, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_37);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_141 = !lean_is_exclusive(x_35);
if (x_141 == 0)
{
return x_35;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_35, 0);
x_143 = lean_ctor_get(x_35, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_35);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
block_32:
{
lean_object* x_16; 
lean_inc(x_8);
x_16 = l_Lean_Elab_Command_addDecl(x_3, x_14, x_8, x_15);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = 0;
x_19 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc(x_11);
x_20 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_3, x_11, x_18, x_13, x_19, x_8, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = 1;
x_23 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_3, x_11, x_22, x_13, x_19, x_8, x_21);
lean_dec(x_13);
lean_dec(x_3);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
else
{
uint8_t x_145; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_145 = !lean_is_exclusive(x_10);
if (x_145 == 0)
{
return x_10;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_10, 0);
x_147 = lean_ctor_get(x_10, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_10);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabAxiom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_2, x_5);
x_7 = lean_unsigned_to_nat(2u);
x_8 = l_Lean_Syntax_getArg(x_2, x_7);
x_9 = l_Lean_Elab_Command_expandDeclSig(x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_3);
x_12 = l_Lean_Elab_Command_getLevelNames(x_3, x_4);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_6);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lambda__3___boxed), 9, 6);
lean_closure_set(x_15, 0, x_6);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_10);
lean_closure_set(x_15, 4, x_11);
lean_closure_set(x_15, 5, x_13);
x_16 = l_Lean_Elab_Command_withDeclId___rarg(x_6, x_15, x_3, x_14);
lean_dec(x_6);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Command_elabAxiom___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_5);
return x_11;
}
}
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Command_elabAxiom___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_elabAxiom___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of attributes in inductive declaration");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'partial' in inductive declaration");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'noncomputable' in inductive declaration");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 1);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 2);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_8, x_9);
if (x_5 == 0)
{
uint8_t x_53; 
x_53 = 0;
x_11 = x_53;
goto block_52;
}
else
{
uint8_t x_54; 
x_54 = 1;
x_11 = x_54;
goto block_52;
}
block_52:
{
uint8_t x_12; 
if (x_6 == 0)
{
uint8_t x_50; 
x_50 = 0;
x_12 = x_50;
goto block_49;
}
else
{
uint8_t x_51; 
x_51 = 1;
x_12 = x_51;
goto block_49;
}
block_49:
{
uint8_t x_13; 
if (x_10 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_dec_eq(x_8, x_41);
lean_dec(x_8);
if (x_42 == 0)
{
x_13 = x_10;
goto block_40;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_43 = l_Lean_Elab_Command_Attribute_inhabited;
x_44 = lean_array_get(x_43, x_7, x_9);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l_Lean_registerClassAttr___closed__2;
x_47 = lean_name_eq(x_45, x_46);
lean_dec(x_45);
x_13 = x_47;
goto block_40;
}
}
else
{
uint8_t x_48; 
lean_dec(x_8);
x_48 = 1;
x_13 = x_48;
goto block_40;
}
block_40:
{
uint8_t x_14; 
if (x_13 == 0)
{
uint8_t x_38; 
x_38 = 0;
x_14 = x_38;
goto block_37;
}
else
{
uint8_t x_39; 
x_39 = 1;
x_14 = x_39;
goto block_37;
}
block_37:
{
lean_object* x_15; 
if (x_11 == 0)
{
x_15 = x_4;
goto block_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__9;
x_32 = l_Lean_Elab_Command_throwError___rarg(x_1, x_31, x_3, x_4);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
return x_32;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
block_30:
{
if (x_12 == 0)
{
if (x_14 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__3;
x_17 = l_Lean_Elab_Command_throwError___rarg(x_1, x_16, x_3, x_15);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_3);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_15);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__6;
x_25 = l_Lean_Elab_Command_throwError___rarg(x_1, x_24, x_3, x_15);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of attributes in constructor declaration");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'unsafe' in constructor declaration");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'partial' in constructor declaration");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'noncomputable' in constructor declaration");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Declaration_2__checkValidCtorModifier(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; 
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 1);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 2);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 3);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_array_get_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_5 == 0)
{
uint8_t x_58; 
x_58 = 0;
x_12 = x_58;
goto block_57;
}
else
{
uint8_t x_59; 
x_59 = 1;
x_12 = x_59;
goto block_57;
}
block_57:
{
uint8_t x_13; 
if (x_6 == 0)
{
uint8_t x_55; 
x_55 = 0;
x_13 = x_55;
goto block_54;
}
else
{
uint8_t x_56; 
x_56 = 1;
x_13 = x_56;
goto block_54;
}
block_54:
{
uint8_t x_14; 
if (x_7 == 0)
{
uint8_t x_52; 
x_52 = 0;
x_14 = x_52;
goto block_51;
}
else
{
uint8_t x_53; 
x_53 = 1;
x_14 = x_53;
goto block_51;
}
block_51:
{
uint8_t x_15; 
if (x_11 == 0)
{
uint8_t x_49; 
x_49 = 1;
x_15 = x_49;
goto block_48;
}
else
{
uint8_t x_50; 
x_50 = 0;
x_15 = x_50;
goto block_48;
}
block_48:
{
uint8_t x_16; 
if (x_15 == 0)
{
uint8_t x_46; 
x_46 = 0;
x_16 = x_46;
goto block_45;
}
else
{
uint8_t x_47; 
x_47 = 1;
x_16 = x_47;
goto block_45;
}
block_45:
{
lean_object* x_17; 
if (x_12 == 0)
{
if (x_13 == 0)
{
x_17 = x_4;
goto block_32;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__9;
x_34 = l_Lean_Elab_Command_throwError___rarg(x_1, x_33, x_3, x_4);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__12;
x_40 = l_Lean_Elab_Command_throwError___rarg(x_1, x_39, x_3, x_4);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_40);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
block_32:
{
if (x_14 == 0)
{
if (x_16 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__3;
x_21 = l_Lean_Elab_Command_throwError___rarg(x_1, x_20, x_3, x_17);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_21);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__6;
x_27 = l_Lean_Elab_Command_throwError___rarg(x_1, x_26, x_3, x_17);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Declaration_2__checkValidCtorModifier(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'protected' constructor in a 'private' inductive datatype");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'private' constructor in a 'private' inductive datatype");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = x_4;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_array_fget(x_4, x_3);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_fset(x_4, x_3, x_12);
x_14 = x_11;
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_getArg(x_14, x_15);
lean_inc(x_5);
x_17 = l_Lean_Elab_Command_elabModifiers(x_16, x_5, x_6);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_Command_Modifiers_isPrivate(x_18);
x_21 = l_Lean_Elab_Command_Modifiers_isProtected(x_18);
x_22 = lean_unsigned_to_nat(2u);
x_23 = l_Lean_Syntax_getIdAt(x_14, x_22);
x_24 = l_Lean_Name_append___main(x_2, x_23);
x_25 = l_Lean_Syntax_getArg(x_14, x_22);
x_26 = lean_ctor_get_uint8(x_18, sizeof(void*)*2);
if (x_20 == 0)
{
uint8_t x_88; 
x_88 = 0;
x_27 = x_88;
goto block_87;
}
else
{
uint8_t x_89; 
x_89 = l_Lean_Elab_Command_Modifiers_isPrivate(x_1);
x_27 = x_89;
goto block_87;
}
block_87:
{
uint8_t x_28; 
if (x_27 == 0)
{
uint8_t x_85; 
x_85 = 0;
x_28 = x_85;
goto block_84;
}
else
{
uint8_t x_86; 
x_86 = 1;
x_28 = x_86;
goto block_84;
}
block_84:
{
uint8_t x_29; 
if (x_21 == 0)
{
uint8_t x_82; 
x_82 = 0;
x_29 = x_82;
goto block_81;
}
else
{
uint8_t x_83; 
x_83 = l_Lean_Elab_Command_Modifiers_isPrivate(x_1);
x_29 = x_83;
goto block_81;
}
block_81:
{
uint8_t x_30; 
if (x_29 == 0)
{
uint8_t x_79; 
x_79 = 0;
x_30 = x_79;
goto block_78;
}
else
{
uint8_t x_80; 
x_80 = 1;
x_30 = x_80;
goto block_78;
}
block_78:
{
if (x_28 == 0)
{
if (x_30 == 0)
{
lean_object* x_31; 
lean_inc(x_5);
x_31 = l___private_Lean_Elab_Declaration_2__checkValidCtorModifier(x_14, x_18, x_5, x_19);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
lean_inc(x_5);
x_33 = l_Lean_Elab_Command_applyVisibility(x_25, x_26, x_24, x_5, x_32);
lean_dec(x_25);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_unsigned_to_nat(3u);
x_37 = l_Lean_Syntax_getArg(x_14, x_36);
x_38 = l_Lean_Syntax_isNone(x_37);
lean_dec(x_37);
x_39 = lean_unsigned_to_nat(4u);
x_40 = l_Lean_Syntax_getArg(x_14, x_39);
x_41 = l_Lean_Elab_Command_expandOptDeclSig(x_40);
lean_dec(x_40);
if (x_38 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = 1;
x_45 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_45, 0, x_14);
lean_ctor_set(x_45, 1, x_18);
lean_ctor_set(x_45, 2, x_34);
lean_ctor_set(x_45, 3, x_42);
lean_ctor_set(x_45, 4, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*5, x_44);
x_46 = lean_nat_add(x_3, x_15);
x_47 = x_45;
x_48 = lean_array_fset(x_13, x_3, x_47);
lean_dec(x_3);
x_3 = x_46;
x_4 = x_48;
x_6 = x_35;
goto _start;
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_41, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_41, 1);
lean_inc(x_51);
lean_dec(x_41);
x_52 = 0;
x_53 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_53, 0, x_14);
lean_ctor_set(x_53, 1, x_18);
lean_ctor_set(x_53, 2, x_34);
lean_ctor_set(x_53, 3, x_50);
lean_ctor_set(x_53, 4, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*5, x_52);
x_54 = lean_nat_add(x_3, x_15);
x_55 = x_53;
x_56 = lean_array_fset(x_13, x_3, x_55);
lean_dec(x_3);
x_3 = x_54;
x_4 = x_56;
x_6 = x_35;
goto _start;
}
}
else
{
uint8_t x_58; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_3);
x_58 = !lean_is_exclusive(x_33);
if (x_58 == 0)
{
return x_33;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_33, 0);
x_60 = lean_ctor_get(x_33, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_33);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_3);
x_62 = !lean_is_exclusive(x_31);
if (x_62 == 0)
{
return x_31;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_31, 0);
x_64 = lean_ctor_get(x_31, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_31);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_3);
x_66 = l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__3;
x_67 = l_Lean_Elab_Command_throwError___rarg(x_14, x_66, x_5, x_19);
lean_dec(x_14);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
return x_67;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_67);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_3);
x_72 = l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__6;
x_73 = l_Lean_Elab_Command_throwError___rarg(x_14, x_72, x_5, x_19);
lean_dec(x_14);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
return x_73;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_73);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_3);
x_90 = !lean_is_exclusive(x_17);
if (x_90 == 0)
{
return x_17;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_17, 0);
x_92 = lean_ctor_get(x_17, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_17);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
x_10 = l_Lean_Elab_Command_getLevelNames(x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
x_13 = l_Lean_Elab_Command_mkDeclName(x_1, x_2, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_nat_add(x_3, x_16);
x_18 = l_Lean_Syntax_getArg(x_4, x_17);
lean_dec(x_17);
x_19 = l_Lean_Syntax_getArgs(x_18);
lean_dec(x_18);
x_20 = x_19;
x_21 = lean_unsigned_to_nat(0u);
lean_inc(x_14);
lean_inc(x_2);
x_22 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___boxed), 6, 4);
lean_closure_set(x_22, 0, x_2);
lean_closure_set(x_22, 1, x_14);
lean_closure_set(x_22, 2, x_21);
lean_closure_set(x_22, 3, x_20);
x_23 = x_22;
x_24 = lean_apply_2(x_23, x_8, x_15);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_2);
lean_ctor_set(x_27, 2, x_7);
lean_ctor_set(x_27, 3, x_14);
lean_ctor_set(x_27, 4, x_11);
lean_ctor_set(x_27, 5, x_5);
lean_ctor_set(x_27, 6, x_6);
lean_ctor_set(x_27, 7, x_26);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
x_30 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_2);
lean_ctor_set(x_30, 2, x_7);
lean_ctor_set(x_30, 3, x_14);
lean_ctor_set(x_30, 4, x_11);
lean_ctor_set(x_30, 5, x_5);
lean_ctor_set(x_30, 6, x_6);
lean_ctor_set(x_30, 7, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
return x_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_24, 0);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_24);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_13);
if (x_36 == 0)
{
return x_13;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_13, 0);
x_38 = lean_ctor_get(x_13, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_13);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_10);
if (x_40 == 0)
{
return x_10;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_10, 0);
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_10);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
lean_object* l___private_Lean_Elab_Declaration_3__inductiveSyntaxToView(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_3, x_6);
x_8 = l_Lean_Syntax_getArg(x_2, x_7);
lean_dec(x_7);
x_9 = l_Lean_Elab_Command_expandOptDeclSig(x_8);
lean_dec(x_8);
lean_inc(x_4);
x_10 = l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier(x_2, x_1, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = l_Lean_Syntax_getArg(x_2, x_3);
lean_inc(x_14);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___lambda__1___boxed), 9, 6);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_2);
lean_closure_set(x_15, 4, x_12);
lean_closure_set(x_15, 5, x_13);
x_16 = l_Lean_Elab_Command_withDeclId___rarg(x_14, x_15, x_4, x_11);
lean_dec(x_14);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Declaration_4__classInductiveSyntaxToView(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(2u);
x_6 = l___private_Lean_Elab_Declaration_3__inductiveSyntaxToView(x_1, x_2, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_elabInductive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(1u);
lean_inc(x_3);
x_6 = l___private_Lean_Elab_Declaration_3__inductiveSyntaxToView(x_1, x_2, x_5, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_mkOptionalNode___closed__2;
x_10 = lean_array_push(x_9, x_7);
x_11 = l_Lean_Elab_Command_elabInductiveCore(x_10, x_3, x_8);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_3);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_elabClassInductive___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_registerClassAttr___closed__2;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabClassInductive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_Elab_Command_elabClassInductive___closed__1;
x_6 = l_Lean_Elab_Command_Modifiers_addAttribute(x_1, x_5);
x_7 = lean_unsigned_to_nat(2u);
lean_inc(x_3);
x_8 = l___private_Lean_Elab_Declaration_3__inductiveSyntaxToView(x_6, x_2, x_7, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_mkOptionalNode___closed__2;
x_12 = lean_array_push(x_11, x_9);
x_13 = l_Lean_Elab_Command_elabInductiveCore(x_12, x_3, x_10);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_elabDeclaration___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected declaration");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabDeclaration___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabDeclaration___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabDeclaration___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabDeclaration___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabDeclaration(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
lean_inc(x_2);
x_6 = l_Lean_Elab_Command_elabModifiers(x_5, x_2, x_3);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_inc(x_11);
x_12 = l_Lean_Syntax_getKind(x_11);
x_13 = l_Lean_Parser_Command_abbrev___elambda__1___closed__2;
x_14 = lean_name_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Parser_Command_def___elambda__1___closed__2;
x_16 = lean_name_eq(x_12, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Parser_Command_theorem___elambda__1___closed__2;
x_18 = lean_name_eq(x_12, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_Parser_Command_constant___elambda__1___closed__2;
x_20 = lean_name_eq(x_12, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_Parser_Command_instance___elambda__1___closed__2;
x_22 = lean_name_eq(x_12, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_Parser_Command_axiom___elambda__1___closed__2;
x_24 = lean_name_eq(x_12, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_Parser_Command_example___elambda__1___closed__2;
x_26 = lean_name_eq(x_12, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_Parser_Command_inductive___elambda__1___closed__2;
x_28 = lean_name_eq(x_12, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lean_Parser_Command_classInductive___elambda__1___closed__2;
x_30 = lean_name_eq(x_12, x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
lean_dec(x_11);
lean_dec(x_8);
x_31 = l_Lean_Parser_Command_structure___elambda__1___closed__2;
x_32 = lean_name_eq(x_12, x_31);
lean_dec(x_12);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_free_object(x_6);
x_33 = l_Lean_Elab_Command_elabDeclaration___closed__3;
x_34 = l_Lean_Elab_Command_throwError___rarg(x_1, x_33, x_2, x_9);
return x_34;
}
else
{
lean_object* x_35; 
lean_dec(x_2);
x_35 = lean_box(0);
lean_ctor_set(x_6, 0, x_35);
return x_6;
}
}
else
{
lean_object* x_36; 
lean_dec(x_12);
lean_free_object(x_6);
x_36 = l_Lean_Elab_Command_elabClassInductive(x_8, x_11, x_2, x_9);
return x_36;
}
}
else
{
lean_object* x_37; 
lean_dec(x_12);
lean_free_object(x_6);
x_37 = l_Lean_Elab_Command_elabInductive(x_8, x_11, x_2, x_9);
return x_37;
}
}
else
{
lean_object* x_38; 
lean_dec(x_12);
lean_free_object(x_6);
x_38 = l_Lean_Elab_Command_elabExample(x_8, x_11, x_2, x_9);
return x_38;
}
}
else
{
lean_object* x_39; 
lean_dec(x_12);
lean_free_object(x_6);
x_39 = l_Lean_Elab_Command_elabAxiom(x_8, x_11, x_2, x_9);
return x_39;
}
}
else
{
lean_object* x_40; 
lean_dec(x_12);
lean_free_object(x_6);
x_40 = l_Lean_Elab_Command_elabInstance(x_8, x_11, x_2, x_9);
return x_40;
}
}
else
{
lean_object* x_41; 
lean_dec(x_12);
lean_free_object(x_6);
x_41 = l_Lean_Elab_Command_elabConstant(x_8, x_11, x_2, x_9);
return x_41;
}
}
else
{
lean_object* x_42; 
lean_dec(x_12);
lean_free_object(x_6);
x_42 = l_Lean_Elab_Command_elabTheorem(x_8, x_11, x_2, x_9);
return x_42;
}
}
else
{
lean_object* x_43; 
lean_dec(x_12);
lean_free_object(x_6);
x_43 = l_Lean_Elab_Command_elabDef(x_8, x_11, x_2, x_9);
return x_43;
}
}
else
{
lean_object* x_44; 
lean_dec(x_12);
lean_free_object(x_6);
x_44 = l_Lean_Elab_Command_elabAbbrev(x_8, x_11, x_2, x_9);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_45 = lean_ctor_get(x_6, 0);
x_46 = lean_ctor_get(x_6, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_6);
x_47 = lean_unsigned_to_nat(1u);
x_48 = l_Lean_Syntax_getArg(x_1, x_47);
lean_inc(x_48);
x_49 = l_Lean_Syntax_getKind(x_48);
x_50 = l_Lean_Parser_Command_abbrev___elambda__1___closed__2;
x_51 = lean_name_eq(x_49, x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = l_Lean_Parser_Command_def___elambda__1___closed__2;
x_53 = lean_name_eq(x_49, x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = l_Lean_Parser_Command_theorem___elambda__1___closed__2;
x_55 = lean_name_eq(x_49, x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = l_Lean_Parser_Command_constant___elambda__1___closed__2;
x_57 = lean_name_eq(x_49, x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = l_Lean_Parser_Command_instance___elambda__1___closed__2;
x_59 = lean_name_eq(x_49, x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = l_Lean_Parser_Command_axiom___elambda__1___closed__2;
x_61 = lean_name_eq(x_49, x_60);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = l_Lean_Parser_Command_example___elambda__1___closed__2;
x_63 = lean_name_eq(x_49, x_62);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = l_Lean_Parser_Command_inductive___elambda__1___closed__2;
x_65 = lean_name_eq(x_49, x_64);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = l_Lean_Parser_Command_classInductive___elambda__1___closed__2;
x_67 = lean_name_eq(x_49, x_66);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
lean_dec(x_48);
lean_dec(x_45);
x_68 = l_Lean_Parser_Command_structure___elambda__1___closed__2;
x_69 = lean_name_eq(x_49, x_68);
lean_dec(x_49);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = l_Lean_Elab_Command_elabDeclaration___closed__3;
x_71 = l_Lean_Elab_Command_throwError___rarg(x_1, x_70, x_2, x_46);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_2);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_46);
return x_73;
}
}
else
{
lean_object* x_74; 
lean_dec(x_49);
x_74 = l_Lean_Elab_Command_elabClassInductive(x_45, x_48, x_2, x_46);
return x_74;
}
}
else
{
lean_object* x_75; 
lean_dec(x_49);
x_75 = l_Lean_Elab_Command_elabInductive(x_45, x_48, x_2, x_46);
return x_75;
}
}
else
{
lean_object* x_76; 
lean_dec(x_49);
x_76 = l_Lean_Elab_Command_elabExample(x_45, x_48, x_2, x_46);
return x_76;
}
}
else
{
lean_object* x_77; 
lean_dec(x_49);
x_77 = l_Lean_Elab_Command_elabAxiom(x_45, x_48, x_2, x_46);
return x_77;
}
}
else
{
lean_object* x_78; 
lean_dec(x_49);
x_78 = l_Lean_Elab_Command_elabInstance(x_45, x_48, x_2, x_46);
return x_78;
}
}
else
{
lean_object* x_79; 
lean_dec(x_49);
x_79 = l_Lean_Elab_Command_elabConstant(x_45, x_48, x_2, x_46);
return x_79;
}
}
else
{
lean_object* x_80; 
lean_dec(x_49);
x_80 = l_Lean_Elab_Command_elabTheorem(x_45, x_48, x_2, x_46);
return x_80;
}
}
else
{
lean_object* x_81; 
lean_dec(x_49);
x_81 = l_Lean_Elab_Command_elabDef(x_45, x_48, x_2, x_46);
return x_81;
}
}
else
{
lean_object* x_82; 
lean_dec(x_49);
x_82 = l_Lean_Elab_Command_elabAbbrev(x_45, x_48, x_2, x_46);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_6);
if (x_83 == 0)
{
return x_6;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_6, 0);
x_85 = lean_ctor_get(x_6, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_6);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabDeclaration___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabDeclaration(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDeclaration___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_declaration___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_Declaration_5__isMutualInductive___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_7, x_8);
lean_dec(x_7);
x_10 = l_Lean_Syntax_getKind(x_9);
x_11 = l_Lean_Parser_Command_inductive___elambda__1___closed__2;
x_12 = lean_name_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_4);
x_13 = 1;
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_nat_add(x_4, x_8);
lean_dec(x_4);
x_4 = x_14;
goto _start;
}
}
}
}
uint8_t l___private_Lean_Elab_Declaration_5__isMutualInductive(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getArgs(x_3);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_Declaration_5__isMutualInductive___spec__1(x_1, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_Declaration_5__isMutualInductive___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_Declaration_5__isMutualInductive___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Declaration_5__isMutualInductive___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Declaration_5__isMutualInductive(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_6__elabMutualInductive___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = x_2;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_array_fget(x_2, x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_fset(x_2, x_1, x_10);
x_12 = x_9;
x_13 = l_Lean_Syntax_getArg(x_12, x_10);
lean_inc(x_3);
x_14 = l_Lean_Elab_Command_elabModifiers(x_13, x_3, x_4);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_12, x_17);
lean_dec(x_12);
lean_inc(x_3);
x_19 = l___private_Lean_Elab_Declaration_3__inductiveSyntaxToView(x_15, x_18, x_17, x_3, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_nat_add(x_1, x_17);
x_23 = x_20;
x_24 = lean_array_fset(x_11, x_1, x_23);
lean_dec(x_1);
x_1 = x_22;
x_2 = x_24;
x_4 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_14);
if (x_30 == 0)
{
return x_14;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_14, 0);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_14);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Declaration_6__elabMutualInductive(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = x_1;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_6__elabMutualInductive___spec__1), 4, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_4);
x_7 = x_6;
lean_inc(x_2);
x_8 = lean_apply_2(x_7, x_2, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Elab_Command_elabInductiveCore(x_9, x_2, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
uint8_t l___private_Lean_Elab_Declaration_7__isMutualPreambleCommand(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Syntax_getKind(x_1);
x_3 = l_Lean_Parser_Command_variable___elambda__1___closed__2;
x_4 = lean_name_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Parser_Command_variables___elambda__1___closed__2;
x_6 = lean_name_eq(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Parser_Command_universe___elambda__1___closed__2;
x_8 = lean_name_eq(x_2, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Parser_Command_universes___elambda__1___closed__2;
x_10 = lean_name_eq(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Parser_Command_check___elambda__1___closed__2;
x_12 = lean_name_eq(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Parser_Command_set__option___elambda__1___closed__2;
x_14 = lean_name_eq(x_2, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Parser_Command_open___elambda__1___closed__2;
x_16 = lean_name_eq(x_2, x_15);
lean_dec(x_2);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_2);
x_17 = 1;
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_2);
x_18 = 1;
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_2);
x_19 = 1;
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_2);
x_20 = 1;
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_2);
x_21 = 1;
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_2);
x_22 = 1;
return x_22;
}
}
}
lean_object* l___private_Lean_Elab_Declaration_7__isMutualPreambleCommand___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Declaration_7__isMutualPreambleCommand(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Declaration_8__splitMutualPreamble___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget(x_1, x_2);
x_7 = l___private_Lean_Elab_Declaration_7__isMutualPreambleCommand(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Array_extract___rarg(x_1, x_8, x_2);
x_11 = l_Array_extract___rarg(x_1, x_2, x_3);
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_box(0);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
lean_dec(x_2);
x_2 = x_16;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_Declaration_8__splitMutualPreamble___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Declaration_8__splitMutualPreamble___main(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Declaration_8__splitMutualPreamble(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Declaration_8__splitMutualPreamble___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Declaration_8__splitMutualPreamble___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Declaration_8__splitMutualPreamble(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Parser_Command_section___elambda__1___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__2;
x_2 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Command_section___elambda__1___closed__2;
x_2 = l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Parser_Command_mutual___elambda__1___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__7;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__7;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__8;
x_2 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Command_end___elambda__1___closed__1;
x_2 = l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkOptionalNode___closed__2;
x_2 = l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkOptionalNode___closed__2;
x_2 = l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__10;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l___private_Lean_Elab_Declaration_8__splitMutualPreamble___main(x_6, x_7);
lean_dec(x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Array_empty___closed__1;
x_16 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_14, x_14, x_7, x_15);
lean_dec(x_14);
x_17 = l_Lean_nullKind___closed__2;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__6;
x_20 = lean_array_push(x_19, x_18);
x_21 = l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__7;
x_22 = lean_array_push(x_20, x_21);
x_23 = l_Lean_Parser_Command_mutual___elambda__1___closed__2;
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__11;
x_26 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_13, x_13, x_7, x_25);
lean_dec(x_13);
x_27 = l_Lean_mkOptionalNode___closed__2;
x_28 = lean_array_push(x_27, x_24);
x_29 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_28, x_28, x_7, x_26);
lean_dec(x_28);
x_30 = l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__12;
x_31 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_30, x_30, x_7, x_29);
x_32 = l_Lean_nullKind;
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_8, 0, x_33);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_8);
lean_ctor_set(x_34, 1, x_3);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_35 = lean_ctor_get(x_8, 0);
lean_inc(x_35);
lean_dec(x_8);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Array_empty___closed__1;
x_39 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_37, x_37, x_7, x_38);
lean_dec(x_37);
x_40 = l_Lean_nullKind___closed__2;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__6;
x_43 = lean_array_push(x_42, x_41);
x_44 = l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__7;
x_45 = lean_array_push(x_43, x_44);
x_46 = l_Lean_Parser_Command_mutual___elambda__1___closed__2;
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__11;
x_49 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_36, x_36, x_7, x_48);
lean_dec(x_36);
x_50 = l_Lean_mkOptionalNode___closed__2;
x_51 = lean_array_push(x_50, x_47);
x_52 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_51, x_51, x_7, x_49);
lean_dec(x_51);
x_53 = l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__12;
x_54 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_53, x_53, x_7, x_52);
x_55 = l_Lean_nullKind;
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_3);
return x_58;
}
}
}
}
lean_object* l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Command_elabMutual___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid mutual block");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabMutual___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabMutual___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabMutual___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabMutual___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabMutual(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = l_Lean_Elab_Command_getCurrMacroScope(x_2, x_3);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_2);
x_34 = l_Lean_Elab_Command_getEnv(x_2, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_2);
x_37 = l___private_Lean_Elab_Command_2__getState(x_2, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 3);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_environment_main_module(x_35);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_32);
x_43 = l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f(x_1, x_42, x_40);
lean_dec(x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_2);
x_46 = l___private_Lean_Elab_Command_2__getState(x_2, x_39);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 3);
lean_dec(x_50);
lean_ctor_set(x_47, 3, x_45);
lean_inc(x_2);
x_51 = l___private_Lean_Elab_Command_3__setState(x_47, x_2, x_48);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_4 = x_44;
x_5 = x_52;
goto block_30;
}
else
{
uint8_t x_53; 
lean_dec(x_44);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_51);
if (x_53 == 0)
{
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_51, 0);
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_51);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_47, 0);
x_58 = lean_ctor_get(x_47, 1);
x_59 = lean_ctor_get(x_47, 2);
x_60 = lean_ctor_get(x_47, 4);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_47);
x_61 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set(x_61, 1, x_58);
lean_ctor_set(x_61, 2, x_59);
lean_ctor_set(x_61, 3, x_45);
lean_ctor_set(x_61, 4, x_60);
lean_inc(x_2);
x_62 = l___private_Lean_Elab_Command_3__setState(x_61, x_2, x_48);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_4 = x_44;
x_5 = x_63;
goto block_30;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_44);
lean_dec(x_2);
lean_dec(x_1);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_66 = x_62;
} else {
 lean_dec_ref(x_62);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_46);
if (x_68 == 0)
{
return x_46;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_46, 0);
x_70 = lean_ctor_get(x_46, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_46);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_35);
lean_dec(x_32);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_37);
if (x_72 == 0)
{
return x_37;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_37, 0);
x_74 = lean_ctor_get(x_37, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_37);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_32);
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_34);
if (x_76 == 0)
{
return x_34;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_34, 0);
x_78 = lean_ctor_get(x_34, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_34);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
block_30:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_6; 
x_6 = l___private_Lean_Elab_Declaration_5__isMutualInductive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Elab_Command_elabMutual___closed__3;
x_8 = l_Lean_Elab_Command_throwError___rarg(x_1, x_7, x_2, x_5);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
lean_dec(x_1);
x_11 = l_Lean_Syntax_getArgs(x_10);
lean_dec(x_10);
x_12 = l___private_Lean_Elab_Declaration_6__elabMutualInductive(x_11, x_2, x_5);
return x_12;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
lean_dec(x_4);
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_2, 5);
lean_inc(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_13);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_2, 5, x_17);
x_18 = l_Lean_Elab_Command_elabCommand___main(x_13, x_2, x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get(x_2, 2);
x_22 = lean_ctor_get(x_2, 3);
x_23 = lean_ctor_get(x_2, 4);
x_24 = lean_ctor_get(x_2, 5);
x_25 = lean_ctor_get(x_2, 6);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_2);
lean_inc(x_13);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_13);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
x_28 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_20);
lean_ctor_set(x_28, 2, x_21);
lean_ctor_set(x_28, 3, x_22);
lean_ctor_set(x_28, 4, x_23);
lean_ctor_set(x_28, 5, x_27);
lean_ctor_set(x_28, 6, x_25);
x_29 = l_Lean_Elab_Command_elabCommand___main(x_13, x_28, x_5);
return x_29;
}
}
}
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMutual___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMutual), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_mutual___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabMutual___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_CollectLevelParams(lean_object*);
lean_object* initialize_Lean_Elab_Definition(lean_object*);
lean_object* initialize_Lean_Elab_Inductive(lean_object*);
lean_object* initialize_Lean_Elab_Structure(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Declaration(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectLevelParams(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Definition(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Inductive(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Structure(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_elabAbbrev___closed__1 = _init_l_Lean_Elab_Command_elabAbbrev___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabAbbrev___closed__1);
l_Lean_Elab_Command_elabAbbrev___closed__2 = _init_l_Lean_Elab_Command_elabAbbrev___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabAbbrev___closed__2);
l_Lean_Elab_Command_elabAbbrev___closed__3 = _init_l_Lean_Elab_Command_elabAbbrev___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabAbbrev___closed__3);
l_Lean_Elab_Command_elabAbbrev___closed__4 = _init_l_Lean_Elab_Command_elabAbbrev___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabAbbrev___closed__4);
l_Lean_Elab_Command_elabConstant___closed__1 = _init_l_Lean_Elab_Command_elabConstant___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabConstant___closed__1);
l_Lean_Elab_Command_elabConstant___closed__2 = _init_l_Lean_Elab_Command_elabConstant___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabConstant___closed__2);
l_Lean_Elab_Command_elabConstant___closed__3 = _init_l_Lean_Elab_Command_elabConstant___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabConstant___closed__3);
l_Lean_Elab_Command_elabConstant___closed__4 = _init_l_Lean_Elab_Command_elabConstant___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabConstant___closed__4);
l_Lean_Elab_Command_elabConstant___closed__5 = _init_l_Lean_Elab_Command_elabConstant___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabConstant___closed__5);
l_Lean_Elab_Command_elabConstant___closed__6 = _init_l_Lean_Elab_Command_elabConstant___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabConstant___closed__6);
l_Lean_Elab_Command_elabInstance___closed__1 = _init_l_Lean_Elab_Command_elabInstance___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabInstance___closed__1);
l_Lean_Elab_Command_elabInstance___closed__2 = _init_l_Lean_Elab_Command_elabInstance___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabInstance___closed__2);
l_Lean_Elab_Command_elabInstance___closed__3 = _init_l_Lean_Elab_Command_elabInstance___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabInstance___closed__3);
l_Lean_Elab_Command_elabInstance___closed__4 = _init_l_Lean_Elab_Command_elabInstance___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabInstance___closed__4);
l_Lean_Elab_Command_elabInstance___closed__5 = _init_l_Lean_Elab_Command_elabInstance___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabInstance___closed__5);
l_Lean_Elab_Command_elabExample___closed__1 = _init_l_Lean_Elab_Command_elabExample___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabExample___closed__1);
l_Lean_Elab_Command_elabExample___closed__2 = _init_l_Lean_Elab_Command_elabExample___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabExample___closed__2);
l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__1 = _init_l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__1);
l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__2 = _init_l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__2);
l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__3 = _init_l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__3);
l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__4 = _init_l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__4);
l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__5 = _init_l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__5);
l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__6 = _init_l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__6);
l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__7 = _init_l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__7);
l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__8 = _init_l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__8);
l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__9 = _init_l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Declaration_1__checkValidInductiveModifier___closed__9);
l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__1 = _init_l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__1);
l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__2 = _init_l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__2);
l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__3 = _init_l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__3);
l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__4 = _init_l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__4);
l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__5 = _init_l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__5);
l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__6 = _init_l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__6);
l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__7 = _init_l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__7);
l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__8 = _init_l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__8);
l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__9 = _init_l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__9);
l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__10 = _init_l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__10);
l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__11 = _init_l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__11);
l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__12 = _init_l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Declaration_2__checkValidCtorModifier___closed__12);
l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__1 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__1);
l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__2 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__2);
l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__3 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__3();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__3);
l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__4 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__4();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__4);
l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__5 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__5();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__5);
l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__6 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__6();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_3__inductiveSyntaxToView___spec__1___closed__6);
l_Lean_Elab_Command_elabClassInductive___closed__1 = _init_l_Lean_Elab_Command_elabClassInductive___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabClassInductive___closed__1);
l_Lean_Elab_Command_elabDeclaration___closed__1 = _init_l_Lean_Elab_Command_elabDeclaration___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabDeclaration___closed__1);
l_Lean_Elab_Command_elabDeclaration___closed__2 = _init_l_Lean_Elab_Command_elabDeclaration___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabDeclaration___closed__2);
l_Lean_Elab_Command_elabDeclaration___closed__3 = _init_l_Lean_Elab_Command_elabDeclaration___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabDeclaration___closed__3);
l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabDeclaration(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__1 = _init_l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__1);
l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__2 = _init_l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__2);
l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__3 = _init_l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__3);
l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__4 = _init_l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__4);
l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__5 = _init_l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__5);
l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__6 = _init_l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__6);
l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__7 = _init_l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__7);
l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__8 = _init_l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__8);
l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__9 = _init_l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__9);
l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__10 = _init_l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__10);
l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__11 = _init_l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__11);
l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__12 = _init_l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Declaration_9__expandMutualPreamble_x3f___closed__12);
l_Lean_Elab_Command_elabMutual___closed__1 = _init_l_Lean_Elab_Command_elabMutual___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabMutual___closed__1);
l_Lean_Elab_Command_elabMutual___closed__2 = _init_l_Lean_Elab_Command_elabMutual___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabMutual___closed__2);
l_Lean_Elab_Command_elabMutual___closed__3 = _init_l_Lean_Elab_Command_elabMutual___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabMutual___closed__3);
l___regBuiltin_Lean_Elab_Command_elabMutual___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabMutual___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMutual___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabMutual(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
