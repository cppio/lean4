#pragma once

namespace lean {
void initialize_ir_jit();
void finalize_ir_jit();
namespace ir {
void * get_jit_compiled_symbol(environment const & env, name const & name);
}
}
