add_library(compiler OBJECT init_module.cpp ## New
  compiler util.cpp lcnf.cpp csimp.cpp elim_dead_let.cpp cse.cpp
  erase_irrelevant.cpp specialize.cpp compiler.cpp lambda_lifting.cpp
  extract_closed.cpp simp_app_args.cpp llnf.cpp ll_infer_type.cpp
  reduce_arity.cpp closed_term_cache.cpp
  export_attribute.cpp extern_attribute.cpp
  borrowed_annotation.cpp init_attribute.cpp eager_lambda_lifting.cpp
  struct_cases_on.cpp find_jp.cpp ir.cpp implemented_by_attribute.cpp
  ir_interpreter.cpp ir_jit.cpp llvm.cpp)

ExternalProject_add(xbyak
  PREFIX xbyak
  GIT_REPOSITORY https://github.com/herumi/xbyak
  GIT_TAG v7.22
  BUILD_IN_SOURCE ON
  INSTALL_COMMAND "")

ExternalProject_Get_Property(xbyak SOURCE_DIR)
target_include_directories(compiler PRIVATE "${SOURCE_DIR}")
