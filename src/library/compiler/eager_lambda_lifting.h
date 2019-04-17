/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "library/compiler/util.h"
namespace lean {
/** \brief Eager version of lambda lifting. See comment at eager_lambda_lifting.cpp. */
pair<environment, comp_decls> eager_lambda_lifting(environment env, comp_decls const & ds);
/* Return true iff `fn` is the name of an auxiliary function generated by `eager_lambda_lifting`. */
bool is_elambda_lifting_name(name fn);
};
