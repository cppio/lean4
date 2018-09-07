/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include <string>
#include "library/messages.h"
#include "util/task_builder.h"

namespace lean {

message::message(parser_exception const & ex) :
        message(ex.get_file_name(), *ex.get_pos(), ERROR, ex.get_msg()) {}

std::ostream & operator<<(std::ostream & out, message const & msg) {
    if (msg.get_severity() != INFORMATION) {
        out << msg.get_filename() << ":" << msg.get_pos().first << ":" << msg.get_pos().second << ": ";
        switch (msg.get_severity()) {
            case INFORMATION: break;
            case WARNING: out << "warning: "; break;
            case ERROR:   out << "error: ";   break;
        }
        if (!msg.get_caption().empty())
            out << msg.get_caption() << ":\n";
    }
    auto const & text = msg.get_text();
    out << text;
    if (!text.size() || text[text.size() - 1] != '\n')
        out << "\n";
    return out;
}

void report_message(message const & msg0) {
    lean_assert(global_message_log());
    *global_message_log() = cons(msg0, *global_message_log());
}

bool has_errors(message_log const & l) {
    for (auto const & m : l) {
        if (m.get_severity() == ERROR)
            return true;
    }
    return false;
}

LEAN_THREAD_PTR(message_log, g_message_log);

scope_message_log::scope_message_log(message_log * l) :
        flet<message_log *>(g_message_log, l) {}

message_log * global_message_log() {
    return g_message_log;
}
}
