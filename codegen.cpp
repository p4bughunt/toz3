#include "codegen.h"

namespace TOZ3 {
Visitor::profile_t CodeGenToz3::init_apply(const IR::Node *node) {
    return Inspector::init_apply(node);
}

void CodeGenToz3::end_apply(const IR::Node *) {
    if (nullptr != outStream) {
        cstring res = builder->toString();
        *outStream << res.c_str();
        outStream->flush();
    }
}

bool CodeGenToz3::preorder(const IR::P4Program *p) {
    builder->append("from p4z3.expressions import *\n\n");
    builder->newline();
    builder->newline();
    builder->append("def p4_program(z3_reg):");
    builder->newline();

    // Start to visit the actual AST objects
    for (auto o: p->objects) {
        visit(o);

        /*        if (auto t = o->to<IR::Type_Declaration>()) {
                    auto decl_name = t->name.name;
                    builder->appendFormat(depth, "z3_reg.declare_global(\"%s\",
                       %s_py)", decl_name, decl_name);
                    builder->newline();
                }*/
    }
    builder->appendFormat(depth,
                        "return main_py if \"main_py\" in locals() else None");
    return false;
}

bool CodeGenToz3::preorder(const IR::P4Parser *p) {
    auto parser_name = p->name.name;

    builder->delim_comment(depth, "PARSER %s", parser_name);

    builder->append(depth, "def PARSER():");
    builder->newline();
    depth++;

    // output header
    builder->appendFormat(depth, "%s_args = [\n", parser_name);

    for (auto cp : p->getApplyParameters()->parameters) {
        builder->append(depth + 1, "");
        visit(cp);
        builder->append(",");
        builder->newline();
    }
    builder->append(depth, "]\n");
    builder->appendFormat(depth, "%s_py = P4Parser()", parser_name);
    builder->newline();
    builder->appendFormat(depth,
                          "%s_py.add_instance(z3_reg, \"%s_state\", %s_args)",
                          parser_name, parser_name, parser_name);
    builder->newline();
    builder->newline();

    builder->appendFormat(depth, "return %s_py", parser_name);
    builder->newline();

    depth--;
    builder->appendFormat(depth, "%s = PARSER()", parser_name);
    builder->newline();
    builder->newline();
    builder->appendFormat(depth,
                          "z3_reg.declare_global(\"control\", \"%s\", %s)",
                          parser_name,
                          parser_name);
    builder->delim_comment(depth, "END PARSER %s", parser_name);
    builder->newline();
    return false;
}

bool CodeGenToz3::preorder(const IR::P4Control *c) {
    auto ctrl_name = c->name.name;

    in_local_scope = true;
    builder->delim_comment(depth, "CONTROL %s", ctrl_name);

    builder->append(depth, "def CONTROL():");
    builder->newline();
    depth++;

    // output header
    builder->appendFormat(depth, "%s_args = [\n", ctrl_name);

    for (auto cp : c->getApplyParameters()->parameters) {
        builder->append(depth + 1, "(");
        visit(cp);
        builder->append("),");
        builder->newline();
    }
    builder->append(depth, "]\n");
    builder->appendFormat(depth, "%s_py = P4Control()", ctrl_name);
    builder->newline();
    builder->appendFormat(depth,
                          "%s_py.add_instance(z3_reg, \"%s_state\", %s_args)",
                          ctrl_name, ctrl_name, ctrl_name);
    builder->newline();
    builder->newline();

    /*
     * (1) Action
     * (2) Tables
     * (3) Instance Declarations
     */
    for (auto a : c->controlLocals) {
        visit(a);

        if (a->is<IR::Declaration_Variable>())
            builder->appendFormat(depth, "%s_py.add_stmt(stmt)", ctrl_name);
        else
            builder->appendFormat(depth,
                                  "%s_py.declare_local(\"%s\", %s_py)",
                                  ctrl_name,
                                  a->name.name,
                                  a->name.name);
        builder->newline();
        builder->newline();
    }

    /*
     * (3) Apply Part
     */
    builder->delim_comment(depth, "CONTROL %s APPLY", ctrl_name);
    visit(c->body);
    builder->appendFormat(depth, "%s_py.add_stmt(stmt)", ctrl_name);
    builder->newline();
    builder->appendFormat(depth, "return %s_py", ctrl_name);
    builder->newline();

    depth--;
    in_local_scope = false;
    builder->appendFormat(depth, "%s = CONTROL()", ctrl_name);
    builder->newline();
    builder->appendFormat(depth,
                          "z3_reg.declare_global(\"control\", \"%s\", %s)",
                          ctrl_name,
                          ctrl_name);
    builder->newline();

    builder->delim_comment(depth, "END CONTROL %s", ctrl_name);
    builder->newline();

    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Extern *t) {
    auto extern_name = t->name.name;

    builder->delim_comment(depth, "EXTERN %s", extern_name);
    builder->appendFormat(depth,
                          "%s_py = P4Extern(\"%s\", z3_reg)",
                          extern_name,
                          extern_name);
    builder->newline();

    for (auto param : t->typeParameters->parameters) {
        builder->appendFormat(depth, "%s_py.add_parameter(", extern_name);
        visit(param);
        builder->append(")");
        builder->newline();
    }

    for (auto m : t->methods) {
        // top part
        in_local_scope = true;
        builder->append(depth, "def INTERNAL_METHOD():");
        builder->newline();
        depth++;
        visit(m);
        builder->appendFormat(depth, "return %s_py", m->name.name);
        builder->newline();
        in_local_scope = false;
        depth--;
        builder->appendFormat(depth,
                                                             "%s_py.add_method",
                              extern_name);
        builder->appendFormat("(\"%s\", INTERNAL_METHOD())", m->name.name);
        builder->newline();
    }
    builder->appendFormat(depth,
                          "z3_reg.declare_global(\"extern\", \"%s\", %s_py)",
                          extern_name,
                          extern_name);
    builder->newline();
    builder->delim_comment(depth, "END EXTERN %s", extern_name);
    builder->newline();
    return false;
}

bool CodeGenToz3::preorder(const IR::Method *t) {
    auto method_name = t->name.name;

    builder->delim_comment(depth, "METHOD %s ", method_name);
    builder->appendFormat(depth,
                          "%s_py = P4Extern(\"%s\", z3_reg, ",
                          method_name,
                          method_name);
    visit(t->type->returnType);
    builder->append(")");
    builder->newline();

    for (auto param : t->getParameters()->parameters) {
        builder->appendFormat(depth, "%s_py.add_parameter(", method_name);
        visit(param);
        builder->append(")");
        builder->newline();
    }

    if (!in_local_scope) {
        builder->appendFormat(depth,
                              "z3_reg.declare_global(\"method\", \"%s\", %s_py)",
                              method_name,
                              method_name);
        builder->newline();
    }
    builder->delim_comment(depth, "END METHOD %s", method_name);
    return false;
}

bool CodeGenToz3::preorder(const IR::Function *function) {
    auto function_name = function->name.name;

    builder->delim_comment(depth, "FUNCTION %s", function_name);
    builder->appendFormat(depth, "%s_py = P4Function(", function_name);
    visit(function->type->returnType);
    builder->append(")");
    builder->newline();

    for (auto param : function->getParameters()->parameters) {
        builder->appendFormat(depth, "%s_py.add_parameter(", function_name);
        visit(param);
        builder->append(")");
        builder->newline();
    }

    // body BlockStatement
    visit(function->body);

    builder->appendFormat(depth, "%s_py.add_stmt(stmt)", function_name);
    builder->newline();
    builder->appendFormat(depth,
                          "z3_reg.declare_global(\"function\", \"%s\", %s_py)",
                          function_name,
                          function_name);
    builder->newline();
    builder->delim_comment(depth, "END FUNCTION %s", function_name);
    builder->newline();
    return false;
}

bool CodeGenToz3::preorder(const IR::P4Action *p4action) {
    auto action_name = p4action->name.name;

    builder->delim_comment(depth, "ACTION %s", action_name);
    builder->appendFormat(depth, "%s_py = P4Action()", action_name);
    builder->newline();

    for (auto param : p4action->parameters->parameters) {
        builder->appendFormat(depth, "%s_py.add_parameter(", action_name);
        visit(param);
        builder->append(")");
        builder->newline();
    }

    // body BlockStatement
    visit(p4action->body);

    builder->appendFormat(depth, "%s_py.add_stmt(stmt)", action_name);
    builder->newline();

    if (!in_local_scope) {
        builder->appendFormat(depth,
                              "z3_reg.declare_global(\"p4action\", \"%s\", %s_py)",
                              action_name,
                              action_name);
        builder->newline();
    }
    builder->delim_comment(depth, "END ACTION %s", action_name);
    builder->newline();
    return false;
}

bool CodeGenToz3::preorder(const IR::P4Table *p4table) {
    tab_name = p4table->name.name;
    builder->delim_comment(depth, "TABLE %s", tab_name);
    builder->appendFormat(depth, "%s_py = P4Table(\"%s\")", tab_name, tab_name);
    builder->newline();

    for (auto p : p4table->properties->properties) {
        // IR::Property
        visit(p);
    }
    builder->delim_comment(depth, "END TABLE %s", tab_name);
    builder->newline();
    return false;
}

bool CodeGenToz3::preorder(const IR::Property *p) {
    // Tao: a trick here
    if ((table_skips.find(p->name.name) != table_skips.end()))
        // skip it
        return false;

    if (p->name.name == "default_action") {
        builder->appendFormat(depth, "%s_py.add_default(", tab_name);
        visit(p->value);
        builder->append(")");
        builder->newline();
    } else {
        visit(p->value);
    }
    return false;
}

bool CodeGenToz3::preorder(const IR::ActionList *acl) {
    // Tao: a trick here
    for (auto act: acl->actionList) {
        bool ignore_default = false;

        for (const auto *anno : act->getAnnotations()->annotations) {
            if (anno->name.name == "defaultonly") {
                ignore_default = true;
            }
        }

        if (ignore_default)
            continue;

        builder->appendFormat(depth, "%s_py.add_action(", tab_name);
        visit(act->expression);
        builder->append(")");
        builder->newline();
    }
    builder->newline();
    return false;
}

bool CodeGenToz3::preorder(const IR::Entry *e) {
    // Tao: a trick here
    visit(e->keys);
    builder->append(", ");
    visit(e->action);
    builder->newline();
    return false;
}

bool CodeGenToz3::preorder(const IR::EntriesList *el) {
    // Tao: a trick here
    for (auto entry: el->entries) {
        builder->appendFormat(depth, "%s_py.add_const_entry(", tab_name);
        visit(entry);
        builder->append(")");
        builder->newline();
    }
    builder->newline();
    return false;
}

bool CodeGenToz3::preorder(const IR::Key *key) {
    for (auto ke : key->keyElements) {
        builder->append(depth, "table_key = ");
        visit(ke->expression);
        builder->newline();
        builder->appendFormat(depth, "%s_py.add_match(table_key)",
                              tab_name);
        builder->newline();
    }
    builder->newline();
    return false;
}

bool CodeGenToz3::preorder(const IR::KeyElement *ke) {
    visit(ke->expression);
    return false;
}

bool CodeGenToz3::preorder(const IR::ExpressionValue *ev) {
    visit(ev->expression);
    return false;
}

bool CodeGenToz3::preorder(const IR::MethodCallExpression *mce) {
    if (!is_inswitchstmt) {
        builder->append("MethodCallExpr(");
        visit(mce->method);
        builder->append(", ");

        for (auto arg : *mce->arguments) {
            visit(arg);
            builder->append(", ");
        }
        builder->append(")");
    }
    else {
        key_words.insert("apply");
        visit(mce->method);
        key_words.erase("apply");
    }

    return false;
}

bool CodeGenToz3::preorder(const IR::ListExpression *le) {
    bool first = true;

    builder->append("[");

    for (auto e : le->components) {
        if (!first)
            builder->append(", ");
        first = false;
        visit(e);
    }
    builder->append("]");
    return false;
}

bool CodeGenToz3::preorder(const IR::BlockStatement *b) {
    // top part
    builder->append(depth, "def BLOCK():");
    builder->newline();
    depth++;
    builder->append(depth, "block = BlockStatement()");
    builder->newline();

    // body part
    for (auto c : b->components) {
        visit(c);
        builder->append(depth, "block.add(stmt)");
        builder->newline();
    }

    // bot part
    builder->append(depth, "return block");
    builder->newline();
    depth--;

    builder->append(depth, "stmt = BLOCK()");
    builder->newline();

    return false;
}

bool CodeGenToz3::preorder(const IR::EmptyStatement *) {
    builder->append(depth, "stmt = P4Noop()");
    builder->newline();
    return false;
}

bool CodeGenToz3::preorder(const IR::ExitStatement *) {
    builder->append(depth, "stmt = P4Exit()");
    builder->newline();
    return false;
}

bool CodeGenToz3::preorder(const IR::ReturnStatement *r) {
    // TODO: Make this a proper return statement
    builder->append(depth, "stmt = P4Return(");
    visit(r->expression);
    builder->append(")");
    builder->newline();
    return false;
}

bool CodeGenToz3::preorder(const IR::AssignmentStatement *as) {
    builder->append(depth, "lval = ");

    // Tao: slice assignment
    if (as->left->is<IR::Slice>())
        visit(as->left->to<IR::Slice>()->e0);
    else
        visit(as->left);
    builder->newline();
    builder->append(depth, "rval = ");
    visit(as->right);
    builder->newline();

    // Tao: slice assignment
    if (auto sl = as->left->to<IR::Slice>()) {
        builder->append(depth, "stmt = SliceAssignment(lval, rval, ");
        builder->appendFormat("%d, %d)", sl->getH(), sl->getL());
        builder->newline();
    }
    else {
        builder->append(depth, "stmt = AssignmentStatement(lval, rval)");
        builder->newline();
    }
    return false;
}

bool CodeGenToz3::preorder(const IR::MethodCallStatement *mcs) {
    builder->append(depth, "stmt = MethodCallStmt(");
    visit(mcs->methodCall);
    builder->append(")");
    builder->newline();
    return false;
}

bool CodeGenToz3::preorder(const IR::IfStatement *ifs) {
    builder->append(depth, "def IF_BLOCK():\n");
    depth++;
    builder->append(depth, "if_block = IfStatement()\n");

    // basically, ifs->condition is an expression
    builder->append(depth, "condition = ");
    visit(ifs->condition);
    builder->newline();
    builder->append(depth, "if_block.add_condition(condition)\n\n\n");

    visit(ifs->ifTrue);
    builder->append(depth, "if_block.add_then_stmt(stmt)\n\n\n");

    if (ifs->ifFalse != nullptr) {
        visit(ifs->ifFalse);
        builder->append(depth, "if_block.add_else_stmt(stmt)\n\n\n");
    }
    builder->append(depth, "return if_block\n");
    depth--;
    builder->append(depth, "stmt = IF_BLOCK()\n\n");

    return false;
}

void CodeGenToz3::visit_unary(const IR::Operation_Unary *expr) {
    builder->append("(");
    visit(expr->expr);
    builder->append(")");
}

void CodeGenToz3::visit_binary(const IR::Operation_Binary *expr) {
    builder->append("(");
    visit(expr->left);
    builder->append(", ");
    visit(expr->right);
    builder->append(")");
}

void CodeGenToz3::visit_ternary(const IR::Operation_Ternary *expr) {
    builder->append("(");
    visit(expr->e0);
    builder->append(", ");
    visit(expr->e1);
    builder->append(", ");
    visit(expr->e2);
    builder->append(")");
}

bool CodeGenToz3::preorder(const IR::Neg *expr) {
    builder->append("P4neg");
    visit_unary(expr);
    return false;
}

bool CodeGenToz3::preorder(const IR::Cmpl *expr) {
    builder->append("P4inv");
    visit_unary(expr);
    return false;
}

bool CodeGenToz3::preorder(const IR::LNot *expr) {
    builder->append("P4not");
    visit_unary(expr);
    return false;
}

bool CodeGenToz3::preorder(const IR::Mul *expr) {
    builder->append("P4mul");
    visit_binary(expr);
    return false;
}

bool CodeGenToz3::preorder(const IR::Div *expr) {
    builder->append("P4div");
    visit_binary(expr);
    return false;
}

bool CodeGenToz3::preorder(const IR::Mod *expr) {
    builder->append("P4mod");
    visit_binary(expr);
    return false;
}

bool CodeGenToz3::preorder(const IR::Add *expr) {
    builder->append("P4add");
    visit_binary(expr);
    return false;
}

bool CodeGenToz3::preorder(const IR::AddSat *expr) {
    builder->append("P4addsat");
    visit_binary(expr);
    return false;
}

bool CodeGenToz3::preorder(const IR::Sub *expr) {
    builder->append("P4sub");
    visit_binary(expr);
    return false;
}

bool CodeGenToz3::preorder(const IR::SubSat *expr) {
    builder->append("P4subsat");
    visit_binary(expr);
    return false;
}

bool CodeGenToz3::preorder(const IR::Shl *expr) {
    builder->append("P4lshift");
    visit_binary(expr);
    return false;
}

bool CodeGenToz3::preorder(const IR::Shr *expr) {
    builder->append("P4rshift");
    visit_binary(expr);
    return false;
}

bool CodeGenToz3::preorder(const IR::Equ *expr) {
    builder->append("P4eq");
    visit_binary(expr);
    return false;
}

bool CodeGenToz3::preorder(const IR::Neq *expr) {
    builder->append("P4ne");
    visit_binary(expr);
    return false;
}

bool CodeGenToz3::preorder(const IR::Lss *expr) {
    builder->append("P4lt");
    visit_binary(expr);
    return false;
}

bool CodeGenToz3::preorder(const IR::Leq *expr) {
    builder->append("P4le");
    visit_binary(expr);
    return false;
}

bool CodeGenToz3::preorder(const IR::Grt *expr) {
    builder->append("P4gt");
    visit_binary(expr);
    return false;
}

bool CodeGenToz3::preorder(const IR::Geq *expr) {
    builder->append("P4ge");
    visit_binary(expr);
    return false;
}

bool CodeGenToz3::preorder(const IR::BAnd *expr) {
    builder->append("P4band");
    visit_binary(expr);
    return false;
}

bool CodeGenToz3::preorder(const IR::BOr *expr) {
    builder->append("P4bor");
    visit_binary(expr);
    return false;
}

bool CodeGenToz3::preorder(const IR::BXor *expr) {
    builder->append("P4xor");
    visit_binary(expr);
    return false;
}

bool CodeGenToz3::preorder(const IR::LAnd *expr) {
    builder->append("P4land");
    visit_binary(expr);
    return false;
}

bool CodeGenToz3::preorder(const IR::LOr *expr) {
    builder->append("P4lor");
    visit_binary(expr);
    return false;
}

bool CodeGenToz3::preorder(const IR::Concat *expr) {
    builder->append("P4Concat");
    visit_binary(expr);
    return false;
}

bool CodeGenToz3::preorder(const IR::Mask *expr) {
    builder->append("P4Mask");
    visit_binary(expr);
    return false;
}

bool CodeGenToz3::preorder(const IR::Slice *expr) {
    builder->append("P4Slice");
    visit_ternary(expr);
    return false;
}

bool CodeGenToz3::preorder(const IR::Mux *expr) {
    builder->append("P4Mux");
    visit_ternary(expr);
    return false;
}

bool CodeGenToz3::preorder(const IR::Cast *expr) {
    builder->append("P4Cast(");
    visit(expr->expr);
    builder->append(", ");
    visit(expr->destType);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Member *m) {
    if ((key_words.find(m->member.name) != key_words.end())) {
        // value is on ignore list, ignore the member and just follow the parent
        visit(m->expr);
        return false;
    }
    builder->append("P4Member(");
    visit(m->expr);
    builder->append(", ");
    builder->appendFormat("\"%s\"", m->member.name);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::PathExpression *p) {
    if (key_words.find(p->path->asString()) != key_words.end()) {
        // if the name of the expression is a special keyword, skip it
        return false;
    }
    builder->appendFormat("\"%s\"", p->path->asString());
    return false;
}

bool CodeGenToz3::preorder(const IR::TypeNameExpression *t) {
    builder->append("\"");
    builder->appendFormat("%s", t->typeName->path->name.name);

    if (!is_in_member)
        builder->append("\"");

    return false;
}

bool CodeGenToz3::preorder(const IR::ConstructorCallExpression *cce) {
    builder->appendFormat("\"%s\"", cce->toString());
    return false;
}

bool CodeGenToz3::preorder(const IR::NamedExpression *ne) {
    visit(ne->expression);
    return false;
}

bool CodeGenToz3::preorder(const IR::StructInitializerExpression *sie) {
    auto sie_name = sie->typeName->path->name.name;
    IR::IndexedVector<IR::NamedExpression> components;

    builder->appendFormat("P4Initializer(", sie_name);
    builder->append("[");

    for (auto c : sie->components) {
        visit(c);
        builder->append(", ");
    }
    builder->appendFormat("], z3_reg.instance(\"%s\", ", sie_name);
    visit(sie->typeName);
    builder->append("))");

    return false;
}

bool CodeGenToz3::preorder(const IR::ArrayIndex *a) {
    builder->append("P4Index(");
    visit(a->left);
    builder->append(", ");
    visit(a->right);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::DefaultExpression *) {
    builder->appendFormat("\"default\"");
    return false;
}

bool CodeGenToz3::preorder(const IR::Constant *c) {
    // Ideally we would like to define a z3 var here and then interpret it
    // so we just need to call visit()
    // Unfortunately, z3 python does not handle Var declarations nicely
    // So for now we need to do hardcoded checks.
    // builder->appendFormat("z3.Var(%d, ", c->value.get_ui());
    // visit(c->type);
    // builder->append(")");
    if (auto tb = c->type->to<IR::Type_Bits>())
        builder->appendFormat("z3.BitVecVal(%s, %d)",
                              c->toString(), tb->size);
    else if (c->type->is<IR::Type_InfInt>()) {
        builder->appendFormat("%llu", c->asUint64());
    }
    else
        FATAL_ERROR("Constant Node %s not implemented!",
                    c->type->node_type_name());
    return false;
}

bool CodeGenToz3::preorder(const IR::BoolLiteral *bl) {
    if (bl->value == true)
        builder->append("z3.BoolVal(True)");
    else
        builder->append("z3.BoolVal(False)");
    return false;
}

bool CodeGenToz3::preorder(const IR::Parameter *p) {
    /*
     * p->
     * (1) direction, inout, out, in
     * (2) type
     * (3) id for name
     */
    builder->append("(");

    if (p->direction == IR::Direction::InOut)
        builder->append("\"inout\", ");
    else if (p->direction == IR::Direction::Out)
        builder->append("\"out\", ");
    else
        builder->append("\"in\", ");

    builder->append("\"");
    builder->append(p->name);
    builder->append("\", ");
    visit(p->type);
    builder->append(")");

    return false;
}

bool CodeGenToz3::preorder(const IR::Argument *arg) {
    if (arg->name)
        builder->appendFormat("%s=", arg->name.name);

    visit(arg->expression);

    return false;
}

bool CodeGenToz3::preorder(const IR::Declaration_Constant *dc) {
    builder->append(depth, "lval = \"");
    builder->append(dc->name.name);
    builder->append("\"\n");
    builder->append(depth, "rval = ");

    if (nullptr != dc->initializer)
        visit(dc->initializer);
    else {
        builder->append("z3_reg.instance(\"");
        builder->append(dc->name.name);
        builder->append("\", ");
        visit(dc->type);
        builder->append(")");
    }
    builder->newline();

    if (in_local_scope)
        builder->append(depth, "stmt = P4Declaration(lval, rval)");
    else
        builder->append(depth, "z3_reg.declare_global(\"decl\", lval, rval)");
    builder->newline();
    return false;
}

bool CodeGenToz3::preorder(const IR::Declaration_Variable *dv) {
    builder->append(depth, "lval = \"");
    builder->append(dv->name.name);
    builder->append("\"\n");
    builder->append(depth, "rval = ");

    if (dv->initializer) {
        builder->append("P4Initializer(");
        visit(dv->initializer);
        builder->append(", ");
    }
    builder->append("z3_reg.instance(\"");
    builder->append(dv->name.name);
    builder->append("\", ");
    visit(dv->type);
    builder->append(")");

    if (dv->initializer) {
        builder->append(")");
    }
    builder->newline();
    builder->append(depth, "stmt = AssignmentStatement(lval, rval)");
    builder->newline();
    return false;
}

bool CodeGenToz3::preorder(const IR::SwitchStatement *ss) {
    // TODO: This also should have context
    builder->append(depth, "switch_block = SwitchStatement(");

    is_inswitchstmt = true;
    visit(ss->expression);
    is_inswitchstmt = false;
    builder->append(")\n");

    // switch case
    for (size_t i = 0; i < ss->cases.size(); i++)
        visit(ss->cases.at(i));
    builder->append(depth, "stmt = switch_block\n\n");

    return false;
}

bool CodeGenToz3::preorder(const IR::SwitchCase *sc) {
    int if_output_def_blk = 0;

    builder->append(depth, "switch_block.add_case(");
    visit(sc->label);
    builder->append(")\n");

    if_output_def_blk = sc->statement->is<IR::BlockStatement>() ? 0 : 1;

    if (if_output_def_blk) {
        builder->append(depth,     "def BLOCK():\n");
        builder->append(depth + 1, "block = BlockStatement()\n");
        depth++;
    }
    visit(sc->statement);

    if (if_output_def_blk) {
        depth--;
        builder->append(depth + 1, "return block\n");
        builder->append(depth,     "stmt = BLOCK()\n\n");
    }

    builder->append(depth, "switch_block.add_stmt_to_case(");
    visit(sc->label);
    builder->append(", stmt)\n");
    return false;
}

bool CodeGenToz3::preorder(const IR::Declaration_ID *di) {
    builder->appendFormat("\"%s\"", di->name.name);
    return false;
}

void CodeGenToz3::emit_args(const IR::Type_StructLike *t) {
    builder->append(depth, "z3_args = [");

    for (auto f : t->fields) {
        builder->appendFormat("(\"%s\", ", f->name.name);
        visit(f->type);
        builder->append("), ");
    }
    builder->append("]");
}

bool CodeGenToz3::preorder(const IR::Type_Header *t) {
    emit_args(t);
    builder->newline();

    builder->appendFormat(depth,
                          "z3_reg.declare_global(\"header\", \"%s\", z3_args)",
                          t->name.name);
    builder->newline();
    builder->newline();

    return false;
}

bool CodeGenToz3::preorder(const IR::Type_HeaderUnion *t) {
    emit_args(t);
    builder->newline();

    builder->appendFormat(depth,
                          "z3_reg.declare_global(\"header\", \"%s\", z3_args)",
                          t->name.name);
    builder->newline();
    builder->newline();

    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Struct *t) {
    emit_args(t);
    builder->newline();

    builder->appendFormat(depth,
                          "z3_reg.declare_global(\"struct\", \"%s\", z3_args)",
                          t->name.name);
    builder->newline();
    builder->newline();
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Enum *t) {
    builder->append(depth, "enum_args = [");
    builder->newline();

    for (auto m : t->members) {
        builder->append(builder->indent(depth + 1));
        visit(m);
        builder->append(",\n");
    }
    builder->appendFormat(depth, "]");
    builder->newline();
    builder->appendFormat(depth,
                          "z3_reg.declare_global(\"enum\", \"%s\", enum_args)",
                          t->name.name,
                          t->name.name);
    builder->newline();
    builder->newline();

    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Error *t) {
    /* We consider a type error to just be an enum */
    builder->append(depth, "enum_args = [");
    builder->newline();

    for (auto m : t->members) {
        builder->append(builder->indent(depth + 1));
        visit(m);
        builder->append(",\n");
    }
    builder->appendFormat(depth, "]");
    builder->newline();
    builder->appendFormat(depth,
                          "z3_reg.declare_global(\"enum\", \"%s\", enum_args)",
                          t->name.name,
                          t->name.name);
    builder->newline();
    builder->newline();

    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Control *t) {
    auto ctrl_name = t->name.name;

    builder->delim_comment(depth, "CONTROL_TYPE %s", ctrl_name);
    builder->appendFormat(depth,
                          "%s_py = P4Extern(\"%s\", z3_reg)",
                          ctrl_name,
                          ctrl_name);
    builder->newline();

    for (auto param : t->applyParams->parameters) {
        builder->appendFormat(depth, "%s_py.add_parameter(", ctrl_name);
        visit(param);
        builder->append(")");
        builder->newline();
    }
    builder->appendFormat(depth,
                          "z3_reg.declare_global(\"extern\", \"%s\", %s_py)",
                          ctrl_name,
                          ctrl_name);
    builder->newline();
    builder->delim_comment(depth, "END CONTROL_TYPE %s", ctrl_name);
    builder->newline();
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Parser *t) {
    auto parser_name = t->name.name;

    builder->delim_comment(depth, "PARSER_TYPE %s", parser_name);
    builder->appendFormat(depth,
                          "%s_py = P4Extern(\"%s\", z3_reg)",
                          parser_name,
                          parser_name);
    builder->newline();

    for (auto param : t->applyParams->parameters) {
        builder->appendFormat(depth, "%s_py.add_parameter(", parser_name);
        visit(param);
        builder->append(")");
        builder->newline();
    }
    builder->appendFormat(depth,
                          "z3_reg.declare_global(\"extern\", \"%s\", %s_py)",
                          parser_name,
                          parser_name);
    builder->newline();
    builder->delim_comment(depth, "END PARSER_TYPE %s", parser_name);
    builder->newline();
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Package *t) {
    auto t_name = t->getName().name;

    builder->appendFormat(depth,
                          "%s = P4Package(z3_reg, \"%s\", ",
                          t_name,
                          t_name);

    for (auto cp : t->getConstructorParameters()->parameters) {
        visit(cp);
        builder->append(", ");
    }
    builder->append(")");
    builder->newline();
    builder->appendFormat(depth,
                          "z3_reg.declare_global(\"package\", \"%s\", %s)",
                          t_name,
                          t_name);
    builder->newline();
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Typedef *t) {
    builder->appendFormat(depth, "z3_reg.declare_global(\"typedef\", \"%s\", ",
                          t->name.name);
    visit(t->type);
    builder->appendFormat(")\n");
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Newtype *t) {
    builder->appendFormat(depth, "z3_reg.declare_global(\"typedef\", \"%s\", ",
                          t->name.name);
    visit(t->type);
    builder->appendFormat(")\n");
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Bits *t) {
    builder->appendFormat("z3.BitVecSort(");

    if (t->expression) {
        visit(t->expression);
        builder->append(".get_value()");
    }
    else
        builder->appendFormat("%d", t->size);

    builder->appendFormat(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Boolean *) {
    builder->appendFormat("z3.BoolSort()");
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Void *) {
    builder->appendFormat("None");
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_String *) {
    builder->appendFormat("z3.DeclareSort(\"string\")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Varbits *t) { \
    ::warning("Replacing Varbit  %1% with Bitvector.", t);
    builder->appendFormat("z3.BitVecSort(%d)", t->size);
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Tuple *t) {
    ::warning("Using generic width bits for a tuple type.");
    builder->appendFormat("z3.BitVecSort(%d)", t->width_bits());
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Name *t) {
    builder->appendFormat("z3_reg.type(\"%s\")", t->path->name.name);
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Stack *type) {
    builder->append("z3_reg.stack(");
    visit(type->elementType);
    builder->appendFormat(", %d)", type->getSize());
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_InfInt *) {
    builder->append("z3.IntSort()");
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Specialized *t) {
    builder->appendFormat("\"%s\"", t->baseType->toString());
    return false;
}

bool CodeGenToz3::preorder(const IR::Declaration_Instance *di) {
    builder->appendFormat(depth, "%s_py = P4Instance(z3_reg, ", di->name.name);

    if (auto tp = di->type->to<IR::Type_Specialized>()) {
        builder->appendFormat("\"%s\", ", tp->baseType->toString());
    } else if (auto tn = di->type->to<IR::Type_Name>()) {
        builder->appendFormat("\"%s\", ", tn->path->name.name);
    }

    for (auto arg: *di->arguments) {
        if (arg->name.name != nullptr)
            builder->appendFormat("%s=", arg->name.name);
        visit(arg->expression);

        // builder->append("_py");
        if (arg->expression != nullptr)
            builder->append(", ");
    }
    builder->append(")");
    builder->newline();

    if (!in_local_scope) {
        builder->appendFormat(depth,
                              "z3_reg.declare_global(\"decl\", \"%s\", %s_py)",
                              di->name.name,
                              di->name.name);
        builder->newline();
    }

    return false;
}
} // namespace TOZ3
