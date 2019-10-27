#include "codegen.h"

namespace TOZ3 {

Visitor::profile_t CodeGenToz3::init_apply(const IR::Node* node) {
    return Inspector::init_apply(node);
}

void CodeGenToz3::end_apply(const IR::Node *) {

    if (nullptr != outStream) {
        cstring res = builder->toString();
        *outStream << res.c_str();
        outStream->flush();
    }
    else {
    }
}


bool CodeGenToz3::preorder(const IR::P4Parser* p) {
    auto parser_name = p->name.name;

    // output header
    builder->appendFormat(depth, "%s_args = [\n", parser_name);
    for (auto cp : p->getApplyParameters()->parameters) {
        builder->appendFormat(depth+1,
         "(\"%s\", z3_reg.type(\"%s\")),\n", cp->name.name, cp->type->toString());
    }
    builder->append(depth, "]\n");

    builder->appendFormat(depth, "def %s(p4_vars):\n", parser_name);
    builder->append(depth+1, "pass\n");

    return false;
}

bool CodeGenToz3::preorder(const IR::P4Control* c) {

    auto ctrl_name = c->name.name;
    // output header
    builder->appendFormat(depth, "%s_args = [\n", ctrl_name);
    for (auto cp : c->getApplyParameters()->parameters) {
        builder->appendFormat(depth+1,
         "(\"%s\", z3_reg.type(\"%s\")),\n", cp->name.name, cp->type->toString());
    }
    builder->append(depth, "]\n");

    builder->appendFormat(depth, "def %s(input_args):\n", ctrl_name);

    depth++;
    builder->append(depth, "z3_reg.register_inouts(\"inouts\", input_args)\n\n");
    builder->appendFormat(depth, "p4_vars = z3_reg.instance(\"\", z3_reg.type(\"inouts\"))\n\n", ctrl_name);
    builder->appendFormat(depth, "p4_vars.add_externs(z3_reg._externs)\n");

    /*
     * (1) Action
     * (2) Table
     */
    builder->append(depth, "ctrl_body = BlockStatement()\n\n");
    for (auto a : c->controlLocals) {
            visit(a);
            if (a->is<IR::Declaration_Variable>())
                builder->append(depth, "ctrl_body.add(stmt)\n");
    }

    /*
     * (3) Apply Part
     */
    builder->appendFormat(depth, "p4_vars.add_externs(z3_reg._externs)\n");
    visit(c->body);

    builder->append(depth, "ctrl_body.add(stmt)\n");
    builder->append(depth, "return ctrl_body.eval(p4_vars=p4_vars, expr_chain=[])\n\n");
    depth--;
    return false;
}

bool CodeGenToz3::preorder(const IR::P4Action* p4action) {
    std::stringstream ss;
    ss << p4action->name.name << " = P4Action()\n";
    builder->append(depth, ss.str());

    for (auto param : p4action->parameters->parameters) {
        ss.str("");
        ss << p4action->name.name << ".add_parameter(";
        builder->append(depth, ss.str());
        visit(param);
        builder->append(")\n");
    }

    // body BlockStatement
    visit(p4action->body);

    ss.str("");
    ss << p4action->name.name << ".add_stmt(stmt)\n\n\n";
    builder->append(depth, ss.str());
    ss.str("");
    ss << "z3_reg.register_extern(\"" << p4action->name.name << "\", " << p4action->name.name <<")\n\n";
    builder->append(depth, ss.str());
    return false;
}

bool CodeGenToz3::preorder(const IR::P4Table* p4table) {
    std::stringstream ss;
    tab_name = p4table->name.name;
    ss << p4table->name.name << " = P4Table(\"" << p4table->name.name
        << "\")\n";
    builder->append(depth, ss.str());
    for (auto p : p4table->properties->properties) {
        // IR::Property
        visit(p);
    }
    ss.str("");
    ss << "p4_vars.set_or_add_var(\"" << p4table->name.name << "\", " << p4table->name.name <<")\n\n";
    builder->append(depth, ss.str());
    return false;
}

bool CodeGenToz3::preorder(const IR::Property* p) {
    // Tao: a trick here
    std::stringstream ss;
    if (p->name.name == "default_action") {
        ss << tab_name << ".add_default(p4_vars, ";
        builder->append(depth, ss.str());
        visit(p->value);
        ss.str("");
        ss << ")";
        builder->append(ss.str());
        builder->newline();
        builder->newline();
    }
    else if (p->name.name == "size") {
        // skip it
    }
    else {
        visit(p->value);
    }
    return false;
}

bool CodeGenToz3::preorder(const IR::ActionList* acl) {
    std::stringstream ss;
    for (auto act : acl->actionList) {
        ss.str("");
        ss << tab_name << ".add_action(p4_vars, ";
        builder->append(depth, ss.str());
        visit(act->expression);
        builder->append(")\n");
    }
    builder->newline();
    return false;
}

bool CodeGenToz3::preorder(const IR::Key* key) {
    std::stringstream ss;
    for (auto ke : key->keyElements) {
        ss.str("");
        ss << "table_key = ";
        builder->append(depth, ss.str());
        // Tao: maybe use visit here
        // visit(ke->expression);
        visit(ke->expression);
        builder->newline();
        ss.str("");
        ss << tab_name << ".add_match(table_key)\n";
        builder->append(depth, ss.str());
    }
    builder->newline();
    return false;
}

bool CodeGenToz3::preorder(const IR::KeyElement* ke) {
    visit(ke->expression);
    return false;
}

bool CodeGenToz3::preorder(const IR::ExpressionValue* ev) {
    visit(ev->expression);
    return false;
}

bool CodeGenToz3::preorder(const IR::MethodCallExpression* mce) {
    if (if_inswitchstmt == 0) {
        builder->append("MethodCallExpr(");
        visit(mce->method);
        if (mce->arguments->size() != 0) {
            // output arguments
            for (size_t i=0; i<mce->arguments->size(); i++) {
                builder->append(", ");
                visit(mce->arguments->at(i)->expression);
            }
        }
        builder->append(")");
    }
    else {
        key_words.push_back("apply");
        visit(mce->method);
        key_words.pop_back();
    }

    return false;
}

bool CodeGenToz3::preorder(const IR::ListExpression* le) {
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

bool CodeGenToz3::preorder(const IR::BlockStatement* b) {
    // top part
    builder->append(depth, "def BLOCK():\n");
    builder->append(depth+1, "block = BlockStatement()\n");
    // body part
    depth++;
    for (auto c : b->components) {
        visit(c);
        builder->append(depth, "block.add(stmt)\n");
    }
    depth--;

    // bot part
    builder->newline();
    builder->append(depth+1, "return block\n\n");
    builder->append(depth, "stmt = BLOCK()\n\n");

    return false;
}

bool CodeGenToz3::preorder(const IR::AssignmentStatement* as) {
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
        builder->append(depth,"stmt = SliceAssignment(lval, rval, ");
        builder->appendFormat("%d, %d)", sl->getH(), sl->getL());
        builder->newline();
    }
    else {
        builder->append(depth, "stmt = AssignmentStatement(lval, rval)");
        builder->newline();
    }

    if (if_stmtadd) {
        builder->append(depth, "block.add(stmt)");
        builder->newline();
    }
    return false;
}

bool CodeGenToz3::preorder(const IR::MethodCallStatement* mcs) {
    builder->append(depth, "stmt = MethodCallStmt(");
    visit(mcs->methodCall);
    builder->append(")");
    builder->newline();
    return false;
}

bool CodeGenToz3::preorder(const IR::IfStatement* ifs) {


    builder->append(depth, "if_block = IfStatement()\n\n");
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

    builder->append(depth, "stmt = if_block\n");

    return false;
}

bool CodeGenToz3::preorder(const IR::Neg* expr) {
    builder->append("P4neg(");
    visit(expr->expr);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Cmpl* expr) {
    builder->append("P4inv(");
    visit(expr->expr);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::LNot* expr) {
    builder->append("P4not(");
    visit(expr->expr);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Mul* expr) {
    builder->append("P4mul(");
    visit(expr->left);
    builder->append(", ");
    visit(expr->right);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Div* expr) {
    builder->append("P4div(");
    visit(expr->left);
    builder->append(", ");
    visit(expr->right);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Mod* expr) {
    builder->append("P4mod(");
    visit(expr->left);
    builder->append(", ");
    visit(expr->right);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Add* expr) {
    builder->append("P4add(");
    visit(expr->left);
    builder->append(", ");
    visit(expr->right);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Sub* expr) {
    builder->append("P4sub(");
    visit(expr->left);
    builder->append(", ");
    visit(expr->right);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Shl* expr) {
    builder->append("P4lshift(");
    visit(expr->left);
    builder->append(", ");
    visit(expr->right);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Shr* expr) {
    builder->append("P4rshift(");
    visit(expr->left);
    builder->append(", ");
    visit(expr->right);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Equ* expr) {
    // a single line
    builder->append("P4eq(");
    visit(expr->left);
    builder->append(", ");
    visit(expr->right);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Neq* expr) {
    // a single line
    builder->append("P4ne(");
    visit(expr->left);
    builder->append(", ");
    visit(expr->right);
    builder->append(")\n");
    return false;
}

bool CodeGenToz3::preorder(const IR::Lss* expr) {
    std::stringstream ss;
    builder->append("P4lt(");
    visit(expr->left);
    builder->append(", ");
    visit(expr->right);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Leq* expr) {
    std::stringstream ss;
    builder->append("P4le(");
    visit(expr->left);
    builder->append(", ");
    visit(expr->right);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Grt* expr) {
    std::stringstream ss;
    builder->append("P4gt(");
    visit(expr->left);
    builder->append(", ");
    visit(expr->right);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Geq* expr) {
    std::stringstream ss;
    builder->append("P4ge(");
    visit(expr->left);
    builder->append(", ");
    visit(expr->right);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::BAnd* expr) {
    builder->append("P4band(");
    visit(expr->left);
    builder->append(", ");
    visit(expr->right);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::BOr* expr) {
    builder->append("P4bor(");
    visit(expr->left);
    builder->append(", ");
    visit(expr->right);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::BXor* expr) {
    builder->append("P4xor(");
    visit(expr->left);
    builder->append(", ");
    visit(expr->right);
    builder->append(")");
    return false;
}

/* LAnd and BAnd seem to be the same in Python. TODO: Check that */
bool CodeGenToz3::preorder(const IR::LAnd* expr) {
    builder->append("P4land(");
    visit(expr->left);
    builder->append(", ");
    visit(expr->right);
    builder->append(")");
    return false;
}

/*Bor and Lor seem to be the same in Python. TODO: Check that */
bool CodeGenToz3::preorder(const IR::LOr* expr) {
    builder->append("P4lor(");
    visit(expr->left);
    builder->append(", ");
    visit(expr->right);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Member* m) {

    visit(m->expr);
    if (std::find(key_words.begin(),
                key_words.end(),
                m->member.name) != key_words.end()) {
        if_keywords = 1;
    }

    if (!if_keywords)
        builder->appendFormat("\".%s\"",  m->member.name);

    if_keywords = 0;
    return false;
}

bool CodeGenToz3::preorder(const IR::DefaultExpression*) {
    builder->appendFormat("\"default\"");
    return false;
}


bool CodeGenToz3::preorder(const IR::PathExpression* p) {

    if (std::find(key_words.begin(),
                key_words.end(),
                p->path->asString()) != key_words.end()) {
        // do nothing
        if_keywords = 1;
    }
    else {
        builder->appendFormat("\"%s\"", p->path->asString());
    }
    return false;
}

bool CodeGenToz3::preorder(const IR::Constant* c) {

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
    else if (c->type->is<IR::Type_InfInt>())
        builder->appendFormat("%d", c->value.get_ui());
    else
        P4C_UNIMPLEMENTED("Constant type %1% not supported!", c);
    return false;
}

bool CodeGenToz3::preorder(const IR::BoolLiteral* bl) {
    if (bl->value == true)
        builder->append("z3.BoolVal(True)");
    else
        builder->append("z3.BoolVal(False)");
    return false;
}

bool CodeGenToz3::preorder(const IR::Cast* c) {
    builder->append("P4Cast(");
    visit(c->expr);
    builder->append(", ");
    visit(c->destType);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Concat* c) {
    builder->append("P4Concat(");
    visit(c->left);
    builder->append(", ");
    visit(c->right);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Slice* s) {
    builder->append("P4Slice(");
    visit(s->e0);
    builder->append(", ");
    visit(s->e1);
    // Tao: assume it always be integer constant
    slice_l = con_val;
    builder->append(", ");
    visit(s->e2);
    // Tao: assume it always be integer constant
    slice_r = con_val;
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Parameter* param) {
    /*
     * param->
     * (1) direction, inout, in, out
     * (2) type
     * (3) id for name
     */
    builder->append("\"");
    builder->append(param->name);
    builder->append("\", ");
    visit(param->type);

    return false;
}

bool CodeGenToz3::preorder(const IR::Declaration_Variable* dv) {
    builder->append(depth, "lval = \"");
    builder->append(dv->name.name);
    builder->append("\"\n");
    builder->append(depth, "rval = ");
    if (nullptr != dv->initializer)
        visit(dv->initializer);
    else {
        builder->append("z3_reg.instance(\"");
        builder->append(dv->name.name);
        builder->append("\", ");
        visit(dv->type);
        builder->append(")");
    }
    builder->newline();
    builder->append(depth, "stmt = P4Declaration(lval, rval)");
    builder->newline();
    return false;
}

bool CodeGenToz3::preorder(const IR::SwitchStatement* ss) {
    builder->append(depth, "switch_block = SwitchStatement(");

    if_inswitchstmt = 1;
    builder->append("p4_vars.get_var(\n");
    visit(ss->expression);
    if_inswitchstmt = 0;
    builder->append("))\n");

    // switch case
    for (size_t i=0; i<ss->cases.size(); i++)
        visit(ss->cases.at(i));


    builder->append(depth, "stmt = switch_block\n\n");


    return false;
}

bool CodeGenToz3::preorder(const IR::SwitchCase* sc) {
    int if_output_def_blk = 0;

    builder->append(depth, "switch_block.add_case(");
    visit(sc->label);
    builder->append(")\n");

    if_output_def_blk = sc->statement->is<IR::BlockStatement>()?0:1;
    if (if_output_def_blk) {
        builder->append(depth, "def BLOCK():\n");
        builder->append(depth+1, "block = BlockStatement()\n");
        depth++;
    }
    visit(sc->statement);

    if (if_output_def_blk) {
        depth--;
        builder->append(depth+1, "return block\n");
        builder->append(depth, "stmt = BLOCK()\n\n");
    }

    builder->append(depth, "switch_block.add_stmt_to_case(");
    visit(sc->label);
    builder->append(", stmt)\n");
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Header* t) {

    builder->appendFormat("%sz3_args = [\n", builder->indent(depth));
    for (auto f : t->fields) {
        builder->appendFormat("%s(\'%s\', ", builder->indent(depth+1), f->name.name);
        visit(f->type);
        builder->append("),\n");
    }
    builder->appendFormat("%s]\n", builder->indent(depth));
    builder->appendFormat("%sz3_reg.register_header(\"%s\", z3_args)\n\n", builder->indent(depth), t->name.name);

    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Struct* t) {

    builder->appendFormat("%sz3_args = [\n", builder->indent(depth));
    for (auto f : t->fields) {
        builder->appendFormat("%s(\'%s\', ", builder->indent(depth+1), f->name.name);
        visit(f->type);
        builder->append("),\n");
    }
    builder->appendFormat("%s]\n", builder->indent(depth));
    builder->appendFormat("%sz3_reg.register_struct(\"%s\", z3_args)\n\n", builder->indent(depth), t->name.name);

    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Typedef* t) {
    builder->appendFormat("%sz3_reg.register_typedef(\"%s\", ", builder->indent(depth), t->name.name);
    visit(t->type);
    builder->appendFormat(")\n");
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Bits* t) {
    builder->appendFormat("z3.BitVecSort(%d)", t->size);
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Boolean*) {
    builder->appendFormat("z3.BoolSort()");
    return false;
}


bool CodeGenToz3::preorder(const IR::Type_Varbits* t) {\
    ::warning("Replacing Varbit  %1% with Bitvector.",t);
    builder->appendFormat("z3.BitVecSort(%d)", t->size);
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Name* t) {
    builder->appendFormat("z3_reg.type(\"%s\")", t->path->name.name);
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Stack* type) {
    builder->append("z3_reg.stack(");
    visit(type->elementType);
    builder->appendFormat(", %d)", type->getSize());
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_InfInt*) {
    builder->append("z3.IntSort()");
    return false;
}

bool CodeGenToz3::preorder(const IR::ArrayIndex* a) {
    visit(a->left);
    builder->append("\".");
    visit(a->right);
    builder->append("\"");
    return false;
}

// for V1Switch Declaration Instance
bool CodeGenToz3::preorder(const IR::Declaration_Instance* di) {
    if (di->type->is<IR::Type_Specialized>()) {
        auto tp = di->type->to<IR::Type_Specialized>();
        builder->appendFormat(depth, "return %s(", tp->baseType->toString());
        for (size_t i=0; i<di->arguments->size(); i++) {
            const IR::Argument* const arg = di->arguments->at(i);
            // std::cout << arg->name.name << std::endl;
            if (auto cce = arg->expression->to<IR::ConstructorCallExpression>()) {
                if (arg->name.name != nullptr)
                    builder->appendFormat("%s=", arg->name.name);
                builder->appendFormat("(%s, %s_args), ",
                  cce->toString(), cce->toString());
            } else {
                BUG("Type %1% not supported!", arg->expression);
            }
        }
        builder->append(")");
    } else {
        BUG("Decl Instance type %1% not supported!", di);
    }

    return false;
}


} // namespace TOZ3
