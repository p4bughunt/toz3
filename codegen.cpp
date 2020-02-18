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
    builder->append("from p4z3 import *\n\n");
    builder->newline();
    builder->newline();
    builder->append("def p4_program(z3_reg):");
    depth = 1;
    builder->newline();

    // Start to visit the actual AST objects
    for (auto o: p->objects) {
        builder->append(depth, "z3_reg.declare_global(");
        builder->newline();
        depth++;
        builder->append(depth,"");
        visit(o);
        depth--;
        builder->newline();
        builder->append(depth, ")");
        builder->newline();
    }
    builder->appendFormat(depth,
                          "return z3_reg._globals[\"main\"] if \"main\" in z3_reg._globals else None");
    builder->newline();
    depth = 0;
    return false;
}

bool CodeGenToz3::preorder(const IR::P4Parser *p) {
    auto parser_name = p->name.name;

    in_local_scope = true;

    builder->append("P4Parser(");
    builder->newline();
    depth++;
    builder->append(depth, "z3_reg=z3_reg,");
    builder->newline();
    builder->appendFormat(depth, "name=\"%s\",", parser_name);
    builder->newline();
    builder->append(depth, "params=");


    visit(p->getApplyParameters());
    builder->append(",");
    builder->newline();

    builder->append(depth, "const_params=");
    visit(p->getConstructorParameters());

    builder->append(",");
    builder->newline();
    builder->append(depth,"local_decls=[");
    depth++;
    for (auto a : p->parserLocals) {
        builder->newline();
        builder->appendFormat(depth, "P4Declaration(\"%s\", ", a->name.name);
        visit(a);
        builder->append("), ");
    }
    builder->append("],");
    depth--;
    builder->newline();
    builder->append(depth, "body=[]");
    // builder->append(depth, "body=ParserTree([");
    // builder->newline();
    // depth++;
    // for (auto s : p->states) {
    //     builder->append(depth, "");
    //     visit(s);
    //     builder->append(",");
    //     builder->newline();
    // }
    // builder->append(depth, "])");
    // depth--;
    // builder->newline();
    depth--;
    builder->append(")");
    in_local_scope = false;

    return false;
}

bool CodeGenToz3::preorder(const IR::ParserState *ps) {
    builder->appendFormat("ParserState(name=\"%s\", select=", ps->name.name);
    if (ps->selectExpression)
        visit(ps->selectExpression);
    else
        builder->append("P4Exit()");
    builder->append(",");
    builder->newline();
    builder->append(depth, "components=[");
    for (auto c : ps->components) {
        builder->newline();
        builder->append(depth, "");
        visit(c);
        builder->append(",");
    }
    builder->append(depth, "])");

    return false;
}

bool CodeGenToz3::preorder(const IR::P4ValueSet *pvs) {
    // Since we declare a symbolic value we only need the type and an instance
    builder->appendFormat("z3_reg.instance(\"%s\", ", pvs->name.name);
    visit(pvs->elementType);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::SelectExpression *se) {
    builder->append("ParserSelect(");
    visit(se->select);
    builder->append(", ");
    for (auto c: se->selectCases) {
        visit(c);
        builder->append(", ");
    }
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::SelectCase *sc) {
    builder->append("(");
    visit(sc->keyset);
    builder->append(", ");
    visit(sc->state);
    builder->append(")");
    return false;
}


bool CodeGenToz3::preorder(const IR::P4Control *c) {
    auto ctrl_name = c->name.name;

    in_local_scope = true;

    builder->appendFormat("P4Control(");
    builder->newline();
    depth++;
    builder->append(depth, "z3_reg=z3_reg,");
    builder->newline();
    builder->appendFormat(depth, "name=\"%s\",", ctrl_name);
    builder->newline();
    builder->append(depth, "params=");


    visit(c->getApplyParameters());
    builder->append(",");
    builder->newline();

    builder->append(depth, "const_params=");
    visit(c->getConstructorParameters());
    builder->append(",");
    builder->newline();

    builder->append(depth, "body=");
    visit(c->body);
    builder->append(",");
    builder->newline();
    builder->append(depth,"local_decls=[");
    depth++;
    for (auto a : c->controlLocals) {
        builder->newline();
        builder->appendFormat(depth, "P4Declaration(\"%s\", ", a->name.name);
        visit(a);
        builder->append("), ");
    }
    depth--;
    builder->append("]");
    builder->newline();
    depth--;
    builder->append(depth, ")");

    in_local_scope = false;

    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Extern *t) {
    auto extern_name = t->name.name;

    builder->appendFormat("P4Extern(\"%s\", z3_reg, type_params=", extern_name);
    visit(t->getTypeParameters());
    builder->append(", methods=[");

    for (auto m : t->methods) {
        in_local_scope = true;
        visit(m);
        in_local_scope = false;
        builder->append(", ");
    }
    builder->append("])");
    return false;
}

bool CodeGenToz3::preorder(const IR::Method *t) {
    auto method_name = t->name.name;

    builder->appendFormat("P4Method(\"%s\", z3_reg, return_type=", method_name);
    if (t->type->returnType)
        visit(t->type->returnType);
    else
        builder->append("None");

    builder->append(", params=");
    visit(t->getParameters());
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Function *function) {
    auto function_name = function->name.name;

    builder->appendFormat("P4Function(\"%s\", z3_reg, return_type=", function_name);
    visit(function->type->returnType);
    builder->append(", params=");
    visit(function->getParameters());
    builder->append(", "),

    builder->appendFormat(depth, "body=", function_name);
    in_local_scope=true;
    visit(function->body);
    in_local_scope=false;
    builder->append(depth, ")");
    return false;
}

bool CodeGenToz3::preorder(const IR::P4Action *p4action) {
    auto action_name = p4action->name.name;
    builder->appendFormat("P4Action(\"%s\", z3_reg, params=", action_name);
    visit(p4action->getParameters());
    builder->append(", "),

    builder->appendFormat(depth, "body=", action_name);
    visit(p4action->body);
    builder->append(depth, ")");
    return false;
}

bool CodeGenToz3::preorder(const IR::P4Table *p4table) {
    auto tab_name = p4table->name.name;
    builder->appendFormat("P4Table(\"%s\", ", tab_name);
    for (auto p : p4table->properties->properties) {
        // IR::Property
        visit(p);
        builder->append(", ");
    }
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Property *p) {
    builder->appendFormat("%s=", p->name.name);
    visit(p->value);
    return false;
}

bool CodeGenToz3::preorder(const IR::ActionList *acl) {
    builder->append("[");
    for (auto act: acl->actionList) {
        bool ignore_default = false;
        for (const auto *anno : act->getAnnotations()->annotations) {
            if (anno->name.name == "defaultonly") {
                ignore_default = true;
            }
        }
        if (ignore_default)
            continue;
        visit(act->expression);
        builder->append(", ");
    }
    builder->append("]");
    return false;
}

bool CodeGenToz3::preorder(const IR::Entry *e) {
    builder->append("(");
    visit(e->keys);
    builder->append(", ");
    visit(e->action);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::EntriesList *el) {
    // Tao: a trick here
    builder->append("[");
    for (auto entry: el->entries) {
        visit(entry);
        builder->append(", ");
    }
    builder->append("]");
    return false;
}

bool CodeGenToz3::preorder(const IR::Key *key) {
    builder->append("[");
    for (auto ke : key->keyElements) {
        visit(ke->expression);
        builder->append(", ");
    }
    builder->append("]");
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
    builder->append("MethodCallExpr(");
    visit(mce->method);
    builder->append(", [");
    for (auto arg : *mce->typeArguments) {
        visit(arg);
        builder->append(", ");
    }
    builder->append("]");
    builder->append(", ");
    for (auto arg : *mce->arguments) {
        visit(arg);
        builder->append(", ");
    }
    builder->append(")");

    return false;
}

bool CodeGenToz3::preorder(const IR::ListExpression *le) {

    builder->append("[");
    for (auto e : le->components) {
        visit(e);
        builder->append(", ");
    }
    builder->append("]");
    return false;
}

bool CodeGenToz3::preorder(const IR::BlockStatement *b) {
    builder->append("BlockStatement([");
    // body part
    depth++;
    for (auto c : b->components) {
        builder->newline();
        builder->append(depth, "");
        if (auto dc = c->to<IR::Declaration_Variable>())
            builder->appendFormat("P4Declaration(\"%s\", ", dc->name.name);
        visit(c);
        if (c->is<IR::Declaration_Variable>())
            builder->append(")");
        builder->append(",");
    }
    builder->append("]");
    depth--;
    builder->newline();
    builder->append(depth,")");

    return false;
}

bool CodeGenToz3::preorder(const IR::EmptyStatement *) {
    builder->append("P4Noop()");
    return false;
}

bool CodeGenToz3::preorder(const IR::ExitStatement *) {
    builder->append("P4Exit()");
    return false;
}

bool CodeGenToz3::preorder(const IR::ReturnStatement *r) {
    // TODO: Make this a proper return statement
    builder->append("P4Return(");
    visit(r->expression);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::AssignmentStatement *as) {
    builder->append("AssignmentStatement(");
    visit(as->left);
    builder->append(", ");
    visit(as->right);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::MethodCallStatement *mcs) {
    builder->append("MethodCallStmt(");
    visit(mcs->methodCall);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::IfStatement *ifs) {
    builder->append("IfStatement(");
    visit(ifs->condition);
    builder->append(", ");
    visit(ifs->ifTrue);
    builder->append(", ");
    visit(ifs->ifFalse);
    builder->append(")");

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

bool CodeGenToz3::preorder(const IR::ArrayIndex *expr) {
    builder->append("P4Member");
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
    builder->append("P4Member(");
    visit(m->expr);
    builder->append(", ");
    builder->appendFormat("\"%s\"", m->member.name);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::PathExpression *p) {
    builder->appendFormat("\"%s\"", p->path->asString());
    return false;
}

bool CodeGenToz3::preorder(const IR::TypeNameExpression *t) {
    builder->appendFormat("\"%s\"", t->typeName->path->name.name);
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


bool CodeGenToz3::preorder(const IR::DefaultExpression *) {
    builder->appendFormat("\"default\"");
    return false;
}

bool CodeGenToz3::preorder(const IR::Constant *c) {
    // so we just need to call visit()
    // Unfortunately, z3 python does not handle Var declarations nicely
    // So for now we need to do hardcoded checks.
    // builder->appendFormat("z3.Var(%d, ", c->value.get_ui());
    // visit(c->type);
    // builder->append(")");
    if (auto tb = c->type->to<IR::Type_Bits>())
        if (tb->isSigned)
            builder->appendFormat("Z3Int(%s, %d)",
                                  c->toString(), tb->size);
        else
            builder->appendFormat("z3.BitVecVal(%s, %d)",
                                  c->toString(), tb->size);
    else if (c->type->is<IR::Type_InfInt>()) {
        builder->appendFormat("Z3Int(%s)", c->toString());
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
    builder->append(", ");
    if (p->defaultValue)
        visit(p->defaultValue);
    else
        builder->append("None");
    builder->append(")");

    return false;
}

bool CodeGenToz3::preorder(const IR::ParameterList *p) {
    builder->append("[");
    depth++;
    for (auto param : p->parameters) {
        builder->newline();
        builder->append(depth, "");
        visit(param);
        builder->append(",");
    }
    depth--;
    builder->append("]");

    return false;
}

bool CodeGenToz3::preorder(const IR::TypeParameters *tp) {
    builder->append("[");
    depth++;
    for (auto param : tp->parameters) {
        builder->newline();
        builder->append(depth, "");
        visit(param);
        builder->append(",");
    }
    depth--;
    builder->append("]");

    return false;
}


bool CodeGenToz3::preorder(const IR::Argument *arg) {
    if (arg->name)
        builder->appendFormat("%s=", arg->name.name);

    visit(arg->expression);

    return false;
}

bool CodeGenToz3::preorder(const IR::Declaration_Constant *dc) {
    if (!in_local_scope)
        builder->appendFormat("P4Declaration(\"%s\", ", dc->name.name);
    if (dc->initializer)
        visit(dc->initializer);
    else {
        builder->append("z3_reg.instance(\"");
        builder->append(dc->name.name);
        builder->append("\", ");
        visit(dc->type);
        builder->append(")");
    }
    if (!in_local_scope)
        builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Declaration_Variable *dv) {
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
    return false;
}

bool CodeGenToz3::preorder(const IR::SwitchStatement *ss) {
    builder->append("SwitchStatement(");
    visit(ss->expression);
    builder->append(",cases=[");
    // switch case
    for (size_t i = 0; i < ss->cases.size(); i++) {
        visit(ss->cases.at(i));
        builder->append(", ");
    }
    builder->append("])");
    return false;
}

bool CodeGenToz3::preorder(const IR::SwitchCase *sc) {

    builder->append("(");
    visit(sc->label);
    builder->append(", ");
    if (sc->statement)
        visit(sc->statement);
    else
        builder->append("None");

    builder->append(")");

    return false;
}

bool CodeGenToz3::preorder(const IR::Declaration_ID *di) {
    builder->appendFormat("\"%s\"", di->name.name);
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Control *t) {
    auto ctrl_name = t->name.name;

    builder->appendFormat("P4Extern(\"%s\", z3_reg, type_params=", ctrl_name, ctrl_name);
    visit(t->applyParams);
    builder->append(")");

    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Parser *t) {
    auto parser_name = t->name.name;

    builder->appendFormat("P4Extern(\"%s\", z3_reg, type_params=",
                          parser_name,
                          parser_name);
    visit(t->applyParams);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Package *t) {
    auto t_name = t->getName().name;

    builder->appendFormat("P4Package(z3_reg, \"%s\", ",
                          t_name,
                          t_name);
    visit(t->getConstructorParameters());
    builder->append(")");
    return false;
}

void CodeGenToz3::emit_args(const IR::Type_StructLike *t) {
    builder->append("z3_args=[");
    for (auto f : t->fields) {
        builder->appendFormat("(\"%s\", ", f->name.name);
        visit(f->type);
        builder->append("), ");
    }
    builder->append("]");
}

bool CodeGenToz3::preorder(const IR::Type_Header *t) {
    builder->appendFormat("Header(z3_reg, \"%s\", ", t->name.name);
    emit_args(t);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_HeaderUnion *t) {
    builder->appendFormat("HeaderUnion(z3_reg, \"%s\", ", t->name.name);
    emit_args(t);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Struct *t) {
    builder->appendFormat("Struct(z3_reg, \"%s\", ", t->name.name);
    emit_args(t);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Enum *t) {
    builder->appendFormat("Enum(z3_reg, \"%s\", [", t->name.name);
    for (auto m : t->members) {
        visit(m);
        builder->append(", ");
    }

    builder->append("])");
    return false;
}

bool CodeGenToz3::preorder(const IR::SerEnumMember *m) {
    builder->appendFormat("(\"%s\", ", m->name.name);
    visit(m->value);
    builder->append(")");
    return false;
}


bool CodeGenToz3::preorder(const IR::Type_SerEnum *t) {
    builder->appendFormat("SerEnum(z3_reg, \"%s\", [", t->name.name);
    for (auto m : t->members) {
        visit(m);
        builder->append(", ");
    }

    builder->append("], ");
    visit(t->type);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Error *t) {
    /* We consider a type error to just be an enum */
    builder->appendFormat("Enum(z3_reg, \"%s\", [", t->name.name);
    for (auto m : t->members) {
        visit(m);
        builder->append(", ");
    }

    builder->append("])");
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Typedef *t) {
    if (!in_local_scope)
        builder->appendFormat("P4Declaration(\"%s\", ", t->name.name);
    in_local_scope = true;
    visit(t->type);
    in_local_scope = false;
    if (!in_local_scope) {
        builder->append(")");
    }
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Newtype *t) {
    if (!in_local_scope)
        builder->appendFormat("P4Declaration(\"%s\", ", t->name.name);
    visit(t->type);
    if (!in_local_scope) {
        builder->append(")");
    }
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

bool CodeGenToz3::preorder(const IR::Type_Stack *type) {
    builder->append("z3_reg.stack(");
    visit(type->elementType);
    builder->appendFormat(", %d)", type->getSize());
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Tuple *t) {
    // This is a dummy type, not sure how to name it
    // TODO: Figure out a better way to instantiate
    builder->append("ListType(z3_reg, \"tuple\", [");
    for (auto c : t->components) {
        visit(c);
        builder->append(", ");
    }
    builder->append("])");
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Name *t) {
    builder->appendFormat("z3_reg.type(\"%s\")", t->path->name.name);
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Var *t) {
    builder->appendFormat("z3_reg.type(\"%s\")", t->getVarName());
    return false;
}


bool CodeGenToz3::preorder(const IR::Type_InfInt *) {
    builder->append("z3.IntSort()");
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Dontcare *t) {
    builder->append("None");
    return false;
}


bool CodeGenToz3::preorder(const IR::Type_Specialized *t) {
    visit(t->baseType);
    builder->append(".init_type_params(");
    for (auto arg: *t->arguments) {
        visit(arg);
        builder->append(", ");
    }
    builder->appendFormat(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Declaration_Instance *di) {
    if (!in_local_scope) {
        builder->appendFormat("P4Declaration(\"%s\", ", di->name.name);
    }
    visit(di->type);
    builder->append(".initialize(");
    for (auto arg: *di->arguments) {
            if (arg->name.name != nullptr)
                builder->appendFormat("%s=", arg->name.name);
            visit(arg->expression);
        if (arg->expression != nullptr)
            builder->append(", ");
    }
    builder->append(")");
    if (!in_local_scope)
        builder->append(")");


    return false;
}
} // namespace TOZ3
