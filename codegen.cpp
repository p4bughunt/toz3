#include "codegen.h"

namespace TOZ3 {

cstring infer_name(const IR::Annotations *annots, cstring default_name) {
    // This function is a bit of a hacky way to infer the true name of a
    // declaration. Since there are a couple of passes that rename but add
    // annotations we can infer the original name from the annotation.
    // not sure if this generalizes but this is as close we can get for now
    for (auto anno : annots->annotations) {
        // there is an original name in the form of an annotation
        if (anno->name.name == "name") {
            for (auto token : anno->body) {
                // the full name can be a bit more convoluted
                // we only need the last bit after the dot
                // so hack it out
                cstring full_name = token->text;

                // find the last dot
                const char *last_dot = full_name.findlast((int)'.');
                // there is no dot in this string, just return the full name
                if (not last_dot) {
                    return full_name;
                }
                // otherwise get the index, remove the dot
                size_t idx = (size_t)(last_dot - full_name + 1);
                return token->text.substr(idx);
            }
            // if the annotation is a member just get the root name
            if (auto member = anno->expr.to<IR::Member>()) {
                return member->member.name;
            }
        }
    }

    return default_name;
}

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
    for (auto o : p->objects) {
        builder->append(depth, "z3_reg.declare_global(");
        builder->newline();
        depth++;
        builder->append(depth, "");
        visit(o);
        depth--;
        builder->newline();
        builder->append(depth, ")");
        builder->newline();
    }
    builder->append(depth, "var = z3_reg.get_main_function()");
    builder->newline();
    builder->append(depth,
                    "return var if isinstance(var, P4Package) else None");
    builder->newline();
    depth = 0;
    return false;
}

bool CodeGenToz3::preorder(const IR::P4Parser *p) {
    auto parser_name = p->name.name;

    builder->append("ControlDeclaration(");
    builder->append("P4Parser(");
    builder->newline();
    depth++;
    builder->appendFormat(depth, "name=\"%s\",", parser_name);
    builder->newline();
    builder->append(depth, "type_params=");
    visit(p->getTypeParameters());
    builder->append(",");
    builder->newline();
    builder->append(depth, "params=");

    visit(p->getApplyParameters());
    builder->append(",");
    builder->newline();

    builder->append(depth, "const_params=");
    visit(p->getConstructorParameters());

    builder->append(",");
    builder->newline();
    builder->append(depth, "local_decls=[");
    depth++;
    for (auto a : p->parserLocals) {
        builder->newline();
        visit(a);
        builder->append(", ");
    }
    builder->append("],");
    depth--;
    builder->newline();
    // builder->append(depth, "body=[]");
    builder->append(depth, "body=ParserTree([");
    builder->newline();
    depth++;
    for (auto s : p->states) {
        builder->append(depth, "");
        visit(s);
        builder->append(",");
        builder->newline();
    }
    builder->append(depth, "])");
    depth--;
    builder->newline();
    depth--;
    builder->append(")");
    builder->append(")");

    return false;
}

bool CodeGenToz3::preorder(const IR::ParserState *ps) {
    builder->appendFormat("ParserState(name=\"%s\", select=", ps->name.name);
    if (ps->selectExpression)
        visit(ps->selectExpression);
    else
        builder->append("RejectState()");
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
    auto pvs_name = infer_name(pvs->getAnnotations(), pvs->name.name);
    builder->appendFormat("P4Declaration(\"%s\", ", pvs->name.name);
    // Since we declare a symbolic value we only need the type and an instance
    builder->appendFormat("gen_instance(z3_reg, \"%s\", ", pvs_name);
    visit(pvs->elementType);
    builder->append(")");
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::SelectExpression *se) {
    builder->append("ParserSelect(");
    visit(se->select);
    builder->append(", ");
    for (auto c : se->selectCases) {
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

    builder->append("ControlDeclaration(");
    builder->append("P4Control(");
    builder->newline();
    depth++;
    builder->appendFormat(depth, "name=\"%s\",", ctrl_name);
    builder->newline();
    builder->append(depth, "type_params=");
    visit(c->getTypeParameters());
    builder->append(",");
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
    builder->append(depth, "local_decls=[");
    depth++;
    for (auto a : c->controlLocals) {
        builder->newline();
        visit(a);
        builder->append(", ");
    }
    depth--;
    builder->append("]");
    builder->newline();
    depth--;
    builder->append(depth, ")");
    builder->append(")");

    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Extern *t) {
    auto extern_name = t->name.name;

    builder->appendFormat("P4Extern(\"%s\", type_params=", extern_name);
    visit(t->getTypeParameters());
    builder->append(", methods=[");

    for (auto m : t->methods) {
        visit(m);
        builder->append(", ");
    }
    builder->append("])");
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Method *t) {
    builder->append("(");
    if (t->returnType)
        visit(t->returnType);
    else
        builder->append("None");
    builder->append(", ");
    visit(t->typeParameters);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Method *method) {
    auto method_name = infer_name(method->getAnnotations(), method->name.name);
    builder->appendFormat("P4Declaration(\"%s\", ", method->name.name);
    builder->appendFormat("P4Method(\"%s\", type_params=", method_name);
    visit(method->type);
    builder->append(", params=");
    visit(method->getParameters());
    builder->append(")");
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Function *function) {
    auto function_name = function->name.name;
    builder->appendFormat("P4Declaration(\"%s\", ", function_name);
    builder->appendFormat("P4Function(\"%s\", return_type=", function_name);
    visit(function->type->returnType);
    builder->append(", params=");
    visit(function->getParameters());
    builder->append(", "), builder->appendFormat(depth, "body=", function_name);
    visit(function->body);
    builder->append(depth, ")");
    builder->append(depth, ")");
    return false;
}

bool CodeGenToz3::preorder(const IR::P4Action *p4action) {
    auto action_name =
        infer_name(p4action->getAnnotations(), p4action->name.name);
    builder->appendFormat("P4Declaration(\"%s\", ", p4action->name.name);
    builder->appendFormat("P4Action(\"%s\", params=", action_name);
    visit(p4action->getParameters());
    builder->append(", "),

        builder->appendFormat(depth, "body=", action_name);
    visit(p4action->body);
    builder->append(depth, ")");
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::P4Table *p4table) {
    auto tab_name = infer_name(p4table->getAnnotations(), p4table->name.name);
    builder->appendFormat("P4Declaration(\"%s\", ", p4table->name.name);
    builder->appendFormat("P4Table(\"%s\", ", tab_name);
    bool immutable = false;
    for (auto p : p4table->properties->properties) {
        // IR::Property
        visit(p);
        // if the entries properties is constant it means the entries are fixed
        // we cannot add or remove table entries
        if (p->name.name == "entries" and p->isConstant) {
            immutable = true;
        }
        builder->append(", ");
    }
    // also check if the table is invisible to the control plane
    // this also implies that it cannot be modified
    auto annos = p4table->getAnnotations()->annotations;
    if (std::any_of(annos.begin(), annos.end(),
                    [](const IR::Annotation *anno) {
                        return anno->name.name == "hidden";
                    })) {
        immutable = true;
    }
    if (immutable) {
        builder->append("immutable=True");
    } else {
        builder->append("immutable=False");
    }
    builder->append("))");
    return false;
}

bool CodeGenToz3::preorder(const IR::Property *p) {
    builder->appendFormat("%s=", p->name.name);
    visit(p->value);
    return false;
}

bool CodeGenToz3::preorder(const IR::ActionList *acl) {
    builder->append("[");
    for (auto act : acl->actionList) {
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
    builder->append("[");
    for (auto entry : el->entries) {
        visit(entry);
        builder->append(", ");
    }
    builder->append("]");
    return false;
}

bool CodeGenToz3::preorder(const IR::Key *key) {
    builder->append("[");
    for (auto ke : key->keyElements) {
        visit(ke);
        builder->append(", ");
    }
    builder->append("]");
    return false;
}

bool CodeGenToz3::preorder(const IR::KeyElement *ke) {
    builder->append("(");
    visit(ke->expression);
    builder->append(", ");
    visit(ke->matchType);
    builder->append(")");
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
        visit(c);
        builder->append(",");
    }
    builder->append("]");
    depth--;
    builder->newline();
    builder->append(depth, ")");

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
    builder->append("P4Return(");
    if (r->expression) {
        visit(r->expression);
    } else {
        builder->append("None");
    }

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
    if (not ifs->ifFalse) {
        builder->append("P4Noop()");
    } else {
        visit(ifs->ifFalse);
    }
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

bool CodeGenToz3::preorder(const IR::Range *expr) {
    builder->append("P4Range");
    visit_binary(expr);
    return false;
}

bool CodeGenToz3::preorder(const IR::ArrayIndex *expr) {
    builder->append("P4Index");
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
    cstring path = p->path->asString();
    // FIXME: Stupid hack to fix vars that start with a dot...
    if (path.startsWith(".")) {
        path = path.substr(1);
    }
    builder->appendFormat("\"%s\"", path);
    return false;
}

bool CodeGenToz3::preorder(const IR::TypeNameExpression *t) {
    builder->appendFormat("\"%s\"", t->typeName->path->name.name);
    return false;
}

bool CodeGenToz3::preorder(const IR::ConstructorCallExpression *cce) {
    // TODO: What do we do about constructedType? Do not really need it
    builder->append("ConstCallExpr(");
    visit(cce->constructedType);
    builder->append(", ");
    for (auto arg : *cce->arguments) {
        visit(arg);
        builder->append(", ");
    }
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::NamedExpression *ne) {
    visit(ne->expression);
    return false;
}

bool CodeGenToz3::preorder(const IR::StructExpression *sie) {
    IR::IndexedVector<IR::NamedExpression> components;

    builder->appendFormat("P4Initializer(");
    builder->append("[");

    for (auto c : sie->components) {
        visit(c);
        builder->append(", ");
    }
    builder->append("], ");
    if (sie->typeName) {
        visit(sie->typeName);
    }
    builder->append(")");

    return false;
}

bool CodeGenToz3::preorder(const IR::DefaultExpression *) {
    builder->append("DefaultExpression()");
    return false;
}

bool CodeGenToz3::preorder(const IR::Constant *c) {
    if (auto tb = c->type->to<IR::Type_Bits>()) {
        if (tb->isSigned) {
            builder->appendFormat("Z3Int(%s, %d)", c->toString(), tb->size);
        } else {
            builder->appendFormat("z3.BitVecVal(%s, %d)", c->toString(),
                                  tb->size);
        }
    } else if (c->type->is<IR::Type_InfInt>()) {
        builder->appendFormat("%s", c->toString());
    } else {
        FATAL_ERROR("Constant Node %s not implemented!",
                    c->type->node_type_name());
    }
    return false;
}

bool CodeGenToz3::preorder(const IR::BoolLiteral *bl) {
    if (bl->value == true)
        builder->append("z3.BoolVal(True)");
    else
        builder->append("z3.BoolVal(False)");
    return false;
}

bool CodeGenToz3::preorder(const IR::StringLiteral *str) {
    auto var_string = str->value.replace("\n", "\\n");
    builder->appendFormat("z3.StringVal(\"%s\")", var_string);
    return false;
}

bool CodeGenToz3::preorder(const IR::Parameter *p) {
    /*
     * p->
     * (1) direction, inout, out, in
     * (2) type
     * (3) id for name
     */
    builder->append("P4Parameter(");

    if (p->direction == IR::Direction::InOut)
        builder->append("\"inout\", ");
    else if (p->direction == IR::Direction::Out)
        builder->append("\"out\", ");
    else if (p->direction == IR::Direction::In)
        builder->append("\"in\", ");
    else
        builder->append("\"none\", ");

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
    builder->appendFormat("ValueDeclaration(\"%s\", ", dc->name.name);
    if (dc->initializer) {
        visit(dc->initializer);
    } else {
        builder->append("None");
    }
    builder->appendFormat(", z3_type=");
    visit(dc->type);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Declaration_MatchKind *dm) {
    // TODO: Figure out what it means to declare a match kind
    builder->append("P4Declaration(\"match_kind\", [");
    for (auto kind : dm->members) {
        builder->appendFormat("\"%s\", ", kind->name.name);
    }
    builder->append("])");
    return false;
}

bool CodeGenToz3::preorder(const IR::Declaration_Variable *dv) {
    builder->appendFormat("ValueDeclaration(\"%s\", ", dv->name.name);
    if (dv->initializer) {
        builder->append("P4Initializer(");
        visit(dv->initializer);
        builder->append(", ");
        visit(dv->type);
        builder->append(")");
    } else {
        builder->append("None");
    }
    builder->appendFormat(", z3_type=");
    visit(dv->type);
    builder->append(")");
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

    builder->appendFormat("ControlDeclaration(P4ControlType(\"%s\", params=",
                          ctrl_name);
    visit(t->getApplyParameters());
    builder->append(", type_params=");
    visit(t->getTypeParameters());
    builder->append(")");
    builder->append(")");

    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Parser *t) {
    auto parser_name = t->name.name;

    builder->appendFormat("ControlDeclaration(P4ParserType(\"%s\", params=",
                          parser_name);
    visit(t->getApplyParameters());
    builder->append(", type_params=");
    visit(t->getTypeParameters());
    builder->append(")");
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Package *t) {
    auto t_name = t->getName().name;
    builder->appendFormat("ControlDeclaration(");
    builder->appendFormat("P4Package(z3_reg, \"%s\", params=", t_name);
    visit(t->getConstructorParameters());
    builder->append(",type_params=");
    visit(t->getTypeParameters());
    builder->append(")");
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
    builder->appendFormat("HeaderType(\"%s\", z3_reg, ", t->name.name);
    emit_args(t);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_HeaderUnion *t) {
    builder->appendFormat("HeaderUnionType(\"%s\", z3_reg,  ", t->name.name);
    emit_args(t);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Struct *t) {
    builder->appendFormat("StructType(\"%s\", z3_reg, ", t->name.name);
    emit_args(t);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Enum *t) {
    builder->appendFormat("Enum( \"%s\", [", t->name.name);
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
    builder->appendFormat("SerEnum( \"%s\", [", t->name.name);
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
    builder->appendFormat("Enum( \"%s\", [", t->name.name);
    for (auto m : t->members) {
        visit(m);
        builder->append(", ");
    }

    builder->append("])");
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Typedef *t) {
    builder->appendFormat("TypeDeclaration(\"%s\", ", t->name.name);
    visit(t->type);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Newtype *t) {
    builder->appendFormat("TypeDeclaration(\"%s\", ", t->name.name);
    visit(t->type);
    builder->append(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Bits *t) {
    builder->appendFormat("z3.BitVecSort(");

    if (t->expression) {
        builder->append("z3_reg.get_value(");
        visit(t->expression);
        builder->append(")");
    } else {
        builder->appendFormat("%d", t->size);
    }

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
    builder->appendFormat("z3.StringSort()");
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Varbits *t) {
    ::warning(ErrorType::WARN_UNSUPPORTED,
              "Replacing varbit %1% with bitvector.", t);
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
    // TODO(Fabian): Figure out a better way to instantiate
    builder->append("ListType(\"tuple\", z3_reg, [");
    for (auto c : t->components) {
        visit(c);
        builder->append(", ");
    }
    builder->append("])");
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Name *t) {
    builder->appendFormat("\"%s\"", t->path->name.name);
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Var *t) {
    builder->appendFormat("\"%s\"", t->getVarName());
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_InfInt *) {
    builder->append("z3.IntSort()");
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Dontcare *) {
    builder->append("None");
    return false;
}

bool CodeGenToz3::preorder(const IR::Type_Specialized *t) {
    builder->append("TypeSpecializer(");
    visit(t->baseType);
    builder->append(", ");
    for (auto arg : *t->arguments) {
        visit(arg);
        builder->append(", ");
    }
    builder->appendFormat(")");
    return false;
}

bool CodeGenToz3::preorder(const IR::Declaration_Instance *di) {
    builder->appendFormat("InstanceDeclaration(\"%s\", ", di->name.name);
    visit(di->type);
    builder->append(", ");
    for (auto arg : *di->arguments) {
        visit(arg);
        builder->append(", ");
    }
    builder->append(")");

    return false;
}

} // namespace TOZ3
