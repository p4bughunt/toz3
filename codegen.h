#ifndef _TOZ3_CODEGEN_H_
#define _TOZ3_CODEGEN_H_

#include <vector>
#include <map>

#include "ir/ir.h"
#include "lib/sourceCodeBuilder.h"

#ifndef TAO_INDENT
#define TAO_INDENT "    "
#endif

namespace TOZ3 {

static cstring indent(int dep) {
    std::stringstream ss;
    for (int i=0; i<dep; i++) {
        ss << TAO_INDENT;
    }
    return ss.str();
}


class SourceBuilder {
public:
    Util::SourceCodeBuilder* builder = nullptr;

    static cstring indent(int dep) {
        std::stringstream ss;
        for (int i=0; i<dep; i++) {
            ss << TAO_INDENT;
        }
        return ss.str();
    }

    SourceBuilder() {
        builder = new Util::SourceCodeBuilder();
    }

    std::string toString() {
        return builder->toString();
    }

    void append(cstring str) {
        builder->appendFormat("%s", str);
    }

    void append(int dep, cstring str) {
        builder->appendFormat("%s%s", indent(dep), str);
    }

    void appendFormat(const char* format, ...) {
        va_list ap;
        va_start(ap, format);
        cstring str = Util::vprintf_format(format, ap);
        va_end(ap);
        append(str);
    }

    void appendFormat(int dep, const char* format, ...) {
        builder->append(indent(dep));
        va_list ap;
        va_start(ap, format);
        cstring str = Util::vprintf_format(format, ap);
        va_end(ap);
        append(str);
    }

    void newline() {
        builder->append("\n");
    }
    void newline(int dep) {
        builder->appendFormat("%s\n", indent(dep));
    }

    cstring emit() {
        return builder->toString();
    }
};

struct V1Switch {
    cstring p;
    cstring vr;
    cstring ig;
    cstring eg;
    cstring ck;
    cstring dep;
};


class CodeGenToz3 : public Inspector {
protected:

    // for table
    cstring tab_name;
    // for action
    cstring act_name;

    // for slice op
    int con_val = 0;
    int slice_l = 0;
    int slice_r = 0;


    // reserved keywords
    std::vector<std::string> key_words = {"action_run"};


    int if_keywords = 0;
    int if_stmtadd = 0;
    int if_inswitchstmt = 0;
    struct V1Switch v1sw;

public:
    int depth;
    std::ostream* outStream = nullptr;
    SourceBuilder* builder = nullptr;

    CodeGenToz3(int dep, std::ostream* ostream) :
                    depth(dep), outStream(ostream) {
        visitDagOnce = false;

        builder = new SourceBuilder();
    }

    // for initilization and ending
    Visitor::profile_t init_apply(const IR::Node* node) override;
    void end_apply(const IR::Node* node) override;


    cstring emit() {
        return builder->emit();
    }



    bool preorder(const IR::Expression* expr) override {    P4C_UNIMPLEMENTED("expr %s: not yet supported",
         expr->node_type_name()); return false; }
    bool preorder(const IR::StatOrDecl* expr) override
    {          P4C_UNIMPLEMENTED("expr %s: not yet supported",
         expr->node_type_name()); return false; }
    bool preorder(const IR::PropertyValue* expr) override
    {          P4C_UNIMPLEMENTED("expr %s: not yet supported",
         expr->node_type_name()); return false; }
    bool preorder(const IR::Statement* expr) override
    { P4C_UNIMPLEMENTED("expr %s: not yet supported",
        expr->node_type_name()); return false; }

    bool preorder(const IR::TableProperties* tbp) override
    { BUG("tbp %1%: not supported", tbp); return false; }


    bool preorder(const IR::P4Control* c) override;
    bool preorder(const IR::P4Parser* p) override;
    bool preorder(const IR::P4Action* p4action) override;
    bool preorder(const IR::P4Table* p4table) override;
    bool preorder(const IR::Declaration_Variable* dv) override;
    bool preorder(const IR::Parameter* param) override;

    // Statement
    bool preorder(const IR::BlockStatement* b) override;
    bool preorder(const IR::AssignmentStatement* as) override;
    bool preorder(const IR::MethodCallStatement* mcs) override;
    bool preorder(const IR::IfStatement* ifs) override;
    bool preorder(const IR::SwitchStatement* ss) override;
    bool preorder(const IR::SwitchCase* sc) override;

    // Expression
    bool preorder(const IR::Member *m) override;
    bool preorder(const IR::PathExpression* p) override;
    bool preorder(const IR::DefaultExpression*) override;
    bool preorder(const IR::ListExpression* le) override;
    bool preorder(const IR::MethodCallExpression* mce) override;
    bool preorder(const IR::Constant* c) override;
    bool preorder(const IR::BoolLiteral* bl) override;
    bool preorder(const IR::Cast* c) override;
    bool preorder(const IR::Concat* c) override;
    bool preorder(const IR::Slice* s) override;

    // TODO: not all operations supported
    // Fabian: We can implement a general solution here and just change the string
    bool preorder(const IR::Neg* expr) override;
    bool preorder(const IR::Cmpl* expr) override;
    bool preorder(const IR::LNot* expr) override;
    bool preorder(const IR::Mul* expr) override;
    bool preorder(const IR::Div* expr) override;
    bool preorder(const IR::Mod* expr) override;
    bool preorder(const IR::Add* expr) override;
    bool preorder(const IR::Sub* expr) override;
    bool preorder(const IR::Shl* expr) override;
    bool preorder(const IR::Shr* expr) override;
    bool preorder(const IR::Equ* expr) override;
    bool preorder(const IR::Neq* expr) override;
    bool preorder(const IR::Lss* expr) override;
    bool preorder(const IR::Leq* expr) override;
    bool preorder(const IR::Grt* expr) override;
    bool preorder(const IR::Geq* expr) override;
    bool preorder(const IR::BAnd* expr) override;
    bool preorder(const IR::BOr* expr) override;
    bool preorder(const IR::BXor* expr) override;
    bool preorder(const IR::LAnd* expr) override;
    bool preorder(const IR::LOr* expr) override;

    bool preorder(const IR::Property* p) override;
    bool preorder(const IR::ActionList* acl) override;
    bool preorder(const IR::Key* key) override;
    bool preorder(const IR::KeyElement* ke) override;
    bool preorder(const IR::ExpressionValue* ev) override;

    /***** types *****/
    bool preorder(const IR::Type* t) {
        P4C_UNIMPLEMENTED("type %1% not supported", t);
        return false;
    }
    bool preorder(const IR::Type_Struct* t) override;
    bool preorder(const IR::Type_Header* t) override;
    bool preorder(const IR::Type_Typedef* t) override;
    bool preorder(const IR::Type_Bits* t) override;
    bool preorder(const IR::Type_Varbits* t) override;
    bool preorder(const IR::Type_Name* t) override;
    bool preorder(const IR::Type_Boolean* t) override;
    bool preorder(const IR::Type_Stack* t) override;
    bool preorder(const IR::Type_InfInt*) override;
    bool preorder(const IR::ArrayIndex* a) override;

    // declarations
    bool preorder(const IR::Declaration_Instance* di) override;


    /********************************************************************/
    /* Skip these types */
    bool preorder(const IR::Method*) override { return false; }
    bool preorder(const IR::Vector<IR::Argument>*) override { return false; }

    bool preorder(const IR::Type_Tuple*) override { return false; }
    bool preorder(const IR::Type_Error*) override { return false; }
    bool preorder(const IR::Type_Enum*) override { return false; }
    bool preorder(const IR::Type_Extern*) override { return false; }
    bool preorder(const IR::Type_Parser*) override { return false; }
    bool preorder(const IR::Type_Control*) override { return false; }
    bool preorder(const IR::Type_Package*) override { return false; }
    bool preorder(const IR::Declaration*) override { return false; }
    bool preorder(const IR::TypeNameExpression*) override { return false; }

};


} // namespace TOZ3




#endif // _TOZ3_CODEGEN_H_
