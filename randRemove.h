#ifndef _RAND_REMOVE_H_
#define _RAND_REMOVE_H_


#include "ir/ir.h"

#include "sub_toP4.h"


namespace TOZ3 {

class DoRandRemove : public Transform {

public:

    explicit DoRandRemove() {
        setName("DoRandRemove");
    }

    ~DoRandRemove() {
    }

    std::set<cstring>safe_exprs      = {"emit", "extract"};

    const IR::Node* preorder(IR::Statement *s);
    const IR::Node* preorder(IR::BlockStatement *s);
    const IR::Node* preorder(IR::ReturnStatement *s);
    const IR::Node* preorder(IR::MethodCallStatement *s);


};

} // namespace TOZ3


#endif // _RAND_REMOVE_H_
