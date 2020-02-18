

#include "randRemove.h"


namespace TOZ3 {
const IR::Node * DoRandRemove::preorder(IR::Statement *s) {
    // 10% chance to remove a statement
    if (rand() % 100 < 10)
        return nullptr;
    else
        return s;
}

const IR::Node * DoRandRemove::preorder(IR::BlockStatement *s) {
    return s;
}

const IR::Node * DoRandRemove::preorder(IR::ReturnStatement *s) {
    return s;
}

const IR::Node * DoRandRemove::preorder(IR::MethodCallStatement *s) {
    // there are certain method calls we can not omit
    // for example "emit" or "extract" affect the behavior of the (de)parser
    // so we use this hardcoded hack to let some expressions pass through
    if (s->methodCall) {
        if (auto m =  s->methodCall->method->to<IR::Member>()) {
            if ((safe_exprs.find(m->member.name) != safe_exprs.end())) {
                return s;
            }
        }
    }

    if (rand() % 100 < 10)
        return nullptr;
    else
        return s;
}
} // namespace TOZ3
