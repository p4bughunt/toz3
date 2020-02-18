

#include "randRemove.h"



namespace TOZ3 {

const IR::Node* DoRandRemove::preorder(IR::Statement* s) {
    // 10% chance to remove a statement
    if (rand()%100 < 10)
        return nullptr;
    else
        return s;
}

const IR::Node* DoRandRemove::preorder(IR::BlockStatement* s) {
        return s;
}

const IR::Node* DoRandRemove::preorder(IR::ReturnStatement* s) {
        return s;
}


} // namespace TOZ3


