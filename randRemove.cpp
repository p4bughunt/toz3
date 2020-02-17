

#include "randRemove.h"



namespace TOZ3 {

const IR::Node* DoRandRemove::preorder(IR::Statement* stat) {
    if (rand()%100 < 10) {
        return nullptr;
    }
    else {
        return stat;
    }
}

} // namespace TOZ3


