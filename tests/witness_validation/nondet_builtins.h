#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

bool __VERIFIER_nondet_bool() {
    bool b; //= arc4random() & 1;
    return b;
}

bool __VERIFIER_nondet_int() {
    int i; //= arc4random() & 1;
    return i;
}
