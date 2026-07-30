#include <stdio.h>
#include <stdlib.h>

#include "../utils.h"
#include "../nondet_builtins.h"

typedef struct sll {
    struct sll *next;
} sll;

struct sll* sll_create()
{
    sll *head = NULL;

    while(__VERIFIER_nondet_bool()) {
        sll *new = malloc(sizeof(sll));
        new->next = head;
        head = new;
    }

    return head;
}

void sll_loop(sll *list)
{
    __VERIFIER_print_state();
    while (list) {
        printf("%p -> %p\n", list, list->next);
        list = list->next;
    }
    __VERIFIER_print_state();
}

void sll_destroy(sll *list)
{
    while (list) {
        sll *tmp = list->next;
        free(list);
        list = tmp;
    }
}

int main()
{
    sll *list2 = sll_create();
    sll_loop(list2);
    __VERIFIER_print_state();
    sll_destroy(list2);
    return 0;
}
