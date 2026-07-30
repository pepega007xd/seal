// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks
//
// SPDX-FileCopyrightText: 2023 Broom team
//
// SPDX-License-Identifier: GPL-3.0-or-later
/**
 * Singly-Linked Nested List twice times
 * Functions which create, traverse, and destroy list
 */

#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);
// void __VERIFIER_plot(const char *name, ...);
#define random() __VERIFIER_nondet_int()

struct node {
    struct node *next1;
    struct internal_node *nested1,*nested2;
};

struct internal_node {
    struct internal_node *next2;
};

struct node* alloc_and_zero(void)
{
    struct node *pi = malloc(sizeof(*pi));
    pi->next1 = NULL;
    pi->nested1 = NULL;
    pi->nested2 = NULL;

    return pi;
}

struct internal_node* alloc_and_zero_internal(void)
{
    struct internal_node *pi = malloc(sizeof(*pi));
    pi->next2 = NULL;

    return pi;
}

struct internal_node* create_internal(void)
{
    struct internal_node *sll = alloc_and_zero_internal();
    struct internal_node *now = sll;

    while(random()) {
        now->next2 = alloc_and_zero_internal();
        now = now->next2;
    }
    return sll;
}

struct node* create(void)
{
    struct node *sll = alloc_and_zero();
    struct node *now = sll;
    now->nested1 = create_internal();
    now->nested2 = create_internal();

    while(random()) {
        now->next1 = alloc_and_zero();
        now->next1->nested1 = create_internal();
        now->next1->nested2 = create_internal();
        now = now->next1;
    }
    return sll;
}

void loop_internal(struct internal_node *l)
{
    while (l) {
        l = l->next2;
    }
}

void loop(struct node *l)
{
    __VERIFIER_print_state();
    while(l) {
        loop_internal(l->nested1);
        loop_internal(l->nested2);
        l = l->next1;
    }
    __VERIFIER_print_state();
}

void destroy_internal(struct internal_node *l)
{
    while (l) {
        struct internal_node *next2 = l->next2;
        free(l);
        l = next2;
    }
}

void destroy(struct node *l)
{
    while (l) {
        struct node *next1 = l->next1;
        destroy_internal(l->nested1);
        destroy_internal(l->nested2);
        free(l);
        l = next1;
    }
}

int main()
{
    struct node *lx = create();
    // __VERIFIER_plot("create");
    __VERIFIER_print_state();
    loop(lx);
    __VERIFIER_print_state();
    destroy(lx);
    return 0;
}
