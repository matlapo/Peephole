/*
 * JOOS is Copyright (C) 1997 Laurie Hendren & Michael I. Schwartzbach
 *
 * Reproduction of all or part of this software is permitted for
 * educational or research use on condition that this copyright notice is
 * included in any copy. This software comes with no warranty of any
 * kind. In no event will the authors be liable for any damages resulting from
 * use of this software.
 *
 * email: hendren@cs.mcgill.ca, mis@brics.dk
 */

/* iload x        iload x        iload x
 * ldc 0          ldc 1          ldc 2
 * imul           imul           imul
 * ------>        ------>        ------>
 * ldc 0          iload x        iload x
 *                               dup
 *                               iadd
 */

int simplify_multiplication_right(CODE **c)
{ int x,k;
  if (is_iload(*c,&x) &&
      is_ldc_int(next(*c),&k) &&
      is_imul(next(next(*c)))) {
     if (k==0) return replace(c,3,makeCODEldc_int(0,NULL));
     else if (k==1) return replace(c,3,makeCODEiload(x,NULL));
     else if (k==2) return replace(c,3,makeCODEiload(x,
                                       makeCODEdup(
                                       makeCODEiadd(NULL))));
     return 0;
  }
  return 0;
}

/* dup
 * astore x
 * pop
 * -------->
 * astore x
 */
int simplify_astore(CODE **c)
{ int x;
  if (is_dup(*c) &&
      is_astore(next(*c),&x) &&
      is_pop(next(next(*c)))) {
     return replace(c,3,makeCODEastore(x,NULL));
  }
  return 0;
}

/* iload x
 * ldc k   (0<=k<=127)
 * iadd
 * istore x
 * --------->
 * iinc x k
 */
int positive_increment(CODE **c)
{ int x,y,k;
  if (is_iload(*c,&x) &&
      is_ldc_int(next(*c),&k) &&
      is_iadd(next(next(*c))) &&
      is_istore(next(next(next(*c))),&y) &&
      x==y && 0<=k && k<=127) {
     return replace(c,4,makeCODEiinc(x,k,NULL));
  }
  return 0;
}

/* goto L1
 * ...
 * L1:
 * goto L2
 * ...
 * L2:
 * --------->
 * goto L2
 * ...
 * L1:    (reference count reduced by 1)
 * goto L2
 * ...
 * L2:    (reference count increased by 1)
 */
int simplify_goto_goto(CODE **c)
{ int l1,l2;
  if (is_goto(*c,&l1) && is_goto(next(destination(l1)),&l2)) {
     droplabel(l1);
     copylabel(l2);
     return replace(c,1,makeCODEgoto(l2,NULL));
  }
  return 0;
}

/***********************************/
/******** HELPER FUNCTIONS *********/
/***********************************/

CODE *makeCODEif(CODE *previous_if, int label, CODE *next)
{
  int l;
  if (is_if_acmpeq(previous_if, &l))
    return makeCODEif_acmpeq(label, next);
  if (is_if_acmpne(previous_if, &l))
    return makeCODEif_acmpne(label, next);
  if (is_if_icmpeq(previous_if, &l))
    return makeCODEif_icmpeq(label, next);
  if (is_if_icmpge(previous_if, &l))
    return makeCODEif_icmpge(label, next);
  if (is_if_icmpgt(previous_if, &l))
    return makeCODEif_icmpgt(label, next);
  if (is_if_icmple(previous_if, &l))
    return makeCODEif_icmple(label, next);
  if (is_if_icmplt(previous_if, &l))
    return makeCODEif_icmplt(label, next);
  if (is_if_icmpne(previous_if, &l))
    return makeCODEif_icmpne(label, next);
  if (is_ifeq(previous_if, &l))
    return makeCODEifeq(label, next);
  if (is_ifne(previous_if, &l))
    return makeCODEifne(label, next);
  if (is_ifnonnull(previous_if, &l))
    return makeCODEifnonnull(label, next);
  if (is_ifnull(previous_if, &l))
    return makeCODEifnull(label, next);

  return NULL;
}

CODE *makeCODEif_not(CODE *previous_if, int label, CODE *next)
{
  int l;
  if (is_if_acmpeq(previous_if, &l))
    return makeCODEif_acmpne(label, next);
  if (is_if_acmpne(previous_if, &l))
    return makeCODEif_acmpeq(label, next);
  if (is_if_icmpeq(previous_if, &l))
    return makeCODEif_icmpne(label, next);
  if (is_if_icmpge(previous_if, &l))
    return makeCODEif_icmplt(label, next);
  if (is_if_icmpgt(previous_if, &l))
    return makeCODEif_icmple(label, next);
  if (is_if_icmple(previous_if, &l))
    return makeCODEif_icmpgt(label, next);
  if (is_if_icmplt(previous_if, &l))
    return makeCODEif_icmpge(label, next);
  if (is_if_icmpne(previous_if, &l))
    return makeCODEif_icmpeq(label, next);
  if (is_ifeq(previous_if, &l))
    return makeCODEifne(label, next);
  if (is_ifne(previous_if, &l))
    return makeCODEifeq(label, next);
  if (is_ifnonnull(previous_if, &l))
    return makeCODEifnull(label, next);
  if (is_ifnull(previous_if, &l))
    return makeCODEifnonnull(label, next);

  return NULL;
}

/*  
 *  replace2 - replaces a sequence of instructions by another one
 *  Same as replace_modified but takes into account labels added in the replaced version of the code
 */
int replace2(CODE **c, int k, CODE *r)
{ 
  CODE *p = *c;
  int i;
  for (i = 0; i < k; i++) {
    int label;
    if (uses_label(p, &label) && !deadlabel(label))
      droplabel(label);
    p = p->next;
  }

  if (r == NULL) {
    *c = p;
  } else {
    int label;
    *c = r;
    if (uses_label(r, &label))
        copylabel(label);
    while (r->next != NULL) {
      r = r->next;
      if (uses_label(r, &label))
        copylabel(label);
    }
    r->next = p;
  }

  return 1;
}

/***********************************/
/***** OUR PATTERNS START HERE *****/
/***********************************/

/* [if] L1
 * ...
 * L1:
 * goto L2
 * ...
 * L2:
 * --------->
 * [if] L2
 * ...
 * L1:    (reference count reduced by 1)
 * goto L2
 * ...
 * L2:    (reference count increased by 1)
 */
int simplify_if_goto(CODE **c) {
  int l1,l2;
  if (is_if(c, &l1) && is_goto(next(destination(l1)), &l2)) {
    return replace2(c, 1, makeCODEif(*c, l2, NULL));
  }
  return 0;
}

/* [iconst_x, aconst_null, ldc x, iload x, aload x, dup]
 * pop
 * -------->
 */
/* Soundness: this is sound because we push onto the stack x than pop x, equivalent of doing nothing */
int simplify_push_pop(CODE **c)
{
  if ((is_simplepush(*c) || is_dup(*c)) && is_pop(next(*c)))
     return replace2(c, 2, NULL);
  return 0;
}

/* dup
 * istore x
 * pop
 * -------->
 * istore x
 */
/* Soundness: istore operation already takes care of popping the stack */
int simplify_dup_istore(CODE **c)
{
  int x = 0;
  if (is_dup(*c) && is_istore(next(*c), &x) && is_pop(nextby(*c, 2)))
     return replace2(c, 3, makeCODEistore(x, NULL));
  return 0;
}

/* iconst_0
 * if_icmpeq L
 * -------->
 * ifeq L
 */
 /* Soundness: ifeq already checks by default if it is 0, no need to load a const 0 */
int simplify_cmpeq_with_0_loaded(CODE **c)
{
  int x = 0;
  int y = 0;
  if (is_ldc_int(*c, &x) && x == 0 && is_if_icmpeq(next(*c), &y))
    return replace2(c, 2, makeCODEifeq(y, NULL));

  return 0;
}

/* iconst_0
 * if_icmpne L
 * -------->
 * ifne L
 */
 /* Soundness: same as above, but for cmpne */
int simplify_icmpne_with_0_loaded(CODE **c)
{
  int x = 0;
  int y = 0;
  if (is_ldc_int(*c, &x) && x == 0 && is_if_icmpne(next(*c), &y))
    return replace2(c, 2, makeCODEifne(y, NULL));
  return 0;
}

/*
 * aload x or iload x
 * const_0
 * add
 * -------->
 * aload x or iload x
*/
int simplify_add_0(CODE **c)
{
  int x = 0;
  int k = 0;
  if (is_aload(*c, &x) && is_ldc_int(next(*c), &k) && k == 0 && is_iadd(next(next(*c))))
    return replace2(c, 3, makeCODEaload(x, NULL));
  else if (is_iload(*c, &x) && is_ldc_int(next(*c), &k) && k == 0 && is_iadd(next(next(*c))))
    return replace2(c, 3, makeCODEiload(x, NULL));
  return 0;
}

/*
 * aload x or iload x
 * const_0
 * mul
 * -------->
 * aload x or iload x
*/
int simplify_mul_1(CODE **c)
{
  int x = 0;
  int k = 0;
  if (is_aload(*c, &x) && is_ldc_int(next(*c), &k) && k == 1 && is_imul(next(next(*c))))
    return replace2(c, 3, makeCODEaload(x, NULL));
  else if (is_iload(*c, &x) && is_ldc_int(next(*c), &k) && k == 1 && is_imul(next(next(*c))))
      return replace2(c, 3, makeCODEiload(x, NULL));
  return 0;
}

/* goto L
 * L:
 * ...
 * -------->
 * L:
 */
 /* Soundness: goto L followed directly by the label it refers is the same as the label itself */
int simplify_unecessary_goto(CODE **c)
{
  int x = 0;
  int y = 0;
  if (is_goto(*c, &x) && is_label(next(*c), &y) && x == y)
    return replace2(c, 2, makeCODElabel(x, NULL));
  return 0;
}

/* [if] L
 * L:
 * ...
 * -------->
 * L:
 */
 /* Soundness: any if L followed directly by the label it refers is the same as the label itself */
int simplify_unecessary_if(CODE **c)
{
  int x = 0;
  int y = 0;
  if (is_if(c, &x) && is_label(next(*c), &y) && x == y)
    return replace2(c, 2, makeCODElabel(x, NULL));
  return 0;
}

/* aload x
 * aload x
 * -------->
 * aload x
 * dup
 */
int simplify_double_aload(CODE **c)
{
  int x = 0;
  int y = 0;
  if (is_aload(*c, &x) && is_aload(next(*c), &y) && x == y)
    return replace2(c, 2, makeCODEaload(x, makeCODEdup(NULL)));
  return 0;
}

/*
 * iload x
 * iload x
 * -------->
 * iload x
 * dup
*/
int simplify_double_iload(CODE **c)
{
  int x = 0;
  int y = 0;
  if (is_iload(*c, &x) && is_iload(next(*c), &y) && x == y)
    return replace2(c, 2, makeCODEiload(x,
                         makeCODEdup(NULL)
    ));
  return 0;
}

/*
 * istore x
 * iload x
 * ------>
 * dup
 * istore x
 */
int simplify_istore_iload(CODE **c)
{
  int x = 0;
  int y = 0;
  if (is_istore(*c, &x) && is_iload(next(*c), &y) && x == y)
    return replace2(c, 2, makeCODEdup(makeCODEistore(x, NULL)));
  return 0;
}

/*
 * astore x
 * aload x
 * ------>
 * dup
 * astore x
 */
int simplify_astore_aload(CODE **c)
{
  int x = 0;
  int y = 0;
  if (is_astore(*c, &x) && is_aload(next(*c), &y) && x == y)
    return replace2(c, 2, makeCODEdup(makeCODEastore(x, NULL)));
  return 0;
}

/*
 * goto L1
 * ...
 * L1:
 * L2:
 * --------->
 * goto L2
 * ...
 * L1:
 * L2:
 */
int simplify_goto_label(CODE **c)
{
  int l1;
  int l2;
  if (is_goto(*c, &l1) && is_label(next(destination(l1)), &l2)) {
    return replace2(c, 1, makeCODEgoto(l2, NULL));
  }
  return 0;
}

/*
 * [if] L1
 * ...
 * L1:
 * L2:
 * --------->
 * [if] L2
 * ...
 * L1:
 * L2:
 */
int simplify_if_label(CODE **c)
{
  int l1;
  int l2;
  if (is_if(c, &l1) && is_label(next(destination(l1)), &l2)) {
    return replace2(c, 1, makeCODEif(*c, l2, NULL));
  }
  return 0;
}

/*
 * L:
 * --------->
 *
 */
int simplify_unecessary_label(CODE **c)
{
  int x = 0;
  if (is_label(*c, &x) && deadlabel(x))
    return replace2(c, 1, NULL);
  return 0;
}

/*
 * aload x
 * getfield y
 * aload x
 * getfield y
 * --------->
 * aload x
 * getfield y
 * dup
 * Soundess: same logic as double aload, but with an object field.
 */
int simplify_double_getfield(CODE **c)
{
  int x1 = 0;
  char* y1 = 0;
  int x2 = 0;
  char* y2 = 0;
  CODE* inst1 = *c;
  CODE* inst2 = next(inst1);
  CODE* inst3 = next(inst2);
  CODE* inst4 = next(inst3);
  if (is_aload(inst1, &x1) && is_getfield(inst2, &y1)
  && is_aload(inst3, &x2) && is_getfield(inst4, &y2)
  && x1 == x2 && strcmp(y1, y2) == 0)
    return replace2(c, 4, makeCODEaload(x1, makeCODEgetfield(y1, makeCODEdup(NULL))));
  return 0;
}

/*
 * iconst_0
 * ifeq L1
 * -------->
 * goto L1
 */
int remove_unecessary_ifeq(CODE **c)
{
  int x;
  int l1;
  if (is_ldc_int(*c, &x) && is_ifeq(next(*c), &l1) && x == 0){
    return replace2(c, 2, makeCODEgoto(l1, NULL));
  }
  return 0;
}

/*
 * iconst_1
 * ifeq L1
 * -------->
 */
int remove_unecessary_ifeq2(CODE **c)
{
  int x;
  int l1;
  if (is_ldc_int(*c, &x) && x == 1 && is_ifeq(next(*c), &l1)) {
    return replace2(c, 2, NULL);
  }
  return 0;
}

/*
 * if_* L1 // If true, add a 1 on the stack, add 0 otherwise
 * iconst_0
 * goto L2
 * L1:
 * iconst_1
 * L2:
 * dup
 * ifeq L3 // If stack has 0, keep 0 to L3. Otherwise, pop the 1 and continue
 * pop
 * ...
 * L3:
 * ifeq L4 // If the jump is coming from L3, it will necessarily go to L4 since there is a 0 on the stack
 * --------> If L1 and L2 are NOT unique
 * [reverse if_*] L4
 * L1:
 * iconst_1
 * L2:
 * dup
 * ifeq L3
 * pop
 * ...
 * L3:
 * ifeq L4
 * --------> If L1 and L2 are unique
 * [reverse if_*] L4
 * ...
 * L3:
 * ifeq L4
 * Soundness: this one is a bit complicated. I tried adding comments to the code to explain how it works. Also, if L1 and L2 are only referenced once, we can remove them. They are doing nothing since they add 1 to the stack, then duplicates it, then compare ifeq (which always fails) then pop to cancel the duplicate. Therefore, this code can be deleted since it makes no sence without the code we initially removed.
 */
int remove_unecessary_if(CODE **c)
{
  int l1_1, l1_2, l2_1, l2_2, l3, l4, x;

  CODE* inst0 = *c;           /* if_* L1 */
  CODE* inst1 = next(inst0);  /* iconst_0 */
  CODE* inst2 = next(inst1);  /* goto L2 */
  CODE* inst3 = next(inst2);  /* L1: */
  CODE* inst4 = next(inst3);  /* iconst_1 */
  CODE* inst5 = next(inst4);  /* L2: */
  CODE* inst6 = next(inst5);  /* dup */
  CODE* inst7 = next(inst6);  /* ifeq L3 */
  CODE* inst8 = next(inst7);  /* pop */

  if(is_if(c, &l1_1)
  && is_ldc_int(inst1, &x) && x == 0
  && is_goto(inst2, &l2_1)
  && is_label(inst3, &l1_2)
  && is_ldc_int(inst4, &x) && x == 1
  && is_label(inst5, &l2_2)
  && is_dup(inst6)
  && is_ifeq(inst7, &l3)
  && is_pop(inst8)
  && is_ifeq(next(destination(l3)), &l4)
  && l1_1 == l1_2 && l2_1 == l2_2) {
    if (!uniquelabel(l1_1) || !uniquelabel(l2_2)) {
      return replace2(c, 9, makeCODEif_not(*c, l4, makeCODElabel(l1_1, makeCODEldc_int(1, makeCODElabel(l2_1, makeCODEdup(makeCODEifeq(l3, makeCODEpop(NULL))))))));
    } else {
      return replace2(c, 9, makeCODEif_not(*c, l4, NULL));
    }
  }
  return 0;
}

/*
 * if_* L1 // If true, add a 1 on the stack, add 0 otherwise
 * iconst_0
 * goto L2
 * L1:
 * iconst_1
 * L2:
 * dup
 * ifeq L3 // If stack has 0, keep 0 to L3. Otherwise, pop the 1 and continue
 * pop
 * ...
 * L3:
 * dup
 * ifeq L4 // If the jump is coming from L3, it will necessarily go to L4 since there is a 0 on the stack
 * pop
 * --------> If L1 and L2 are NOT unique
 * [reverse if_*] L4
 * L1:
 * iconst_1
 * L2:
 * dup
 * ifeq L3
 * pop
 * ...
 * L3:
 * dup
 * ifeq L4
 * pop
 * --------> If L1 and L2 are unique
 * [reverse if_*] L4
 * ...
 * L3:
 * dup
 * ifeq L4
 * pop
 * ...
 * L6:
 * ifeq L7 // Stop after last else
 * Soundness: this one is a bit complicated. I tried adding comments to the code to explain how it works. Also, if L1 and L2 are only referenced once, they are doing nothing since they add 1 to the stack, then removes duplicates it, then compare ifeq (which always fails) then pop to cancel the duplicate. Therefore, this code can be deleted since it makes no sence without the code we initially removed.
 */
/* FIXME: I don't think it can work because after the jump to L4 there needs to ne a zero on the stack. A solution might be to follow thr ifeq until there is one without dup in front. */
int remove_unecessary_ifeq4(CODE **c)
{
  int l1_1, l1_2, l2_1, l2_2, l3, l4, x;

  CODE* inst0 = *c;           /* if_* L1 */
  CODE* inst1 = next(inst0);  /* iconst_0 */
  CODE* inst2 = next(inst1);  /* goto L2 */
  CODE* inst3 = next(inst2);  /* L1: */
  CODE* inst4 = next(inst3);  /* iconst_1 */
  CODE* inst5 = next(inst4);  /* L2: */
  CODE* inst6 = next(inst5);  /* dup */
  CODE* inst7 = next(inst6);  /* ifeq L3 */
  CODE* inst8 = next(inst7);  /* pop */

  if(is_if(c, &l1_1)
  && is_ldc_int(inst1, &x) && x == 0
  && is_goto(inst2, &l2_1)
  && is_label(inst3, &l1_2)
  && is_ldc_int(inst4, &x) && x == 1
  && is_label(inst5, &l2_2)
  && is_dup(inst6)
  && is_ifeq(inst7, &l3)
  && is_pop(inst8)
  && is_ifeq(next(destination(l3)), &l4)
  && l1_1 == l1_2 && l2_1 == l2_2) {
    if (!uniquelabel(l1_1) || !uniquelabel(l2_2)) {
      return replace2(c, 9, makeCODEif_not(*c, l4, makeCODElabel(l1_1, makeCODEldc_int(1, makeCODElabel(l2_1, makeCODEdup(makeCODEifeq(l3, makeCODEpop(NULL))))))));
    } else {
      return replace2(c, 9, makeCODEif_not(*c, l4, NULL));
    }
  }
  return 0;
}

/*
 * iconst_1
 * ifne L1
 * -------->
 * goto L1
 */
int remove_unecessary_ifne(CODE **c)
{
  int x;
  int l1;
  if (is_ldc_int(*c, &x) && is_ifne(next(*c), &l1) && x == 1){
    return replace2(c, 2, makeCODEgoto(l1, NULL));
  }
  return 0;
}

/*
 * iconst_0
 * ifne L1
 * -------->
 */
int remove_unecessary_ifne2(CODE **c)
{
  int x;
  int l1;
  if (is_ldc_int(*c, &x) && x == 0 && is_ifne(next(*c), &l1)){
    return replace2(c, 2, NULL);
  }
  return 0;
}

/*
 * iconst_1
 * iconst_0
 * iadd
 * -------->
 * iconst_1
 */
int remove_one_plus_zero(CODE **c)
{
  int x;
  if (is_ldc_int(*c, &x) && x == 1 && is_ldc_int(*c, &x) && x == 0 && is_iadd(next(next(*c)))){
    return replace2(c, 3, makeCODEldc_int(x, NULL));
  }
  return 0;
}

/*
 * iconst_0
 * goto L1
 * ...
 * L1:
 * ifeq L2
 * ------->
 * goto L2
 * ...
 * L1:
 * ifeq L2
 */
int remove_unecessary_ldc_int(CODE **c)
{
  int x;
  int l1;
  int l2;
  if (is_ldc_int(*c, &x) && x == 0 && is_goto(next(*c), &l1) && is_ifeq(next(destination(l1)), &l2)) {
    return replace2(c, 2, makeCODEgoto(l2, NULL));
  }
  return 0;
}

/*
 * iconst_1
 * goto L1
 * ...
 * L1:
 * ifne L2
 * ------->
 * goto L2
 * ...
 * L1:
 * ifne L2
 */
int remove_unecessary_ldc_int2(CODE **c)
{
  int x;
  int l1;
  int l2;
  if (is_ldc_int(*c, &x) && x == 1 && is_goto(next(*c), &l1) && is_ifne(next(destination(l1)), &l2)) {
    return replace2(c, 2, makeCODEgoto(l2, NULL));
  }
  return 0;
}

/*
 * [return, goto]
 * [not a label, dead label]
 * --------->
 * [return, goto]
 */
int remove_deadcode(CODE **c)
{
  int x, l;
  if (is_return(*c) && (*c)->next != NULL && !(is_label(next(*c), &x)))
    return replace2(c, 2, makeCODEreturn(NULL));
  if (is_areturn(*c) && (*c)->next != NULL && !(is_label(next(*c), &x)))
    return replace2(c, 2, makeCODEareturn(NULL));
  if (is_ireturn(*c) && (*c)->next != NULL && !(is_label(next(*c), &x)))
    return replace2(c, 2, makeCODEireturn(NULL));
  if (is_goto(*c, &l) && (*c)->next != NULL && !(is_label(next(*c), &x)))
    return replace2(c, 2, makeCODEgoto(l, NULL));
  return 0;
}

/*
 * goto L1
 * ...
 * L1:
 * return
 * ----->
 * return
 * ...
 * L1:
 * return
 */
int inline_return(CODE **c)
{
  int l;
  if (is_goto(*c, &l) && is_return(next(destination(l)))) {
    return replace2(c, 1, makeCODEreturn(NULL));
  }
  if (is_goto(*c, &l) && is_areturn(next(destination(l)))) {
    return replace2(c, 1, makeCODEareturn(NULL));
  }
  if (is_goto(*c, &l) && is_ireturn(next(destination(l)))) {
    return replace2(c, 1, makeCODEireturn(NULL));
  }
  return 0;
}

/* [if_cmpge, if_cmpgt, if_cmple, if_cmplt, if_cmpeq, if_cmpne, if_acmpeq, if_acmpne, ifeq, ifne, ifnull, ifnonnull] L1
 * goto L2
 * L1:
 * ------->
 * [if_cmplt, if_cmple, if_cmpgt, if_cmpge, if_cmpne, if_cmpne, if_acmpne, if_acmpne, ifne, ifeq, ifnonnull, ifnull] L2
 * L1:
 */
int inverse_cmp(CODE **c) {
  int l1;
  int l2;
  int l3;
  if (is_if(c, &l1) && is_goto(next(*c), &l2) && is_label(next(next(*c)), &l3) && l1 == l3) {
    return replace2(c, 2, makeCODEif_not(*c, l2, NULL));
  }
  return 0;
}
/*
 * iconst x
 * istore y
 * iconst x
 * istore z
 * ------>
 * iconst x
 * dup
 * istore y
 * istore z
 */
int duplicate_store(CODE **c) {
  int x1;
  int x2;
  int y;
  int z;
  if (is_ldc_int(*c, &x1)
  && is_istore(next(*c), &y)
  && is_ldc_int(next(next(*c)), &x2)
  && is_istore(next(next(next(*c))), &z)
  && x1 == x2) {
    return replace2(c, 4, makeCODEldc_int(x1, makeCODEdup(makeCODEistore(y, makeCODEistore(z, NULL)))));
  }
  return 0;
}

/*
 * if_* L1
 * iconst_0
 * goto L2
 * L1:
 * iconst_1
 * L2:
 * ifeq L3
 * ------>
 * if_* L3
 */
int simplify_local_branching_01eq(CODE **c) {
  int l1, l2, l3, l4, l5, k1, k2;
  if (
    is_if(c, &l1) && uniquelabel(l1) &&
    is_ldc_int(nextby(*c, 1), &k1) && k1 == 0 &&
    is_goto(nextby(*c, 2), &l2) && uniquelabel(l2) &&
    is_label(nextby(*c, 3), &l3) && l3 == l1 &&
    is_ldc_int(nextby(*c, 4), &k2) && k2 == 1 &&
    is_label(nextby(*c, 5), &l4) && l4 == l2 &&
    is_ifeq(nextby(*c, 6), &l5) &&
    uniquelabel(l1) && uniquelabel(l2)
  ) {
    return replace2(c, 7, makeCODEif_not(*c, l5, NULL));
  }
  return 0;
}

/*
 * if_* L1
 * iconst_0
 * goto L2
 * L1:
 * iconst_1
 * L2:
 * ifne L3
 * ------>
 * if_* L3
 */
int simplify_local_branching_01ne(CODE **c) {
  int l1, l2, l3, l4, l5, k1, k2;
  if (
    is_if(c, &l1) && uniquelabel(l1) &&
    is_ldc_int(nextby(*c, 1), &k1) && k1 == 0 &&
    is_goto(nextby(*c, 2), &l2) && uniquelabel(l2) &&
    is_label(nextby(*c, 3), &l3) && l3 == l1 &&
    is_ldc_int(nextby(*c, 4), &k2) && k2 == 1 &&
    is_label(nextby(*c, 5), &l4) && l4 == l2 &&
    is_ifne(nextby(*c, 6), &l5) &&
    uniquelabel(l1) && uniquelabel(l2)
  ) {
    return replace2(c, 7, makeCODEif(*c, l5, NULL));
  }
  return 0;
}

/*
 * if_* L1
 * iconst_1
 * goto L2
 * L1:
 * iconst_0
 * L2:
 * ifeq L3
 * ------>
 * if_* L3
 */
int simplify_local_branching_10eq(CODE **c) {
  int l1, l2, l3, l4, l5, k1, k2;
  if (
    is_if(c, &l1) && uniquelabel(l1) &&
    is_ldc_int(nextby(*c, 1), &k1) && k1 == 1 &&
    is_goto(nextby(*c, 2), &l2) && uniquelabel(l2) &&
    is_label(nextby(*c, 3), &l3) && l3 == l1 &&
    is_ldc_int(nextby(*c, 4), &k2) && k2 == 0 &&
    is_label(nextby(*c, 5), &l4) && l4 == l2 &&
    is_ifeq(nextby(*c, 6), &l5) &&
    uniquelabel(l1) && uniquelabel(l2)
  ) {
    return replace2(c, 7, makeCODEif(*c, l5, NULL));
  }
  return 0;
}

/*
 * if_* L1
 * iconst_1
 * goto L2
 * L1:
 * iconst_0
 * L2:
 * ifne L3
 * ------>
 * if_* L3
 */
int simplify_local_branching_10ne(CODE **c) {
  int l1, l2, l3, l4, l5, k1, k2;
  if (
    is_if(c, &l1) && uniquelabel(l1) &&
    is_ldc_int(nextby(*c, 1), &k1) && k1 == 1 &&
    is_goto(nextby(*c, 2), &l2) && uniquelabel(l2) &&
    is_label(nextby(*c, 3), &l3) && l3 == l1 &&
    is_ldc_int(nextby(*c, 4), &k2) && k2 == 0 &&
    is_label(nextby(*c, 5), &l4) && l4 == l2 &&
    is_ifne(nextby(*c, 6), &l5) &&
    uniquelabel(l1) && uniquelabel(l2)
  ) {
    return replace2(c, 7, makeCODEif_not(*c, l5, NULL));
  }
  return 0;
}

/*
 * aconst_null
 * [if_acmpeq, if_acmpne] L
 * ------>
 * [ifnull, ifnonnull] L
 */
int collapse_if_null(CODE **c) {
  int l;
  if (is_aconst_null(*c) && is_if_acmpeq(next(*c), &l))
    return replace2(c, 2, makeCODEifnull(l, NULL));
  if (is_aconst_null(*c) && is_if_acmpne(next(*c), &l))
    return replace2(c, 2, makeCODEifnonnull(l, NULL));
  return 0;
}

/*
 * dup
 * astore x
 * dup
 * ------->
 * dup2
 * astore x
 * Cannot do this peephole optimizer does not support dup2 :(
 */


void init_patterns(void) {
	ADD_PATTERN(simplify_multiplication_right);
	ADD_PATTERN(simplify_astore);
	ADD_PATTERN(positive_increment);
	ADD_PATTERN(simplify_goto_goto);
	ADD_PATTERN(simplify_if_goto);
	ADD_PATTERN(simplify_push_pop);
  ADD_PATTERN(simplify_dup_istore);
  ADD_PATTERN(simplify_cmpeq_with_0_loaded);
  ADD_PATTERN(simplify_icmpne_with_0_loaded);
  ADD_PATTERN(simplify_unecessary_goto);
  ADD_PATTERN(simplify_unecessary_if);
  ADD_PATTERN(simplify_double_aload);
  ADD_PATTERN(simplify_double_iload);
  ADD_PATTERN(simplify_astore_aload);
  ADD_PATTERN(simplify_istore_iload);
  ADD_PATTERN(simplify_double_getfield);
  ADD_PATTERN(simplify_add_0);
  ADD_PATTERN(simplify_mul_1);
  ADD_PATTERN(simplify_unecessary_label);
  ADD_PATTERN(simplify_goto_label);
  ADD_PATTERN(simplify_if_label);
  ADD_PATTERN(remove_one_plus_zero);
  ADD_PATTERN(remove_unecessary_ldc_int);
  ADD_PATTERN(remove_unecessary_ldc_int2);
  ADD_PATTERN(remove_unecessary_ifeq);
  ADD_PATTERN(remove_unecessary_ifeq2);
  ADD_PATTERN(remove_unecessary_if);
  ADD_PATTERN(remove_unecessary_ifne);
  ADD_PATTERN(remove_unecessary_ifne2);
  ADD_PATTERN(inline_return);
  ADD_PATTERN(inverse_cmp);
  ADD_PATTERN(remove_deadcode);
  ADD_PATTERN(duplicate_store);
  ADD_PATTERN(simplify_local_branching_01ne);
  ADD_PATTERN(simplify_local_branching_01eq);
  ADD_PATTERN(simplify_local_branching_10ne);
  ADD_PATTERN(simplify_local_branching_10eq);
  ADD_PATTERN(collapse_if_null);
}
