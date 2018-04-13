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
  if (is_goto(*c,&l1) && is_goto(next(destination(l1)),&l2) && l1>l2) {
     droplabel(l1);
     copylabel(l2);
     return replace(c,1,makeCODEgoto(l2,NULL));
  }
  return 0;
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
int simplify_if_goto(CODE **c)
{ int l1,l2;
  CODE *d;
  if (is_if(c,&l1) && is_goto(next(destination(l1)),&l2) && l1>l2) {
    droplabel(l1);
    copylabel(l2);

    /* Change the label of the if no matter what type of if it is */
    d = NEW(CODE);
    d->kind = (*c)->kind;
    d->visited = 0;
    d->val.ifeqC = l2;
    d->val.ifeqC = l2;
    d->val.ifneC = l2;
    d->val.if_acmpeqC = l2;
    d->val.if_acmpneC = l2;
    d->val.ifnullC = l2;
    d->val.ifnonnullC = l2;
    d->val.if_icmpeqC = l2;
    d->val.if_icmpgtC = l2;
    d->val.if_icmpltC = l2;
    d->val.if_icmpleC = l2;
    d->val.if_icmpgeC = l2;
    d->val.if_icmpneC = l2;
    d->next = NULL;
    return replace(c,1,d);
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
     return replace(c, 2, NULL);
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
     return replace(c, 3, makeCODEistore(x, NULL));
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
    return replace(c, 2, makeCODEifeq(y, NULL));

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
    return replace(c, 2, makeCODEifne(y, NULL));
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
    return replace(c, 3, makeCODEaload(x, NULL));
  else if (is_iload(*c, &x) && is_ldc_int(next(*c), &k) && k == 0 && is_iadd(next(next(*c))))
    return replace(c, 3, makeCODEiload(x, NULL));
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
    return replace(c, 3, makeCODEaload(x, NULL));
  else if (is_iload(*c, &x) && is_ldc_int(next(*c), &k) && k == 1 && is_imul(next(next(*c))))
      return replace(c, 3, makeCODEiload(x, NULL));
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
  if (is_goto(*c, &x) && is_label(next(*c), &y) && x == y) {
    droplabel(y);
    return replace(c, 2, makeCODElabel(x, NULL));
  }
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
  if (is_if(c, &x) && is_label(next(*c), &y) && x == y){
    droplabel(y);
    return replace(c, 2, makeCODElabel(x, NULL));
  }
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
    return
      replace(c, 2, makeCODEaload(x,
        makeCODEdup(NULL)
        )
      );
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
    return replace(c, 2, makeCODEiload(x,
                         makeCODEdup(NULL)
    )
  );
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
    return replace(c, 2, makeCODEdup(makeCODEistore(x, NULL)));
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
    return replace(c, 2, makeCODEdup(makeCODEastore(x, NULL)));
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
    droplabel(l1);
    copylabel(l2);
    return replace(c, 1, makeCODEgoto(l2, NULL));
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
  CODE *d;
  if (is_if(c, &l1) && is_label(next(destination(l1)), &l2)) {
    droplabel(l1);
    copylabel(l2);

    /* Change the label of the if no matter what type of if it is */
    d = NEW(CODE);
    d->kind = (*c)->kind;
    d->visited = 0;
    d->val.ifeqC = l2;
    d->val.ifeqC = l2;
    d->val.ifneC = l2;
    d->val.if_acmpeqC = l2;
    d->val.if_acmpneC = l2;
    d->val.ifnullC = l2;
    d->val.ifnonnullC = l2;
    d->val.if_icmpeqC = l2;
    d->val.if_icmpgtC = l2;
    d->val.if_icmpltC = l2;
    d->val.if_icmpleC = l2;
    d->val.if_icmpgeC = l2;
    d->val.if_icmpneC = l2;
    d->next = NULL;
    return replace(c, 1, d);
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
    return replace(c, 1, NULL);
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
    return replace(c, 4, makeCODEaload(x1, makeCODEgetfield(y1, makeCODEdup(NULL))));
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
    return replace(c, 2, makeCODEgoto(l1, NULL));
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
  if (is_ldc_int(*c, &x) && x == 1 && is_ifeq(next(*c), &l1)){
    droplabel(l1);
    return replace(c, 2, NULL);
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
    return replace(c, 2, makeCODEgoto(l1, NULL));
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
    droplabel(l1);
    return replace(c, 2, NULL);
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
    return replace(c, 3, makeCODEldc_int(x, NULL));
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
    droplabel(l1);
    copylabel(l2);
    return replace(c, 2, makeCODEgoto(l2, NULL));
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
    droplabel(l1);
    copylabel(l2);
    return replace(c, 2, makeCODEgoto(l2, NULL));
  }
  return 0;
}

/*
 * return
 * [not a label]
 * --------->
 * return
 */
int remove_deadcode(CODE **c)
{
  int x;
  if (is_return(*c) && (*c)->next != NULL && !(is_label(next(*c), &x)))
    return replace(c, 2, makeCODEreturn(NULL));
  if (is_areturn(*c) && (*c)->next != NULL && !(is_label(next(*c), &x)))
    return replace(c, 2, makeCODEareturn(NULL));
  if (is_ireturn(*c) && (*c)->next != NULL && !(is_label(next(*c), &x)))
    return replace(c, 2, makeCODEireturn(NULL));
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
    droplabel(l);
    return replace(c, 1, makeCODEreturn(NULL));
  }
  if (is_goto(*c, &l) && is_areturn(next(destination(l)))) {
    droplabel(l);
    return replace(c, 1, makeCODEareturn(NULL));
  }
  if (is_goto(*c, &l) && is_ireturn(next(destination(l)))) {
    droplabel(l);
    return replace(c, 1, makeCODEireturn(NULL));
  }
  return 0;
}

/* [if_cmpge, if_cmpgt, if_cmple, if_cmplt, if_cmpeq, if_cmpne, if_acmpeq, if_acmpne] L1
 * goto L2
 * L1:
 * ------->
 * [if_cmplt, if_cmple, if_cmpgt, if_cmpge, if_cmpne, if_cmpne, if_acmpne, if_acmpne] L2
 * L1:
 */
int inverse_cmp(CODE **c) {
  int l1;
  int l2;
  int l3;
  /* if_cmpge */
  if (is_if_icmpge(*c, &l1) && is_goto(next(*c), &l2) && is_label(next(next(*c)), &l3) && l1 == l3) {
    droplabel(l1);
    return replace(c, 2, makeCODEif_icmplt(l2, NULL));
  }
  /* if_cmpgt */
  if (is_if_icmpgt(*c, &l1) && is_goto(next(*c), &l2) && is_label(next(next(*c)), &l3) && l1 == l3) {
    droplabel(l1);
    return replace(c, 2, makeCODEif_icmple(l2, NULL));
  }
  /* if_cmple */
  if (is_if_icmple(*c, &l1) && is_goto(next(*c), &l2) && is_label(next(next(*c)), &l3) && l1 == l3) {
    droplabel(l1);
    return replace(c, 2, makeCODEif_icmpgt(l2, NULL));
  }
  /* if_cmplt */
  if (is_if_icmplt(*c, &l1) && is_goto(next(*c), &l2) && is_label(next(next(*c)), &l3) && l1 == l3) {
    droplabel(l1);
    return replace(c, 2, makeCODEif_icmpge(l2, NULL));
  }
  /* if_cmpeq */
  if (is_if_icmpeq(*c, &l1) && is_goto(next(*c), &l2) && is_label(next(next(*c)), &l3) && l1 == l3) {
    droplabel(l1);
    return replace(c, 2, makeCODEif_icmpne(l2, NULL));
  }
  /* if_cmpne */
  if (is_if_icmpne(*c, &l1) && is_goto(next(*c), &l2) && is_label(next(next(*c)), &l3) && l1 == l3) {
    droplabel(l1);
    return replace(c, 2, makeCODEif_icmpeq(l2, NULL));
  }
  /* if_acmpeq */
  if (is_if_acmpeq(*c, &l1) && is_goto(next(*c), &l2) && is_label(next(next(*c)), &l3) && l1 == l3) {
    droplabel(l1);
    return replace(c, 2, makeCODEif_acmpne(l2, NULL));
  }
  /* if_acmpne */
  if (is_if_acmpne(*c, &l1) && is_goto(next(*c), &l2) && is_label(next(next(*c)), &l3) && l1 == l3) {
    droplabel(l1);
    return replace(c, 2, makeCODEif_acmpeq(l2, NULL));
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
    return replace(c, 4, makeCODEldc_int(x1, makeCODEdup(makeCODEistore(y, makeCODEistore(z, NULL)))));
  }
  return 0;
}

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
  ADD_PATTERN(remove_unecessary_ifne);
  ADD_PATTERN(remove_unecessary_ifne2);
  ADD_PATTERN(inline_return);
  ADD_PATTERN(inverse_cmp);
  ADD_PATTERN(remove_deadcode);
  ADD_PATTERN(duplicate_store);
}
