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

/***********************************/
/******** HELPER FUNCTIONS *********/
/***********************************/

/*
 * Generates a copy of an existing if instruction
 */
CODE *makeCODEif(CODE *previous_if, int label, CODE *next) {
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

/*
 * Generates an if statement that is the inverse of an existing if statement
 */
CODE *makeCODEif_not(CODE *previous_if, int label, CODE *next) {
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
 * Generates a copy of a simplepush instruction
 */
CODE *makeCODEsimplepush(CODE *c, CODE *next)
{
  int i;
  char* s;
  if (is_aload(c, &i))
    return makeCODEaload(i, next);
  if (is_iload(c, &i))
    return makeCODEiload(i, next);
  if (is_ldc_int(c, &i))
    return makeCODEldc_int(i, next);
  if (is_ldc_string(c, &s))
    return makeCODEldc_string(s, next);
  if (is_aconst_null(c))
    return makeCODEaconst_null(next);

  return NULL;
}

/*
 * replace2 - replaces a sequence of instructions by another one
 * Same as replace_modified but takes into account labels added in the replaced version of the code
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

/*
 * iload x        iload x        iload x
 * ldc 0          ldc 1          ldc 2
 * imul           imul           imul
 * ------>        ------>        ------>
 * ldc 0          iload x        iload x
 *                               dup
 *                               iadd
 * 
 * Soundness: Multiplication by 0 is the same as replacing a value by 0.
 * Multiplication by 1 doesn't do anything.
 * Multiplication by 2 is the same as adding a value to itself.
 */
int simplify_multiplication_right(CODE **c)
{ int x,k;
  if (is_iload(*c,&x) &&
      is_ldc_int(next(*c),&k) &&
      is_imul(next(next(*c)))) {
     if (k==0) return replace2(c,3,makeCODEldc_int(0,NULL));
     else if (k==1) return replace2(c,3,makeCODEiload(x,NULL));
     else if (k==2) return replace2(c,3,makeCODEiload(x,
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
 * 
 * Soundness: There is no need to duplicate the value currently on the stack if we're going to pop it later anyways.
 * In both cases, this stores the value currently on top of the stack.
 */
int simplify_astore(CODE **c)
{ int x;
  if (is_dup(*c) &&
      is_astore(next(*c),&x) &&
      is_pop(next(next(*c)))) {
     return replace2(c,3,makeCODEastore(x,NULL));
  }
  return 0;
}

/*
 * iload x
 * ldc k   (-128<=k<=127)
 * iadd
 * istore x
 * --------->
 * iinc x k
 * 
 * Soundness: Adding a constant to a value is the same as using the builtin iinc instruction
 */
int positive_increment(CODE **c) {
  int x1, x2, k;
  if (
    is_iload(*c, &x1) &&
    is_ldc_int(next(*c), &k) &&
    is_iadd(nextby(*c, 2)) &&
    is_istore(nextby(*c, 3), &x2) &&
    x1==x2 && -128<=k && k<=127
  ) {
    int bytes_taken = 0;
    bytes_taken += (0 <= x1 && x1 <= 3) ? 1 : 2;
    bytes_taken += (0 <= k && k <= 5) ? 1 : 2;
    bytes_taken += 1;
    bytes_taken += (0 <= x1 && x1 <= 3) ? 1 : 2;

    if (bytes_taken > 6)
      return replace2(c, 4, makeCODEiinc(x1, k, NULL));
  }
  return 0;
}

/*
 * iload x
 * ldc k   (-127<=k<=128)
 * isub
 * istore x
 * --------->
 * iinc x -k
 * 
 * Soundness: Substracting a constant from a value is the same as using the builtin iinc instruction
 */
int negative_increment(CODE **c) {
  int x1, x2, k;
  if (
    is_iload(*c, &x1) &&
    is_ldc_int(next(*c), &k) &&
    is_isub(nextby(*c, 2)) &&
    is_istore(nextby(*c, 3), &x2) &&
    x1==x2 && -127<=k && k<=128
  ) {
    int bytes_taken = 0;
    bytes_taken += (0 <= x1 && x1 <= 3) ? 1 : 2;
    bytes_taken += (0 <= k && k <= 5) ? 1 : 2;
    bytes_taken += 1;
    bytes_taken += (0 <= x1 && x1 <= 3) ? 1 : 2;

    if (bytes_taken > 6)
      return replace2(c, 4, makeCODEiinc(x1, -k, NULL));
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
 * 
 * Soundness: Jumping to L1 and then to L2 is the same as going straight to L2.
 * This potentially helps with dead label removal.
 */
int simplify_goto_goto(CODE **c)
{ int l1,l2;
  if (is_goto(*c,&l1) && is_goto(next(destination(l1)),&l2)) {
    return replace2(c,1,makeCODEgoto(l2,NULL));
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
 * 
 * Soundness: If the conditionnal branching happens, jumping to L1 and then to L2 is the same as going straight to L2.
 * If the conditionnal branching does not happen, the label in the if doesn't matter.
 * This potentially helps with dead label removal.
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
 * 
 * Soundness: All the possibilities of first instruction have no side effect. Thus, pushing a value on the stack and
 * popping it immediately doesn't change anything.
 */
int simplify_push_pop(CODE **c) {
  if ((is_simplepush(*c) || is_dup(*c)) && is_pop(next(*c)))
     return replace2(c, 2, NULL);
  return 0;
}

/* dup
 * istore x
 * pop
 * -------->
 * istore x
 * 
 * Soundness: The dup will allow keeping the current value onto the stack after the istore, but the pop discards it right after.
 * Thus, we can simply remove the dup and the pop.
 */
int simplify_dup_istore(CODE **c) {
  int x = 0;
  if (is_dup(*c) && is_istore(next(*c), &x) && is_pop(nextby(*c, 2)))
     return replace2(c, 3, makeCODEistore(x, NULL));
  return 0;
}

/* iconst_0
 * if_icmpeq L
 * -------->
 * ifeq L
 * 
 * Soundness: By definition, ifeq acts like if_icmpeq and compares the top of the stack to 0.
 */
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
 * 
 * Soundness: Soundness: By definition, ifne acts like if_icmpne and compares the top of the stack to 0.
 */
int simplify_icmpne_with_0_loaded(CODE **c)
{
  int x = 0;
  int y = 0;
  if (is_ldc_int(*c, &x) && x == 0 && is_if_icmpne(next(*c), &y))
    return replace2(c, 2, makeCODEifne(y, NULL));
  return 0;
}

/*
 * const_0
 * add
 * -------->
 * 
 * Soundness: Adding 0 to a number is the same as not doing anything
*/
int simplify_add_0(CODE **c)
{
  int x = 0;
  int k = 0;
  if (is_iload(*c, &x) && is_ldc_int(next(*c), &k) && k == 0 && is_iadd(next(next(*c))))
    return replace2(c, 3, makeCODEiload(x, NULL));
  return 0;
}

/*
 * const_1
 * imul
 * -------->
 * 
 * Soundness: Multiplying a number by 1 is the same as not doing anything
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
 * 
 * Soundness: The goto is useless because it points to the next line. The program counter will naturally go to the
 * next line anyways, which is the intended behavior.
 */
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
 * [pop, pop pop]
 * L:
 * 
 * Soundness: Wether or not the if branches, the following line will be executed next. One or two pops are needed instead of the if,
 * because ifs pop from the stack.
 */
int simplify_unecessary_if(CODE **c) {
  int l1, l2, inc, affected, used;
  if (is_if(c, &l1) && is_label(next(*c), &l2) && l1 == l2) {
    stack_effect(*c, &inc, &affected, &used);
    if (inc == -1) {
      return replace2(c, 2, makeCODEpop(makeCODElabel(l1, NULL)));
    } else if (inc == -2) {
      return replace2(c, 2, makeCODEpop(makeCODEpop(makeCODElabel(l1, NULL))));
    }
  }
  return 0;
}

/* load x
 * load x
 * -------->
 * load x
 * dup
 * 
 * Soundness: Loading the same value twice is the same as loading it, then duplicating it. This applies to both aloads and iloads.
 */
int simplify_double_load(CODE **c)
{
  int x = 0;
  int y = 0;
  if (is_aload(*c, &x) && is_aload(next(*c), &y) && x == y)
    return replace2(c, 2, makeCODEaload(x, makeCODEdup(NULL)));
  if (is_iload(*c, &x) && is_iload(next(*c), &y) && x == y)
    return replace2(c, 2, makeCODEiload(x, makeCODEdup(NULL)));
  return 0;
}

/*
 * store x
 * load x
 * ------>
 * dup
 * store x
 * 
 * Soundness: Storing a value, then loading it back is the same as storing a copy of a value, then storing it.
 * The dup is important, because the stack should contain the value that was stored at the end of this operation.
 * This applies to both iload/istore and aload/astore.
 */
int simplify_store_load(CODE **c)
{
  int x = 0;
  int y = 0;
  if (is_istore(*c, &x) && is_iload(next(*c), &y) && x == y)
    return replace2(c, 2, makeCODEdup(makeCODEistore(x, NULL)));
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
 * 
 * Soundness: Since the labels are consecutive, it is equivalent to jump to the second label. This enables some dead label removal.
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
 * 
 * Soundness: Since the labels are consecutive, it is equivalent to branch to the second label. This enables some dead label removal.
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
 * Soundness: Since nothing points to this label, it can safely be removed.
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
 * 
 * Soundess: Getting the value of a field twice is equivalent to getting it once and duplicating that value.
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
 * 
 * Soundness: Since 0 will be on the stack when the ifeq gets executed, it will always jump to L1.
 * This is equivalent to a goto instruction.
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
 * iconst x
 * ifeq L1
 * -------->
 * 
 * Soundness: Since a non-zero will be on the stack when the ifeq gets executed, it will never jump to L1.
 * This can thus be safely removed.
 */
int remove_unecessary_ifeq2(CODE **c)
{
  int x;
  int l1;
  if (is_ldc_int(*c, &x) && x != 0 && is_ifeq(next(*c), &l1))
    return replace2(c, 2, NULL);
  return 0;
}

/*
 * iconst x
 * ifne L1
 * -------->
 * goto L1
 * 
 * Soundness: Since a non-zero value will be on the stack when the ifeq gets executed, it will always jump to L1.
 * This is equivalent to a goto instruction.
 */
int remove_unecessary_ifne(CODE **c)
{
  int x;
  int l1;
  if (is_ldc_int(*c, &x) && is_ifne(next(*c), &l1) && x != 0)
    return replace2(c, 2, makeCODEgoto(l1, NULL));
  return 0;
}

/*
 * iconst_0
 * ifne L1
 * -------->
 * 
 * Soundness: Since 0 will be on the stack when the ifeq gets executed, it will never jump to L1.
 * This can thus be safely removed.
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
 * 
 * Soundness: One plus zero will be 1, regardless.
 */
int remove_one_plus_zero(CODE **c)
{
  int x;
  if (is_ldc_int(*c, &x) && x == 1 && is_ldc_int(*c, &x) && x == 0 && is_iadd(next(next(*c))))
    return replace2(c, 3, makeCODEldc_int(x, NULL));
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
 * 
 * Soundness: Since 0 will be on top of the stack, the ifeq instruction will jump to L2.
 * Thus, we know we can already jump to L2 and remove the iconst_0
 */
int remove_unecessary_ldc_int(CODE **c) {
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
 * 
 * Soundness: Since 1 will be on top of the stack, the ifne instruction will jump to L2.
 * Thus, we know we can already jump to L2 and remove the iconst_0
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
 * 
 * Soundness: Any code after a return or a goto that is not a label is unreachable. It can be safely removed.
 */
int remove_deadcode(CODE **c) {
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
 * 
 * Soundness: If a goto instruction points to a label that simply consists of a return statement,
 * it is equivalent to return instead of jumping to L1 and then returning.
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
 * 
 * Soundness: In the unoptimized version, if the if instruction branches, it will go to L1.
 * Otherwise, it will execute the goto and go to L2. This is equivalent to flipping the if and going
 * to L2 if the if branches and falling to L1 otherwise.
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
 * [if] L1
 * iconst_0
 * goto L2
 * L1:
 * iconst_1
 * L2:
 * ifeq L3
 * ------>
 * [if inverted] L3
 * 
 * Soundness: The first part of the code loads 0 or one on the stack depending on the result of an
 * if instruction. Then, the ifeq branches based on wether there is a 0 of 1 in the stack. This is
 * equivalent to simply branching (or not) to L3 in the first place. Due to the placement of the 0
 * and 1 constants, the initial if instruction needs to be inverted.
 */
int simplify_branching_to_constants(CODE **c) {
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
 * 
 * Soundness: Pushing null on the stack, then comparing a value to it is equivalend to using the
 * dedicated ifnull and ifnonnull instructions.
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
 * aload k
 * swap
 * putfield
 * pop
 * ------>
 * aload k
 * swap
 * putfield
 * 
 * Soundness: The three middle instructions don't use the lower part of the stack, so it is safe to cancel out the dup with the pop.
 */
int putfield_dup_pop(CODE **c) {
  int k;
  char* f;
  if(
    is_dup(*c) &&
    is_aload(next(*c), &k) &&
    is_swap(nextby(*c, 2)) &&
    is_putfield(nextby(*c, 3), &f) &&
    is_pop(nextby(*c, 4))
  ) {
    return replace2(c, 5, makeCODEaload(k, makeCODEswap(makeCODEputfield(f, NULL))));
  }
  return 0;
}

/*
 * [simplepush_1]
 * [simplepush_2]
 * swap
 * ------>
 * [simplepush_2]
 * [simplepush_1]
 * 
 * Soundness: Since the two pushing instructions don't have any side-effect (apart from pushing a value on the stack)
 * or special dependencies, their order can be swapped to avoid the swap instruction.
 */
int remove_unecessary_swap(CODE **c) {
  if (
    is_simplepush(*c) &&
    is_simplepush(next(*c)) &&
    is_swap(nextby(*c, 2))
  ) {
    return replace2(c, 3, makeCODEsimplepush(next(*c), makeCODEsimplepush(*c, NULL)));
  }
  return 0;
}

/*
 * store x
 * [not if, not goto, not load x]*
 * return
 * ------>
 * pop
 * [not if, not goto, not load x]*
 * return
 * 
 * Soundness: This simply remover store instructions that happen right before a return. It is useless
 * to store a value if it won't be used after.
 */
int store_before_return(CODE **c) {
  int x1;
  if (is_astore(*c, &x1) || is_istore(*c, &x1)) {
    CODE *p;
    for (p = *c; p != NULL; p = p->next) {
      int l, x2;
      if (is_if(&p, &l) || is_goto(p, &l) || (is_aload(p, &x2) && x1 == x2) || (is_iload(p, &x2) && x1 == x2)) break;

      if (is_return(p) || is_areturn(p) || is_ireturn(p))
        return replace2(c, 1, makeCODEpop(NULL));
    }
  }
  return 0;
}

/*
 * (if_eq, if_ne) L1
 * ...
 * L1:
 * dup
 * (if_eq, if_ne) L2
 * pop
 * ...
 * L2:
 * (if_ne, if_eq) L3
 * ------->
 * (if_eq, if_ne) L2 // We change the jump from L1 to L2 since we know for sure that if the if_eq/if_ne succeeded then the second one will succeed for sure (assuming they are the same comparison).
 * ...
 * L1:
 * dup
 * (if_eq, if_ne) L2
 * ...
 * L2:
 * (if_ne, if_eq) L3
 * Soudness: this pattern does not reduce the size of the code, but formats it for simplify_if_else[1,2,3] patterns. It does so by removing unecessary jumps (see explanations in code).
 */
int remove_unecessary_jump(CODE **c)
{
  int l1, l2,l3;
  /* Check if we have a ifne pair */
  if(is_ifne(*c, &l1)
  && is_dup(next(destination(l1)))
  && is_ifne(next(next(destination(l1))), &l2)
  && is_ifeq(next(destination(l2)), &l3)) {
    return replace2(c, 1, makeCODEifne(l2, NULL));
  }
  /* Check if we have a ifeq pair */
  if(is_ifeq(*c, &l1)
  && is_dup(next(destination(l1)))
  && is_ifeq(next(next(destination(l1))), &l2)
  && is_ifne(next(destination(l2)), &l3)) {
    return replace2(c, 1, makeCODEifeq(l2, NULL));
  }
  return 0;
}

/*
 * dup
 * (if_eq, if_ne) L1
 * pop
 * ...
 * L1:
 * dup
 * (if_eq, if_ne) L2
 * pop
 * ...
 * L2:
 * (if_eq, if_ne) L3
 * ------->
 * dup
 * (if_eq, if_ne) L3 // We jump directly to L3 since we know that the comparison under L1 and L2 will succeed for sure (since they are all doing the same comparison ifne-ifne-ifne or ifeq-ifeq-ifeq). We can therefore directly jump to the end when the first comparison succeeded. The dup and pop needs to be there because we assume all the ifeq/ifne will use a duplication of the same value to do the comparison.
 * pop
 * ...
 * L1:
 * dup
 * (if_eq, if_ne) L2
 * ...
 * L2:
 * (if_eq, if_ne) L3
 * Soudness: this pattern does not reduce the size of the code, but formats it for simplify_if_else[1,2,3] patterns. It does so by removing unecessary jumps (see explanations in code).
 */
int remove_unecessary_jump2(CODE **c)
{
  int l1, l2, l3;
  /* For ifne-ifne-ifne pairs */
  if(is_dup(*c)
  && is_ifne(next(*c), &l1)
  && is_pop(next(next(*c)))
  && is_dup(next(destination(l1)))
  && is_ifne(next(next(destination(l1))), &l2)
  && is_ifne(next(destination(l2)), &l3)) {
    return replace2(c, 3, makeCODEifne(l3, NULL));
  }
  /* For ifeq-ifeq-ifeq pairs */
  if(is_dup(*c)
  && is_ifeq(next(*c), &l1)
  && is_pop(next(next(*c)))
  && is_dup(next(destination(l1)))
  && is_ifeq(next(next(destination(l1))), &l2)
  && is_ifeq(next(destination(l2)), &l3)) {
    return replace2(c, 3, makeCODEifeq(l3, NULL));
  }
  return 0;
}

/*
 * dup
 * (if_eq, if_ne) L1
 * ...
 * L1:
 * dup
 * (if_eq, if_ne) L2
 * pop
 * ...
 * L2:
 * .return
 * ------->
 * dup
 * (if_eq, if_ne) L2
 * ...
 * L1:
 * dup
 * (if_eq, if_ne) L2
 * ...
 * L2:
 * .return
 * Soundness: same as remove_unecessary_jump2, but it's a return in the end
 */
int remove_unecessary_jump3(CODE **c)
{
  int l1, l2;
  if(is_dup(*c)
  && is_ifne(next(*c), &l1)
  && is_dup(next(destination(l1)))
  && is_ifne(next(next(destination(l1))), &l2)
  && (is_return(next(destination(l2))) || is_areturn(next(destination(l2))) || is_ireturn(next(destination(l2))))) {
    return replace2(c, 2, makeCODEdup(makeCODEifne(l2, NULL)));
  }
  if(is_dup(*c)
  && is_ifeq(*c, &l1)
  && is_dup(next(destination(l1)))
  && is_ifeq(next(next(destination(l1))), &l2)
  && (is_return(next(destination(l2))) || is_areturn(next(destination(l2))) || is_ireturn(next(destination(l2))))) {
    return replace2(c, 2, makeCODEdup(makeCODEifeq(l2, NULL)));
  }
  return 0;
}

/*
 * if_* L1      // If true, add a 1 on the stack, add 0 otherwise
 * iconst_0
 * goto L2
 * L1:
 * iconst_1
 * L2:          // Here, if the if_* branch succeeded, the stack contains 1 (else, 0)
 * dup          // Copy the value that may be send to the code after label L3
 * ifeq L3      // If 0, jump to L3 (and bring the duplicated value).
 * pop          // If 1, pop the result that we won't be using
 * ...          // The stack is EXACTLY the same as before if if_* thanks to the pop
 * L3:
 * ifeq L4      // If the jump is coming from the previous ifeq, it will necessarily go to L4 since there is a 0 on the stack
 * --------> If L1 and L2 are NOT unique, we need to keep the code under L1 and L2
 * [reverse if_*] L4 // Since we know that if the if_* fails, the code will fallthrough L4, we can use the inverse if and jump directly to L4
 * L1:               // Since, in the original code, if the if_* succeeded it jumped to L1, then is it good that the inverse if_* goes to L1 if it failed
 * iconst_1          // The remaining is unchanged code
 * L2:
 * dup
 * ifeq L3
 * pop
 * ...
 * L3:
 * ifeq L4
 * --------> If L1 and L2 are unique, we can delete the code under L1 and L2
 * [reverse if_*] L4 // This instruction reproduces the behavior of the previous code. The difference is that it jumps directly to L4 instead of L3. It, therefore, does not need the code to put a 0 or a 1 on top of the stack.
 * ...
 * L3:
 * ifeq L4
 * Soundness: this one is a bit complicated. I tried adding comments to the code to explain how it works and why it works. Also, if L1 and L2 are only referenced once, we can remove them. They are doing nothing since they add 1 to the stack, then duplicates it, then compare ifnethen pop to cancel the duplicate. Therefore, this code can be deleted since it makes no sence without the code we initially removed.
 */
int simplify_if_else(CODE **c)
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
 * iconst x     // We need to keep track of the constant loading because we will put it at a different place in the final pattern
 * if_.cmp* L1  // Any comparison of two elements
 * iconst_0     // If the comparison failed, push 0 on stack
 * goto L2
 * L1:
 * iconst_1     // If the comparison succeeded, push 1 on stack
 * L2:
 * dup          // Copy the value that may be send to the code after label L3
 * ifne L3      // If 1, jump to L3 (and bring the duplicated value).
 * pop          // If 0, pop the result that we won't be using
 * ...          // The stack is EXACTLY the same as before if if_.cmp* thanks to the pop
 * L3:
 * ifeq L4      // If the jump is coming from the previous ifne, we know the comparison will fail because 1 will be on the stack
 * ---->        // If L1 and L2 are unique, we can remove the unused code under them since, in the end, the pattern does not affect the stack
 * iconst_1     // We load a value of one that is going to be used to make the ifeq fail in case the if_.cmp* succeeds
 * swap         // Swap to bring back the first value to compare with the if_.cmp*
 * iconst x     // Add back the iconst we caugh in the pattern (first line of the original pattern). We needed to catch it to add the const_1 and swap before
 * if_.cmp* L3  // Same comparison as in the original pattern. The only different is that we jump to L3 directly since we don't need to put a 0 or 1 anymore on the stack (the const_1 and swap takes care of that)
 * pop          // Pop the iconst_1 added previously is not useful if we are not jumping to L3. The iconst_1 was only there in case we jump to L3 and needed to fail the ifeq (to respect the behavior of the original pattern)
 * ...
 * L3:
 * ifeq L4
 * Soundness: this is the most complicated pattern. I tried adding comments to the code to explain how it works and why it works. It is complicated because a value need to be inserted in the stack before the two operands of the comparison. Also, if L1 and L2 are only referenced once, we can remove them. They are doing nothing since they add 1 to the stack, then duplicates it, then compare ifne (which always fails) then pop to cancel the duplicate. Therefore, this code can be deleted since it makes no sence without the code we initially removed.
 */
int simplify_if_else2(CODE **c)
{
  int l1_1, l1_2, l2_1, l2_2, l3, l4, x, y;

  CODE* inst0 = *c;           /* iconst x */
  CODE* inst1 = next(inst0);  /* if_.cmp* L1 */
  CODE* inst2 = next(inst1);  /* iconst_0 */
  CODE* inst3 = next(inst2);  /* goto L2 */
  CODE* inst4 = next(inst3);  /* L1: */
  CODE* inst5 = next(inst4);  /* iconst_1 */
  CODE* inst6 = next(inst5);  /* L2: */
  CODE* inst7 = next(inst6);  /* dup */
  CODE* inst8 = next(inst7);  /* ifne L3 */
  CODE* inst9 = next(inst8);  /* pop */

  if(is_ldc_int(inst0, &x)
  && (is_if_acmpeq(inst1, &l1_1) || is_if_acmpne(inst1, &l1_1) || is_if_icmpeq(inst1, &l1_1) || is_if_icmpge(inst1, &l1_1) || is_if_icmpgt(inst1, &l1_1) || is_if_icmple(inst1, &l1_1) || is_if_icmplt(inst1, &l1_1) || is_if_icmpne(inst1, &l1_1))
  && is_ldc_int(inst2, &y) && y == 0
  && is_goto(inst3, &l2_1)
  && is_label(inst4, &l1_2)
  && is_ldc_int(inst5, &y) && y == 1
  && is_label(inst6, &l2_2)
  && is_dup(inst7)
  && is_ifne(inst8, &l3)
  && is_pop(inst9)
  && is_ifeq(next(destination(l3)), &l4)
  && l1_1 == l1_2 && l2_1 == l2_2) {
    if (uniquelabel(l1_1) && uniquelabel(l2_1)) {
      return replace2(c, 10, makeCODEldc_int(1, makeCODEswap(makeCODEldc_int(x, makeCODEif(inst1, l3, makeCODEpop(NULL))))));
    }
  }
  return 0;
}

/* // Like simplify_if_else2, but for one operand comparators
 * if_* L1       // If of one operand only (no cmp operartion)
 * iconst_0      // Load 0 on the stack if comparison failed
 * goto L2
 * L1:
 * iconst_1      // Load 1 on the stack if comparison succeeded
 * L2:
 * dup           // Copy the value that may be send to the code after label L3
 * ifne L3       // If 1, jump to L3 (and bring the duplicated value).
 * pop           // If 0, pop the result that we won't be using
 * ...
 * L3:
 * ifeq L4       // If the jump is coming from the previous ifne, the comparison will always fail since 1 will be on the stack
 * ----> // If L1 and L2 are unique, we can delete the code under L1 and L2
 * iconst_1     // Load 1 into the stack (to be used to make the ifeq fail)
 * swap         // Put the initial operand of the comparison back to the top
 * if_* L3      // If success, jump directly to L3 then fail the ifeq thanks to the iconst_1 on the stack
 * pop          // If failure, we are not jumping to L3, therefore the iconst_1 on the stack is not needed anymore
 * ...
 * L3:
 * ifeq L4
 * Soundness: this one is a bit complicated. I tried adding comments to the code to explain how it works and why it works. Also, if L1 and L2 are only referenced once, we can remove them. They are doing nothing since they add 1 to the stack, then duplicates it, then compare ifne then pop to cancel the duplicate. Therefore, this code can be deleted since it makes no sence without the code we initially removed.
 */
int simplify_if_else3(CODE **c)
{
  int l1_1, l1_2, l2_1, l2_2, l3, l4, x;

  CODE* inst0 = *c;           /* ifeq L1 */
  CODE* inst1 = next(inst0);  /* iconst_0 */
  CODE* inst2 = next(inst1);  /* goto L2 */
  CODE* inst3 = next(inst2);  /* L1: */
  CODE* inst4 = next(inst3);  /* iconst_1 */
  CODE* inst5 = next(inst4);  /* L2: */
  CODE* inst6 = next(inst5);  /* dup */
  CODE* inst7 = next(inst6);  /* ifne L3 */
  CODE* inst8 = next(inst7);  /* pop */

  if(is_if(c, &l1_1)
  && is_ldc_int(inst1, &x) && x == 0
  && is_goto(inst2, &l2_1)
  && is_label(inst3, &l1_2)
  && is_ldc_int(inst4, &x) && x == 1
  && is_label(inst5, &l2_2)
  && is_dup(inst6)
  && is_ifne(inst7, &l3)
  && is_pop(inst8)
  && is_ifeq(next(destination(l3)), &l4)
  && l1_1 == l1_2 && l2_1 == l2_2
  && (is_ifeq(*c, &l4) || is_ifne(*c, &l4) || is_ifnull(*c, &l4) || is_ifnonnull(*c, &l4))) {
    /* TODO: We could support the case where one of them is unique */
    if (uniquelabel(l1_1) && uniquelabel(l2_2)) {
      return replace2(c, 9, makeCODEldc_int(1, makeCODEswap(makeCODEif(*c, l3, makeCODEpop(NULL)))));
    }
  }
  return 0;
}

/*
 * iconst k (k = 0)
 * goto L1
 * ...
 * L1:
 * dup
 * ifeq L2
 * ------>
 * iconst k
 * goto L2
 * ...
 * L1:
 * dup
 * ifeq L2
 *
 *
 *
 * iconst k (k != 0)
 * goto L1
 * ...
 * L1:
 * dup
 * ifne
 * ------>
 * iconst k
 * goto L2
 * ...
 * L1:
 * dup
 * ifne L2
 * 
 * Soundness: Since a constant is on the stack, the behavior of the if instruction can be determined in advance.
 * Thus, the goto instruction can jump to L2 right away instead of going to L1 first.
 * This pattern helps trigger dead lanel removal.
 */
int const_goto_if_dup(CODE **c) {
  int l1, l2, k;
  if (
    is_ldc_int(*c, &k) &&
    is_goto(next(*c), &l1) &&
    is_dup(next(destination(l1)))
  ) {
    if (is_ifeq(nextby(destination(l1), 2), &l2) && k == 0)
      return replace2(c, 2, makeCODEldc_int(k, makeCODEgoto(l2, NULL)));
    if (is_ifne(nextby(destination(l1), 2), &l2) && k != 0)
      return replace2(c, 2, makeCODEldc_int(k, makeCODEgoto(l2, NULL)));
  }
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
	ADD_PATTERN(negative_increment);
	ADD_PATTERN(simplify_goto_goto);
	ADD_PATTERN(simplify_if_goto);
	ADD_PATTERN(simplify_push_pop);
  ADD_PATTERN(simplify_dup_istore);
  ADD_PATTERN(simplify_cmpeq_with_0_loaded);
  ADD_PATTERN(simplify_icmpne_with_0_loaded);
  ADD_PATTERN(simplify_unecessary_goto);
  ADD_PATTERN(simplify_unecessary_if);
  ADD_PATTERN(simplify_double_load);
  ADD_PATTERN(simplify_store_load);
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
  ADD_PATTERN(simplify_if_else);
  ADD_PATTERN(simplify_if_else2);
  ADD_PATTERN(simplify_if_else3);
  ADD_PATTERN(remove_unecessary_ifne);
  ADD_PATTERN(remove_unecessary_ifne2);
  ADD_PATTERN(inline_return);
  ADD_PATTERN(inverse_cmp);
  ADD_PATTERN(remove_deadcode);
  ADD_PATTERN(simplify_branching_to_constants);
  ADD_PATTERN(collapse_if_null);
  ADD_PATTERN(putfield_dup_pop);
  ADD_PATTERN(remove_unecessary_swap);
  ADD_PATTERN(store_before_return);
  ADD_PATTERN(remove_unecessary_jump);
  ADD_PATTERN(remove_unecessary_jump2);
  ADD_PATTERN(remove_unecessary_jump3);
  ADD_PATTERN(const_goto_if_dup);
}
