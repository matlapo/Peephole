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

/* aload x
 * pop
 * -------->
 */
/* Soundness: this is sound because we push onto the stack x than pop x, equivalent of doing nothing */
int simplify_push_pop(CODE **c)
{
  if (is_simplepush(*c) && is_pop(next(*c)))
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
    replace(c, 3, makeCODEaload(x, NULL));
  else if (is_iload(*c, &x) && is_ldc_int(next(*c), &k) && k == 0 && is_iadd(next(next(*c))))
      replace(c, 3, makeCODEiload(x, NULL));
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
    replace(c, 3, makeCODEaload(x, NULL));
  else if (is_iload(*c, &x) && is_ldc_int(next(*c), &k) && k == 1 && is_imul(next(next(*c))))
      replace(c, 3, makeCODEiload(x, NULL));
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
    return replace(c, 2, makeCODElabel(x, NULL));
  return 0;
}

/* aload x
 * aload x
 * mul
 * -------->
 * aload x
 * dup
 * mul
 */
int simplify_double_aload_mul(CODE **c)
{
  int x = 0;
  int y = 0;
  if (is_aload(*c, &x) && is_aload(next(*c), &y) && x == y && is_imul(next(next(*c))))
    return
      replace(c, 3, makeCODEaload(x,
        makeCODEdup(
          makeCODEimul(NULL)
        )
      )
    );
  return 0;
}

/* aload x
 * aload x
 * add
 * -------->
 * aload x
 * dup
 * add
 */
int simplify_double_aload_add(CODE **c)
{
  int x = 0;
  int y = 0;
  if (is_aload(*c, &x) && is_aload(next(*c), &y) && x == y && is_iadd(next(next(*c))))
    return
      replace(c, 3, makeCODEaload(x,
        makeCODEdup(
          makeCODEiadd(NULL)
        )
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
 * iload x
 * iload x
 * ...
 * -------->
 * iload x
 * dup
*/
int simplify_duplicate_iload(CODE **c)
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

void init_patterns(void) {
	ADD_PATTERN(simplify_multiplication_right);
	ADD_PATTERN(simplify_astore);
	ADD_PATTERN(positive_increment);
	ADD_PATTERN(simplify_goto_goto);
	ADD_PATTERN(simplify_push_pop);
  ADD_PATTERN(simplify_dup_istore);
  ADD_PATTERN(simplify_cmpeq_with_0_loaded);
  ADD_PATTERN(simplify_icmpne_with_0_loaded);
  ADD_PATTERN(simplify_unecessary_goto);
  ADD_PATTERN(simplify_double_aload_mul);
  ADD_PATTERN(simplify_double_aload_add);
  ADD_PATTERN(simplify_astore_aload);
  ADD_PATTERN(simplify_istore_iload);
  ADD_PATTERN(simplify_duplicate_iload);
  ADD_PATTERN(simplify_add_0);
  ADD_PATTERN(simplify_mul_1);
  ADD_PATTERN(simplify_unecessary_label);
}
