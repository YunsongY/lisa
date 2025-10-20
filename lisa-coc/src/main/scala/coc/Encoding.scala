package coc

import lisa.maths.SetTheory.Ordinals.Ordinal.*
import lisa.maths.SetTheory.Base.Pair.*

object Encoding extends lisa.Main {

  // private val x, y, z, t, u, Gamma, Delta = variable[Ind]
  // private val n, A, B = variable[Ind]

  // // (sort, (tag, data))

  // // Sort(Term/Type/Kind)
  // val SORT_TERM: Expr[Ind] = zero
  // val SORT_TYPE: Expr[Ind] = S(SORT_TERM)
  // val SORT_KIND: Expr[Ind] = S(SORT_TYPE)

  // // Type(Base/Pi)
  // val TAG_BASE: Expr[Ind] = zero
  // val TAG_PI: Expr[Ind] = S(TAG_BASE)

  // // Term(Var/Abs/App)
  // val TAG_VAR: Expr[Ind] = zero
  // val TAG_ABS: Expr[Ind] = S(TAG_VAR)
  // val TAG_APP: Expr[Ind] = S(TAG_ABS)

  // /**
  //  * Base type: o
  //  *
  //  * Format: (SORT_TYPE, (TAG_BASE, n))
  //  *
  //  * - n: index which base type
  //  */
  // val Base: Expr[Ind] = DEF(λ(n, (pair(SORT_TYPE, pair(TAG_BASE, n)))))

  // /**
  //  * Pi type: Πx:A. B
  //  *
  //  * Format: (SORT_TYPE, (TAG_PI, (A, B)))
  //  *
  //  * Parameters:
  //  * - A: type of the parameter (must be SORT_TYPE)
  //  * - B: type of the body (must be SORT_TYPE)
  //  *
  //  * Note: B may contain Var(0), representing a reference to the parameter
  //  */
  // val Pi = DEF(λ(A, λ(B, pair(SORT_TYPE, pair(TAG_PI, pair(A, B))))))

  // // ========================================
  // // Term Constructors
  // // ========================================

  // /**
  //  * Variable: Var(n)
  //  *
  //  * Format: (SORT_TERM, (TAG_VAR, n))
  //  *
  //  * Parameters:
  //  * - n: de Bruijn index (natural number)
  //  */
  // val Var = DEF(λ(x, pair(SORT_TERM, pair(TAG_VAR, x))))

  // /**
  //  * Abstraction: λx:A. t
  //  *
  //  * Format: (SORT_TERM, (TAG_ABS, (A, t)))
  //  *
  //  * Parameters:
  //  * - A: type of the parameter (must be SORT_TYPE)
  //  * - t: body (must be SORT_TERM)
  //  *
  //  * Examples:
  //  * - λx:o. x
  //  *   = Abs(Base, Var(0))
  //  *   = (SORT_TERM, (TAG_ABS, (Base, Var(0))))
  //  *
  //  * - λx:o. λy:o. x
  //  *   = Abs(Base, Abs(Base, Var(1)))
  //  *   = (SORT_TERM, (TAG_ABS, (Base,
  //  *        (SORT_TERM, (TAG_ABS, (Base, Var(1)))))))
  //  */
  // val Abs = DEF(λ(A, (λ(t, pair(SORT_TERM, pair(TAG_ABS, pair(A, t)))))))

  // /**
  //  * Application: t u
  //  *
  //  * Format: (SORT_TERM, (TAG_APP, (t, u)))
  //  *
  //  * Parameters:
  //  * - t: function (must be SORT_TERM)
  //  * - u: argument (must be SORT_TERM)
  //  *
  //  * Examples:
  //  * - id id (identity function applied to itself)
  //  *   = App(Abs(Base, Var(0)), Abs(Base, Var(0)))
  //  *   = (SORT_TERM, (TAG_APP, (id, id)))
  //  *   where id = (SORT_TERM, (TAG_ABS, (Base, Var(0))))
  //  */
  // val App = DEF(λ(t, λ(u, pair(SORT_TERM, pair(TAG_APP, pair(t, u))))))
}
