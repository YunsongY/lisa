package lisa.maths.SetTheory.Relations

import lisa.maths.SetTheory.Base.Predef.{*, given}

import Relation.*
import Properties.*

/**
  * This file defines equivalence relations and related notions of
  * equivalence classes and quotients.
  */
object Equivalence extends lisa.Main {

  private val ~ = variable[Set]
  private val X = variable[Set]

  extension (x: Expr[Set]) {
    // This notation only works for relation `~`, so we keep it private to this file.
    private inline infix def ~(y: Expr[Set]): Expr[Prop] = (x, y) ∈ Equivalence.~
  }

  /**
   * Equivalence Relation --- A relation `~` is an equivalence relation on `X`
   * if it is [[reflexive]], [[symmetric]], and [[transitive]].
   */
  val equivalence = DEF(λ(~, λ(X, relationOn(~)(X) /\ reflexive(~)(X) /\ symmetric(~)(X) /\ transitive(~)(X))))

  /**
    * Equivalence class --- The equivalence class of `a` under `~` is the set
    * of elements related to `a`.
    */
  val equivalenceClass = DEF(λ(a, λ(~, λ(X, { x ∈ X | x ~ a })))).printAs(args => {
    val (a, r, _) = (args(0), args(1), args(2))
    s"[$a]_$r"
  })

  /**
    * Quotient set --- The set of all equivalence classes of `X` by `~` is called
    * the quotient set of `X` of `~`, and is denoted by `X/~`.
    */
  val quotient = DEF(λ(X, λ(~, { equivalenceClass(x)(~)(X) | x ∈ X }))).printAs(args => {
    val (x, r) = (args(0), args(1))
    s"$x/$r"
  })

  extension (X: Expr[Set]) {
    /** Notation `X / ~` for `quotient(X, ~)`. */
    inline infix def /(~ : Expr[Set]): Expr[Set] = quotient(X)(~)
  }

}

