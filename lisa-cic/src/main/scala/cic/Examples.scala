package cic

import Symbols.*
import Tactics.*
import TypingRules.*
import lisa.maths.SetTheory.Base.Predef.{*, given}
import cic.Tactics.Typecheck

object Examples extends lisa.Main {
  private val Typ = variable[Ind]
  private val Nat, Bool, String = variable[Ind]
  private val A, B, C, T = variable[Ind]
  private val f, g, x, y, a, s, t = variable[Ind]

  ////////////////////////////////
  //////// Basic Tests ///////////
  ////////////////////////////////

  // Identity function
  val test0_identity = Theorem(a ∈ Nat |- app(fun(x :: Nat, x))(a) ∈ Nat) {
    have(thesis) by Typecheck.prove
  }
  // Curried function
  val test1_curried = Theorem(s ∈ String |- fun(x :: Nat, fun(y :: Bool, s)) ∈ (Nat ->: (Bool ->: String))) {
    have(thesis) by Typecheck.prove
  }
  // Composition function
  val test2_composition = Theorem((f ∈ (A ->: B), g ∈ (B ->: C), a ∈ A) |- app(g)(app(f)(a)) ∈ C) {
    have(thesis) by Typecheck.prove
  }
  // Dependent function
  val test3_dependent = Theorem(Nat ∈ Typ |- app(fun(x :: Typ, fun(y :: x, y)))(Nat) ∈ Π(y :: Nat, Nat)) {
    have(thesis) by Typecheck.prove
  }
  // Nested Polymorphic Projection
  val test4_nested_polymorphic_projection = Theorem(
    (a ∈ Nat, b ∈ Nat, Nat ∈ Typ) |-
      app(app(app(fun(T :: Typ, fun(x :: T, fun(y :: T, x))))(Nat))(a))(b) ∈ Nat
  ) {
    have(thesis) by Typecheck.prove
  }

  ///////////////////////////////////////////////
  ///////// Relative Complicated Tests //////////
  ///////////////////////////////////////////////

  /**
   * Test1: S.K.I combinator
   */
  val STerm = fun(f :: (A ->: A ->: A), fun(g :: (A ->: A), fun(x :: A, app(app(f)(x))(app(g)(x)))))
  val SType = (A ->: A ->: A) ->: (A ->: A) ->: A ->: A
  val KTerm = fun(x :: A, fun(y :: A, x))
  val KType = A ->: A ->: A
  val ITerm = fun(x :: A, x)
  val IType = A ->: A
  val testS = Theorem(STerm ∈ SType) {
    have(thesis) by Typecheck.prove
  }
  val testK = Theorem(KTerm ∈ KType) {
    have(thesis) by Typecheck.prove
  }
  val testI = Theorem(ITerm ∈ IType) {
    have(thesis) by Typecheck.prove
  }
  val test_SKI = Theorem(a ∈ A |- app(app(app(STerm)(KTerm))(ITerm))(a) ∈ A) {
    have(thesis) by Typecheck.prove
  }

  /**
   * Test2: Polymorphic Identity
   */
  val PolyId = fun(T :: Typ, fun(t :: T, t))
  val PolyIdType = Π(T :: Typ, T ->: T)
  val test = Theorem(Typ ∈ Typ |- PolyId ∈ PolyIdType) {
    have(thesis) by Typecheck.prove
  }
  // The following one will fail since without form-Rule
  // val test_SelfApp = Theorem(Typ ∈ Typ |- app(app(PolyId)(PolyIdType))(PolyId) ∈ PolyIdType) {
  //   have(thesis) by Typecheck.prove
  // }
}
