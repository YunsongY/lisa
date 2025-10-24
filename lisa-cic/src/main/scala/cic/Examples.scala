package cic

import Symbols.*
import TypingRules.*
import lisa.maths.SetTheory.Base.Predef.{*, given}

object Examples extends lisa.Main {
  private val Nat = variable[Set]
  private val Bool = variable[Set]
  private val x, y = variable[Ind]
  private val A, B = variable[Set]
  private val a = variable[Ind]

  val test1 = Theorem(y ∈ Nat |- app(fun(x, Nat, x))(y) === y) {
    assume(y ∈ Nat)
    have(thesis) by Tautology.from(BetaReduction of (e2 := y, T := Nat, e := λ(x, x)))
  }

  val test2 = Theorem(a ∈ A |- typeOf(app(fun(x, A, fun(y, B, x)))(a))(Pi(B)(λ(x, A)))) {
    assume(a ∈ A)
    have(∀(x ∈ A, fun(y, B, x) ∈ Pi(B)(λ(x, A)))) subproof {
      have(x ∈ A |- ∀(y ∈ B, x ∈ A)) subproof {
        have((x ∈ A, y ∈ B) |- x ∈ A) by Hypothesis
        thenHave(x ∈ A |- y ∈ B ==> x ∈ A) by Tautology.fromLastStep()
        thenHave(thesis) by RightForall
      }
      thenHave(x ∈ A ==> fun(y, B, x) ∈ Pi(B)(λ(x, A))) by Tautology.fromLastStep(
        TAbs of (
          e := λ(y, x),
          T1 := B,
          T2 := λ(x, A)
        )
      )
      thenHave(thesis) by RightForall
    }
    thenHave(fun(x, A, fun(y, B, x)) ∈ Pi(A)(λ(x, Pi(B)(λ(x, A))))) by Tautology.fromLastStep(
      TAbs of (
        e := λ(x, fun(y, B, x)),
        T1 := A,
        T2 := λ(x, Pi(B)(λ(x, A)))
      )
    )
    thenHave(thesis) by Tautology.fromLastStep(
      TApp of (
        e1 := fun(x, A, fun(y, B, x)),
        e2 := a,
        T2 := λ(x, Pi(B)(λ(x, A))),
        T1 := A
      )
    )
  }
}
