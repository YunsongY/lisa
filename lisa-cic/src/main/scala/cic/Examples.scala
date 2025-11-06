package cic

import Symbols.*
import Tactics.*
import TypingRules.*
import lisa.maths.SetTheory.Base.Predef.{*, given}
import cic.Tactics.Typecheck
import lisa.utils.prooflib.BasicStepTactic.Hypothesis

object Examples extends lisa.Main {
  private val Nat = variable[Ind]
  private val Bool = variable[Ind]
  private val x, y = variable[Ind]
  private val A, B = variable[Ind]
  private val a = variable[Ind]
  private val Typ = variable[Ind]

  val test1 = Theorem(y ∈ Nat |- app(fun(x, Nat, x))(y) === y) {
    assume(y ∈ Nat)
    have(thesis) by Tautology.from(BetaReduction of (e2 := y, T := Nat, e := λ(x, x)))
  }

  val test2 = Theorem(a ∈ A |- typeOf(app(fun(x, A, fun(y, B, x)))(a))(B ->: A)) {
    val stmt1 = have(fun(x, A, fun(y, B, x)) ∈ (A ->: B ->: A)) subproof {
      have(x ∈ A |- fun(y, B, x) ∈ (B ->: A)) subproof {
        assume(x ∈ A)
        have(∀(y ∈ B, x ∈ A)) subproof {
          have(y ∈ B |- x ∈ A) subproof {
            assume(y ∈ B)
            have(x ∈ A) by Hypothesis
          }
          thenHave(y ∈ B ==> x ∈ A) by Restate
          thenHave(thesis) by RightForall
        }
        thenHave(thesis) by Tautology.fromLastStep(
          TAbs of (
            e := λ(y, x),
            T1 := B,
            T2 := λ(x, A)
          )
        )
      }
      thenHave(x ∈ A ==> fun(y, B, x) ∈ (B ->: A)) by Restate
      thenHave(∀(x ∈ A, fun(y, B, x) ∈ (B ->: A))) by RightForall
      thenHave(thesis) by Tautology.fromLastStep(
        TAbs of (
          e := λ(x, fun(y, B, x)),
          T1 := A,
          T2 := λ(x, B ->: A)
        )
      )
    }
    thenHave(thesis) by Tautology.fromLastStep(
      TApp of (
        e1 := fun(x, A, fun(y, B, x)),
        e2 := a,
        T2 := λ(x, B ->: A),
        T1 := A
      )
    )
  }

  // val test3 = Theorem(a ∈ A |- app(fun(x, A, fun(y, B, x)))(a) ∈ (B ->: A)) {
  //   have(thesis) by Typecheck.prove
  // }

  // Counter example
  // val test4 = Theorem(Pi(B)(λ(x, A)) === Pi(B)(λ(y, A))) {
  //   have(thesis) by RightRefl
  // }

  val test5 = Theorem(Nat ∈ Typ |- app(fun(x, Typ, fun(y, x, y)))(Nat) ∈ Pi(Nat)(λ(y, Nat))) {
    have(thesis) by Typecheck.prove
  }
}
