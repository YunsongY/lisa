package cic

import Symbols.*
import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Cardinal.Predef.{*}
import lisa.maths.SetTheory.Functions.Predef.{*}
import lisa.maths.Quantifiers.*

/**
 * This file defines some useful helper theorem used in the typing rules
 */

object Helper extends lisa.Main {

  /**
   * Predicate Logic Lemma: Distributes a universal implication (∀)
   * over an existential conjunction (∃).
   *
   * Proves: (∀x. P(x) => Q(x), ∃x. P(x) ∧ H(x)) |- ∃x. Q(x) ∧ H(x)
   */
  val existPartialApply = Theorem(
    (∀(x, P(x) ==> Q(x)), ∃(x, P(x) /\ H(x))) |- ∃(x, Q(x) /\ H(x))
  ) {
    assume(∀(x, P(x) ==> Q(x)))
    val premise = thenHave(P(x) ==> Q(x)) by InstantiateForall(x)
    val goal = have(P(x) /\ H(x) |- Q(x) /\ H(x)) subproof {
      assume(P(x) /\ H(x))
      have(thesis) by Tautology.from(premise)
    }
    thenHave(P(x) /\ H(x) |- ∃(x, Q(x) /\ H(x))) by RightExists
    thenHave(thesis) by LeftExists
  }

  /**
   * One-Point Rule for a function F:
   * If there exists an x such that P(F(x)) holds and F(x) equals y,
   * then P(y) must hold.
   *
   * Proves: ∃x. (P(F(x)) ∧ y = F(x)) ==> P(y)
   */
  val onePointFunctionRule = Theorem(
    ∃(x, P(F(x)) /\ (y === F(x))) ==> P(y)
  ) {
    have((P(F(x)), y === F(x)) |- P(y)) by Congruence
    thenHave(P(F(x)) /\ (y === F(x)) |- P(y)) by Restate
    thenHave(∃(x, P(F(x)) /\ (y === F(x))) |- P(y)) by LeftExists
    thenHave(thesis) by Restate
  }

  /**
   * Transitivity of Equality (Sequent form).
   *
   * Proves: (x = y ∧ y = z) |- x = z
   */
  val equalTransitivity = Theorem(
    ((x === y) /\ (y === z)) |- (x === z)
  ) {
    assume(x === y)
    assume(y === z)
    have(x === z) by Congruence
    thenHave(thesis) by Restate
  }

  /**
   * Transitivity of Equality (Implication form).
   * This is friendlier for use with Tautology.from.
   *
   * Proves: (x = y ∧ y = z) ==> x = z
   */
  val equalTransitivityApplication = Theorem(
    ((x === y) /\ (y === z)) ==> (x === z)
  ) {
    have(thesis) by Tautology.from(equalTransitivity)
  }

  /**
   * Substitution rule (Congruence) in implication form.
   *
   * Proves: (P(x) ∧ y = x) ==> P(y)
   */
  val localSubstitute = Theorem(
    (P(x) /\ (y === x)) ==> P(y)
  ) {
    have((P(x), y === x) |- P(y)) by Congruence
    thenHave(P(x) /\ (y === x) |- P(y)) by Restate
    thenHave(thesis) by Restate
  }

  /**
   */
  val universeFamilyUnionClosure = Theorem(
    (isUniverse(U), A ∈ U, ∀(x, x ∈ A ==> T2(x) ∈ U)) |- ⋃({ T2(x) | x ∈ A }) ∈ U
  ) {
    sorry
  }

  val universePiClosure = Theorem(
    (isUniverse(U), T1 ∈ U, ∀(x, x ∈ T1 ==> T2(x) ∈ U)) |-
      Pi(T1)(T2) ∈ U
  ) {
    sorry
  }

  /**
   * Theorem --- If A is a subset of B, then the union of A and B is B.
   *
   * (A ⊆ B) |- (A ∪ B) === B
   */
  val unionAbsorb = Theorem(
    (A ⊆ B) |- (A ∪ B) === B
  ) {
    assume(A ⊆ B)
    val forward = have((A ∪ B) ⊆ B) by Tautology.from(
      Union.leftUnionSubset of (x := A, y := B, z := B),
      Subset.reflexivity of (x := B)
    )
    val backward = have(B ⊆ (A ∪ B)) by Tautology.from(
      Union.rightSubset of (x := A, y := B)
    )
    have(thesis) by Tautology.from(
      forward,
      backward,
      Subset.antisymmetry of (x := (A ∪ B), y := B)
    )
  }
}
