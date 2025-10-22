package coc

import Symbols.*
import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.Quantifiers.*

/**
 * This file defines some useful helper theorem used in the typing rules
 */

object Helper extends lisa.Main {

  /**
   * Unfolds the Set Comprehension definition of the Pi type.
   *
   * Proves: e1 ∈ {f ∈ S | P(f)} <=> e1 ∈ S ∧ P(e1)
   */
  val Pi_expansion = Theorem(
    e1 ∈ {
      f ∈ 𝒫(T1 × ⋃({ app(T2)(a) | a ∈ T1 })) |
        (∀(x ∈ T1, ∃!(y, (x, y) ∈ f))) /\ (∀(a, ∀(b, (a, b) ∈ f ==> (b ∈ app(T2)(a)))))
    } <=> e1 ∈ 𝒫(T1 × ⋃({ app(T2)(a) | a ∈ T1 })) /\
      (∀(x ∈ T1, ∃!(y, (x, y) ∈ e1))) /\ (∀(a, ∀(b, (a, b) ∈ e1 ==> (b ∈ app(T2)(a)))))
  ) {
    have(thesis) by Comprehension.apply
  }

  /**
   * Predicate Logic Lemma: Distributes a universal implication (∀)
   * over an existential conjunction (∃).
   *
   * Proves: (∀x. P(x) => Q(x), ∃x. P(x) ∧ R(x)) |- ∃x. Q(x) ∧ R(x)
   */
  val existPartialApply = Theorem(
    (∀(x, P(x) ==> Q(x)), ∃(x, P(x) /\ R(x))) |- ∃(x, Q(x) /\ R(x))
  ) {
    assume(∀(x, P(x) ==> Q(x)))
    val premise = thenHave(P(x) ==> Q(x)) by InstantiateForall(x)
    val goal = have(P(x) /\ R(x) |- Q(x) /\ R(x)) subproof {
      assume(P(x) /\ R(x))
      have(thesis) by Tautology.from(premise)
    }
    thenHave(P(x) /\ R(x) |- ∃(x, Q(x) /\ R(x))) by RightExists
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
}
