package lisa.maths.SetTheory.Cardinal

import lisa.maths.SetTheory.Ordinals.Ordinal.*
import lisa.maths.SetTheory.Base.Predef.*
import lisa.maths.Quantifiers.*

import Cardinal.*

object Universe extends lisa.Main:
  private val U, U1 = variable[Ind]
  private val s, x, y, z = variable[Ind]
  private val P, Q, R = variable[Ind >>: Prop]

  /**
   * Definition --- Structual definition of the Tarski/Grothendieck Universe U.
   *
   * A set U is a Tarski Universe if it is a non-empty set that is closed
   * under the fundamental operations of ZFC set theory. The existence o
   * f such a
   * set (the Tarski Axiom) is equivalent to assuming the existence of a
   * Strongly Inaccessible Cardinal κ, where U is often Vκ.
   *
   * The universe U must satisfy:
   * 1. Non-empty: U =/= ∅.
   * 2. Transitivity: ∀y ∈ U. x ∈ y ==> x ∈ U
   * 3. Pairing Closure: ∀x, y ∈ U. (x, y) ∈ U
   * 4. Union Closure: ∀x ∈ U. ∪(x) ∈ U
   * 5. Power Set Closure: ∀x ∈ U. 𝒫(x) ∈ U
   *
   * `isUniverse(U) <=> U ≠ ∅ ∧ transitiveSet(U) ∧ ...`
   *
   * @see [[TransitiveSet]]
   * @see [[tarskiAxiom]]
   */
  val isUniverse = DEF(
    λ(
      U,
      // 1. Transitivity: ∀x ∈ U. x ⊆ U
      (∀(x, (x ∈ U) ==> (x ⊆ U))) /\
        // 2. Pairing: ∀x, y ∈ U. {x, y} ∈ U
        (∀(x, ∀(y, (x ∈ U /\ y ∈ U) ==> (unorderedPair(x, y) ∈ U)))) /\
        // 3. Power Set: ∀x ∈ U. P(x) ∈ U
        (∀(x, (x ∈ U) ==> (⋃(x) ∈ U))) /\
        // 4. Union: ∀x ∈ U. ∪x ∈ U
        (∀(x, (x ∈ U) ==> (𝒫(x) ∈ U)))
    )
  )

  /**
   * Definition of universeOf(x).
   * The smallest (or chosen) universe containing x.
   */
  val universeOf = DEF(λ(x, ε(U, (x ∈ U) /\ isUniverse(U))))

  val existsReplacement = Lemma(
    (∃(x, P(x) /\ Q(x)), ∀(x, Q(x) <=> R(x))) |- ∃(x, P(x) /\ R(x))
  ) {
    have(∀(x, Q(x) <=> R(x)) |- ∀(x, Q(x) <=> R(x))) by Hypothesis
    thenHave(∀(x, Q(x) <=> R(x)) |- Q(x) <=> R(x)) by InstantiateForall(x)
    thenHave((P(x) /\ Q(x), ∀(x, Q(x) <=> R(x))) |- (P(x) /\ R(x))) by Tautology.fromLastStep()
    thenHave((P(x) /\ Q(x), ∀(x, Q(x) <=> R(x))) |- ∃(x, P(x) /\ R(x))) by RightExists
    thenHave(thesis) by LeftExists
  }

  /**
   * Theorem: universeOf(x) exists, contains x, and is a universe.
   */
  val universeOfIsUniverse = Theorem(
    isUniverse(universeOf(x)) /\ (x ∈ universeOf(x))
  ) {
    have(
      isUniverse(U) <=> ((∀(x, (x ∈ U) ==> (x ⊆ U))) /\
        (∀(x, ∀(y, (x ∈ U /\ y ∈ U) ==> (unorderedPair(x, y) ∈ U)))) /\
        (∀(x, (x ∈ U) ==> (⋃(x) ∈ U))) /\
        (∀(x, (x ∈ U) ==> (𝒫(x) ∈ U))))
    ) by Tautology.from(isUniverse.definition)
    val definition = thenHave(
      ∀(
        U,
        isUniverse(U) <=> ((∀(x, (x ∈ U) ==> (x ⊆ U))) /\
          (∀(x, ∀(y, (x ∈ U /\ y ∈ U) ==> (unorderedPair(x, y) ∈ U)))) /\
          (∀(x, (x ∈ U) ==> (⋃(x) ∈ U))) /\
          (∀(x, (x ∈ U) ==> (𝒫(x) ∈ U))))
      )
    ) by RightForall
    have(
      ∀(
        x,
        ∃(
          U,
          (x ∈ U) /\
            (∀(y, (y ∈ U) ==> (y ⊆ U))) /\
            (∀(y, ∀(z, (y ∈ U /\ z ∈ U) ==> (unorderedPair(y, z) ∈ U)))) /\
            (∀(y, (y ∈ U) ==> (⋃(y) ∈ U))) /\
            (∀(y, (y ∈ U) ==> (𝒫(y) ∈ U)))
        )
      )
    ) by Tautology.from(tarskiAxiom)
    thenHave(
      ∃(
        U,
        (x ∈ U) /\
          (∀(y, (y ∈ U) ==> (y ⊆ U))) /\
          (∀(y, ∀(z, (y ∈ U /\ z ∈ U) ==> (unorderedPair(y, z) ∈ U)))) /\
          (∀(y, (y ∈ U) ==> (⋃(y) ∈ U))) /\
          (∀(y, (y ∈ U) ==> (𝒫(y) ∈ U)))
      )
    ) by InstantiateForall(x)
    thenHave(
      ∃(
        U,
        (x ∈ U) /\ ((∀(x, (x ∈ U) ==> (x ⊆ U))) /\
          (∀(x, ∀(y, (x ∈ U /\ y ∈ U) ==> (unorderedPair(x, y) ∈ U)))) /\
          (∀(x, (x ∈ U) ==> (⋃(x) ∈ U))) /\
          (∀(x, (x ∈ U) ==> (𝒫(x) ∈ U))))
      )
    ) by Restate
    val rawEpsilonFact = thenHave(x ∈ ε(U, (x ∈ U) /\ isUniverse(U)) /\ isUniverse(ε(U, (x ∈ U) /\ isUniverse(U)))) by Tautology.fromLastStep(
      definition,
      existsReplacement of (
        x := U,
        P := λ(U, x ∈ U),
        Q := λ(
          U,
          (∀(y, (y ∈ U) ==> (y ⊆ U))) /\
            (∀(y, ∀(z, (y ∈ U /\ z ∈ U) ==> (unorderedPair(y, z) ∈ U)))) /\
            (∀(y, (y ∈ U) ==> (⋃(y) ∈ U))) /\
            (∀(y, (y ∈ U) ==> (𝒫(y) ∈ U)))
        ),
        R := λ(U, isUniverse(U))
      ),
      existsEpsilon of (x := U, P := λ(U, (x ∈ U) /\ isUniverse(U)))
    )
    thenHave(x ∈ ε(U, (x ∈ U) /\ isUniverse(U)) /\ isUniverse(ε(U1, (x ∈ U1) /\ isUniverse(U1)))) by Restate
    thenHave(x ∈ universeOf(x) /\ isUniverse(ε(U1, (x ∈ U1) /\ isUniverse(U1)))) by Substitute(universeOf.definition)
    thenHave(x ∈ universeOf(x) /\ isUniverse(universeOf(x))) by Substitute(universeOf.definition of (U := U1))
  }

  /**
   * product closure in universe
   */
  val universeProductClosure = Theorem(
    (isUniverse(U), A ∈ U, B ∈ U) |- (A × B) ∈ U
  ) {
    sorry
  }
