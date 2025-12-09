package lisa.maths.SetTheory.Cardinal

import lisa.maths.SetTheory.Ordinals.Ordinal.*
import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.Quantifiers.*

import Cardinal.*
import java.time.Instant
import java.security.DrbgParameters.Reseed
import lisa.SetTheoryLibrary.unorderedPair
import lisa.SetTheoryLibrary.unorderedPair
import java.lang.Character.Subset
import lisa.maths.SetTheory.Functions.Function.functionBetween
import lisa.maths.SetTheory.Functions.Function.functionBetween

object Universe extends lisa.Main:
  private val U, U1, G, I = variable[Ind]
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
        (∀(x, (x ∈ U) ==> (𝒫(x) ∈ U))) /\
        // 5. Replacement closure
        (∀(A, (A ∈ U) ==> ∀(f, (f :: (A, U)) ==> (range(f) ∈ U))))
    )
  )

  /**
   * Definition of universeOf(x).
   * The smallest (or chosen) universe containing x.
   */
  val universeOf = DEF(λ(x, ε(U, (x ∈ U) /\ isUniverse(U))))

  /**
   * Lemma related to sugar for epsilon and replacement.
   */
  private def _pair(x: Expr[Ind], y: Expr[Ind]): Expr[Ind] = unorderedPair(unorderedPair(x, x), unorderedPair(x, y))
  val functionLemma = Theorem(
    ∀(a, a ∈ A ==> ∃(b, (b ∈ U) /\ (_pair(a, b) ∈ G) /\ (∀(z, ((z ∈ U) /\ (_pair(a, z) ∈ G)) ==> (z === b))))) ==> functionOn(G)(A)
  ) {
    assume(∀(a, a ∈ A ==> ∃(b, (b ∈ U) /\ (_pair(a, b) ∈ G) /\ (∀(z, ((z ∈ U) /\ (_pair(a, z) ∈ G)) ==> (z === b))))))
    thenHave(a ∈ A ==> ∃(b, (b ∈ U) /\ (_pair(a, b) ∈ G) /\ (∀(z, ((z ∈ U) /\ (_pair(a, z) ∈ G)) ==> (z === b))))) by InstantiateForall(a)
    thenHave(a ∈ A |- ∃(b, (b ∈ U) /\ (_pair(a, b) ∈ G) /\ (∀(z, ((z ∈ U) /\ (_pair(a, z) ∈ G)) ==> (z === b))))) by Restate
    thenHave(
      a ∈ A |- ∃(b, (b ∈ U) /\ (unorderedPair(singleton(a), unorderedPair(a, b)) ∈ G) /\ (∀(z, ((z ∈ U) /\ (_pair(a, z) ∈ G) ==> (z === b)))))
    ) by Substitute(singleton.definition of (x := a))
    thenHave(
      a ∈ A |- ∃(b, (b ∈ U) /\ (unorderedPair(singleton(a), unorderedPair(a, b)) ∈ G) /\ (∀(z, ((z ∈ U) /\ (unorderedPair(singleton(a), unorderedPair(a, z)) ∈ G)) ==> (z === b))))
    ) by Substitute(singleton.definition of (x := a))
    // thenHave(
    //   a ∈ A |- ∃(b, (b ∈ U) /\ (pair(a)(b) ∈ G) /\ (∀(z, ((z ∈ U) /\ (pair(a)(z) ∈ G)) ==> (z === b))))
    // ) by Substitute(pair.definition of (x := a, y := z), pair.definition of (x := a, y := b))
    have(a ∈ A |- ∃(b, (b ∈ U) /\ (pair(a)(b) ∈ G) /\ (∀(z, ((z ∈ U) /\ (pair(a)(z) ∈ G)) ==> (z === b))))) subproof {
      sorry
    }
    thenHave(a ∈ A |- ∃!(b, (b ∈ U) /\ (pair(a)(b) ∈ G))) by Substitute(∃!.definition of (P := λ(b, (b ∈ U) /\ (pair(a)(b) ∈ G))))

    sorry
    // assume(functionOn(G)(A))
    // thenHave(relationBetween(G)(A)(U)) by Substitute(functionOn.definition)
    // thenHave(∀(a ∈ A, ∃(b ∈ U, pair(a, b) ∈ G))) by Substitute(relationBetween.definition)
    // thenHave(thesis) by Restate
  }

  val existsReplacement = Lemma(
    (∃(x, P(x) /\ Q(x)), ∀(x, Q(x) <=> R(x))) |- ∃(x, P(x) /\ R(x))
  ) {
    have(∀(x, Q(x) <=> R(x)) |- ∀(x, Q(x) <=> R(x))) by Hypothesis
    thenHave(∀(x, Q(x) <=> R(x)) |- Q(x) <=> R(x)) by InstantiateForall(x)
    thenHave((P(x) /\ Q(x), ∀(x, Q(x) <=> R(x))) |- (P(x) /\ R(x))) by Tautology.fromLastStep()
    thenHave((P(x) /\ Q(x), ∀(x, Q(x) <=> R(x))) |- ∃(x, P(x) /\ R(x))) by RightExists
    thenHave(thesis) by LeftExists
  }

  val universeExistence = Theorem(
    ∀(x, ∃(U, (x ∈ U) /\ isUniverse(U)))
  ) {
    sorry
  }

  /**
   * Theorem: universeOf(x) exists, contains x, and is a universe.
   */
  val universeOfIsUniverse = Theorem(
    isUniverse(universeOf(x)) /\ (x ∈ universeOf(x))
  ) {
    sorry
    // have(
    //   isUniverse(U) <=> ((∀(x, (x ∈ U) ==> (x ⊆ U))) /\
    //     (∀(x, ∀(y, (x ∈ U /\ y ∈ U) ==> (unorderedPair(x, y) ∈ U)))) /\
    //     (∀(x, (x ∈ U) ==> (⋃(x) ∈ U))) /\
    //     (∀(x, (x ∈ U) ==> (𝒫(x) ∈ U))))
    // ) by Tautology.from(isUniverse.definition)
    // val definition = thenHave(
    //   ∀(
    //     U,
    //     isUniverse(U) <=> ((∀(x, (x ∈ U) ==> (x ⊆ U))) /\
    //       (∀(x, ∀(y, (x ∈ U /\ y ∈ U) ==> (unorderedPair(x, y) ∈ U)))) /\
    //       (∀(x, (x ∈ U) ==> (⋃(x) ∈ U))) /\
    //       (∀(x, (x ∈ U) ==> (𝒫(x) ∈ U))))
    //   )
    // ) by RightForall
    // have(
    //   ∀(
    //     x,
    //     ∃(
    //       U,
    //       (x ∈ U) /\
    //         (∀(y, (y ∈ U) ==> (y ⊆ U))) /\
    //         (∀(y, ∀(z, (y ∈ U /\ z ∈ U) ==> (unorderedPair(y, z) ∈ U)))) /\
    //         (∀(y, (y ∈ U) ==> (⋃(y) ∈ U))) /\
    //         (∀(y, (y ∈ U) ==> (𝒫(y) ∈ U)))
    //     )
    //   )
    // ) by Tautology.from(tarskiAxiom)
    // thenHave(
    //   ∃(
    //     U,
    //     (x ∈ U) /\
    //       (∀(y, (y ∈ U) ==> (y ⊆ U))) /\
    //       (∀(y, ∀(z, (y ∈ U /\ z ∈ U) ==> (unorderedPair(y, z) ∈ U)))) /\
    //       (∀(y, (y ∈ U) ==> (⋃(y) ∈ U))) /\
    //       (∀(y, (y ∈ U) ==> (𝒫(y) ∈ U)))
    //   )
    // ) by InstantiateForall(x)
    // thenHave(
    //   ∃(
    //     U,
    //     (x ∈ U) /\ ((∀(x, (x ∈ U) ==> (x ⊆ U))) /\
    //       (∀(x, ∀(y, (x ∈ U /\ y ∈ U) ==> (unorderedPair(x, y) ∈ U)))) /\
    //       (∀(x, (x ∈ U) ==> (⋃(x) ∈ U))) /\
    //       (∀(x, (x ∈ U) ==> (𝒫(x) ∈ U))))
    //   )
    // ) by Restate
    // val rawEpsilonFact = thenHave(x ∈ ε(U, (x ∈ U) /\ isUniverse(U)) /\ isUniverse(ε(U, (x ∈ U) /\ isUniverse(U)))) by Tautology.fromLastStep(
    //   definition,
    //   existsReplacement of (
    //     x := U,
    //     P := λ(U, x ∈ U),
    //     Q := λ(
    //       U,
    //       (∀(y, (y ∈ U) ==> (y ⊆ U))) /\
    //         (∀(y, ∀(z, (y ∈ U /\ z ∈ U) ==> (unorderedPair(y, z) ∈ U)))) /\
    //         (∀(y, (y ∈ U) ==> (⋃(y) ∈ U))) /\
    //         (∀(y, (y ∈ U) ==> (𝒫(y) ∈ U)))
    //     ),
    //     R := λ(U, isUniverse(U))
    //   ),
    //   existsEpsilon of (x := U, P := λ(U, (x ∈ U) /\ isUniverse(U)))
    // )
    // thenHave(x ∈ ε(U, (x ∈ U) /\ isUniverse(U)) /\ isUniverse(ε(U1, (x ∈ U1) /\ isUniverse(U1)))) by Restate
    // thenHave(x ∈ universeOf(x) /\ isUniverse(ε(U1, (x ∈ U1) /\ isUniverse(U1)))) by Substitute(universeOf.definition)
    // thenHave(x ∈ universeOf(x) /\ isUniverse(universeOf(x))) by Substitute(universeOf.definition of (U := U1))
  }

  /**
   * product closure in universe
   */
  val universeProductClosure = Theorem(
    (isUniverse(U), A ∈ U, B ∈ U) |- (A × B) ∈ U
  ) {
    sorry
  }

  val bridgeProof = Theorem(
    (∀(
      A,
      (A ∈ U) ==> ∀(
        G,
        ∀(a, a ∈ A ==> ∃(b, (b ∈ U) /\ (_pair(a, b) ∈ G) /\ (∀(z, ((z ∈ U) /\ (_pair(a, z) ∈ G)) ==> (z === b))))) ==>
          ∃(I, (I ∈ U) /\ ∀(b, b ∈ I <=> ∃(a, (a ∈ A) /\ (_pair(a, b) ∈ G))))
      )
    )) |- (∀(A, (A ∈ U) ==> ∀(f, (f :: (A, U)) ==> (range(f) ∈ U))))
  ) {
    assume(
      ∀(
        A,
        (A ∈ U) ==> ∀(
          G,
          ∀(a, a ∈ A ==> ∃(b, (b ∈ U) /\ (_pair(a, b) ∈ G) /\ (∀(z, ((z ∈ U) /\ (_pair(a, z) ∈ G)) ==> (z === b))))) ==> ∃(I, (I ∈ U) /\ ∀(b, b ∈ I <=> ∃(a, (a ∈ A) /\ (_pair(a, b) ∈ G))))
        )
      )
    )
    thenHave(
      (A ∈ U) ==> ∀(
        G,
        ∀(a, a ∈ A ==> ∃(b, (b ∈ U) /\ (_pair(a, b) ∈ G) /\ (∀(z, ((z ∈ U) /\ (_pair(a, z) ∈ G)) ==> (z === b))))) ==> ∃(I, (I ∈ U) /\ ∀(b, b ∈ I <=> ∃(a, (a ∈ A) /\ (_pair(a, b) ∈ G))))
      )
    ) by InstantiateForall(A)

    have(∀(A, (A ∈ U) ==> ∀(f, (f :: (A, U)) ==> (range(f) ∈ U)))) subproof {
      have((A ∈ U, f :: (A, U)) |- functionBetween(f)(A)(U))
      // thenHave(
      //   (A ∈ U, f :: (A, U)) |- relationBetween(f)(A)(U) /\ ∀(x ∈ A, ∃!(y, (x, y) ∈ f))
      // ) by Substitute(functionBetween.definition of (f := f, A := A, B := U))

      sorry
    }

    sorry
  }
