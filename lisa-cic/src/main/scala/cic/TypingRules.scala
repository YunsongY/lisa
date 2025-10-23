package cic
import Symbols.*
import Helper.*
import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.Quantifiers.*
import lisa.utils.prooflib.BasicStepTactic.Hypothesis
import lisa.utils.prooflib.BasicStepTactic.Hypothesis
import lisa.utils.prooflib.BasicStepTactic.Hypothesis
import lisa.utils.prooflib.SimpleDeducedSteps.InstantiateForall

object TypingRules extends lisa.Main {

  /**
   * Unfolds the Set Comprehension definition of the Pi type.
   *
   * Proves: e1 ∈ {f ∈ S | P(f)} <=> e1 ∈ S ∧ P(e1)
   */
  val pi_expansion = Theorem(
    e1 ∈ {
      f ∈ 𝒫(T1 × ⋃({ app(T2)(a) | a ∈ T1 })) |
        (∀(x ∈ T1, ∃!(y, (x, y) ∈ f))) /\ (∀(a, ∀(b, (a, b) ∈ f ==> (b ∈ app(T2)(a)))))
    } <=> e1 ∈ 𝒫(T1 × ⋃({ app(T2)(a) | a ∈ T1 })) /\
      (∀(x ∈ T1, ∃!(y, (x, y) ∈ e1))) /\ (∀(a, ∀(b, (a, b) ∈ e1 ==> (b ∈ app(T2)(a)))))
  ) {
    have(thesis) by Comprehension.apply
  }

  /**
   * Abs Application Characterization (Full Equivalence)
   *
   * This is the defining property for the abstract application relation, abs(T1)(e).
   * A tuple (x, y) belongs to the relation if and only if:
   * 1. x satisfies the domain constraint T1.
   * 2. y is exactly the result of the concrete application e(x).
   *
   * This theorem is crucial for both introducing and eliminating the abs operator from proofs.
   */
  val absApplicationMembership = Theorem(
    ((x, y) ∈ abs(T)(e) <=> x ∈ T /\ (y === e(x)))
  ) {
    val `==>` = have((x, y) ∈ abs(T)(e) ==> x ∈ T /\ (y === e(x))) subproof {
      assume((x, y) ∈ abs(T)(e))
      have(((a, e(a)) === (x, y)) ==> (a === x) /\ (e(a) === y)) by Tautology.from(Pair.extensionality of (b := e(a), c := x, d := y))
      val premise = thenHave(∀(a, ((a, e(a)) === (x, y)) ==> (a === x) /\ (e(a) === y))) by RightForall
      assume((x, y) ∈ abs(T)(e))
      thenHave((x, y) ∈ { (a, e(a)) | a ∈ T }) by Substitute(abs.definition of (x := a, T := T))
      thenHave(thesis) by Tautology.fromLastStep(
        Replacement.membership of (y := (x, y), x := a, A := T, F := λ(x, (x, e(x)))),
        premise,
        existPartialApply of (
          P := λ(a, (a, e(a)) === (x, y)),
          Q := λ(a, (a === x) /\ (e(a) === y)),
          R := λ(a, a ∈ T)
        ),
        onePointRule of (x := a, y := x, P := λ(x, x ∈ T /\ (e(x) === y)))
      )
    }
    val `<==` = have(x ∈ T /\ (y === e(x)) ==> (x, y) ∈ abs(T)(e)) subproof {
      have(x ∈ T |- x ∈ T) by Hypothesis
      thenHave(x ∈ T |- (x, e(x)) ∈ { (x, e(x)) | x ∈ T }) by
        Tautology.fromLastStep(Replacement.map of (F := λ(x, (x, e(x))), A := T))
      val stmT = thenHave(x ∈ T |- (x, e(x)) ∈ abs(T)(e)) by Substitute(abs.definition of (T := T))
      have(y === e(x) |- y === e(x)) by Hypothesis
      thenHave(thesis) by Tautology.fromLastStep(
        stmT,
        localSubstitute of (P := λ(y, (x, y) ∈ abs(T)(e)), x := e(x))
      )
    }
    have(thesis) by Tautology.from(`<==`, `==>`)
  }

  /**
   * Abs Application Functionality
   *
   * For any x in the domain T, there exists a unique result y such that (x, y) is in abs(T)(e).
   */
  val absApplicationFunctionality = Theorem(∀(x ∈ T, ∃!(y, (x, y) ∈ abs(T)(e)))) {
    have(x ∈ T |- x ∈ T) by Hypothesis
    // Ensure exist y for (x, y) ∈ λ(x: T).e
    val existCond = have(x ∈ T |- ∃(y, (x, y) ∈ abs(T)(e))) subproof {
      assume(x ∈ T)
      have((x, e(x)) ∈ { (x, e(x)) | x ∈ T }) by Tautology.from(Replacement.map of (A := T, F := λ(x, (x, e(x)))))
      thenHave((x, e(x)) ∈ abs(T)(e)) by Substitute(abs.definition of (T := T))
      thenHave(thesis) by RightExists
    }
    // Ensure uniqueness
    val uniqueness = have(∀(y, ∀(z, (x, y) ∈ abs(T)(e) /\ (x, z) ∈ abs(T)(e) ==> (y === z)))) subproof {
      have((x, y) ∈ abs(T)(e) |- (x, y) ∈ abs(T)(e)) by Hypothesis
      val case1 = thenHave((x, y) ∈ abs(T)(e) |- y === e(x)) by Tautology.fromLastStep(absApplicationMembership of (T := T))
      have((x, z) ∈ abs(T)(e) |- (x, z) ∈ abs(T)(e)) by Hypothesis
      thenHave((x, y) ∈ abs(T)(e) /\ (x, z) ∈ abs(T)(e) ==> (y === z)) by Tautology.fromLastStep(
        case1,
        absApplicationMembership of (y := z, T := T),
        equalTransitivityApplication of (x := y, y := e(x), z := z)
      )
      thenHave(thesis) by Generalize
    }
    have(x ∈ T ==> ∃(y, (x, y) ∈ abs(T)(e)) /\ ∀(y, ∀(z, (x, y) ∈ abs(T)(e) /\ (x, z) ∈ abs(T)(e) ==> (y === z)))) by
      Tautology.from(existCond, uniqueness)
    thenHave(x ∈ T ==> ∃!(y, (x, y) ∈ abs(T)(e))) by
      Substitute(existsOneAlternativeDefinition of (x := y, P := λ(y, (x, y) ∈ abs(T)(e))))
    thenHave(thesis) by RightForall
  }

  /**
   *    x : T ∈ Γ
   *    ───────── (T-Var)
   *    x : T
   */
  val TVar = Theorem(typeOf(x)(T) |- typeOf(x)(T)) {
    have(thesis) by Tautology
  }

  /**
   *    ∀(x: T1). e(x) : T2(x)
   *    ───────────────────── (T-Abs)
   *    (λx:T1.e(x)) : Π(x: T1).T2
   */
  val TAbs = Theorem(
    ∀(x ∈ T1, typeOf(e(x))(app(T2)(x)))
      |- typeOf(abs(T1)(e))(Pi(T1)(T2))
  ) {
    assume(∀(x ∈ T1, typeOf(e(x))(app(T2)(x))))
    val premise = have(x ∈ T1 ==> typeOf(e(x))(app(T2)(x))) by InstantiateForall

    // Set boundary checking
    have(abs(T1)(e) ⊆ (T1 × ⋃({ app(T2)(a) | a ∈ T1 }))) subproof {
      have(z ∈ abs(T1)(e) |- z ∈ abs(T1)(e)) by Hypothesis
      thenHave(z ∈ abs(T1)(e) |- z ∈ { (x, e(x)) | x ∈ T1 }) by Substitute(abs.definition of (T := T1))
      val stmt1 = thenHave(z ∈ abs(T1)(e) |- ∃(x, x ∈ T1 /\ ((x, e(x)) === z))) by
        Tautology.fromLastStep(Replacement.membership of (y := z, F := λ(x, (x, e(x))), A := T1))
      have(x ∈ T1 ==> (x, e(x)) ∈ (T1 × ⋃({ app(T2)(a) | a ∈ T1 }))) subproof {
        assume(x ∈ T1)
        have(app(T2)(x) ∈ { app(T2)(a) | a ∈ T1 }) by Tautology.from(Replacement.map of (A := T1, F := λ(x, app(T2)(x))))
        have(e(x) ∈ app(T2)(x) /\ app(T2)(x) ∈ { app(T2)(a) | a ∈ T1 }) by Tautology.from(lastStep, premise)
        thenHave(∃(y, e(x) ∈ y /\ y ∈ { app(T2)(a) | a ∈ T1 })) by RightExists
        have(thesis) by Tautology.from(
          lastStep,
          unionAxiom of (z := e(x), x := { app(T2)(a) | a ∈ T1 }),
          CartesianProduct.membershipSufficientCondition of (y := e(x), A := T1, B := ⋃({ app(T2)(a) | a ∈ T1 }))
        )
      }
      thenHave(∀(x ∈ T1, (x, e(x)) ∈ (T1 × ⋃({ app(T2)(a) | a ∈ T1 })))) by RightForall
      thenHave(z ∈ abs(T1)(e) |- z ∈ (T1 × ⋃({ app(T2)(a) | a ∈ T1 }))) by Tautology.fromLastStep(
        stmt1,
        existPartialApply of (
          P := λ(x, x ∈ T1),
          Q := λ(x, (x, e(x)) ∈ (T1 × ⋃({ app(T2)(a) | a ∈ T1 }))),
          R := λ(x, (x, e(x)) === z)
        ),
        onePointFunctionRule of (P := λ(x, x ∈ (T1 × ⋃({ app(T2)(a) | a ∈ T1 }))), y := z, F := λ(x, (x, e(x))))
      )
      thenHave(z ∈ abs(T1)(e) ==> z ∈ (T1 × ⋃({ app(T2)(a) | a ∈ T1 }))) by Restate
      thenHave(∀(z, z ∈ abs(T1)(e) ==> z ∈ (T1 × ⋃({ app(T2)(a) | a ∈ T1 })))) by RightForall
      thenHave(thesis) by Tautology.fromLastStep(subsetAxiom of (x := abs(T1)(e), y := (T1 × ⋃({ app(T2)(a) | a ∈ T1 }))))
    }
    val boundary_check = thenHave(abs(T1)(e) ∈ 𝒫(T1 × ⋃({ app(T2)(a) | a ∈ T1 }))) by Substitute(powerSetAxiom)

    // Expression type check
    val typing_check = have(∀(a, ∀(b, (a, b) ∈ abs(T1)(e) ==> (b ∈ app(T2)(a))))) subproof {
      have((a, b) ∈ abs(T1)(e) |- (a, b) ∈ abs(T1)(e)) by Hypothesis
      thenHave((a, b) ∈ abs(T1)(e) |- b ∈ app(T2)(a)) by Tautology.fromLastStep(
        absApplicationMembership of (x := a, y := b, T := T1),
        premise of (x := a),
        localSubstitute of (P := λ(x, x ∈ app(T2)(a)), x := e(a), y := b)
      )
      thenHave((a, b) ∈ abs(T1)(e) ==> b ∈ app(T2)(a)) by Restate
      thenHave(thesis) by Generalize
    }

    // Combine three lemmas all together
    have(
      abs(T1)(e) ∈ 𝒫(T1 × ⋃({ app(T2)(a) | a ∈ T1 })) /\
        (∀(x ∈ T1, ∃!(y, (x, y) ∈ abs(T1)(e)))) /\
        (∀(a, ∀(b, (a, b) ∈ abs(T1)(e) ==> (b ∈ app(T2)(a)))))
    ) by Tautology.from(boundary_check, absApplicationFunctionality of (T := T1), typing_check)
    thenHave(abs(T1)(e) ∈ {
      f ∈ 𝒫(T1 × ⋃({ app(T2)(a) | a ∈ T1 })) |
        (∀(x ∈ T1, ∃!(y, (x, y) ∈ f))) /\ (∀(a, ∀(b, (a, b) ∈ f ==> (b ∈ app(T2)(a)))))
    }) by Substitute(pi_expansion of (e1 := abs(T1)(e)))
    thenHave(thesis) by Substitute(Pi.definition)
  }

  /**
   *    e1: Π(x: T1).T2, e2: T1
   *    ────────────────────────── (T-App)
   *    e1(e2): T2(e2)
   */
  val TApp = Theorem(
    (typeOf(e1)(Pi(T1)(T2)), typeOf(e2)(T1))
      |- typeOf(app(e1)(e2))(app(T2)(e2))
  ) {
    assume(typeOf(e1)(Pi(T1)(T2)))
    assume(typeOf(e2)(T1))
    have(e1 ∈ Pi(T1)(T2)) by Restate
    thenHave(
      e1 ∈ {
        f ∈ 𝒫(T1 × ⋃({ app(T2)(a) | a ∈ T1 })) |
          (∀(x ∈ T1, ∃!(y, (x, y) ∈ f))) /\ (∀(a, ∀(b, (a, b) ∈ f ==> (b ∈ app(T2)(a)))))
      }
    ) by Substitute(Pi.definition)
    val stmt = have(
      e1 ∈ 𝒫(T1 × ⋃({ app(T2)(a) | a ∈ T1 })) /\
        (∀(x ∈ T1, ∃!(y, (x, y) ∈ e1))) /\ (∀(a, ∀(b, (a, b) ∈ e1 ==> (b ∈ app(T2)(a)))))
    ) by Tautology.from(pi_expansion, lastStep)

    have(∀(x ∈ T1, ∃!(y, (x, y) ∈ e1))) by Weakening(stmt)
    thenHave(x ∈ T1 ==> ∃!(y, (x, y) ∈ e1)) by InstantiateForall(x)
    have(∃!(y, (e2, y) ∈ e1)) by Tautology.from(lastStep of (x := e2))
    have((e2, ε(y, (e2, y) ∈ e1)) ∈ e1) by Tautology.from(lastStep, existsOneEpsilon of (P := λ(x, (e2, x) ∈ e1)))
    val stmt1 = thenHave((e2, app(e1)(e2)) ∈ e1) by Substitute(app.definition of (f := e1, x := e2))

    have((∀(a, ∀(b, (a, b) ∈ e1 ==> (b ∈ app(T2)(a)))))) by Weakening(stmt)
    thenHave((e2, app(e1)(e2)) ∈ e1 ==> app(e1)(e2) ∈ app(T2)(e2)) by InstantiateForall(e2, app(e1)(e2))
    have(thesis) by Tautology.from(lastStep, stmt1)
  }

  /**
   * Beta Reduction(β-reduction):
   *
   *  (λx:T1. e(x))(e2) --> e(e2)
   *
   *  e2: T1 ==> app(abs(T1)(e))(e2) === e(e2)
   */
  val BetaReduction = Theorem(
    typeOf(e2)(T1) |- app(abs(T1)(e))(e2) === e(e2)
  ) {
    assume(e2 ∈ T1)
    have(e(e2) === e(e2)) by RightRefl
    val stmt1 = thenHave((e2, e(e2)) ∈ abs(T1)(e)) by
      Tautology.fromLastStep(absApplicationMembership of (x := e2, y := e(e2), T := T1))
    have(e2 ∈ T ==> ∃!(y, (e2, y) ∈ abs(T)(e))) by InstantiateForall(e2)(absApplicationFunctionality)
    have(e(e2) === ε(y, (e2, y) ∈ abs(T1)(e))) by Tautology.from(
      stmt1,
      lastStep of (T := T1),
      existsOneEpsilonUniqueness of (x := y, y := e(e2), P := λ(x, (e2, x) ∈ abs(T1)(e)))
    )
    thenHave(thesis) by Tautology.fromLastStep(
      app.definition of (x := e2, f := abs(T1)(e)),
      equalTransitivityApplication of (x := app(abs(T1)(e))(e2), y := ε(y, (e2, y) ∈ abs(T1)(e)), z := e(e2))
    )
  }

  // app(fun(x, Nat, sqrt(x+x)), 3)
  // app(abs(Nat, λ(x, sqrt(x+x))), 3) === λ(x, sqrt(x+x))(3) ========= sqrt(3+3)
}
