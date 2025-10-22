package coc
import Symbols.*
import lisa.utils.prooflib.BasicStepTactic.Weakening
import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.Quantifiers.*

object TypingRules extends lisa.Main {

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
    ∀(x ∈ T1, typeOf(app(e)(x))(app(T2)(x)))
      |- typeOf(abs(T1)(e))(Pi(T1)(T2))
  ) {
    assume(∀(x ∈ T1, typeOf(app(e)(x))(app(T2)(x))))
    val premise1 = have(x ∈ T1 ==> typeOf(app(e)(x))(app(T2)(x))) by InstantiateForall

    // Set boundary checking
    have(abs(T1)(e) ⊆ (T1 × ⋃({ app(T2)(a) | a ∈ T1 }))) subproof {
      have(z ∈ abs(T1)(e) |- z ∈ abs(T1)(e)) by Hypothesis
      thenHave(z ∈ abs(T1)(e) |- z ∈ { (x, app(e)(x)) | x ∈ T1 }) by Substitute(abs.definition of (T := T1))
      val stmt1 = thenHave(z ∈ abs(T1)(e) |- ∃(x, x ∈ T1 /\ ((x, app(e)(x)) === z))) by
        Tautology.fromLastStep(Replacement.membership of (y := z, F := λ(x, (x, app(e)(x))), A := T1))
      have(x ∈ T1 ==> (x, app(e)(x)) ∈ (T1 × ⋃({ app(T2)(a) | a ∈ T1 }))) subproof {
        assume(x ∈ T1)
        have(app(T2)(x) ∈ { app(T2)(a) | a ∈ T1 }) by Tautology.from(Replacement.map of (A := T1, F := λ(x, app(T2)(x))))
        have(app(e)(x) ∈ app(T2)(x) /\ app(T2)(x) ∈ { app(T2)(a) | a ∈ T1 }) by Tautology.from(lastStep, premise1)
        thenHave(∃(y, app(e)(x) ∈ y /\ y ∈ { app(T2)(a) | a ∈ T1 })) by RightExists
        have(thesis) by Tautology.from(
          lastStep,
          unionAxiom of (z := app(e)(x), x := { app(T2)(a) | a ∈ T1 }),
          CartesianProduct.membershipSufficientCondition of (y := app(e)(x), A := T1, B := ⋃({ app(T2)(a) | a ∈ T1 }))
        )
      }
      thenHave(∀(x ∈ T1, (x, app(e)(x)) ∈ (T1 × ⋃({ app(T2)(a) | a ∈ T1 })))) by RightForall
      thenHave(z ∈ abs(T1)(e) |- z ∈ (T1 × ⋃({ app(T2)(a) | a ∈ T1 }))) by Tautology.fromLastStep(
        stmt1,
        existPartialApply of (
          P := λ(x, x ∈ T1),
          Q := λ(x, (x, app(e)(x)) ∈ (T1 × ⋃({ app(T2)(a) | a ∈ T1 }))),
          R := λ(x, (x, app(e)(x)) === z)
        ),
        onePointFunctionRule of (P := λ(x, x ∈ (T1 × ⋃({ app(T2)(a) | a ∈ T1 }))), y := z, F := λ(x, (x, app(e)(x))))
      )
      thenHave(z ∈ abs(T1)(e) ==> z ∈ (T1 × ⋃({ app(T2)(a) | a ∈ T1 }))) by Restate
      thenHave(∀(z, z ∈ abs(T1)(e) ==> z ∈ (T1 × ⋃({ app(T2)(a) | a ∈ T1 })))) by RightForall
      thenHave(thesis) by Tautology.fromLastStep(subsetAxiom of (x := abs(T1)(e), y := (T1 × ⋃({ app(T2)(a) | a ∈ T1 }))))
    }
    val boundary_check = thenHave(abs(T1)(e) ∈ 𝒫(T1 × ⋃({ app(T2)(a) | a ∈ T1 }))) by Substitute(powerSetAxiom)

    // Expression e's functionality check
    val functional = have(∀(x ∈ T1, ∃!(y, (x, y) ∈ abs(T1)(e)))) subproof {
      sorry
    }
    sorry
    // val typing_check = have(∀(a, ∀(b, (a, b) ∈ abs(T1)(e) ==> (b ∈ app(T2)(a))))) subproof {
    //   sorry
    // }

    // have(
    //   abs(T1)(e) ∈ 𝒫(T1 × ⋃({ app(T2)(a) | a ∈ T1 })) /\
    //     (∀(x ∈ T1, ∃!(y, (x, y) ∈ abs(T1)(e)))) /\
    //     (∀(a, ∀(b, (a, b) ∈ abs(T1)(e) ==> (b ∈ app(T2)(a)))))
    // ) by Tautology.from(boundary_check, functional, typing_check)
    // thenHave(abs(T1)(e) ∈ {
    //   f ∈ 𝒫(T1 × ⋃({ app(T2)(a) | a ∈ T1 })) |
    //     (∀(x ∈ T1, ∃!(y, (x, y) ∈ f))) /\ (∀(a, ∀(b, (a, b) ∈ f ==> (b ∈ app(T2)(a)))))
    // }) by Substitute(Pi_expansion of (e1 := abs(T1)(e)))
    // thenHave(thesis) by Substitute(Pi.definition)
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
    ) by Tautology.from(Pi_expansion, lastStep)

    have(∀(x ∈ T1, ∃!(y, (x, y) ∈ e1))) by Weakening(stmt)
    thenHave(x ∈ T1 ==> ∃!(y, (x, y) ∈ e1)) by InstantiateForall(x)
    have(∃!(y, (e2, y) ∈ e1)) by Tautology.from(lastStep of (x := e2))
    have((e2, ε(y, (e2, y) ∈ e1)) ∈ e1) by Tautology.from(lastStep, existsOneEpsilon of (P := λ(x, (e2, x) ∈ e1)))
    val stmt1 = thenHave((e2, app(e1)(e2)) ∈ e1) by Substitute(app.definition of (f := e1, x := e2))

    have((∀(a, ∀(b, (a, b) ∈ e1 ==> (b ∈ app(T2)(a)))))) by Weakening(stmt)
    thenHave((e2, app(e1)(e2)) ∈ e1 ==> app(e1)(e2) ∈ app(T2)(e2)) by InstantiateForall(e2, app(e1)(e2))
    have(thesis) by Tautology.from(lastStep, stmt1)
  }
}
