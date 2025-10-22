package coc
import Symbols.*
import lisa.utils.prooflib.BasicStepTactic.Weakening
import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.Quantifiers.*
import java.time.Instant
import lisa.utils.prooflib.SimpleDeducedSteps.InstantiateForall

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
    // thenHave(x ∈ T1 ==> typeOf(app(e)(x)))
    sorry
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
    val premise1 = have(
      e1 ∈ {
        f ∈ 𝒫(T1 × ⋃({ app(T2)(a) | a ∈ T1 })) |
          (∀(x ∈ T1, ∃!(y, (x, y) ∈ f))) /\ (∀(a, ∀(b, (a, b) ∈ f ==> (b ∈ app(T2)(a)))))
      } <=> e1 ∈ 𝒫(T1 × ⋃({ app(T2)(a) | a ∈ T1 })) /\
        (∀(x ∈ T1, ∃!(y, (x, y) ∈ e1))) /\ (∀(a, ∀(b, (a, b) ∈ e1 ==> (b ∈ app(T2)(a)))))
    ) by Comprehension.apply
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
    ) by Tautology.from(premise1, lastStep)

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
