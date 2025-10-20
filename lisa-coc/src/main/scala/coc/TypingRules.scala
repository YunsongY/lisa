package coc
import Symbols.*
import lisa.utils.prooflib.BasicStepTactic.Weakening
import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.Quantifiers.∃!

object TypingRules extends lisa.Main {

  /**
   *    x : T ∈ Γ
   *    ───────── (T-Var)
   *    x : T
   */
  val TVar = Theorem(hasType(x)(T) |- hasType(x)(T)) {
    have(thesis) by Tautology
  }

  /**
   *    x : T1 /\ e(x) : T2
   *    ───────────────────── (T-Abs)
   *    abs(T1)(λx.e(x)) : Π(x: T1).e
   */
  val TAbs = Theorem(
    ∀(x, (x ∈ T1) ==> hasType(app(e)(x))(app(T2)(x)))
      |- hasType(abs(T1)(e))(Pi(T1)(T2))
  ) {
    // assume(hasType(x)(T1))
    // assume(hasType(app(e)(x))(app(T2)(x)))
    sorry
  }

  /**
   *    e1 : Π(x: T1).T2, e2 : T1
   *    ────────────────────────── (T-App)
   *    app(e1)(e2): T2(e2)
   */

  val TApp = Theorem(
    (hasType(e1)(Pi(T1)(T2)), hasType(e2)(T1))
      |- hasType(app(e1)(e2))(app(T2)(e2))
  ) {
    assume(hasType(e2)(T1))
    assume(hasType(e1)(Pi(T1)(T2)))
    // have(
    //   e1 ∈ 𝒫(T1 × { app(T2)(a) | a ∈ T1 }) ∧
    //     ∀(x ∈ T1, ∃!(y, (x, y) ∈ e1 /\ y ∈ app(T2)(x)))
    // ) by Tautology.from(Comprehension.membership of (x := e1, y := 𝒫(T1 × { app(T2)(a) | a ∈ T1 }), φ := λ(f, ∀(x ∈ T1, ∃!(y, (x, y) ∈ f /\ y ∈ app(T2)(x))))))
    sorry
  }

}
