package coc

import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.Quantifiers.∃!
import lisa.utils.prooflib.BasicStepTactic.LeftForall

/**
 * This file defines the most common variable symbols (x, y, z, etc.)
 * and their types for a consitent use through the Calculus of Construction
 */

object Symbols extends lisa.Main {
  // Base term
  val e, e1, e2 = variable[Ind]

  // Base type
  val T, T1, T2 = variable[Set]

  val Q, R = variable[Ind >>: Prop]

  // x : T <=> x ∈ T
  val typeOf = ∈

  // Type/Term application e1 e2 <=> app(e1)(e2)
  val app = DEF(λ(f, λ(x, ε(y, (x, y) ∈ f))))
    .printAs(args => {
      val func = args(0)
      val arg = args(1)
      s"$func($arg)"
    })

  // Type/Term abstraction λx:T.e <=> abs(T)(λx.e)
  val abs = DEF(λ(T, λ(e, { (x, app(e)(x)) | x ∈ T }))).printAs(args => {
    val typ = args(0)
    val body = args(1)
    s"λ(x: $typ). $body(x)"
  })

  // Dependent productin type: Π(x:T1).T2
  val Pi = DEF(
    λ(
      T1,
      λ(
        T2, {
          f ∈ 𝒫(T1 × ⋃({ app(T2)(a) | a ∈ T1 })) |
            // f is a function
            (∀(x ∈ T1, ∃!(y, (x, y) ∈ f))) /\
            // f(a)'s type should be T2(a)
            (∀(a, ∀(b, (a, b) ∈ f ==> (b ∈ app(T2)(a))))) //
        }
      )
    )
  )

  val Pi_expansion = Theorem(
    e1 ∈ {
      f ∈ 𝒫(T1 × ⋃({ app(T2)(a) | a ∈ T1 })) |
        (∀(x ∈ T1, ∃!(y, (x, y) ∈ f))) /\ (∀(a, ∀(b, (a, b) ∈ f ==> (b ∈ app(T2)(a)))))
    } <=> e1 ∈ 𝒫(T1 × ⋃({ app(T2)(a) | a ∈ T1 })) /\
      (∀(x ∈ T1, ∃!(y, (x, y) ∈ e1))) /\ (∀(a, ∀(b, (a, b) ∈ e1 ==> (b ∈ app(T2)(a)))))
  ) {
    have(thesis) by Comprehension.apply
  }

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

  val onePointFunctionRule = Theorem(
    ∃(x, P(F(x)) /\ (y === F(x))) ==> P(y)
  ) {
    have((P(F(x)), y === F(x)) |- P(y)) by Congruence
    thenHave(P(F(x)) /\ (y === F(x)) |- P(y)) by Restate
    thenHave(∃(x, P(F(x)) /\ (y === F(x))) |- P(y)) by LeftExists
    thenHave(thesis) by Restate
  }
}
