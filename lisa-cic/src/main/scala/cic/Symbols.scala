package cic

import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.Quantifiers.∃!

/**
 * This file defines the most common variable symbols (x, y, z, etc.)
 * and their types for a consitent use through the Calculus of Construction
 */

object Symbols extends lisa.Main {
  // Base term
  val e1, e2 = variable[Ind]

  // Function
  val e = variable[Ind >>: Ind]

  // Base type
  val T, T1 = variable[Set]

  // Dependent type
  val T2 = variable[Ind >>: Set]

  // Proposition
  val Q, R = variable[Ind >>: Prop]

  // x : T <=> x ∈ T
  val typeOf = ∈

  // Type/Term application e1 e2 <=> app(e1)(e2)
  val app: Constant[Set >>: Set >>: Set] = DEF(λ(f, λ(x, ε(y, (x, y) ∈ f))))
    .printAs(args => {
      val func = args(0)
      val arg = args(1)
      s"$func($arg)"
    })

  // Type/Term abstraction λx:T.e <=> abs(T)(λx.e)
  val abs: Constant[Set >>: (Ind >>: Ind) >>: Ind] = DEF(λ(T, λ(e, { (x, e(x)) | x ∈ T })))
    .printAs(args => {
      val typ = args(0)
      val body = args(1)
      s"λ(x: $typ). $body(x)"
    })
  def fun(x: Variable[Ind], typ: Expr[Set], expr: Expr[Ind]) = abs(typ)(λ(x, expr))

  // Dependent productin type: Π(x:T1).T2
  val Pi: Constant[Set >>: (Ind >>: Set) >>: Set] = DEF(
    λ(
      T1,
      λ(
        T2, {
          f ∈ 𝒫(T1 × ⋃({ T2(a) | a ∈ T1 })) |
            // f is a function
            (∀(x ∈ T1, ∃!(y, (x, y) ∈ f))) /\
            // f(a)'s type should be T2(a)
            (∀(a, ∀(b, (a, b) ∈ f ==> (b ∈ T2(a))))) //
        }
      )
    )
  )
}
