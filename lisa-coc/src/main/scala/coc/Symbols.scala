package coc

import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.Quantifiers.∃!

/**
 * This file defines the most common variable symbols (x, y, z, etc.)
 * and their types for a consitent use through the Calculus of Construction
 */

object Symbols extends lisa.Main {
  // Base term
  val e, e1, e2 = variable[Ind]

  // Base type
  val T, T1, T2 = variable[Set]

  // x : T <=> x ∈ T
  val hasType = DEF(λ(x, λ(T, x ∈ T)))

  // Type/Term application e1 e2 <=> app(e1)(e2)
  val app = DEF(λ(f, λ(x, ε(y, (x, y) ∈ f)))).printAs(args => {
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
          f ∈ 𝒫(T1 × { app(T2)(a) | a ∈ T1 }) |
            (∀(x ∈ T1, ∃!(y, (x, y) ∈ f /\ y ∈ app(T2)(x))))
        }
      )
    )
  )
}
