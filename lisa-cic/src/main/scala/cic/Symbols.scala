package cic

import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.Quantifiers.∃!

/**
 * This file defines the most common variable symbols (x, y, z, etc.)
 * and their types for a consitent use through the Calculus of Construction
 */

object Symbols extends lisa.Main:
  // Base term
  val e1, e2 = variable[Ind]

  // Function
  val e = variable[Ind >>: Ind]

  // Base type
  val T, T1 = variable[Ind]

  // Dependent type
  val T2 = variable[Ind >>: Ind]

  // Proposition
  val Q, R = variable[Ind >>: Prop]

  // x : T <=> x ∈ T
  val typeOf = ∈

  // Type/Term application e1 e2 <=> app(e1)(e2)
  val app: Constant[Ind >>: Ind >>: Ind] = DEF(λ(f, λ(x, ε(y, (x, y) ∈ f))))
    .printAs(args => {
      val func = args(0)
      val arg = args(1)
      s"($func)($arg)"
    })

  // Pattern extractor for the 'app' Shallow Embedding constant.
  // It allows matching expressions of the form app(func)(arg) using the pattern Sapp(func, arg)
  object Sapp:
    def unapply(e: Expr[?]): Option[(Expr[Ind], Expr[Ind])] =
      e match
        case App(App(`app`, func), arg) =>
          Some((func.asInstanceOf[Expr[Ind]], arg.asInstanceOf[Expr[Ind]]))
        case _ => None

  // Type/Term abstraction λx:T.e <=> abs(T)(λx.e)
  val abs: Constant[Ind >>: (Ind >>: Ind) >>: Ind] = DEF(λ(T, λ(e, { (x, e(x)) | x ∈ T })))
    .printAs(args =>
      val typ = args(0)
      val (v, body) = args(1) match
        case Abs(v, b) => (v, b)
        case _ => (x, args(1))
      s"λ($v: $typ). $body"
    )
  case class typeAssign(x: Variable[Ind], typ: Expr[Ind])
  extension (x: Variable[Ind]) {
    infix def ::(e: Expr[Ind]) = typeAssign(x, e)
  }
  def fun(v: typeAssign, b: Expr[Ind]): Expr[Ind] = abs(v.typ)(λ(v.x, b))

  // Pattern extractor for the 'abs' Shallow Embedding constant.
  // It allows matching expressions of the form abs(typ)(body) using the pattern Sabs(typ, body).
  object Sabs:
    def unapply(e: Expr[?]): Option[(Expr[Ind], Expr[Ind >>: Ind])] =
      e match
        // We match against the specific Constant 'abs' being applied twice: App(App(abs, typ), body)
        case App(App(`abs`, typ), body) =>
          Some((typ.asInstanceOf[Expr[Ind]], body.asInstanceOf[Expr[Ind >>: Ind]]))
        case _ => None

  // Dependent productin type: Π(x:T1).T2
  val Pi: Constant[Ind >>: (Ind >>: Ind) >>: Ind] = DEF(
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
  ).printAs(args =>
    val ty1 = args(0)
    val (v, ty2) = args(1) match
      case Abs(v, body) => (v, body)
      case _ => (x, args(1))
    s"Π($v: $ty1). $ty2"
  )
  def `Π`(v: typeAssign, b: Expr[Ind]): Expr[Ind] = Pi(v.typ)(λ(v.x, b))

  // Pattern extractor for the 'Pi' Shallow Embedding constant.
  // It allows matching expressions of the form Pi(T1)(T2) using the pattern SPi(T1, T2).
  object SPi:
    def unapply(e: Expr[?]): Option[(Expr[Ind], Expr[Ind >>: Ind])] =
      e match
        // We match against the specific Constant 'Pi' being applied twice: App(App(Pi, T1), T2)
        case App(App(`Pi`, t1), t2) =>
          Some((t1.asInstanceOf[Expr[Ind]], t2.asInstanceOf[Expr[Ind >>: Ind]]))
        case _ => None

  /**
   * Notation `A ->: B <=> Π(x :: A). B`
   * where B is independent on x
   */
  extension (a: Expr[Ind]) {
    infix def ->:(b: Expr[Ind]): Expr[Ind] =
      Pi(a)(λ(x, b))
  }
