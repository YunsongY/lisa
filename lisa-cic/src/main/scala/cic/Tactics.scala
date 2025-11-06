package cic

import lisa.utils.prooflib.*
import lisa.utils.prooflib.ProofTacticLib.*
import lisa.utils.prooflib.Library
import lisa.utils.fol.{FOL => F}
import scala.collection.Set
import lisa.SetTheoryLibrary
import TypingRules.{TVar, TAbs, TApp, TConv}
import Symbols.*
import lisa.utils.prooflib.BasicStepTactic.TacticSubproof
import lisa.utils.prooflib.SimpleDeducedSteps.Restate
import lisa.utils.prooflib.BasicStepTactic.RightRefl

object Tactics:
  object Typecheck extends ProofTactic:
    // Bidirectional type checking proof construct(infer, check, equal)
    def prove(using proof: SetTheoryLibrary.Proof)(bot: F.Sequent): proof.ProofTacticJudgement =
      if (bot.right.size != 1) return proof.InvalidProofTactic("Typecheck can only prove one theorem once upon a time")
      val premises = bot.left
      val goal = bot.right.head
      goal match
        case typeOf(tm, ty) => checkProof(using SetTheoryLibrary)(premises, tm, ty)
        case _ => proof.InvalidProofTactic("Type check can only check type relation(∈)")

    /**
     * Infer the type of the given term(↑)
     */
    def inferProof(using lib: SetTheoryLibrary.type, proof: lib.Proof)(localContext: Set[Expr[Prop]], tm: Expr[Ind]): proof.ProofTacticJudgement =
      import lib.*
      TacticSubproof {
        tm match
          // e1: Π(x:T1).T2, e2: T1 => e1(e2): T2(e2)
          // Need more check here, pass the wrong result back
          case Sapp(func: Expr[Ind], tm2: Expr[Ind]) =>
            val funcProof = inferProof(using SetTheoryLibrary)(localContext, func)
            if !funcProof.isValid then return proof.InvalidProofTactic(s"Failed to infer the type of the given func($func)")
            val h1 = have(funcProof)
            val funcInferredType = h1.bot.right.head match
              case typeOf(tm, ty) => ty
              case _ => return proof.InvalidProofTactic(s"Failed to extract the inferred type from valid proof")
            funcInferredType match // func's type must be Π-class
              case SPi(ty1: Expr[Ind], ty2: Expr[Ind >>: Ind]) =>
                val typeLevelProof = checkProof(using SetTheoryLibrary)(localContext, tm2, ty1)
                if !typeLevelProof.isValid then return proof.InvalidProofTactic(s"Failed to construct the proof of $tm2 ∈ $ty1")
                val h2 = have(typeLevelProof)
                val (boundVar, typeBody) = ty2 match
                  case Abs(v, body) => (v, body)
                  case _ => return proof.InvalidProofTactic(s"Inferred type T2($ty2) is not a lambda expression")
                val statement = (tm ∈ typeBody.substitute((boundVar, tm2))) ++<< h1.bot ++<< h2.bot
                have(statement) by Tautology.from(h1, h2, TApp of (e1 := func, e2 := tm2, T1 := ty1, T2 := ty2))
              case _ => (None, proof.InvalidProofTactic(s"$funcInferredType must be a Π-type"))

          // ∀(x ∈ T1, e(x) ∈ T2(x)) => abs(T1)(e) ∈ Pi(T1)(T2)
          // Warning: this part may not be correct
          case Sabs(ty: Expr[Ind], Abs(boundVar: Expr[Ind], body: Expr[Ind])) =>
            val newContext = localContext ++ Set(boundVar ∈ ty)
            val bodyProof = inferProof(using SetTheoryLibrary)(newContext, body)
            if !bodyProof.isValid then return proof.InvalidProofTactic(s"Failed to infer the type of the given body($body)")
            val h1 = have(bodyProof)
            val bodyInferredType = h1.bot.right.head match
              case typeOf(tm, ty) => ty
              case _ => return proof.InvalidProofTactic(s"Failed to extract the inferred type from valid proof")
            val resetBot = h1.bot -<< (boundVar ∈ ty)
            have((boundVar ∈ ty |- body ∈ bodyInferredType) ++<< h1.bot) by Weakening(h1)
            thenHave((boundVar ∈ ty ==> body ∈ bodyInferredType) ++<< resetBot) by RightImplies
            thenHave((∀(boundVar ∈ ty, body ∈ bodyInferredType)) ++<< resetBot) by RightForall
            thenHave((tm ∈ Pi(ty)(λ(boundVar, bodyInferredType))) ++<< resetBot) by Tautology.fromLastStep(
              TAbs of (T1 := ty, T2 := Abs(boundVar, bodyInferredType), e := Abs(boundVar, body))
            )

          case _ =>
            val tyOpt: Option[Expr[Ind]] = localContext.collectFirst { case typeOf(t1, t2) if t1 == tm => t2 }
            tyOpt match
              case Some(ty) => have(tm ∈ ty |- tm ∈ ty) by Hypothesis
              case None => return proof.InvalidProofTactic(s"Given $tm does not appear in the context")
      }

    def checkProof(using lib: SetTheoryLibrary.type, proof: lib.Proof)(localContext: Set[Expr[Prop]], tm: Expr[Ind], ty: Expr[Ind]): proof.ProofTacticJudgement =
      import lib.*
      TacticSubproof {
        (tm, ty) match
          // ∀(x ∈ T1, e(x) ∈ T2(x)) => abs(T1)(e) ∈ Pi(T1)(T2)
          case (Sabs(ty1: Expr[Ind], body: Expr[Ind >>: Ind]), SPi(ty1prime: Expr[Ind], ty2: Expr[Ind >>: Ind])) =>
            val (newBoundVariable, replaceVar, body1, body2) = (body, ty2) match
              case (Abs(v1, b1), Abs(v2, b2)) => (v1, v2, b1, b2)
              case _ => return proof.InvalidProofTactic(s"Term and Type must be lambda expressions")
            val typeLevelProof = equalProof(using SetTheoryLibrary)(ty1, ty1prime)
            if typeLevelProof.isValid then
              val newContext = localContext ++ Set(newBoundVariable ∈ ty1)
              val newBody2 = body2.substitute((replaceVar, newBoundVariable)) // replace the originalVar with new bound variable
              val bodyProof = checkProof(using SetTheoryLibrary)(newContext, body1, newBody2)
              if bodyProof.isValid then
                val h1 = lib.have(bodyProof)
                val resetBot = h1.bot -<< (newBoundVariable ∈ ty1)
                have((newBoundVariable ∈ ty1 ==> body1 ∈ newBody2) ++<< resetBot) by Restate.from(h1)
                thenHave((∀(newBoundVariable ∈ ty1, body1 ∈ newBody2)) ++<< resetBot) by RightForall
                thenHave((tm ∈ ty) ++<< resetBot) by Tautology.fromLastStep(
                  TAbs of (T1 := ty1, T2 := ty2, e := body)
                )
              else return proof.InvalidProofTactic(s"Failed to construct body proof")
            else return proof.InvalidProofTactic(s"Failed to construct the equivalence proof between $ty1 and $ty1prime")

          case (Sapp(tm1: Expr[Ind], tm2: Expr[Ind]), _) =>
            val inferredProof = inferProof(using SetTheoryLibrary)(localContext, tm)
            if !inferredProof.isValid then return proof.InvalidProofTactic(s"Failed to construct the inference proof for $tm")
            val h1 = have(inferredProof)
            val inferredType = h1.bot.right.head match
              case typeOf(tm, ty) => ty
              case _ => return proof.InvalidProofTactic(s"Failed to extract the inferred type from valid proof")
            val convProof = equalProof(using SetTheoryLibrary)(inferredType, ty)
            if !convProof.isValid then return proof.InvalidProofTactic(s"Failed to construct the equivalence proof for $inferredType and $ty")
            val h2 = have(convProof)
            val statement = (tm ∈ ty) ++<< h1.bot ++<< h2.bot
            have(statement) by Tautology.from(
              h1,
              h2,
              TConv of (
                e1 := tm,
                T := inferredType,
                T1 := ty
              )
            )

          // e1(e2) ∈ T, T === T' -> e1(e2) ∈ T' or any other single variable
          case _ =>
            val inferredProof = inferProof(using SetTheoryLibrary)(localContext, tm)
            if !inferredProof.isValid then return proof.InvalidProofTactic(s"Failed to construct the inference proof for $tm")
            val h1 = have(inferredProof)
            val inferredType = h1.bot.right.head match
              case typeOf(tm, ty) => ty
              case _ => return proof.InvalidProofTactic(s"Failed to extract the inferred type from valid proof")
            val convProof = equalProof(using SetTheoryLibrary)(inferredType, ty)
            if !convProof.isValid then return proof.InvalidProofTactic(s"Failed to construct the equivalence proof for $inferredType and $ty")
            val h2 = have(convProof)
            val statement = (tm ∈ ty) ++<< h1.bot ++<< h2.bot
            have(statement) by Tautology.from(
              h1,
              h2,
              TConv of (
                e1 := tm,
                T := inferredType,
                T1 := ty
              )
            )
      }

    def equalProof(using lib: SetTheoryLibrary.type, proof: lib.Proof)(ty1: Expr[Ind], ty2: Expr[Ind]): proof.ProofTacticJudgement =
      TacticSubproof {
        // (ty1, ty2) match
        //   case (App(a1: Expr[Ind], a2: Expr[Ind]), App(b1: Expr[Ind], b2: Expr[Ind])) =>
        //     val eq1Proof = equalProof(a1, b1)
        //     val eq2Proof = equalProof(a2, b2)
        //     if eq1Proof.isValid && eq2Proof.isValid then have(ty1 === ty2) by Congruence.from(have(eq1Proof), have(eq2Proof))
        //     else return proof.InvalidProofTactic(s"Failed to construct equivalence proof for Application")
        //   case (Abs(v1: Expr[Ind], b1: Expr[Ind]), Abs(v2: Expr[Ind], b2: Expr[Ind])) =>
        //     have(ty1 === ty2) by RightRefl
        //   case _ =>
        have(ty1 === ty2) by RightRefl
      }

  // object RightRefl extends ProofTactic with ProofSequentTactic:
  //   def withParameters(using lib: Library, proof: lib.Proof)(fa: F.Expr[F.Prop])(bot: F.Sequent): proof.ProofTacticJudgement = {
  //     lazy val faK = fa.underlying
  //     lazy val botK = bot.underlying
  //     if (!botK.right.exists(_ == faK))
  //       proof.InvalidProofTactic("Right-hand side of conclusion does not contain φ.")
  //     else
  //       faK match {
  //         case K.Application(K.Application(K.equality, left), right) =>
  //           if (K.isSame(left, right))
  //             proof.ValidProofTactic(bot, Seq(K.RightRefl(botK, faK)), Seq())
  //           else
  //             proof.InvalidProofTactic("φ is not an instance of reflexivity.")
  //         case _ => proof.InvalidProofTactic("φ is not an equality.")
  //       }
  //   }

  //   def apply(using lib: Library, proof: lib.Proof)(bot: F.Sequent): proof.ProofTacticJudgement = {
  //     if (bot.right.isEmpty) proof.InvalidProofTactic("Right-hand side of conclusion does not contain an instance of reflexivity.")
  //     else {
  //       // go through conclusion to see if you can find an reflexive formula
  //       val pivot: Option[F.Expr[F.Prop]] = bot.right.find(f =>
  //         val Eq = F.equality // (F.equality: (F.|->[F.**[F.Expr[F.Ind], 2], F.Expr[F.Prop]]))
  //         f match {
  //           case F.App(F.App(e, l), r) =>
  //             (F.equality) == (e) && l == r // termequality, here it will call Any's type equal function but not Expr
  //           case _ => false
  //         }
  //       )

  //       pivot match {
  //         case Some(phi) => RightRefl.withParameters(phi)(bot)
  //         case _ => proof.InvalidProofTactic("Could not infer an equality as pivot from conclusion.")
  //       }

  //     }

  //   }
