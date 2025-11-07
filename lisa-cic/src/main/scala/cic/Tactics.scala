package cic

import lisa.utils.prooflib.*
import lisa.utils.prooflib.ProofTacticLib.*
import lisa.utils.prooflib.Library
import lisa.utils.fol.{FOL => F}
import scala.collection.Set
import lisa.SetTheoryLibrary
import TypingRules.{TVar, TAbs, TApp, TConv}
import Symbols.*

object Tactics:
  object Typecheck extends ProofTactic:
    // Bidirectional type checking proof construct(infer, check, equal)
    def prove(using lib: SetTheoryLibrary.type, proof: lib.Proof)(bot: F.Sequent): proof.ProofTacticJudgement =
      import lib.*
      if (bot.right.size != 1) return proof.InvalidProofTactic("Typecheck can only prove one theorem once upon a time")
      val premises = bot.left
      val goal = bot.right.head
      TacticSubproof {
        goal match
          case typeOf(tm, ty) =>
            val innerProof = checkProof(using SetTheoryLibrary)(premises, tm, ty)
            have(premises |- tm ∈ ty) by Weakening(have(innerProof))
          case _ => return proof.InvalidProofTactic("Type check can only check type relation(∈)")
      }

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

    /**
     * Check the type of the given term(↓)
     */
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
                have((newBoundVariable ∈ ty1 |- body1 ∈ newBody2) ++<< h1.bot) by Weakening(h1)
                thenHave((newBoundVariable ∈ ty1 ==> body1 ∈ newBody2) ++<< resetBot) by RightImplies
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

    // Construct equivalence proof for the given two expressions
    def equalProof(using lib: SetTheoryLibrary.type, proof: lib.Proof)(ty1: Expr[Ind], ty2: Expr[Ind]): proof.ProofTacticJudgement =
      TacticSubproof {
        have(ty1 === ty2) by RightRefl.withParameters(ty1 === ty2)
      }
