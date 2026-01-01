package cic

import lisa.utils.prooflib.*
import lisa.utils.prooflib.ProofTacticLib.*
import lisa.utils.prooflib.Library
import lisa.utils.fol.{FOL => F}
import scala.collection.Set
import lisa.SetTheoryLibrary
import TypingRules.{TVar, TAbs, TApp, TConv, TForm, TSort, TConvAdv}
import lisa.maths.SetTheory.Base.Predef.∪
import lisa.maths.SetTheory.Base.Subset.{reflexivity, transitivity, doubleInclusion}
import lisa.maths.SetTheory.Base.Union.{commutativity, leftUnionSubset}
import lisa.maths.SetTheory.Cardinal.Predef.{isUniverse, universeOf, universeOfIsUniverse}
import Symbols.*
import Helper.{unionAbsorbVariant, subsetOfUniverse, unionEqual}

object Tactics:
  val x, y, z, A, B, C = variable[Ind]
  object Typecheck extends ProofTactic:
    // Helper function: get universe level
    def getDepth(e: Expr[Ind]): Int = e match
      case App(universeOf, inner: Expr[Ind]) => 1 + getDepth(inner)
      case _ => 1

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
            val stmt = have(innerProof)
            val (toEliminate, toKeep) = stmt.bot.left.partition {
              case App(cmd, App(tag, t2)) =>
                cmd == isUniverse && tag == universeOf
              case _ => false
            }
            val lemmaFacts = toEliminate.map { univFact =>
              univFact match
                case App(cmd, App(tag, v: Expr[Ind])) => universeOfIsUniverse of (x := v)
                case _ => throw new Exception("Unreachable code: structure validation failed")
            }.toSeq
            val allFacts = Seq(stmt) ++ lemmaFacts
            have(stmt.bot.removeAllLeft(toEliminate)) by Tautology.from(allFacts*)
            thenHave(premises |- tm ∈ ty) by Weakening
          case _ => return proof.InvalidProofTactic("Type check can only check type relation(∈)")
      }

    /**
     * Infer the type of the given term(↑)
     */
    def inferProof(using lib: SetTheoryLibrary.type, proof: lib.Proof)(localContext: Set[Expr[Prop]], tm: Expr[Ind]): proof.ProofTacticJudgement =
      import lib.*
      // println("Infer term:" + tm.toString())
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
            if !bodyProof.isValid then return proof.InvalidProofTactic(s"Sabs: Failed to infer the type of the given body($body)")
            val h1 = have(bodyProof)
            val bodyInferredType = h1.bot.right.head match
              case typeOf(tm, ty) => ty
              case _ => return proof.InvalidProofTactic(s"Sabs: Failed to extract the inferred type from valid proof")
            val resetBot = h1.bot -<< (boundVar ∈ ty)
            have((boundVar ∈ ty |- body ∈ bodyInferredType) ++<< h1.bot) by Weakening(h1)
            thenHave((boundVar ∈ ty ==> body ∈ bodyInferredType) ++<< resetBot) by RightImplies
            thenHave((∀(boundVar ∈ ty, body ∈ bodyInferredType)) ++<< resetBot) by RightForall
            thenHave((tm ∈ Pi(ty)(λ(boundVar, bodyInferredType))) ++<< resetBot) by Tautology.fromLastStep(
              TAbs of (T1 := ty, T2 := Abs(boundVar, bodyInferredType), e := Abs(boundVar, body))
            )

          // Π(x: T1).T2 : U, Check if U == U1 ∪ U2
          case SPi(ty: Expr[Ind], Abs(boundVar: Expr[Ind], body: Expr[Ind])) =>
            val newContext = localContext ++ Set(boundVar ∈ ty)
            val bodyProof = inferProof(using SetTheoryLibrary)(newContext, body)
            if !bodyProof.isValid then return return proof.InvalidProofTactic(s"SPi: Failed to infer the type of the given body($body)")
            val h1 = have(bodyProof)
            val bodyInferredType = h1.bot.right.head match
              case typeOf(tm, ty) => ty
              case _ => return proof.InvalidProofTactic(s"SPi: Failed to extract the inferred type from valid proof")
            val contextUnivOpt = localContext.collectFirst {
              case typeOf(subj, univ) if subj == ty => univ
            }
            val resetBot = h1.bot -<< (boundVar ∈ ty)
            have((boundVar ∈ ty |- body ∈ bodyInferredType) ++<< h1.bot) by Weakening(h1)
            thenHave((boundVar ∈ ty ==> body ∈ bodyInferredType) ++<< resetBot) by RightImplies
            thenHave((∀(boundVar ∈ ty, body ∈ bodyInferredType)) ++<< resetBot) by RightForall
            contextUnivOpt match
              case Some(u1) =>
                val finalProof = thenHave(((isUniverse(u1), isUniverse(bodyInferredType), ty ∈ u1) |- tm ∈ (u1 ∪ bodyInferredType)) ++<< resetBot) by Tautology.fromLastStep(
                  TForm of (T1 := ty, T2 := Abs(boundVar, body), U1 := u1, U2 := bodyInferredType)
                )
                val realUniv = getUniverse(math.max(getDepth(u1), getDepth(bodyInferredType)))
                val equivProof = equalProof(using SetTheoryLibrary)((u1 ∪ bodyInferredType), realUniv)
                if !equivProof.isValid then return proof.InvalidProofTactic(s"Hierarchy collapse failed: $u1 ∪ $bodyInferredType !== $realUniv")
                have(((isUniverse(u1), isUniverse(bodyInferredType), ty ∈ u1) |- tm ∈ realUniv) ++<< resetBot) by Substitute(have(equivProof))(finalProof)
              case _ =>
                val finalProof = thenHave((isUniverse(bodyInferredType) |- tm ∈ (universeOf(ty) ∪ bodyInferredType)) ++<< resetBot) by Tautology.fromLastStep(
                  TForm of (T1 := ty, T2 := Abs(boundVar, body), U1 := universeOf(ty), U2 := bodyInferredType),
                  universeOfIsUniverse of (x := ty)
                )
                val realUniv = getUniverse(math.max(getDepth(ty) + 1, getDepth(bodyInferredType)))
                val equivProof = equalProof(using SetTheoryLibrary)((universeOf(ty) ∪ bodyInferredType), realUniv)
                if !equivProof.isValid then return proof.InvalidProofTactic(s"Hierarchy collapse failed: ${universeOf(ty)} ∪ $bodyInferredType !== $realUniv")
                have((isUniverse(bodyInferredType) |- tm ∈ realUniv) ++<< resetBot) by Substitute(have(equivProof))(finalProof)

          case _ =>
            val tyOpt: Option[Expr[Ind]] = localContext.collectFirst { case typeOf(t1, t2) if t1 == tm => t2 }
            tyOpt match
              case Some(ty) => have(tm ∈ ty |- tm ∈ ty) by Hypothesis
              case None => have(tm ∈ universeOf(tm)) by Tautology.from(TSort of (U := tm))
      }

    /**
     * Check the type of the given term(↓)
     */
    def checkProof(using lib: SetTheoryLibrary.type, proof: lib.Proof)(localContext: Set[Expr[Prop]], tm: Expr[Ind], ty: Expr[Ind]): proof.ProofTacticJudgement =
      import lib.*
      // println("Check term's type: " + tm.toString() + " ∈ " + ty.toString())
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
            val convProof = subsetProof(using SetTheoryLibrary)(inferredType, ty)
            if !convProof.isValid then return proof.InvalidProofTactic(s"Failed to construct the equivalence proof for $inferredType and $ty")
            val h2 = have(convProof)
            val statement = (tm ∈ ty) ++<< h1.bot ++<< h2.bot
            have(statement) by Tautology.from(
              h1,
              h2,
              TConvAdv of (
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
            val convProof = subsetProof(using SetTheoryLibrary)(inferredType, ty)
            if !convProof.isValid then return proof.InvalidProofTactic(s"Failed to construct the equivalence proof for $inferredType and $ty")
            val h2 = have(convProof)
            val statement = (tm ∈ ty) ++<< h1.bot ++<< h2.bot
            have(statement) by Tautology.from(
              h1,
              h2,
              TConvAdv of (
                e1 := tm,
                T := inferredType,
                T1 := ty
              )
            )
      }

    def eqOrSubset(e: Expr[Prop]): Boolean = e match
      case App(App(`⊆`, t1: Expr[Ind]), t2: Expr[Ind]) => false
      case _ => true

    def reduceTree(using lib: SetTheoryLibrary.type, proof: lib.Proof)(e: Expr[Ind], typ: Expr[Ind]): proof.ProofTacticJudgement =
      // println(e.toString() + " comparing to " + typ.toString())
      TacticSubproof {
        e match
          case SUnion(t1, t2) =>
            val j1 = reduceTree(using SetTheoryLibrary)(t1, typ)
            val j2 = reduceTree(using SetTheoryLibrary)(t2, typ)
            if !j1.isValid then return proof.InvalidProofTactic(s"Left branch failed: $t1")
            if !j2.isValid then return proof.InvalidProofTactic(s"Right branch failed: $t2")
            val s1 = have(j1)
            val s2 = have(j2)
            (eqOrSubset(s1.bot.right.head), eqOrSubset(s2.bot.right.head)) match
              case (true, true) =>
                have((t1 ∪ t2) === typ) by Tautology.from(s1, s2, unionEqual of (A := t1, B := t2, C := typ))
              case (false, true) =>
                have((t1 ∪ t2) === typ) by Tautology.from(s1, s2, unionAbsorbVariant of (A := t1, B := t2, C := typ))
              case (true, false) =>
                println(s1.bot.right)
                println(s2.bot.right)
                val eq = have((t2 ∪ t1) === (t1 ∪ t2)) by Tautology.from(commutativity of (x := t2, y := t1))
                have((t2 ∪ t1) === typ) by Tautology.from(s1, s2, unionAbsorbVariant of (A := t2, B := t1, C := typ))
                thenHave((t1 ∪ t2) === typ) by Substitute(eq)
              case (false, false) =>
                have((t1 ∪ t2) ⊆ typ) by Tautology.from(s1, s2, leftUnionSubset of (x := t1, y := t2, z := typ))
          case _ =>
            if e == typ then have(e === typ) by RightRefl.withParameters(e === typ)
            else have(subsetProof(using SetTheoryLibrary)(e, typ))
      }

    // Construct equivalence proof for the given two expressions
    def equalProof(using lib: SetTheoryLibrary.type, proof: lib.Proof)(ty1: Expr[Ind], ty2: Expr[Ind]): proof.ProofTacticJudgement =
      println("Equal proof: " + ty1.toString() + " === " + ty2.toString())
      TacticSubproof {
        ty1 match
          case SUnion(t1, t2) =>
            val finalProof = reduceTree(using SetTheoryLibrary)(ty1, ty2)
            if !finalProof.isValid then proof.InvalidProofTactic(s"Failed to reduce union tree $ty1")
            else have(finalProof)
          case _ =>
            have(ty1 === ty2) by RightRefl.withParameters(ty1 === ty2)
      }

    // Construct subset proof(ty1 ⊆ ty2) for the given two expressions
    def subsetProof(using lib: SetTheoryLibrary.type, proof: lib.Proof)(sub: Expr[Ind], sup: Expr[Ind]): proof.ProofTacticJudgement =
      // println("Trying to construct subsetProof for: " + sub.toString() + " ⊆ " + sup.toString())
      TacticSubproof {
        sub match
          case SUnion(t1, t2) =>
            have(equalProof(using SetTheoryLibrary)(sub, sup))
            thenHave(sub ⊆ sup) by Tautology.fromLastStep(doubleInclusion of (x := sub, y := sup))
          case _ =>
            val dSub = getDepth(sub)
            val dSup = getDepth(sup)
            if (dSub > dSup) then proof.InvalidProofTactic(s"Depth mismatch: $sub (d=$dSub) cannot be subset of $sup (d=$dSup)")
            else if (dSub == dSup) then
              if (sub == sup) then have(sub ⊆ sup) by Tautology.from(reflexivity of (x := sub))
              else
                have(sub === sup) by RightRefl.withParameters(sub === sup)
                thenHave(sub ⊆ sup) by Tautology.fromLastStep(doubleInclusion of (x := sub, y := sup))
            else if (dSub == dSup - 1) then have(sub ⊆ universeOf(sub)) by Tautology.from(subsetOfUniverse of (A := sub))
            else
              val step1 = have(sub ⊆ universeOf(sub)) by Tautology.from(subsetOfUniverse of (A := sub))
              val step2Proof = subsetProof(using SetTheoryLibrary)(universeOf(sub), sup)
              if !step2Proof.isValid then return proof.InvalidProofTactic(s"Further subset proof failed: ${universeOf(sub)} and $sup")
              val step2 = have(step2Proof)
              val test = have(sub ⊆ sup) by Tautology.from(
                step1,
                step2,
                transitivity of (x := sub, y := universeOf(sub), z := sup)
              )
      }
