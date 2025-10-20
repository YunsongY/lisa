// seem all first order logic can be proved by
// have(thesis) by Tautology

object Level0 extends lisa.Main:
  val P = variable[Prop]
  val Q = variable[Prop]
  val R = variable[Prop]

  // 1. Identity
  val prop_id = Theorem(
    P |- P
  ) {
    have(thesis) by Hypothesis
  }

  // 2. Constant function
  val prop_const = Theorem(
    (P, Q) |- P
  ) {
    have(thesis) by Hypothesis
  }

  // 3. Function composition
  val prop_compose = Theorem(
    (P ==> Q, Q ==> R) |- P ==> R
  ) {
    val hypPQ = have((P ==> Q, Q ==> R) |- P ==> Q) by Hypothesis
    val hypQR = have((P ==> Q, Q ==> R) |- Q ==> R) by Hypothesis
    val withP = have((P, P ==> Q, Q ==> R) |- P) by Hypothesis
    val getQ  = have((P, P ==> Q, Q ==> R) |- Q) by Tautology.from(withP, hypPQ)
    val getR  = have((P, P ==> Q, Q ==> R) |- R) by Tautology.from(getQ, hypQR)
    have(thesis) by Tautology.from(getR)
  }

  // 4. Modus_ponens
  val modus_ponens = Theorem(
    (P, P ==> Q) |- Q
  ) {
    val hypP  = have((P, P ==> Q) |- P) by Hypothesis
    val hypPQ = have((P, P ==> Q) |- P ==> Q) by Hypothesis
    have(thesis) by Tautology.from(hypP, hypPQ)
  }

  // 5. Conjunction introduction
  val and_intro = Theorem(
    (P, Q) |- P /\ Q
  ) {
    val hypP = have((P, Q) |- P) by Hypothesis
    val hypQ = have((P, Q) |- Q) by Hypothesis
    have(thesis) by Tautology.from(hypP, hypQ)
  }

  // 6. Conjunction left projection
  val and_left = Theorem(
    P /\ Q |- P
  ) {
    have(thesis) by Tautology
  }

  // 7. Conjucntion right projection
  val and_right = Theorem(
    P /\ Q |- Q
  ) {
    have(thesis) by Tautology
  }

  // 8. Conjunction commutativity
  val and_commut = Theorem(
    P /\ Q |- Q /\ P
  ) {
    have(thesis) by Tautology
  }

  // 9. Conjunction associativity
  val and_associate = Theorem(
    (P /\ Q) /\ R |- P /\ (Q /\ R)
  ) {
    have(thesis) by Tautology
  }

  // 10. Disjunction left introduction
  val or_inl = Theorem(
    P |- P \/ Q
  ) {
    have(thesis) by Tautology
  }

  // 11. Disjunction right introduction
  val or_inr = Theorem(
    Q |- P \/ Q
  ) {
    have(thesis) by Tautology
  }

  // 12. Disjunction commutativity
  val or_commut = Theorem(
    P \/ Q |- Q \/ P
  ) {
    have(thesis) by Tautology
  }

  // 13. Disjunction elimination
  val or_elim_to_impl = Theorem(
    (P \/ Q, P ==> R, Q ==> R) |- R
  ) {
    have(thesis) by Tautology
  }

  // 14. Implication transitivity (same as prop_compose)
  val impl_trans = Theorem(
    (P ==> Q, Q ==> R) |- P ==> R
  ) {
    have(thesis) by Tautology
  }

  // 15. Currying
  val curry = Theorem(
    ((P /\ Q) ==> R) |- P ==> (Q ==> R)
  ) {
    have(thesis) by Tautology
  }

  // 16. Uncurrying
  val uncurry = Theorem(
    (P ==> (Q ==> R)) |- (P /\ Q) ==> R
  ) {
    have(thesis) by Tautology
  }

  // 17. Distributivity (∧ over ∨)
  val and_or_distrib = Theorem(
    P /\ (Q \/ R) |- (P /\ Q) \/ (P /\ R)
  ) {
    have(thesis) by Tautology
  }

  // 18. Double negation introduction
  val double_neg_intro = Theorem(
    P |- ¬(¬(P))
  ) {
    have(thesis) by Tautology
  }

  // 19. Ex falso quodlibet
  val ex_falso = Theorem(
    () |- ⊥ ==> P
  ) {
    have(thesis) by Tautology
  }

  // 20. Implication from disjunction
  val or_implies = Theorem(
    (P \/ Q, ¬(P)) |- Q
  ) {
    have(thesis) by Tautology
  }
