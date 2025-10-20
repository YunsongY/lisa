object Refman extends lisa.Main {
  val x = variable[Ind]
  val y = variable[Ind]
  val P = variable[Ind >>: Prop]
  val f = variable[Ind >>: Ind]
  val fixedPointDoubleApplication = Theorem(
    ∀(x, P(x) ==> P(f(x))) |- P(x) ==> P(f(f(x)))
  ) {
    assume(∀(x, P(x) ==> P(f(x))))
    val step1 = have(P(x) ==> P(f(x))) by InstantiateForall
    val step2 = have(P(f(x)) ==> P(f(f(x)))) by InstantiateForall
    have(thesis) by Tautology.from(step1, step2)
  }

  val emptySetIsASubset = Theorem(
    ∅ ⊆ x
  ) {
    have((y ∈ ∅) ==> (y ∈ x)) by Tautology.from(emptySetAxiom of (x := y))
    val rhs = thenHave(∀(y, (y ∈ ∅) ==> (y ∈ x))) by RightForall
    have(thesis) by Tautology.from(subsetAxiom of (x := ∅, y := x), rhs)
  }

  // Tactics:

  // `have(statement) by Restate`, showing statement is equivalent to True
  // `have(statement) by Restate(premise)`, showing statement is equivalent to
  //  the previous statement(premise)

  // `have(statement) by Tautology`, construct a proof of statement
  //  by proving every formula inference that holds in classical propositional logic
  // `have(statement) by Tautology.from(premis1, premise2, ...)`
  //  construct a proof of statement from previously proven
  //  premise1, premise2

  // `RightForall`, generalize a statement by quantifying it over free variables
  // `InstantiateForall`, does the opposite, given a universally quantified
  //  statement, it will specialize it

  // `have(statement by Substituion.ApplyRules(subst*)(premise))`
  //   subst* can be arbitary number of proven facts or formulas,
  //   if proven facts, they must be of the form s === t or A <=> B
  //   or, it should be an assumption in the resulting statement

  // val subst = have(A |- Q(s) <=> P(s)) by ???
  // have(Q(s) /\ s === f(t)) by ???
  // thenHave(A, f(t) === t |- P(s) /\ s === t) by
  //   Substituion.ApplyRules(subst, f(t) === t)

}
