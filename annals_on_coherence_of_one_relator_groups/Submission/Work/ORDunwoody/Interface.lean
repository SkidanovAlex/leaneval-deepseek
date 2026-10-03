/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The N12 inputs, discharged

`Hypotheses.lean` names the inputs of JL §4 that belong to the neighbouring nodes.  This file
collects the *theorems* that discharge them, so that a caller can replace a named hypothesis by
an unconditional theorem.  Nothing here is an axiom: every statement is proved downstream of
`Hypotheses.lean`.

* `freeOnTreeIsFree_free` — the `free` conjunct of `FreeOnTreeIsFree`, proved by node N12 in
  `Submission.Work.ORBassSerre.Assembly.freeOnTreeIsFree_of_noInversions`.
* `bassSerreFinitelyPresentedAll_holds` — `BassSerreFinitelyPresentedAll`, proved by node N12 in
  `Submission.Work.ORBassSerre.Assembly.bassSerreFinitelyPresentedAll`.
* `quotientTreeByNormalClosureOfElliptic_holds` — `QuotientTreeByNormalClosureOfElliptic`
  (Serre §5, with the `lift`/`fibre`/`stab` clauses), the corrected statement of node N12,
  extended with the two extra clauses needed by the descent step.
* `freeOnTreeIsFree_quotient` — the `quotient` conjunct of `FreeOnTreeIsFree`.
-/
import Submission.Work.ORDunwoody.Hypotheses
import Submission.Work.ORDunwoody.freeOnTreeIsFree_quotient
import Submission.Work.ORDunwoody.serreQuotientTree_strengthened
import Submission.Work.ORDunwoody.partialSubdivision
import Submission.Work.ORBassSerre.Assembly.freeOnTreeIsFree_of_noInversions
import Submission.Work.ORBassSerre.Assembly.bassSerreFinitelyPresentedAll

set_option autoImplicit false

set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody

/-- The `free` conjunct of `FreeOnTreeIsFree`, discharged by node N12. -/
theorem freeOnTreeIsFree_free (Y : Type u) :
    (∀ (G : Type u) [Group G] {V : Type u} [MulAction G V] (S : GTree G V),
      (∀ v : V, S.vertexStab v = ⊥) →
      (∀ (g : G) ⦃u v : V⦄, S.Adj u v → g • u = v → g • v = u → g = 1) →
      ∃ (α : Type u), Nonempty (G ≃* FreeGroup α)) :=
  Work.ORBassSerre.Assembly.freeOnTreeIsFree_of_noInversions Y

/-- The `quotient` conjunct of `FreeOnTreeIsFree`, discharged: if `G` acts on a tree without
inversions and `K` is the normal closure of the vertex stabilizers, then `G ⧸ K` is free
(Bass–Serre). -/
theorem freeOnTreeIsFree_quotient_holds (Y : Type u) :
    (∀ (G : Type u) [Group G] {V : Type u} [MulAction G V] (S : GTree G V)
      (K : Subgroup G) [K.Normal],
      (∀ (g : G) ⦃u v : V⦄, S.Adj u v → g • u = v → g • v = u → g = 1) →
      (K = Subgroup.normalClosure (⋃ v : V, (S.vertexStab v : Set G))) →
      ∃ (α : Type u), Nonempty ((G ⧸ K) ≃* FreeGroup α)) :=
  Work.ORDunwoody.freeOnTreeIsFree_quotient Y

/-- **`FreeOnTreeIsFree`, discharged unconditionally**: both freeness criteria of node N12. -/
theorem freeOnTreeIsFree_holds (Y : Type u) : FreeOnTreeIsFree Y :=
  ⟨freeOnTreeIsFree_free Y, freeOnTreeIsFree_quotient_holds Y⟩

/-- `BassSerreFinitelyPresentedAll`, discharged by node N12. -/
theorem bassSerreFinitelyPresentedAll_holds (X : Type u) :
    BassSerreFinitelyPresentedAll X :=
  Work.ORBassSerre.Assembly.bassSerreFinitelyPresentedAll X

/-- **`SerreQuotientTree`, discharged**: Serre, *Trees*, §5, in the strengthened form needed by
the descent step (with the `lift` and `fibre` clauses). -/
theorem serreQuotientTree_holds (Y : Type u) : SerreQuotientTree Y :=
  Work.ORDunwoody.serreQuotientTree_strengthened Y

/-- **`PartialSubdivision`, discharged**: the partial subdivision of a tree along an invariant
set of edges is a tree, with the stated adjacencies, action and stabilizers. -/
theorem partialSubdivision_holds (Y : Type u) : PartialSubdivision Y :=
  Work.ORDunwoody.partialSubdivision Y

/-- **`QuotientTreeByNormalClosureOfElliptic`, discharged unconditionally**: the two tree
constructions of the descent step. -/
theorem quotientTreeByNormalClosureOfElliptic_holds (Y : Type u) :
    QuotientTreeByNormalClosureOfElliptic Y :=
  ⟨serreQuotientTree_holds Y, partialSubdivision_holds Y⟩

end Work.ORDunwoody
