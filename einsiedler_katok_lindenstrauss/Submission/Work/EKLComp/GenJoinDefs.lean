import Mathlib
import Submission.Work.EKLContract.Defs

/-!
# The binary join of two finite partitions (universe-polymorphic)

`joinTwo P Q` is the common refinement of two finite measurable partitions, indexed by
`Fin (P.n * Q.n)` through `finProdFinEquiv`.
-/

open MeasureTheory
open Work.EKLContract

noncomputable section

namespace Work.EKLComp

variable {X : Type*} [mX : MeasurableSpace X]

/-- The common refinement (join) of two finite partitions. -/
def joinTwo (P Q : FinPart X) : FinPart X where
  n := P.n * Q.n
  parts := fun k => P.parts (finProdFinEquiv.symm k).1 ∩ Q.parts (finProdFinEquiv.symm k).2
  measurable := fun k => (P.measurable _).inter (Q.measurable _)
  disjoint := by
    rw [Pairwise]
    intro k l hkl
    rw [Set.disjoint_left]
    intro x hx1 hx2
    rw [Set.mem_inter_iff] at hx1 hx2
    by_cases h1 : (finProdFinEquiv.symm k).1 = (finProdFinEquiv.symm l).1
    · have h2 : (finProdFinEquiv.symm k).2 ≠ (finProdFinEquiv.symm l).2 := by
        intro h2
        refine hkl ?_
        have hp : finProdFinEquiv.symm k = finProdFinEquiv.symm l := Prod.ext h1 h2
        rw [← Equiv.apply_symm_apply finProdFinEquiv k,
          ← Equiv.apply_symm_apply finProdFinEquiv l, hp]
      exact (Q.disjoint h2).le_bot ⟨hx1.2, hx2.2⟩
    · exact (P.disjoint h1).le_bot ⟨hx1.1, hx2.1⟩
  cover := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hxP : x ∈ ⋃ i, P.parts i := by rw [P.cover]; exact trivial
    have hxQ : x ∈ ⋃ j, Q.parts j := by rw [Q.cover]; exact trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxP
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxQ
    refine Set.mem_iUnion.mpr ⟨finProdFinEquiv (i, j), ?_⟩
    have hk : finProdFinEquiv.symm (finProdFinEquiv (i, j)) = (i, j) :=
      Equiv.symm_apply_apply _ _
    rw [hk]
    exact ⟨hi, hj⟩

@[simp] theorem joinTwo_n (P Q : FinPart X) : (joinTwo P Q).n = P.n * Q.n := rfl

/-- The atoms of `joinTwo P Q`, in the canonical index form. -/
theorem joinTwo_parts_symm (P Q : FinPart X) (k : Fin (P.n * Q.n)) :
    (joinTwo P Q).parts k
      = P.parts (finProdFinEquiv.symm k).1 ∩ Q.parts (finProdFinEquiv.symm k).2 := rfl

/-- The atoms of `joinTwo P Q`. -/
theorem joinTwo_parts (P Q : FinPart X) (i : Fin P.n) (j : Fin Q.n) :
    (joinTwo P Q).parts (finProdFinEquiv (i, j)) = P.parts i ∩ Q.parts j := by
  rw [joinTwo_parts_symm, Equiv.symm_apply_apply]

end Work.EKLComp
