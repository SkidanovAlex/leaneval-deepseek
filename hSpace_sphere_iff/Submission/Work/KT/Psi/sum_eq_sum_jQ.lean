import Mathlib
import Submission.Work.KT.Psi.QBlkSetup

namespace Work.KT.Psi

/-- A sum over `SQ (Fin n ⊕ Fin m)` of a function supported on the `q`-word is the
corresponding sum over `SQ (Fin m)`. -/
theorem sum_eq_sum_jQ {N : Type} [AddCommMonoid N] {n m : ℕ} (f : SQ (Fin n ⊕ Fin m) → N)
    (h : ∀ z, ¬ isQ z → f z = 0) :
    (∑ z, f z) = ∑ c : SQ (Fin m), f (jQ (n := n) c) := by
  classical
  have hzero : (∑ i : {x : SQ (Fin n ⊕ Fin m) // ¬ isQ x}, f i.val) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact h i.val i.property
  have hsplit := Fintype.sum_subtype_add_sum_subtype (isQ (n := n) (m := m)) f
  rw [hzero, add_zero] at hsplit
  rw [← hsplit]
  refine Fintype.sum_equiv (blkE n m).symm _ _ (fun z => ?_)
  have hz : jQ (n := n) ((blkE n m).symm z) = z.val := by
    rw [← blkE_apply n m, Equiv.apply_symm_apply]
  rw [hz]

end Work.KT.Psi
