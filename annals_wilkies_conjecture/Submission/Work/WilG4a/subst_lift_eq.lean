import Mathlib
import Submission.Work.WilG0.Defs
import Submission.Work.WilG0.snocIt_natAdd
import Submission.Work.WilG0.snocIt_castAdd
import Submission.Work.WilG0.projLastIter_eq

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4a

open Work.WilG0

/-- The set of `x : ℝ^n` with `x ∘ ι ∈ A` is obtained by putting a fresh block `w : Fin m → ℝ`
at the end, requiring `w ∈ A` (`liftNM`) and `w = x ∘ ι` (`diagSet`), and then projecting the
fresh block away (`projLastIter`).  This is the set-theoretic content of the substitution atom. -/
theorem subst_lift_eq {m n : ℕ} (ι : Fin m → Fin n) (A : Set (Fin m → ℝ)) :
    {x : Fin n → ℝ | x ∘ ι ∈ A} = Work.WilG0.projLastIter n m (Work.WilG0.liftNM n m A ∩ Work.WilG0.diagSet n m ι) := by
  rw [Work.WilG0.projLastIter_eq]
  ext x
  simp only [Work.WilG0.liftNM, Work.WilG0.diagSet, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · intro hx
    refine ⟨x ∘ ι, ?_, ?_⟩
    · rwa [funext fun j => Work.WilG0.snocIt_natAdd n m x (x ∘ ι) j]
    · intro j
      rw [Work.WilG0.snocIt_natAdd, Work.WilG0.snocIt_castAdd]
      rfl
  · rintro ⟨w, hw, hd⟩
    have hwA : w ∈ A := by
      have h := hw
      rwa [funext fun j => Work.WilG0.snocIt_natAdd n m x w j] at h
    have hwx : w = x ∘ ι := by
      funext j
      have hj := hd j
      rw [Work.WilG0.snocIt_natAdd, Work.WilG0.snocIt_castAdd] at hj
      exact hj
    rwa [← hwx]

end Work.WilG4a
