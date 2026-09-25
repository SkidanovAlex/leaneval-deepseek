import Mathlib
import Submission.Work.CR.Flat.Holder.holderNorm_add_le
import Submission.Work.CR.Flat.Holder.holderNorm_le_wirtinger_coord

namespace Work.CR.Flat.Holder

/-- The `C^{k,α}` norm is subadditive over a finite sum: the norm of a finite
sum of functions is at most the sum of the norms.  This is the finite-`Finset`
version of `holderNorm_add_le`, proved by induction. -/
theorem holderNorm_sum_le {n : ℕ} {ι : Type*} (s : Finset ι) {k : ℕ} {α : ℝ}
    {g : ι → (Fin n → ℂ) → ℂ} {Ω : Set (Fin n → ℂ)}
    (hg : ∀ j ∈ s, ContDiffOn ℝ (k : ℕ∞) (g j) Ω) (hΩ : UniqueDiffOn ℝ Ω) :
    Work.CR.Flat.holderNorm k α (fun z => ∑ j ∈ s, g j z) Ω
      ≤ ∑ j ∈ s, Work.CR.Flat.holderNorm k α (g j) Ω := by
  classical
  induction s using Finset.induction with
  | empty =>
    have h0 : (fun z : Fin n → ℂ => ∑ j ∈ (∅ : Finset ι), g j z)
        = (0 : (Fin n → ℂ) → ℂ) := by
      funext z; simp
    rw [h0, Work.CR.Flat.holderNorm_zero, Finset.sum_empty]
  | insert a t ha ih =>
    have hga : ContDiffOn ℝ (k : ℕ∞) (g a) Ω := hg a (Finset.mem_insert_self a t)
    have hgt : ∀ j ∈ t, ContDiffOn ℝ (k : ℕ∞) (g j) Ω :=
      fun j hj => hg j (Finset.mem_insert_of_mem hj)
    have hsumt : ContDiffOn ℝ (k : ℕ∞) (fun z => ∑ j ∈ t, g j z) Ω :=
      ContDiffOn.sum (fun j hj => hgt j hj)
    have hfun : (fun z => ∑ j ∈ insert a t, g j z)
        = g a + (fun z => ∑ j ∈ t, g j z) := by
      funext z
      rw [Finset.sum_insert ha]
      rfl
    rw [hfun, Finset.sum_insert ha]
    calc Work.CR.Flat.holderNorm k α (g a + fun z => ∑ j ∈ t, g j z) Ω
        ≤ Work.CR.Flat.holderNorm k α (g a) Ω
            + Work.CR.Flat.holderNorm k α (fun z => ∑ j ∈ t, g j z) Ω :=
          holderNorm_add_le hga hsumt hΩ
      _ ≤ Work.CR.Flat.holderNorm k α (g a) Ω
            + ∑ j ∈ t, Work.CR.Flat.holderNorm k α (g j) Ω :=
          add_le_add le_rfl (ih hgt)

end Work.CR.Flat.Holder
