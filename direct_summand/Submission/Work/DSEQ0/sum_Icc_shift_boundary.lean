import Mathlib

namespace Work.DSEQ0

universe u

theorem sum_Icc_shift_boundary {M : Type u} [AddCommMonoid M] (f g : ℤ → M) (a b : ℤ) (hab : a ≤ b) :
    ((∑ i ∈ Finset.Icc a b, f i) = ∑ j ∈ Finset.Icc (a - 1) (b - 1), f (j + 1)) ∧
      ((∑ k ∈ Finset.Icc a b, g k) + g (a - 1) = (∑ j ∈ Finset.Icc (a - 1) (b - 1), g j) + g b) := by
  constructor
  · -- Reindex `j ↦ j + 1` maps `Icc (a-1) (b-1)` bijectively onto `Icc a b`.
    have himg : (Finset.Icc (a - 1) (b - 1)).image (fun j => j + 1) = Finset.Icc a b := by
      ext i
      simp only [Finset.mem_image, Finset.mem_Icc]
      constructor
      · rintro ⟨j, ⟨h1, h2⟩, rfl⟩
        omega
      · intro hi
        exact ⟨i - 1, by omega, by omega⟩
    rw [← himg]
    refine Finset.sum_image (g := fun j => j + 1) ?_
    intro x hx y hy h
    simp only [Finset.mem_coe, Finset.mem_Icc] at hx hy
    change x + 1 = y + 1 at h
    omega
  · -- Split off the boundary terms: `Icc a b = insert b (Ico a b)` and
    -- `Icc (a-1) (b-1) = insert (a-1) (Ico a b)`.
    have hIcc : Finset.Icc a b = insert b (Finset.Ico a b) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_Icc, Finset.mem_Ico]
      omega
    have hIco : Finset.Icc (a - 1) (b - 1) = insert (a - 1) (Finset.Ico a b) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_Icc, Finset.mem_Ico]
      omega
    have hmem : (a - 1) ∉ Finset.Ico a b := by
      simp only [Finset.mem_Ico]; omega
    have hmem2 : b ∉ Finset.Ico a b := by
      simp only [Finset.mem_Ico]; omega
    rw [hIcc, hIco, Finset.sum_insert hmem2, Finset.sum_insert hmem]
    abel

end Work.DSEQ0
