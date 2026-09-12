import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Commons.LinearAlgebra.Matrix

/-- If a square real matrix `M` vanishes on the block `Q × H` and on the block
`Qᶜ × Hᶜ` (i.e. rows in `Q` are supported on the complement of `H` and rows
outside `Q` are supported on `H`), then a nonzero determinant forces
`|H| = |ι| - |Q|`. -/
theorem det_ne_zero_card_eq_of_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (Q H : Finset ι)
    (h1 : ∀ s ∈ Q, ∀ i ∈ H, M s i = 0) (h2 : ∀ s ∉ Q, ∀ i ∉ H, M s i = 0)
    (hdet : M.det ≠ 0) : H.card = Fintype.card ι - Q.card := by
  classical
  -- A nonzero determinant forces a permutation all of whose Leibniz factors are nonzero.
  have hex : ∃ σ : Equiv.Perm ι, ∀ i, M (σ i) i ≠ 0 := by
    by_contra h
    push Not at h
    apply hdet
    rw [Matrix.det_apply']
    apply Finset.sum_eq_zero
    intro σ _
    obtain ⟨i, hi⟩ := h σ
    have hprod : (∏ j, M (σ j) j) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [hprod, mul_zero]
  obtain ⟨σ, hσ⟩ := hex
  -- Rewrite the permutation so that the factor at index `s` is `M s (σ.symm s)`.
  have hσinv : ∀ s, M s (σ.symm s) ≠ 0 := fun s => by
    have := hσ (σ.symm s)
    simpa using this
  -- Rows in `Q` are supported off `H`, so `σ.symm` maps `Q` into `Hᶜ`.
  have hQ : Q.card ≤ Fintype.card ι - H.card := by
    have hsub : (Q.image (σ.symm)) ⊆ Hᶜ := by
      intro j hj
      rw [Finset.mem_image] at hj
      obtain ⟨s, hs, rfl⟩ := hj
      rw [Finset.mem_compl]
      intro hjH
      exact hσinv s (h1 s hs (σ.symm s) hjH)
    calc Q.card = (Q.image (σ.symm)).card :=
          (Finset.card_image_of_injective Q (σ.symm).injective).symm
      _ ≤ Hᶜ.card := Finset.card_le_card hsub
      _ = Fintype.card ι - H.card := Finset.card_compl H
  -- Rows outside `Q` are supported on `H`, so `σ.symm` maps `Qᶜ` into `H`.
  have hQc : Fintype.card ι - Q.card ≤ H.card := by
    have hsub : (Qᶜ.image (σ.symm)) ⊆ H := by
      intro j hj
      rw [Finset.mem_image] at hj
      obtain ⟨s, hs, rfl⟩ := hj
      rw [Finset.mem_compl] at hs
      by_contra hjH
      exact hσinv s (h2 s hs (σ.symm s) hjH)
    calc Fintype.card ι - Q.card = Qᶜ.card := (Finset.card_compl Q).symm
      _ = (Qᶜ.image (σ.symm)).card :=
          (Finset.card_image_of_injective Qᶜ (σ.symm).injective).symm
      _ ≤ H.card := Finset.card_le_card hsub
  have hHn : H.card ≤ Fintype.card ι := Finset.card_le_univ H
  have hQn : Q.card ≤ Fintype.card ι := Finset.card_le_univ Q
  omega

end Commons.LinearAlgebra.Matrix