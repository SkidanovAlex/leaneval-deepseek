import Mathlib
import Submission.Work.EKLContract.All

/-!
# `Work.EKLProd.inv_entries_bound`

Uniform bound on the entries of `u⁻¹` for `u` in the displacement neighbourhood `V ε`

    `V ε = {g : SL₃(ℝ) | ∀ i j, |g i j - 1 i j| < ε}`.

`V ε` is bounded entrywise (`|u i j| ≤ 1 + ε` for `u ∈ V ε`, `ε > 0`), and for
`A ∈ SL₃(ℝ)` the inverse matrix is the adjugate (`Matrix.SpecialLinearGroup.coe_inv`), whose
entries are `2 × 2` minors of `A`, hence bounded by `2 (1+ε)²`.  This is what is needed to make
the orbit map `u ↦ u • x` uniformly Lipschitz-free "small" on `V ε`.

We prove the two ingredients separately:

* `abs_det_fin_two_le` — a `2 × 2` determinant with all entries bounded by `B ≥ 0` is bounded
  by `2 B²`;
* `abs_adjugate_entry_le` — every entry of the adjugate of a `3 × 3` matrix with entries
  bounded by `B ≥ 0` is bounded by `2 B²`.
-/

namespace Work.EKLProd

open Work.EKLContract

/-- A `2 × 2` determinant with all entries bounded by `B ≥ 0` is bounded by `2 B²`. -/
lemma abs_det_fin_two_le (M : Matrix (Fin 2) (Fin 2) ℝ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ i j, |M i j| ≤ B) : |M.det| ≤ 2 * B ^ 2 := by
  rw [Matrix.det_fin_two]
  calc |M 0 0 * M 1 1 - M 0 1 * M 1 0| ≤ |M 0 0 * M 1 1| + |M 0 1 * M 1 0| := abs_sub _ _
    _ ≤ B * B + B * B := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul (h 0 0) (h 1 1) (abs_nonneg _) hB)
          (mul_le_mul (h 0 1) (h 1 0) (abs_nonneg _) hB)
    _ = 2 * B ^ 2 := by ring

/-- Every entry of the adjugate of a `3 × 3` real matrix whose entries are bounded by `B ≥ 0`
is bounded by `2 B²` (each entry is a `2 × 2` minor). -/
lemma abs_adjugate_entry_le {A : Matrix (Fin 3) (Fin 3) ℝ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ i j, |A i j| ≤ B) (i j : Fin 3) : |A.adjugate i j| ≤ 2 * B ^ 2 := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  have hsign : |(-1 : ℝ) ^ (j + i : ℕ) * (A.submatrix j.succAbove i.succAbove).det|
      = |(A.submatrix j.succAbove i.succAbove).det| := by
    rw [abs_mul, abs_pow]
    norm_num
  rw [hsign]
  exact abs_det_fin_two_le _ hB (fun p q => h _ _)

theorem inv_entries_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ u : Work.EKLContract.SL3, u ∈ Work.EKLContract.V ε → ∀ i j, |(u⁻¹) i j| ≤ C := by
  refine ⟨2 * (1 + ε) ^ 2, ?_⟩
  intro u hu i j
  rw [Matrix.SpecialLinearGroup.coe_inv]
  refine abs_adjugate_entry_le (by linarith) (fun p q => ?_) i j
  have hlt : |(u : Matrix (Fin 3) (Fin 3) ℝ) p q - (1 : Matrix (Fin 3) (Fin 3) ℝ) p q| < ε :=
    hu p q
  have hone : |(1 : Matrix (Fin 3) (Fin 3) ℝ) p q| ≤ 1 := by
    rw [Matrix.one_apply]; split_ifs <;> simp
  calc |(u : Matrix (Fin 3) (Fin 3) ℝ) p q|
      = |((u : Matrix (Fin 3) (Fin 3) ℝ) p q - (1 : Matrix (Fin 3) (Fin 3) ℝ) p q)
          + (1 : Matrix (Fin 3) (Fin 3) ℝ) p q| := by rw [sub_add_cancel]
    _ ≤ |(u : Matrix (Fin 3) (Fin 3) ℝ) p q - (1 : Matrix (Fin 3) (Fin 3) ℝ) p q|
          + |(1 : Matrix (Fin 3) (Fin 3) ℝ) p q| := abs_add_le _ _
    _ ≤ ε + 1 := add_le_add (le_of_lt hlt) hone
    _ = 1 + ε := by ring

end Work.EKLProd
