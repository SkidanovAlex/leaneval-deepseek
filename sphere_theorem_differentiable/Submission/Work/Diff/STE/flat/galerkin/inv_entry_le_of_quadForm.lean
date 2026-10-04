import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Matrix

namespace Work.Diff.STE.flat.galerkin

/-- The quadratic form `∑ᵢ ∑ⱼ Aᵢⱼ vᵢ vⱼ` is the dot product of `v` with `A *ᵥ v`. -/
private lemma sum_sum_mul_eq_dotProduct {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    ∑ i, ∑ j, A i j * v i * v j = dotProduct v (A.mulVec v) := by
  rw [Matrix.dot_mulVec_eq_sum_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- A nonzero vector has positive sum of squares. -/
private lemma sum_sq_pos_of_ne_zero {n : ℕ} {v : Fin n → ℝ} (hv : v ≠ 0) : 0 < ∑ i, (v i) ^ 2 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
  have hk' : v k ≠ 0 := by simpa using hk
  have hpos := Finset.sum_pos' (s := Finset.univ) (fun i _ => sq_nonneg (v i))
    ⟨k, Finset.mem_univ k, sq_pos_of_ne_zero hk'⟩
  simpa using hpos

/-- A square real matrix whose associated quadratic form dominates `lam * ‖·‖²` with `lam > 0`
is nonsingular. -/
private lemma det_ne_zero_of_quadForm_le_aux {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {lam : ℝ}
    (hlam : 0 < lam)
    (h : ∀ v : Fin n → ℝ, lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, A i j * v i * v j) :
    A.det ≠ 0 := by
  intro hdet
  -- a singular matrix has a nonzero kernel vector
  obtain ⟨v, hvne, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  -- for such a vector the quadratic form vanishes ...
  have h0 : ∑ i, ∑ j, A i j * v i * v j = 0 := by
    rw [sum_sum_mul_eq_dotProduct, hv, dotProduct_zero]
  -- ... but `lam * ∑ᵢ vᵢ²` is strictly positive
  have hvpos : 0 < ∑ i, (v i) ^ 2 := sum_sq_pos_of_ne_zero hvne
  have hle := h v
  rw [h0] at hle
  have hpos := mul_pos hlam hvpos
  linarith

theorem inv_entry_le_of_quadForm {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) {lam : ℝ} (hlam : 0 < lam)
    (h : ∀ v : Fin n → ℝ, lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, B i j * v i * v j) :
    ∀ i j, |(B⁻¹) i j| ≤ lam⁻¹ := by
  have hdet : B.det ≠ 0 := det_ne_zero_of_quadForm_le_aux B hlam h
  have hunit : IsUnit B.det := isUnit_iff_ne_zero.mpr hdet
  have hBBinv : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hunit
  intro i j
  -- `x` is the `j`-th column of `B⁻¹`, so that `B *ᵥ x = eⱼ`
  set x : Fin n → ℝ := B⁻¹ *ᵥ Pi.single j (1 : ℝ) with hx
  have hxi : x i = (B⁻¹) i j := by
    rw [hx, Matrix.mulVec_single_one, Matrix.col_apply]
  rw [← hxi]
  have hBx : B *ᵥ x = Pi.single j (1 : ℝ) := by
    rw [hx, Matrix.mulVec_mulVec, hBBinv, Matrix.one_mulVec]
  -- the quadratic form of `x` is `x j`
  have hq : ∑ a, ∑ b, B a b * x a * x b = x j := by
    rw [sum_sum_mul_eq_dotProduct, hBx, dotProduct_single, mul_one]
  set N : ℝ := ∑ a, (x a) ^ 2 with hN
  have hj : lam * N ≤ x j := by
    have hh := h x
    rw [hq] at hh
    rw [hN]
    exact hh
  have hNnn : 0 ≤ N := by
    rw [hN]
    exact Finset.sum_nonneg (fun a _ => sq_nonneg (x a))
  have hle_sq : ∀ a, (x a) ^ 2 ≤ N := by
    intro a
    rw [hN]
    simpa using Finset.single_le_sum (fun b _ => sq_nonneg (x b)) (Finset.mem_univ a)
  -- squaring the key inequality
  have hkey : lam ^ 2 * N ^ 2 ≤ N := by
    have hsq : (lam * N) ^ 2 ≤ (x j) ^ 2 := by
      have h0 : 0 ≤ lam * N := mul_nonneg (le_of_lt hlam) hNnn
      have := mul_self_le_mul_self h0 hj
      simpa [pow_two] using this
    calc lam ^ 2 * N ^ 2 = (lam * N) ^ 2 := by ring
      _ ≤ (x j) ^ 2 := hsq
      _ ≤ N := hle_sq j
  have hNle : N ≤ (lam⁻¹) ^ 2 := by
    rcases lt_or_eq_of_le hNnn with hNpos | hNzero
    · have hprod : N * (lam ^ 2 * N - 1) ≤ 0 := by nlinarith [hkey]
      have h2 : lam ^ 2 * N - 1 ≤ 0 := nonpos_of_mul_nonpos_right hprod hNpos
      have h1 : lam ^ 2 * N ≤ 1 := by linarith
      have hlam2 : 0 < lam ^ 2 := pow_pos hlam 2
      have h1' : N ≤ 1 / lam ^ 2 := by
        rw [le_div_iff₀ hlam2]
        nlinarith [h1]
      have heq : (1 : ℝ) / lam ^ 2 = (lam⁻¹) ^ 2 := by rw [one_div, ← inv_pow]
      rwa [heq] at h1'
    · rw [← hNzero]
      exact sq_nonneg _
  have hxsq : (x i) ^ 2 ≤ (lam⁻¹) ^ 2 := le_trans (hle_sq i) hNle
  have hfin : |x i| ≤ |lam⁻¹| := (sq_le_sq).mp hxsq
  have hpos : 0 ≤ lam⁻¹ := inv_nonneg.mpr (le_of_lt hlam)
  simpa [abs_of_nonneg hpos] using hfin

end Work.Diff.STE.flat.galerkin
