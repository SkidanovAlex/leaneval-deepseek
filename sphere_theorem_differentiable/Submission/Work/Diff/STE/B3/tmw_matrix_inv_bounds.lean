/-
# Inverse bounds for a matrix whose quadratic form is uniformly pinched

Let `M : Matrix (Fin n) (Fin n) ℝ` be symmetric and assume that its quadratic form is pinched
between two multiples of the squared norm,

`mlo * (ξ ⬝ᵥ ξ) ≤ qf M ξ ≤ Mhi * (ξ ⬝ᵥ ξ)`

with `mlo > 0` (here `qf M ξ = ξ ⬝ᵥ M *ᵥ ξ`).  Then `M` is invertible and the inverse satisfies the
same kind of two-sided bound, with constants `(max Mhi 1)⁻¹` and `mlo⁻¹`; consequently every entry
of the inverse is bounded by `mlo⁻¹`.

This is the linear-algebra input `Work.Diff.STE.B3.tmw_matrix_inv_bounds` used in the short-time
existence analysis (area B3).  The proof is elementary: no spectral theory is used.  The two key
steps are

* `qf (M*M) y ≤ Mhi * qf M y` (the "upper transfer"), proved by evaluating the positivity of the
  quadratic form at the minimising point `t = n/s` of `t ↦ qf M (t • y - M *ᵥ y)`;
* `mlo * qf M y ≤ qf (M*M) y` (the "lower transfer"), proved from Cauchy–Schwarz for the dot
  product together with the lower bound.

Everything is written in the double-sum / dot-product formulation so that it applies verbatim to a
matrix given by its entries `A p q`.
-/
import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

open Matrix
open scoped Matrix

variable {n : ℕ}

/-- The bilinear form attached to a matrix, `ξ ⬝ᵥ M *ᵥ η`. -/
private def tmwBl (M : Matrix (Fin n) (Fin n) ℝ) (ξ η : Fin n → ℝ) : ℝ := ξ ⬝ᵥ M *ᵥ η

/-- The quadratic form attached to a matrix, `ξ ⬝ᵥ M *ᵥ ξ`. -/
private def tmwQf (M : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ) : ℝ := tmwBl M ξ ξ

private lemma tmwBl_apply (M : Matrix (Fin n) (Fin n) ℝ) (ξ η : Fin n → ℝ) :
    tmwBl M ξ η = ξ ⬝ᵥ M *ᵥ η := rfl

private lemma tmwQf_apply (M : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ) :
    tmwQf M ξ = ξ ⬝ᵥ M *ᵥ ξ := rfl

private lemma tmwQf_ext (M : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ) :
    tmwQf M ξ = tmwBl M ξ ξ := rfl

private lemma tmw_dot_eq_sum_sq (ξ : Fin n → ℝ) : ξ ⬝ᵥ ξ = ∑ i, (ξ i) ^ 2 := by
  simp [dotProduct, sq]

/-- The quadratic form expanded in the entries of the matrix. -/
private lemma tmwQf_eq_sum (M : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ) :
    tmwQf M ξ = ∑ p, ∑ q, M p q * ξ p * ξ q := by
  rw [tmwQf_ext, tmwBl_apply, Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

private lemma tmw_self_nonneg (x : Fin n → ℝ) : 0 ≤ x ⬝ᵥ x := by
  simp only [dotProduct]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

private lemma tmw_eq_zero_of_dot_self_eq_zero {x : Fin n → ℝ} (h : x ⬝ᵥ x = 0) : x = 0 := by
  funext i
  have hsum : ∑ j : Fin n, (x j) ^ 2 = 0 := by simpa [dotProduct, sq] using h
  exact (Finset.sum_sq_eq_zero_iff Finset.univ x).mp hsum i (Finset.mem_univ i)

/-- Cauchy–Schwarz for the dot product, in the sum-of-squares form needed here. -/
private lemma tmw_dot_sq_le (x y : Fin n → ℝ) :
    (x ⬝ᵥ y) ^ 2 ≤ (x ⬝ᵥ x) * (y ⬝ᵥ y) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n)) x y
  simpa [dotProduct, sq] using h

/-! ### Bilinearity of `tmwBl` and the derived identities for `tmwQf` -/

private lemma tmwBl_add_left (M : Matrix (Fin n) (Fin n) ℝ) (ξ ξ' η : Fin n → ℝ) :
    tmwBl M (ξ + ξ') η = tmwBl M ξ η + tmwBl M ξ' η := by
  simp only [tmwBl_apply, add_dotProduct]

private lemma tmwBl_add_right (M : Matrix (Fin n) (Fin n) ℝ) (ξ η η' : Fin n → ℝ) :
    tmwBl M ξ (η + η') = tmwBl M ξ η + tmwBl M ξ η' := by
  simp only [tmwBl_apply, Matrix.mulVec_add, dotProduct_add]

private lemma tmwBl_smul_left (M : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) (ξ η : Fin n → ℝ) :
    tmwBl M (a • ξ) η = a * tmwBl M ξ η := by
  simp only [tmwBl_apply, smul_dotProduct, smul_eq_mul]

private lemma tmwBl_smul_right (M : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) (ξ η : Fin n → ℝ) :
    tmwBl M ξ (a • η) = a * tmwBl M ξ η := by
  simp only [tmwBl_apply, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private lemma tmwBl_sub_left (M : Matrix (Fin n) (Fin n) ℝ) (ξ ξ' η : Fin n → ℝ) :
    tmwBl M (ξ - ξ') η = tmwBl M ξ η - tmwBl M ξ' η := by
  simp only [tmwBl_apply, sub_dotProduct]

private lemma tmwBl_sub_right (M : Matrix (Fin n) (Fin n) ℝ) (ξ η η' : Fin n → ℝ) :
    tmwBl M ξ (η - η') = tmwBl M ξ η - tmwBl M ξ η' := by
  simp only [tmwBl_apply, Matrix.mulVec_sub, dotProduct_sub]

/-- `tmwBl` is symmetric when the matrix is. -/
private lemma tmwBl_comm (M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M) (ξ η : Fin n → ℝ) :
    tmwBl M ξ η = tmwBl M η ξ := by
  rw [tmwBl_apply, tmwBl_apply, ← Matrix.dotProduct_transpose_mulVec M η ξ, hM]

private lemma tmwQf_add (M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M) (ξ η : Fin n → ℝ) :
    tmwQf M (ξ + η) = tmwQf M ξ + 2 * tmwBl M ξ η + tmwQf M η := by
  simp only [tmwQf_ext, tmwBl_add_left, tmwBl_add_right]
  rw [← tmwBl_comm M hM ξ η]
  ring

private lemma tmwQf_sub (M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M) (ξ η : Fin n → ℝ) :
    tmwQf M (ξ - η) = tmwQf M ξ - 2 * tmwBl M ξ η + tmwQf M η := by
  simp only [tmwQf_ext, tmwBl_sub_left, tmwBl_sub_right]
  rw [← tmwBl_comm M hM ξ η]
  ring

private lemma tmwQf_smul (M : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) (ξ : Fin n → ℝ) :
    tmwQf M (a • ξ) = a ^ 2 * tmwQf M ξ := by
  simp only [tmwQf_ext, tmwBl_smul_left, tmwBl_smul_right]
  ring

/-- `tmwQf (M*M)` is the squared norm of `M *ᵥ ξ` (for symmetric `M`). -/
private lemma tmwQf_mul_self (M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M) (ξ : Fin n → ℝ) :
    tmwQf (M * M) ξ = (M *ᵥ ξ) ⬝ᵥ (M *ᵥ ξ) := by
  rw [tmwQf_apply, ← Matrix.mulVec_mulVec]
  rw [← Matrix.dotProduct_transpose_mulVec M ξ (M *ᵥ ξ), hM]

/-- The expansion of `tmwQf M (t • y - M *ᵥ y)`, used for the "upper transfer". -/
private lemma tmwQf_smul_sub_mulVec (M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M) (t : ℝ)
    (y : Fin n → ℝ) :
    tmwQf M (t • y - M *ᵥ y)
      = t ^ 2 * tmwQf M y - 2 * t * ((M *ᵥ y) ⬝ᵥ (M *ᵥ y)) + tmwQf M (M *ᵥ y) := by
  rw [tmwQf_sub M hM (t • y) (M *ᵥ y), tmwQf_smul M t y, tmwBl_smul_left M t y (M *ᵥ y),
    ← tmwBl_comm M hM (M *ᵥ y) y, tmwBl_apply]
  ring

/-- If a real quadratic form with positive leading coefficient is nonnegative everywhere, then
its discriminant is nonpositive: `n ^ 2 ≤ c * s`. -/
private lemma tmw_quad_discrim (s n c : ℝ) (hs : 0 < s)
    (h : ∀ t : ℝ, 0 ≤ t ^ 2 * s - 2 * t * n + c) : n ^ 2 ≤ c * s := by
  have h1 := h (n / s)
  have key : s * ((n / s) ^ 2 * s - 2 * (n / s) * n + c) = c * s - n ^ 2 := by
    field_simp
    ring
  have h2 : 0 ≤ s * ((n / s) ^ 2 * s - 2 * (n / s) * n + c) := mul_nonneg (le_of_lt hs) h1
  rw [key] at h2
  linarith

/-- **The main linear-algebra estimate**, for a matrix `M` given directly. -/
private theorem tmw_matrix_inv_bounds_aux (n : ℕ) (mlo Mhi : ℝ) (hmlo : 0 < mlo)
    (M : Matrix (Fin n) (Fin n) ℝ) (hsym : Mᵀ = M)
    (hlow : ∀ ξ : Fin n → ℝ, mlo * (ξ ⬝ᵥ ξ) ≤ tmwQf M ξ)
    (hhigh : ∀ ξ : Fin n → ℝ, tmwQf M ξ ≤ Mhi * (ξ ⬝ᵥ ξ)) :
    (∀ ξ : Fin n → ℝ, (max Mhi 1)⁻¹ * (ξ ⬝ᵥ ξ) ≤ tmwQf M⁻¹ ξ) ∧
      (∀ p q : Fin n, |M⁻¹ p q| ≤ mlo⁻¹) := by
  have hK : 0 < max Mhi 1 := lt_of_lt_of_le zero_lt_one (le_max_right Mhi 1)
  have hpsd : ∀ ξ : Fin n → ℝ, 0 ≤ tmwQf M ξ := fun ξ =>
    le_trans (mul_nonneg (le_of_lt hmlo) (tmw_self_nonneg ξ)) (hlow ξ)
  -- `M` is injective, hence invertible
  have hinj : Function.Injective M.mulVec := by
    intro x y hxy
    have hz : M *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    have hq : tmwQf M (x - y) = 0 := by rw [tmwQf_apply, hz, dotProduct_zero]
    have hB0 : (x - y) ⬝ᵥ (x - y) = 0 := by
      have h1 := hlow (x - y)
      rw [hq] at h1
      exact le_antisymm (le_of_mul_le_mul_left (by simpa using h1) hmlo) (tmw_self_nonneg _)
    exact sub_eq_zero.mp (tmw_eq_zero_of_dot_self_eq_zero hB0)
  have hdet : IsUnit M.det :=
    (Matrix.isUnit_iff_isUnit_det M).mp (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  have hMB : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hdet
  have hBM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hdet
  have hinvT : M⁻¹ᵀ = M⁻¹ := by rw [Matrix.transpose_nonsing_inv, hsym]
  -- **lower transfer**: `mlo * qf M y ≤ qf (M*M) y`
  have hU : ∀ y : Fin n → ℝ, mlo * tmwQf M y ≤ tmwQf (M * M) y := by
    intro y
    rw [tmwQf_apply, tmwQf_mul_self M hsym]
    have h1 : mlo * (y ⬝ᵥ y) ≤ y ⬝ᵥ M *ᵥ y := by
      have h := hlow y
      rwa [tmwQf_apply] at h
    have h2 : (y ⬝ᵥ M *ᵥ y) ^ 2 ≤ (y ⬝ᵥ y) * ((M *ᵥ y) ⬝ᵥ (M *ᵥ y)) :=
      tmw_dot_sq_le y (M *ᵥ y)
    have hB : 0 ≤ y ⬝ᵥ y := tmw_self_nonneg y
    have hn : 0 ≤ (M *ᵥ y) ⬝ᵥ (M *ᵥ y) := tmw_self_nonneg _
    have hs : 0 ≤ y ⬝ᵥ M *ᵥ y := le_trans (mul_nonneg (le_of_lt hmlo) hB) h1
    have hx : 0 ≤ mlo * (y ⬝ᵥ M *ᵥ y) := mul_nonneg (le_of_lt hmlo) hs
    have hstep : (mlo * (y ⬝ᵥ M *ᵥ y)) ^ 2
        ≤ ((M *ᵥ y) ⬝ᵥ (M *ᵥ y)) * (mlo * (y ⬝ᵥ M *ᵥ y)) := by
      have h3 : mlo ^ 2 * (y ⬝ᵥ y) ≤ mlo * (y ⬝ᵥ M *ᵥ y) := by nlinarith [h1, hmlo]
      have h4 : mlo ^ 2 * (y ⬝ᵥ M *ᵥ y) ^ 2
          ≤ mlo ^ 2 * ((y ⬝ᵥ y) * ((M *ᵥ y) ⬝ᵥ (M *ᵥ y))) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg mlo)
      have h5 : mlo ^ 2 * ((y ⬝ᵥ y) * ((M *ᵥ y) ⬝ᵥ (M *ᵥ y)))
          ≤ (mlo * (y ⬝ᵥ M *ᵥ y)) * ((M *ᵥ y) ⬝ᵥ (M *ᵥ y)) := by
        have := mul_le_mul_of_nonneg_right h3 hn
        linarith [this]
      nlinarith [h4, h5]
    by_cases hx0 : mlo * (y ⬝ᵥ M *ᵥ y) = 0
    · rw [hx0]
      exact hn
    · have hxpos : 0 < mlo * (y ⬝ᵥ M *ᵥ y) := lt_of_le_of_ne hx (Ne.symm hx0)
      have h4 : 0 ≤ (mlo * (y ⬝ᵥ M *ᵥ y))
          * (((M *ᵥ y) ⬝ᵥ (M *ᵥ y)) - mlo * (y ⬝ᵥ M *ᵥ y)) := by
        nlinarith [hstep]
      have h5 : 0 ≤ ((M *ᵥ y) ⬝ᵥ (M *ᵥ y)) - mlo * (y ⬝ᵥ M *ᵥ y) :=
        nonneg_of_mul_nonneg_right h4 hxpos
      linarith
  -- **upper transfer**: `qf (M*M) y ≤ Mhi * qf M y`
  have hL : ∀ y : Fin n → ℝ, tmwQf (M * M) y ≤ Mhi * tmwQf M y := by
    intro y
    have hquad : ∀ t : ℝ,
        0 ≤ t ^ 2 * (tmwQf M y) - 2 * t * ((M *ᵥ y) ⬝ᵥ (M *ᵥ y)) + tmwQf M (M *ᵥ y) := by
      intro t
      have h := hpsd (t • y - M *ᵥ y)
      rwa [tmwQf_smul_sub_mulVec M hsym t y] at h
    rw [tmwQf_mul_self M hsym]
    have hn : 0 ≤ (M *ᵥ y) ⬝ᵥ (M *ᵥ y) := tmw_self_nonneg _
    rcases eq_or_lt_of_le (hpsd y) with hs0 | hspos
    · have hy : y = 0 := by
        have h1 := hlow y
        rw [← hs0] at h1
        have hBle : y ⬝ᵥ y ≤ 0 := le_of_mul_le_mul_left (by simpa using h1) hmlo
        exact tmw_eq_zero_of_dot_self_eq_zero (le_antisymm hBle (tmw_self_nonneg y))
      rw [hy]
      simp [tmwQf_ext, tmwBl_apply]
    · have hBpos : 0 < y ⬝ᵥ y := by
        by_contra h
        have hB0 : y ⬝ᵥ y = 0 := le_antisymm (le_of_not_gt h) (tmw_self_nonneg y)
        have hy0 : y = 0 := tmw_eq_zero_of_dot_self_eq_zero hB0
        rw [hy0] at hspos
        simp [tmwQf_ext, tmwBl_apply] at hspos
      have hMhi_pos : 0 < Mhi := by
        have h := hhigh y
        have h2 : 0 < Mhi * (y ⬝ᵥ y) := lt_of_lt_of_le hspos h
        exact pos_of_mul_pos_left h2 (le_of_lt hBpos)
      have hcs : ((M *ᵥ y) ⬝ᵥ (M *ᵥ y)) ^ 2
          ≤ (tmwQf M (M *ᵥ y)) * (tmwQf M y) :=
        tmw_quad_discrim (tmwQf M y) ((M *ᵥ y) ⬝ᵥ (M *ᵥ y)) (tmwQf M (M *ᵥ y)) hspos hquad
      have hc_le : tmwQf M (M *ᵥ y) ≤ Mhi * ((M *ᵥ y) ⬝ᵥ (M *ᵥ y)) := hhigh (M *ᵥ y)
      rcases eq_or_lt_of_le hn with hn0 | hnpos
      · rw [← hn0]
        exact mul_nonneg (le_of_lt hMhi_pos) (le_of_lt hspos)
      · have hc' : (tmwQf M (M *ᵥ y)) * (tmwQf M y)
            ≤ (Mhi * ((M *ᵥ y) ⬝ᵥ (M *ᵥ y))) * (tmwQf M y) :=
          mul_le_mul_of_nonneg_right hc_le (le_of_lt hspos)
        have h2 : ((M *ᵥ y) ⬝ᵥ (M *ᵥ y)) ^ 2
            ≤ Mhi * ((M *ᵥ y) ⬝ᵥ (M *ᵥ y)) * (tmwQf M y) := by
          nlinarith [hcs, hc']
        have h3 : ((M *ᵥ y) ⬝ᵥ (M *ᵥ y))
            * (((M *ᵥ y) ⬝ᵥ (M *ᵥ y)) - Mhi * (tmwQf M y)) ≤ 0 := by
          nlinarith [h2]
        have h4 : ((M *ᵥ y) ⬝ᵥ (M *ᵥ y)) - Mhi * (tmwQf M y) ≤ 0 :=
          nonpos_of_mul_nonpos_right h3 hnpos
        linarith
  -- two-sided bounds for the inverse form
  have form_bounds : ∀ ξ : Fin n → ℝ,
      (max Mhi 1)⁻¹ * (ξ ⬝ᵥ ξ) ≤ tmwQf M⁻¹ ξ ∧ tmwQf M⁻¹ ξ ≤ mlo⁻¹ * (ξ ⬝ᵥ ξ) := by
    intro ξ
    obtain ⟨y, hy⟩ : ∃ y : Fin n → ℝ, M⁻¹ *ᵥ ξ = y := ⟨_, rfl⟩
    have hMy : M *ᵥ y = ξ := by
      rw [← hy, Matrix.mulVec_mulVec, hMB, Matrix.one_mulVec]
    have hq1 : tmwQf M⁻¹ ξ = tmwQf M y := by
      rw [tmwQf_apply, tmwQf_apply, hy, dotProduct_comm, hMy]
    have hq2 : tmwQf (M * M) y = ξ ⬝ᵥ ξ := by
      rw [tmwQf_mul_self M hsym y, ← hMy]
    have hBnn : 0 ≤ tmwQf M⁻¹ ξ := by rw [hq1]; exact hpsd y
    constructor
    · have h1 : ξ ⬝ᵥ ξ ≤ Mhi * tmwQf M⁻¹ ξ := by
        rw [← hq2, hq1]
        exact hL y
      have h2 : ξ ⬝ᵥ ξ ≤ max Mhi 1 * tmwQf M⁻¹ ξ :=
        le_trans h1 (mul_le_mul_of_nonneg_right (le_max_left Mhi 1) hBnn)
      have h3 := mul_le_mul_of_nonneg_left h2 (le_of_lt (inv_pos.mpr hK))
      rwa [inv_mul_cancel_left₀ (ne_of_gt hK)] at h3
    · have h1 : mlo * tmwQf M⁻¹ ξ ≤ ξ ⬝ᵥ ξ := by
        rw [hq1, ← hq2]
        exact hU y
      have h3 := mul_le_mul_of_nonneg_left h1 (le_of_lt (inv_pos.mpr hmlo))
      rwa [inv_mul_cancel_left₀ (ne_of_gt hmlo)] at h3
  refine ⟨fun ξ => (form_bounds ξ).1, fun p q => ?_⟩
  -- entrywise bound: use the positive semidefiniteness of the inverse form on `e_p ± e_q`
  have hBl : ∀ a b : Fin n, tmwBl M⁻¹ (Pi.single a 1) (Pi.single b 1) = M⁻¹ a b := by
    intro a b
    rw [tmwBl_apply, single_dotProduct, one_mul, Matrix.mulVec_apply, dotProduct_single, mul_one]
    rfl
  have hdiag : ∀ a : Fin n, tmwQf M⁻¹ (Pi.single a 1) = M⁻¹ a a := by
    intro a
    rw [tmwQf_ext, hBl a a]
  have hadd : tmwQf M⁻¹ (Pi.single p 1 + Pi.single q 1)
      = M⁻¹ p p + 2 * M⁻¹ p q + M⁻¹ q q := by
    rw [tmwQf_add M⁻¹ hinvT, hdiag p, hdiag q, hBl p q]
  have hsub : tmwQf M⁻¹ (Pi.single p 1 - Pi.single q 1)
      = M⁻¹ p p - 2 * M⁻¹ p q + M⁻¹ q q := by
    rw [tmwQf_sub M⁻¹ hinvT, hdiag p, hdiag q, hBl p q]
  have hnn : ∀ ξ : Fin n → ℝ, 0 ≤ tmwQf M⁻¹ ξ := fun ξ =>
    le_trans (mul_nonneg (le_of_lt (inv_pos.mpr hK)) (tmw_self_nonneg ξ)) (form_bounds ξ).1
  have h1 : 0 ≤ M⁻¹ p p + 2 * M⁻¹ p q + M⁻¹ q q := by
    rw [← hadd]
    exact hnn _
  have h2 : 0 ≤ M⁻¹ p p - 2 * M⁻¹ p q + M⁻¹ q q := by
    rw [← hsub]
    exact hnn _
  have hpp : M⁻¹ p p ≤ mlo⁻¹ := by
    have h := (form_bounds (Pi.single p 1)).2
    rw [hdiag p] at h
    have he : (Pi.single p (1 : ℝ) : Fin n → ℝ) ⬝ᵥ Pi.single p 1 = 1 := by
      rw [single_dotProduct, Pi.single_eq_same, mul_one]
    rwa [he, mul_one] at h
  have hqq : M⁻¹ q q ≤ mlo⁻¹ := by
    have h := (form_bounds (Pi.single q 1)).2
    rw [hdiag q] at h
    have he : (Pi.single q (1 : ℝ) : Fin n → ℝ) ⬝ᵥ Pi.single q 1 = 1 := by
      rw [single_dotProduct, Pi.single_eq_same, mul_one]
    rwa [he, mul_one] at h
  rw [abs_le]
  constructor <;> linarith

/-- **Bounds for the inverse of a uniformly positive definite symmetric matrix.**  For a symmetric
matrix `A` with `mlo * ‖ξ‖² ≤ ξᵀ A ξ ≤ Mhi * ‖ξ‖²` for all `ξ` and `mlo > 0`, the inverse matrix
satisfies `c * ‖ξ‖² ≤ ξᵀ A⁻¹ ξ` with `c = (max Mhi 1)⁻¹`, and all its entries are bounded by
`mlo⁻¹`. -/
theorem tmw_matrix_inv_bounds (n : ℕ) (mlo Mhi : ℝ) (hmlo : 0 < mlo) :
    ∃ (c C : ℝ), 0 < c ∧ 0 ≤ C ∧
      ∀ A : Fin n → Fin n → ℝ,
        (∀ i j, A i j = A j i) →
        (∀ ξ : Fin n → ℝ, mlo * ∑ i, (ξ i) ^ 2 ≤ ∑ p, ∑ q, A p q * ξ p * ξ q) →
        (∀ ξ : Fin n → ℝ, (∑ p, ∑ q, A p q * ξ p * ξ q) ≤ Mhi * ∑ i, (ξ i) ^ 2) →
        (∀ ξ : Fin n → ℝ, c * ∑ i, (ξ i) ^ 2
            ≤ ∑ p, ∑ q, (Matrix.of A)⁻¹ p q * ξ p * ξ q) ∧
        (∀ p q, |(Matrix.of A)⁻¹ p q| ≤ C) := by
  refine ⟨(max Mhi 1)⁻¹, mlo⁻¹, ?_, le_of_lt (inv_pos.mpr hmlo), ?_⟩
  · exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_right Mhi 1))
  · intro A hsym hlow hhigh
    have hsym' : (Matrix.of A)ᵀ = Matrix.of A := by
      ext i j
      exact hsym j i
    have hlow' : ∀ ξ : Fin n → ℝ, mlo * (ξ ⬝ᵥ ξ) ≤ tmwQf (Matrix.of A) ξ := by
      intro ξ
      rw [tmw_dot_eq_sum_sq ξ, tmwQf_eq_sum]
      simpa [Matrix.of_apply] using hlow ξ
    have hhigh' : ∀ ξ : Fin n → ℝ, tmwQf (Matrix.of A) ξ ≤ Mhi * (ξ ⬝ᵥ ξ) := by
      intro ξ
      rw [tmw_dot_eq_sum_sq ξ, tmwQf_eq_sum]
      simpa [Matrix.of_apply] using hhigh ξ
    refine ⟨fun ξ => ?_, fun p q => ?_⟩
    · have h := (tmw_matrix_inv_bounds_aux n mlo Mhi hmlo (Matrix.of A) hsym' hlow' hhigh').1 ξ
      rwa [tmw_dot_eq_sum_sq ξ, tmwQf_eq_sum] at h
    · exact (tmw_matrix_inv_bounds_aux n mlo Mhi hmlo (Matrix.of A) hsym' hlow' hhigh').2 p q

end Work.Diff.STE.B3
