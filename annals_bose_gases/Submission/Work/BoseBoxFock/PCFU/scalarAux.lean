import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU` — elementary arithmetic for the `Ksfr`-image bound

This module collects the elementary real-variable lemmas on which
`Work.BoseBoxFock.PCFU.scalarImageSumBound` (and its two summand-wise halves
`scalarTermOneBound`, `scalarTermTwoBound`) rest.

Throughout, `ℓ > 0` is the box side, `0 < δ ≤ 1` the boundary distance of the localisation
bump, `K ≥ 2N` the flatness exponent and `R := max 3 ℓ⁻¹` the radius of the lattice split.
The two structural facts are

* `ℓ · R = max (3 ℓ) 1`, so `ℓ R ≥ 1` always and `ℓ R ≤ 3` when `ℓ ≤ 1`; consequently
  `(ℓR)^{j} ≥ 1` and `((ℓR)^j)⁻¹ ≤ 1` for every `j : ℕ`;
* `δ^K ((1 + ℓδ)^{2N})⁻¹ ≤ (ℓ^{2N})⁻¹`, because `δ^K ≤ δ^{2N}` and `1 + ℓδ ≥ ℓδ`.

The `2`-power `2^{2N}` and the constants `125`, `8000`, `3³ = 27` only enter through
`125 · 4³ = 8000` (the `ℓ ≤ 1` regime, where `ℓ (1 + R) ≤ 1 + 3 = 4`) and `max 3 ℓ⁻¹ = 3`,
`(1+3)³ = 64` (the `ℓ ≥ 1` regime).
-/

namespace Work.BoseBoxFock.PCFU

/-- `(x^n)⁻¹ ≤ 1` for `x ≥ 1`. -/
lemma inv_pow_le_one_of_one_le {x : ℝ} (hx : 1 ≤ x) (n : ℕ) : (x ^ n)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (one_le_pow₀ hx)

/-- `1 ≤ (ℓ^M)⁻¹` for `0 < ℓ ≤ 1`. -/
lemma one_le_inv_pow_of_le_one {ℓ : ℝ} (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (M : ℕ) :
    1 ≤ (ℓ ^ M)⁻¹ := by
  rw [one_le_inv₀ (by positivity)]
  exact pow_le_one₀ hℓ0.le hℓ1

/-- `ℓ · max 3 ℓ⁻¹ = max (3 ℓ) 1` for `ℓ > 0`; in particular `ℓ · max 3 ℓ⁻¹ ≥ 1`. -/
lemma ell_mul_max_eq {ℓ : ℝ} (hℓ : 0 < ℓ) : ℓ * max 3 ℓ⁻¹ = max (3 * ℓ) 1 := by
  rw [mul_max_of_nonneg _ _ hℓ.le, mul_inv_cancel₀ hℓ.ne', mul_comm]

/-- For `ℓ ≥ 1` the lattice split radius is the constant `3`. -/
lemma max_eq_three_of_one_le {ℓ : ℝ} (hℓ : 1 ≤ ℓ) : max 3 ℓ⁻¹ = 3 :=
  max_eq_left (le_trans (inv_le_one_of_one_le₀ hℓ) (by norm_num))

/-- `ℓ³ (ℓ^{2N})⁻¹ = (ℓ^{2N-3})⁻¹` for `ℓ > 0` and `2N ≥ 3`. -/
lemma pow3_mul_inv_pow_eq {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} (h3 : 3 ≤ 2 * N) :
    ℓ ^ 3 * (ℓ ^ (2 * N))⁻¹ = (ℓ ^ (2 * N - 3))⁻¹ := by
  have h : 3 + (2 * N - 3) = 2 * N := Nat.add_sub_cancel' h3
  conv_lhs => rw [← h]
  rw [pow_add, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hℓ.ne'), one_mul]

/-- Antitonicity of `x ↦ (x^{-j})` on `[1, ∞)`. -/
lemma inv_pow_le_inv_pow_of_le {ℓ : ℝ} (hℓ : 1 ≤ ℓ) {M J : ℕ} (h : M ≤ J) :
    (ℓ ^ J)⁻¹ ≤ (ℓ ^ M)⁻¹ := by
  rw [inv_le_inv₀ (by positivity) (by positivity)]
  exact pow_le_pow_right₀ hℓ h

/-- `δ^K ((1 + ℓδ)^{2N})⁻¹ ≤ (ℓ^{2N})⁻¹`: the decay of the `K`-th power of `δ` beats the
Gaussian factor at the cost of `ℓ^{-2N}`. -/
lemma delta_pow_mul_inv_le {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {K N : ℕ} (hK : 2 * N ≤ K) :
    δ ^ K * ((1 + ℓ * δ) ^ (2 * N))⁻¹ ≤ (ℓ ^ (2 * N))⁻¹ := by
  have h1 : δ ^ K ≤ δ ^ (2 * N) := pow_le_pow_of_le_one hδ0.le hδ1 hK
  have h2 : ((1 + ℓ * δ) ^ (2 * N))⁻¹ ≤ ((ℓ * δ) ^ (2 * N))⁻¹ := by
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    exact pow_le_pow_left₀ (by positivity) (by linarith) (2 * N)
  have h3 : δ ^ (2 * N) * ((ℓ * δ) ^ (2 * N))⁻¹ = (ℓ ^ (2 * N))⁻¹ := by
    rw [mul_pow, mul_inv]
    rw [show δ ^ (2 * N) * ((ℓ ^ (2 * N))⁻¹ * (δ ^ (2 * N))⁻¹)
          = (δ ^ (2 * N) * (δ ^ (2 * N))⁻¹) * (ℓ ^ (2 * N))⁻¹ from by ring,
        mul_inv_cancel₀ (pow_ne_zero _ hδ0.ne'), one_mul]
  calc δ ^ K * ((1 + ℓ * δ) ^ (2 * N))⁻¹
      ≤ δ ^ (2 * N) * ((ℓ * δ) ^ (2 * N))⁻¹ := mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = (ℓ ^ (2 * N))⁻¹ := h3

/-- The previous lemma multiplied by `ℓ³`. -/
lemma delta_pow_mul_ell_cube_mul_inv_le {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {K N : ℕ} (hK : 2 * N ≤ K) :
    δ ^ K * ℓ ^ 3 * ((1 + ℓ * δ) ^ (2 * N))⁻¹ ≤ ℓ ^ 3 * (ℓ ^ (2 * N))⁻¹ := by
  have h := delta_pow_mul_inv_le hℓ hδ0 hδ1 hK
  nlinarith [h, pow_pos hℓ 3]

/-- `δ^K ℓ³ (ℓ^{2N})⁻¹ ((max 3 ℓ⁻¹)^{2N-3})⁻¹ ≤ 1`: the whole far-lattice row is bounded by
the constant `1`, uniformly in `ℓ` and `δ`. -/
lemma powEll_inv_mul_inv_le_one {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {K N : ℕ} (hN3 : 3 ≤ 2 * N) :
    δ ^ K * ℓ ^ 3 * ((ℓ ^ (2 * N))⁻¹ * (((max 3 ℓ⁻¹) ^ (2 * N - 3))⁻¹)) ≤ 1 := by
  have hδK : δ ^ K ≤ 1 := pow_le_one₀ hδ0.le hδ1
  have hℓU1 : 1 ≤ ℓ * max 3 ℓ⁻¹ := by
    rw [ell_mul_max_eq hℓ]; exact le_max_right _ _
  have h3 : ℓ ^ 3 * (ℓ ^ (2 * N))⁻¹ = (ℓ ^ (2 * N - 3))⁻¹ := pow3_mul_inv_pow_eq hℓ hN3
  have hA : ℓ ^ 3 * (ℓ ^ (2 * N))⁻¹ * ((max 3 ℓ⁻¹) ^ (2 * N - 3))⁻¹
      = ((ℓ * max 3 ℓ⁻¹) ^ (2 * N - 3))⁻¹ := by
    rw [h3, ← mul_inv, ← mul_pow]
  have hB : ((ℓ * max 3 ℓ⁻¹) ^ (2 * N - 3))⁻¹ ≤ 1 :=
    inv_pow_le_one_of_one_le hℓU1 _
  rw [mul_assoc, ← mul_assoc (ℓ ^ 3), hA]
  exact mul_le_one₀ hδK (by positivity) hB

/-- In the regime `ℓ ≤ 1`: `ℓ³ (1 + max 3 ℓ⁻¹)³ ≤ 4³ = 64`, because `ℓ(1 + max 3 ℓ⁻¹) =
`ℓ + max (3ℓ) 1 ≤ 1 + 3`. -/
lemma ell_cube_mul_one_add_max_cube_le {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) :
    ℓ ^ 3 * (1 + max 3 ℓ⁻¹) ^ 3 ≤ 64 := by
  have h : ℓ * (1 + max 3 ℓ⁻¹) ≤ 4 := by
    rw [mul_add, mul_one, ell_mul_max_eq hℓ]
    have : max (3 * ℓ) 1 ≤ 3 := max_le (by linarith) (by norm_num)
    linarith
  have h4 : 0 ≤ ℓ * (1 + max 3 ℓ⁻¹) := by positivity
  calc ℓ ^ 3 * (1 + max 3 ℓ⁻¹) ^ 3 = (ℓ * (1 + max 3 ℓ⁻¹)) ^ 3 := by rw [mul_pow]
    _ ≤ 4 ^ 3 := pow_le_pow_left₀ h4 h 3
    _ = 64 := by norm_num

end Work.BoseBoxFock.PCFU
