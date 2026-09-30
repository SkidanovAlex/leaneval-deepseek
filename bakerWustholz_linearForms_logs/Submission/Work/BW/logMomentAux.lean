import Mathlib
import Submission.Work.BW.fejer_cos_sum_ge
import Submission.Work.BW.log_norm_exp_sub_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary definitions and Fejér estimates for the Blanksby–Montgomery second moment bound

This file prepares the two analytic ingredients of `Work.BW.logMoment_sq_ge`:

* the Fourier coefficients `logCoeff ε m = ε^(m+1)/(m+1)` of `log ‖1 - ε e^{iφ}‖` and the
  associated frequencies `logFreq θ m = (m+1) * 2πθ`;
* the Fejér kernel estimates: for any real frequency `x`,
  `∑_{k=1}^{K} w_k cos (k x) ≥ -1/2`, and consequently
  `∑_k w_k cos (k x) cos (k y) + 1/2 ≥ 0` and `∑_k w_k cos (k x)^2 + 1/2 ≥ (K+1)/4`,
  where `w k = 1 - k/(K+1)` is the Fejér weight.

The Fejér weight is called `lmW` here; it is the same function as `Work.BW.fejerW` of
`Submission.Work.BW.mahlerDefs`, written out separately so that this file (and hence every
lemma proved on top of it) does not depend on that module.
-/

open scoped BigOperators
open Finset

namespace Work.BW

/-- The Fejér weight `w k = 1 - k/(K+1)` (same function as `Work.BW.fejerW`). -/
noncomputable def lmW (K k : ℕ) : ℝ := 1 - (k : ℝ) / ((K : ℝ) + 1)

/-- The `m`-th Fourier coefficient of `log ‖1 - ε e^{iφ}‖` in its power series expansion,
namely `ε^(m+1)/(m+1)`. -/
noncomputable def logCoeff (ε : ℝ) (m : ℕ) : ℝ := ε ^ (m + 1) / ((m : ℝ) + 1)

/-- The frequency attached to `logCoeff ε m` when the phase is `2πkθ`: it is `(m+1) * 2πθ`,
so that the cosine arising from the `m`-th coefficient and the `k`-th sample is
`cos (k * logFreq θ m)`. -/
noncomputable def logFreq (θ : ℝ) (m : ℕ) : ℝ := ((m : ℝ) + 1) * (2 * Real.pi * θ)

/-- The `j`-th cosine series `∑_m logCoeff (ε j) m * cos (k * logFreq (θ j) m)`, which is
the negative of `log ‖1 - ε_j exp (2πi k θ_j)‖`. -/
noncomputable def Lfun {n : ℕ} (ε θ : Fin n → ℝ) (j : Fin n) (k : ℕ) : ℝ :=
  ∑' m, logCoeff (ε j) m * Real.cos ((k : ℝ) * logFreq (θ j) m)

/-- The total mass `∑_m logCoeff (ε j) m = log (1/(1 - ε j))`. -/
noncomputable def Afun {n : ℕ} (ε : Fin n → ℝ) (j : Fin n) : ℝ := ∑' m, logCoeff (ε j) m

/-- The squared mass `∑_m (logCoeff (ε j) m)^2 = dilog (ε_j^2)`. -/
noncomputable def Dfun {n : ℕ} (ε : Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑' m, (logCoeff (ε j) m) ^ 2

/-- `logCoeff ε m ≥ 0` for `ε ≥ 0`. -/
lemma logCoeff_nonneg (ε : ℝ) (h0 : 0 ≤ ε) (m : ℕ) : 0 ≤ logCoeff ε m := by
  rw [logCoeff]
  positivity


/-- The pointwise identity behind the dilogarithm term:
`(logCoeff ε m)^2 = (ε^2)^(m+1)/(m+1)^2`. -/
lemma logCoeff_sq_eq (ε : ℝ) (m : ℕ) :
    (logCoeff ε m) ^ 2 = (ε ^ 2) ^ (m + 1) / ((m : ℝ) + 1) ^ 2 := by
  rw [logCoeff, div_pow]
  have h : (ε ^ (m + 1)) ^ 2 = (ε ^ 2) ^ (m + 1) := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [h]

/-- The squared Fourier coefficients are exactly the terms of the dilogarithm series
`dilog (ε^2) = ∑' m, (ε^2)^(m+1)/(m+1)^2`. -/
lemma logCoeff_sq_tsum (ε : ℝ) :
    ∑' m, (logCoeff ε m) ^ 2 = ∑' m : ℕ, (ε ^ 2) ^ (m + 1) / ((m : ℝ) + 1) ^ 2 :=
  tsum_congr (fun m => logCoeff_sq_eq ε m)

/-- `logCoeff ε` is summable for `0 ≤ ε < 1`. -/
lemma logCoeff_summable (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε < 1) : Summable (logCoeff ε) := by
  have hgeo : Summable (fun m : ℕ => ε ^ (m + 1)) := by
    have h2 : Summable (fun m : ℕ => ε ^ m) := by
      rw [summable_geometric_iff_norm_lt_one, Real.norm_eq_abs, abs_of_nonneg h0]
      exact h1
    simpa [pow_succ'] using h2.mul_left ε
  refine Summable.of_norm_bounded hgeo (fun m => ?_)
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have h1m : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (m : ℝ) := by positivity
    linarith
  rw [Real.norm_eq_abs, logCoeff, abs_div, abs_of_pos hm, abs_pow, abs_of_nonneg h0,
    div_le_iff₀ hm]
  nlinarith [pow_nonneg h0 (m + 1)]

/-- The squared Fourier coefficients are summable for `0 ≤ ε < 1`. -/
lemma logCoeff_sq_summable (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε < 1) :
    Summable (fun m => (logCoeff ε m) ^ 2) := by
  have hgeo : Summable (fun m : ℕ => (ε ^ 2) ^ m) := by
    rw [summable_geometric_iff_norm_lt_one, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_lt_one₀ h0 h1 (by norm_num)
  have h2 : Summable (fun m : ℕ => (ε ^ 2) ^ (m + 1)) := by
    have heq : (fun m : ℕ => (ε ^ 2) ^ (m + 1)) = fun m : ℕ => (ε ^ 2) * (ε ^ 2) ^ m := by
      funext m
      rw [pow_succ']
    rw [heq]
    exact hgeo.mul_left (ε ^ 2)
  refine Summable.of_norm_bounded h2 (fun m => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), logCoeff_sq_eq ε m,
    div_le_iff₀ (by positivity : (0 : ℝ) < ((m : ℝ) + 1) ^ 2)]
  have h1m : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ 2 := by
    have : (1 : ℝ) ≤ (m : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (m : ℝ) := by positivity
      linarith
    nlinarith
  nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 2) (m + 1)]

/-- The Fourier series of `log ‖1 - ε e^{iφ}‖` at `φ = 0`: `∑_m logCoeff ε m = log (1/(1-ε))`. -/
lemma logCoeff_tsum (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε < 1) :
    ∑' m, logCoeff ε m = Real.log (1 / (1 - ε)) := by
  have h := log_norm_exp_sub_one ε h0 h1 0
  have hkey : Real.log ‖(ε : ℂ) - 1‖ = -∑' m, logCoeff ε m := by
    rw [show (ε : ℂ) - 1 = (ε : ℂ) * Complex.exp (Complex.I * ((0 : ℝ) : ℂ)) - 1 by simp]
    rw [h]
    congr 1
    apply tsum_congr
    intro m
    rw [logCoeff]
    simp
  have hnorm : ‖(ε : ℂ) - 1‖ = 1 - ε := by
    rw [show (ε : ℂ) - 1 = ((ε - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_neg (by linarith)]
    ring
  rw [hnorm] at hkey
  have h2 : Real.log (1 / (1 - ε)) = -Real.log (1 - ε) := by
    rw [one_div, Real.log_inv]
  rw [h2, hkey]
  ring

/-- `∑_{i<K} i = K(K-1)/2`, over the reals. -/
theorem sum_range_cast (K : ℕ) :
    ∑ i ∈ Finset.range K, (i : ℝ) = (K : ℝ) * ((K : ℝ) - 1) / 2 := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- `∑_{k=1}^{K} k = K(K+1)/2`, over the reals. -/
theorem sum_Icc_one_cast (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, (k : ℝ) = (K : ℝ) * ((K : ℝ) + 1) / 2 := by
  rw [← Finset.Ico_succ_right_eq_Icc (1 : ℕ) K, show Order.succ K = K + 1 from by simp]
  rw [Finset.sum_Ico_eq_sum_range (fun k => (k : ℝ)) 1 (K + 1)]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, sum_range_cast]
  simp only [nsmul_eq_mul, mul_one]
  ring

/-- The Fejér weights `w k = 1 - k/(K+1)` have total mass `K/2`. -/
theorem lmW_sum (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, lmW K k = (K : ℝ) / 2 := by
  have hcs : (∑ k ∈ Finset.Icc 1 K, (1 : ℝ)) = (K : ℝ) := by
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  simp only [lmW]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, hcs, sum_Icc_one_cast]
  have hK : ((K : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- Reduction of the phase: `2π k (x/(2π)) = k x`, so the corresponding cosines agree. -/
theorem cos_two_pi_mul_div (k x : ℝ) :
    Real.cos (2 * Real.pi * k * (x / (2 * Real.pi))) = Real.cos (k * x) := by
  congr 1
  have h2π : (2 * Real.pi) ≠ 0 := by positivity
  calc 2 * Real.pi * k * (x / (2 * Real.pi))
      = k * ((2 * Real.pi) * (2 * Real.pi)⁻¹) * x := by rw [div_eq_mul_inv]; ring
    _ = k * 1 * x := by rw [mul_inv_cancel₀ h2π]
    _ = k * x := by ring

/-- **Fejér kernel bound** for an arbitrary real frequency: the Fejér-weighted cosine sum is
at least `-1/2`. -/
theorem fejer_cos_sum_ge' (K : ℕ) (x : ℝ) :
    -(1 / 2 : ℝ) ≤ ∑ k ∈ Finset.Icc 1 K, lmW K k * Real.cos ((k : ℝ) * x) := by
  have h := fejer_cos_sum_ge K (x / (2 * Real.pi))
  have hcongr : ∀ k ∈ Finset.Icc 1 K,
      (1 - (k : ℝ) / (K + 1)) * Real.cos (2 * Real.pi * k * (x / (2 * Real.pi)))
        = lmW K k * Real.cos ((k : ℝ) * x) := by
    intro k _
    simp only [lmW, cos_two_pi_mul_div]
  rwa [Finset.sum_congr rfl hcongr] at h

/-- **Fejér positivity of the cos-cos kernel**: `∑_k w_k cos (kx) cos (ky) + 1/2 ≥ 0`. -/
theorem fejer_pair_nonneg (K : ℕ) (x y : ℝ) :
    0 ≤ ∑ k ∈ Finset.Icc 1 K,
          lmW K k * (Real.cos ((k : ℝ) * x) * Real.cos ((k : ℝ) * y)) + 1 / 2 := by
  have hx := fejer_cos_sum_ge' K (x - y)
  have hy := fejer_cos_sum_ge' K (x + y)
  have hsplit : ∑ k ∈ Finset.Icc 1 K,
        lmW K k * (Real.cos ((k : ℝ) * x) * Real.cos ((k : ℝ) * y))
      = (1 / 2) * ((∑ k ∈ Finset.Icc 1 K, lmW K k * Real.cos ((k : ℝ) * (x - y)))
          + (∑ k ∈ Finset.Icc 1 K, lmW K k * Real.cos ((k : ℝ) * (x + y)))) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    have hcos : Real.cos ((k : ℝ) * x) * Real.cos ((k : ℝ) * y)
        = (Real.cos ((k : ℝ) * (x - y)) + Real.cos ((k : ℝ) * (x + y))) / 2 := by
      have h1 : Real.cos ((k : ℝ) * (x - y)) + Real.cos ((k : ℝ) * (x + y))
          = 2 * (Real.cos ((k : ℝ) * x) * Real.cos ((k : ℝ) * y)) := by
        rw [show (k : ℝ) * (x - y) = (k : ℝ) * x - (k : ℝ) * y by ring,
          show (k : ℝ) * (x + y) = (k : ℝ) * x + (k : ℝ) * y by ring,
          Real.cos_sub, Real.cos_add]
        ring
      linarith
    rw [hcos]
    ring
  rw [hsplit]
  linarith

/-- **Fejér diagonal bound**: `∑_k w_k cos (kx)^2 + 1/2 ≥ (K+1)/4`. -/
theorem fejer_sq_ge (K : ℕ) (x : ℝ) :
    ((K : ℝ) + 1) / 4
      ≤ ∑ k ∈ Finset.Icc 1 K, lmW K k * (Real.cos ((k : ℝ) * x)) ^ 2 + 1 / 2 := by
  have h := fejer_cos_sum_ge' K (2 * x)
  have hsplit : ∑ k ∈ Finset.Icc 1 K, lmW K k * (Real.cos ((k : ℝ) * x)) ^ 2
      = (1 / 2) * ((∑ k ∈ Finset.Icc 1 K, lmW K k)
          + (∑ k ∈ Finset.Icc 1 K, lmW K k * Real.cos ((k : ℝ) * (2 * x)))) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    have hcos : (Real.cos ((k : ℝ) * x)) ^ 2
        = (1 + Real.cos ((k : ℝ) * (2 * x))) / 2 := by
      rw [Real.cos_sq, show 2 * ((k : ℝ) * x) = (k : ℝ) * (2 * x) by ring]
      ring
    rw [hcos]
    ring
  rw [hsplit, lmW_sum]
  linarith

end Work.BW
