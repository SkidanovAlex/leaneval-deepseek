import Mathlib
import Submission.Work.FITop3.Defs3
import Submission.Work.FITop3.Smooth
import Submission.Work.FITop3.Smooth.sm_props
import Submission.Work.FITop3.Majorant.majorant_props
import Submission.Work.FITop3.Witness.exists_primary_norm
import Submission.Work.FIArea6.elem_helpers

/-!
# `Work.FIArea6.UcutMod_pair_bound` — the elementary pair-level bound for `U(β)`

The triangle inequality in `UcutMod` reduces `‖U(β)‖` to a sum over *pairs* `(z₁,z₂)` of the
product `‖β z₁‖‖β z₂‖` times the absolute value of the `d`-sum of a single pair.  Two elementary
facts control that `d`-sum:

* `|logFac z₁ z₂| ≤ log(4N) + 1` on `|zᵢ|² ≤ 2N` (`logFac_abs_leU`);
* `Σ_{d ≤ M} 1/d ≤ 1 + log M` (`harmonic_sum_le`).

Together with `|φ(d)/d| ≤ 1`, `|χ_d| ≤ 1` and the sector constraint `|Δ| ≤ 4πθN` they give

  `‖UcutMod Rz X β‖ ≤ 128 (log (2+N))² (Σ_{z ∈ boxN} ‖β z‖)²`.

This is `O((log N)²)` per pair, i.e. it avoids any pointwise `τ(Δ/4)` loss; combined with a bound
on the *mass* `Σ ‖β z‖` (which is where the annular divisor-sum input enters) it yields the
elementary estimate for `U(β)`.
-/

set_option autoImplicit false

namespace Work.FIArea6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Elementary Gaussian facts -/

/-- `gnorm z = |z|²` for a Gaussian integer, as the norm-square of the complex number. -/
lemma gnorm_eq_normSqU (z : GaussianInt) :
    Complex.normSq (z : ℂ) = ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by
  rw [Work.FIPlan.gnorm, Nat.cast_natAbs,
    abs_of_nonneg (by exact_mod_cast GaussianInt.norm_nonneg z), GaussianInt.intCast_real_norm]

/-- `gnorm` is multiplicative. -/
lemma gnorm_mulU (z w : GaussianInt) :
    Work.FIPlan.gnorm (z * w) = Work.FIPlan.gnorm z * Work.FIPlan.gnorm w := by
  simp only [Work.FIPlan.gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]

/-- `‖z‖_ℂ = √|z|²`. -/
lemma norm_toComplex_eq_sqrtU (z : GaussianInt) :
    ‖(z : ℂ)‖ = Real.sqrt (((Work.FIPlan.gnorm z : ℕ) : ℝ)) := by
  rw [← gnorm_eq_normSqU z, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- **`|Δ(z₁,z₂)| ≤ |z₁z₂|`.** -/
lemma absDelta_le_sqrt_gnormU (z1 z2 : GaussianInt) :
    ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      ≤ Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) := by
  have h1 : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      = |((Work.FIPlan.Delta z1 z2 : ℤ) : ℝ)| := by
    rw [Work.FIPlan.absDelta, Nat.cast_natAbs, Int.cast_abs]
  have him : ((Work.FIPlan.Delta z1 z2 : ℤ) : ℝ) = (star (z1 : ℂ) * (z2 : ℂ)).im := by
    have h : ((star z1 * z2 : GaussianInt) : ℂ) = star (z1 : ℂ) * (z2 : ℂ) := by
      rw [GaussianInt.toComplex_mul, GaussianInt.toComplex_star]; simp
    rw [Work.FIPlan.Delta, GaussianInt.intCast_im, h]
  calc ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      = |(star (z1 : ℂ) * (z2 : ℂ)).im| := by rw [h1, him]
    _ ≤ ‖star (z1 : ℂ) * (z2 : ℂ)‖ := Complex.abs_im_le_norm _
    _ = ‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖ := by rw [norm_mul, norm_star]
    _ = Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ))
          * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ)) := by
        rw [norm_toComplex_eq_sqrtU, norm_toComplex_eq_sqrtU]
    _ = Real.sqrt ((((Work.FIPlan.gnorm z1 : ℕ) : ℝ) * ((Work.FIPlan.gnorm z2 : ℕ) : ℝ))) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _)]
    _ = Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) := by
        rw [gnorm_mulU, Nat.cast_mul]

/-- If `|zᵢ|² ≤ 2N` (with `1 ≤ N`) then `|z₁z₂| ≤ 2N`. -/
lemma sqrt_gnorm_mul_leU (N : ℝ) (hN : 1 ≤ N) (z1 z2 : GaussianInt)
    (hg1 : (Work.FIPlan.gnorm z1 : ℝ) ≤ 2 * N)
    (hg2 : (Work.FIPlan.gnorm z2 : ℝ) ≤ 2 * N) :
    Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) ≤ 2 * N := by
  have h2N : 0 ≤ 2 * N := by linarith
  have h1 : Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ)) ≤ Real.sqrt (2 * N) :=
    Real.sqrt_le_sqrt hg1
  have h2 : Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ)) ≤ Real.sqrt (2 * N) :=
    Real.sqrt_le_sqrt hg2
  calc Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
      = Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ))
          * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ)) := by
        rw [gnorm_mulU, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
    _ ≤ Real.sqrt (2 * N) * Real.sqrt (2 * N) :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = 2 * N := by
        rw [← Real.sqrt_mul h2N, show 2 * N * (2 * N) = (2 * N) ^ 2 by ring, Real.sqrt_sq h2N]

/-- Two-sided bound for the (7.10) logarithm at scale `N`: `|logFac z₁ z₂| ≤ log(4N) + 1`. -/
lemma logFac_abs_leU (N : ℝ) (hN : 1 ≤ N) (z1 z2 : GaussianInt)
    (hg1 : (Work.FIPlan.gnorm z1 : ℝ) ≤ 2 * N)
    (hg2 : (Work.FIPlan.gnorm z2 : ℝ) ≤ 2 * N) :
    |Work.FITop3.logFac z1 z2| ≤ Real.log (4 * N) + 1 := by
  have hNpos : 0 < N := by linarith
  have hlog4 : 0 ≤ Real.log (4 * N) := Real.log_nonneg (by linarith)
  have hsqrt := sqrt_gnorm_mul_leU N hN z1 z2 hg1 hg2
  rcases Nat.eq_zero_or_pos (Work.FIPlan.absDelta z1 z2) with h0 | hpos
  · have hz : Work.FITop3.logFac z1 z2 = 0 := by
      unfold Work.FITop3.logFac
      rw [h0]; simp
    rw [hz, abs_zero]; linarith
  · have hΔ1 : (1 : ℝ) ≤ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by exact_mod_cast hpos
    have hΔpos : 0 < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by linarith
    have hge : 1 ≤ 2 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
        / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by
      rw [le_div_iff₀ hΔpos]
      linarith [absDelta_le_sqrt_gnormU z1 z2]
    have hstep : 2 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
        / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
        ≤ 2 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) := by
      rw [div_le_iff₀ hΔpos]
      nlinarith [Real.sqrt_nonneg (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)), hΔ1]
    have hle : 2 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
        / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ≤ 4 * N := le_trans hstep (by linarith)
    have hargpos : 0 < 2 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
        / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by linarith
    rw [show Work.FITop3.logFac z1 z2
        = Real.log (2 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
            / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) from rfl,
      abs_of_nonneg (Real.log_nonneg hge)]
    calc Real.log (2 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
          / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) ≤ Real.log (4 * N) :=
          Real.log_le_log hargpos hle
      _ ≤ Real.log (4 * N) + 1 := by linarith


/-! ## 2. The harmonic sum `Σ_{d ≤ M} 1/d ≤ 1 + log M` -/

lemma one_div_succ_le_log_sub (n : ℕ) (hn : 1 ≤ n) :
    (((n:ℝ)) + 1)⁻¹ ≤ Real.log ((n:ℝ) + 1) - Real.log (n:ℝ) := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have h1 : 1 - ((((n:ℝ)+1)/n))⁻¹ ≤ Real.log (((n:ℝ)+1)/n) :=
    Real.one_sub_inv_le_log_of_pos (by positivity)
  have h2 : ((((n:ℝ)+1)/n))⁻¹ = (n:ℝ)/((n:ℝ)+1) := by rw [inv_div]
  have h3 : 1 - (n:ℝ)/((n:ℝ)+1) = (((n:ℝ)+1))⁻¹ := by field_simp; ring
  have h4 : Real.log (((n:ℝ)+1)/n) = Real.log ((n:ℝ)+1) - Real.log n :=
    Real.log_div (by positivity) (by positivity)
  rw [h2, h3, h4] at h1
  exact h1

lemma harmonic_sum_le (m : ℕ) :
    ∑ e ∈ Finset.Icc 1 m, (((e:ℕ):ℝ))⁻¹ ≤ 1 + Real.log (m : ℝ) := by
  induction m with
  | zero => simp
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0; simp
      · rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
        have hstep := one_div_succ_le_log_sub n hpos
        have hcast : (((n+1:ℕ)):ℝ) = (n:ℝ) + 1 := by push_cast; ring
        rw [hcast]
        linarith [ih]

end

end Work.FIArea6
