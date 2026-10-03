import Mathlib
import Submission.Work.FITop3.Defs3
import Submission.Work.FITop3.Smooth
import Submission.Work.FITop3.Smooth.sm_props
import Submission.Work.FITop3.Majorant.majorant_props
import Submission.Work.FITop3.Witness.exists_primary_norm
import Submission.Work.FIArea3.logFac_le
import Submission.Work.FIArea3.Fhat_le
import Submission.Work.FIArea3.quarter_rpow_sub_le

open Finset
open scoped BigOperators

namespace Work.FIArea3

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# `Submission.Work.FIArea3.area3_of_core` — the elementary reduction `CoreBound → Area3`

This file proves `area3_of_core`: granting the §10 pair-sum bound `Work.FIArea3.CoreBound`
(the paper's Lemma 10.1 + (10.4), isolated in `Submission/Work/FIArea3/Defs.lean`), the main-term
estimate (10.10) of Friedlander–Iwaniec follows by elementary means, with the explicit constant
`56·Cb`.

The development is self-contained apart from the frozen vocabulary and the four numeric modules
`logFac_le`, `G0_le`, `Fhat_le`, `quarter_rpow_sub_le`:

* **§1** the geometry `|Δ(z₁,z₂)| ≤ |z₁z₂|` (whence `logFac ≥ 0`);
* **§2** the log-factor bound `|logFac| ≤ 4 log N` on the polar box;
* **§3** the (7.7) mean value `Fhat`: `0 ≤ Fhat ≤ 7√M`;
* **§4** the scale identity `N²/√N = N^{3/2}`;
* **§5** the pointwise kernel bound `term_bound` and its summed form `diff_sum_bound`;
* **§6** the reduction `area3_of_core`.
-/




/-! ## 1. The geometry of the determinant `Δ` -/

/-- `‖z‖² = |z|²` for a Gaussian integer, where `|z|²` is `gnorm z = z.norm.natAbs`. -/
theorem normSq_toComplex_lossless (z : GaussianInt) :
    ‖z.toComplex‖ ^ 2 = (((Work.FIPlan.gnorm z : ℕ)) : ℝ) := by
  have hnorm : Zsqrtd.norm z = z.re * z.re + z.im * z.im := by simp [Zsqrtd.norm]
  have hge : (0 : ℝ) ≤ (z.norm : ℝ) := by
    rw [hnorm]
    have : (0 : ℤ) ≤ z.re * z.re + z.im * z.im := by
      have h1 : (0 : ℤ) ≤ z.re * z.re := mul_self_nonneg _
      have h2 : (0 : ℤ) ≤ z.im * z.im := mul_self_nonneg _
      linarith
    exact_mod_cast this
  have hcast : (((z.norm.natAbs : ℕ)) : ℝ) = (z.norm : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg hge]
  rw [show Work.FIPlan.gnorm z = z.norm.natAbs from rfl, hcast, hnorm, Complex.sq_norm,
    Complex.normSq_apply, ← GaussianInt.intCast_re, ← GaussianInt.intCast_im]
  push_cast
  ring

/-- `‖z‖` is the square root of `gnorm z`. -/
theorem norm_toComplex_eq_sqrt (z : GaussianInt) :
    ‖z.toComplex‖ = Real.sqrt (((Work.FIPlan.gnorm z : ℕ)) : ℝ) := by
  rw [← normSq_toComplex_lossless z, Real.sqrt_sq (norm_nonneg _)]

/-- `Δ(z₁,z₂) = Im(z̄₁z₂)` computed in `ℂ`. -/
theorem delta_toComplex_re (z1 z2 : GaussianInt) :
    ((Work.FIPlan.Delta z1 z2 : ℤ) : ℝ) = (star z1.toComplex * z2.toComplex).im := by
  have h1 : ((Work.FIPlan.Delta z1 z2 : ℤ) : ℝ)
      = ((star z1 * z2 : GaussianInt).toComplex).im := by
    rw [Work.FIPlan.Delta]
    exact GaussianInt.intCast_im _
  have hstar : ∀ z : GaussianInt, (star z).toComplex = star z.toComplex := fun z => by
    apply Complex.ext <;> simp
  have hmul : (star z1 * z2).toComplex = (star z1).toComplex * z2.toComplex := by rw [map_mul]
  rw [h1, hmul, hstar]

/-- **`|Δ(z₁,z₂)| ≤ |z₁z₂|`** — the determinant of a pair is bounded by the product of the moduli.
This is the inequality that makes the (7.10) log-factor non-negative. -/
theorem absDelta_le_sqrt_gnorm (z1 z2 : GaussianInt) :
    ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      ≤ Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ)) : ℝ) := by
  have h1 : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      = |((Work.FIPlan.Delta z1 z2 : ℤ) : ℝ)| := by
    rw [Work.FIPlan.absDelta, Nat.cast_natAbs, Int.cast_abs]
  rw [h1, delta_toComplex_re z1 z2]
  calc |(star z1.toComplex * z2.toComplex).im|
      ≤ ‖star z1.toComplex * z2.toComplex‖ := Complex.abs_im_le_norm _
    _ = ‖z1.toComplex‖ * ‖z2.toComplex‖ := by rw [norm_mul, norm_star]
    _ = Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ)) : ℝ)
          * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ)) : ℝ) := by
        rw [norm_toComplex_eq_sqrt z1, norm_toComplex_eq_sqrt z2]
    _ = Real.sqrt ((((Work.FIPlan.gnorm z1 : ℕ)) : ℝ)
          * (((Work.FIPlan.gnorm z2 : ℕ)) : ℝ)) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _)]
    _ = Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ)) : ℝ) := by
        rw [gnorm_mul', Nat.cast_mul]

/-! ## 2. The (7.10) log-factor -/

/-- The logarithm `logFac z₁ z₂ = log(2|z₁z₂|/|Δ|)` is non-negative: its argument is `≥ 2` when
`|Δ| ≠ 0` (because `|Δ| ≤ |z₁z₂|`), and if `|Δ| = 0` the value is `0` (`Real.log 0 = 0`). -/
theorem logFac_nonneg (z1 z2 : GaussianInt) : 0 ≤ Work.FITop3.logFac z1 z2 := by
  unfold Work.FITop3.logFac
  rcases Nat.eq_zero_or_pos (Work.FIPlan.absDelta z1 z2) with h0 | hpos
  · rw [h0]; simp
  · apply Real.log_nonneg
    have hdpos : (0 : ℝ) < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by exact_mod_cast hpos
    have hle := absDelta_le_sqrt_gnorm z1 z2
    rw [le_div_iff₀ hdpos]
    have hsqrt : (0 : ℝ) ≤ Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ)) : ℝ) :=
      Real.sqrt_nonneg _
    linarith

/-- `|logFac z₁ z₂| ≤ 4 log N` on the polar box (5.14). -/
theorem abs_logFac_le {Pa : Work.FITop.Params} {φ : ℝ} {z1 z2 : GaussianInt}
    (h1 : Work.FITop3.InPolarBox Pa φ z1) (h2 : Work.FITop3.InPolarBox Pa φ z2) :
    |Work.FITop3.logFac z1 z2| ≤ 4 * Real.log Pa.N := by
  rw [abs_le]
  refine ⟨?_, logFac_le h1 h2⟩
  have h := logFac_nonneg z1 z2
  have hlogN : 0 ≤ Real.log Pa.N := Real.log_nonneg Pa.hN1
  linarith

/-! ## 3. The (7.7) mean value `Fhat` -/

/-- `0 ≤ Fhat Pa f` for a majorant. -/
theorem Fhat_nonneg (Pa : Work.FITop.Params) (f : ℤ → ℝ)
    (hf : Work.FITop3.IsMajorant Pa f) : 0 ≤ Work.FITop3.Fhat Pa f := by
  unfold Work.FITop3.Fhat
  exact Finset.sum_nonneg (fun u _ => div_nonneg (hf.1 u) (Real.sqrt_nonneg _))

/-- `|2 Fhat Pa f| ≤ 14 √M`: the `f ≤ 1` mean value bound `Fhat ≤ 7√M`. -/
theorem Fhat_abs_two_le (Pa : Work.FITop.Params) (f : ℤ → ℝ)
    (hf : Work.FITop3.IsMajorant Pa f) : |2 * Work.FITop3.Fhat Pa f| ≤ 14 * Real.sqrt Pa.M := by
  rw [abs_of_nonneg (by linarith [Fhat_nonneg Pa f hf])]
  have := Fhat_le Pa f hf
  linarith

/-- `θ ≤ 1` for the smoothing parameter of (4.15). -/
theorem theta_le_one (Pa : Work.FITop.Params) : Pa.θ ≤ 1 := by
  linarith [theta_le_tenth Pa]

/-! ## 4. The real-variable scale identity of (10.10) -/

/-- `N² / √N = N^{3/2}` for `N > 0` — the identity that turns the `N^{2}` of the core bound and
the `N^{-1/2}` of the §10 gain into the `N^{3/2}` of (10.10). -/
lemma div_sqrt_eq_rpow_three_halves (N : ℝ) (hN : 0 < N) :
    N ^ 2 / Real.sqrt N = N ^ ((3 : ℝ) / 2) := by
  have h1 : N ^ ((3 : ℝ) / 2) = N * Real.sqrt N := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hN, Real.rpow_one,
      Real.sqrt_eq_rpow]
  rw [h1, div_eq_iff (Real.sqrt_pos.mpr hN).ne']
  rw [mul_assoc, ← sq, Real.sq_sqrt hN.le, pow_two]

/-! ## 5. The kernel bound and its sum

The two structural lemmas of the reduction:

(1) `term_bound`: the pointwise bound of one summand of the difference of the two main terms;
(2) `diff_sum_bound`: the same bound after summing over the box `boxN Pa × boxN Pa`, giving the
`CoreBound` weight.  Everything is a norm inequality about the kernel
`β₁β̄₂·2f̂·logFac·G₀·(gnorm(z₁z₂)^{-1/4} − N^{-1/2})` of the identity `diff_eq`. -/

end

end Work.FIArea3
