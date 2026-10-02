import Mathlib
import Submission.Work.ParamRays.Basic
import Submission.Work.ParamRays.Green
import Submission.Work.ParamRays.Bottcher
import Submission.Work.ParamRays.IsDynBottcher_norm_div
import Submission.Work.ParamRays.greenSeq_tendsto_greenFun

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ParamRays

open Filter
open scoped Real Topology ComplexConjugate

/-! # The modulus of a Böttcher coordinate is the exponential of the Green function

The Böttcher equation `φ (T_c z) = conj (φ z) ^ 2` iterated gives
`‖φ (T_c^[2n] z)‖ = ‖φ z‖ ^ (4 ^ n)`, so for every `n`

`log ‖φ z‖ = 4^{-n} log ‖φ (T_c^[2n] z)‖`.

Since `φ w / w → 1` as `w → ∞`, the right-hand side differs from
`4^{-n} log ‖T_c^[2n] z‖` by a term which tends to `0`; the sequence
`greenSeq c z n = 2^{-n} log⁺ ‖T_c^[n] z‖` converges to `greenFun c z` because `z`
escapes (`Work.ParamRays.greenSeq_tendsto_greenFun`), and its even subsequence is
exactly `4^{-n} log ‖T_c^[2n] z‖` for large `n`.  Hence
`log ‖φ z‖ = greenFun c z`, and exponentiating (with `‖φ z‖ ≠ 0`, which follows
from the functional equation and the asymptotic) gives the claim. -/

/-- The modulus of a Böttcher coordinate is the exponential of the Green function.

Route: `IsDynBottcher.functional_iterate` gives `‖φ (orbit c z (2n))‖ = ‖φ z‖ ^ (4^n)`, so
`‖φ z‖ = ‖φ (orbit c z (2n))‖ ^ (4^n)⁻¹`, and `‖φ w‖ / ‖w‖ → 1` at infinity (cocompact).
Hence `log ‖φ z‖ = lim 4⁻ⁿ log ‖orbit c z (2n)‖`, and the even (and, with one extra estimate,
the odd) subsequence of `greenSeq` converges to that limit, which is `greenFun c z`. -/
theorem IsDynBottcher_modulus {c : ℂ} {φ : ℂ → ℂ} (h : Work.ParamRays.IsDynBottcher c φ)
    {z : ℂ} (hz : Work.ParamRays.Escaping c z) :
    ‖φ z‖ = Real.exp (Work.ParamRays.greenFun c z) := by
  -- the even-indexed orbit points, and the ratio of the `φ`-image to the point
  have h2n : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun b =>
      ⟨b, fun a ha => le_trans ha (Nat.le_mul_of_pos_left a (by norm_num))⟩)
  -- the whole sequence converges to the Green function
  have hconv := greenSeq_tendsto_greenFun c z hz
  -- `‖φ (T_c^[2n] z)‖ / ‖T_c^[2n] z‖ → 1`
  have hratio : Tendsto (fun n : ℕ => ‖φ (orbit c z (2*n))‖ / ‖orbit c z (2*n)‖)
      atTop (nhds 1) := (IsDynBottcher_norm_div h hz).comp h2n
  have hlogr : Tendsto (fun n : ℕ => Real.log (‖φ (orbit c z (2*n))‖ / ‖orbit c z (2*n)‖))
      atTop (nhds 0) := by
    have h1 := hratio.log (by norm_num : (1 : ℝ) ≠ 0)
    simpa using h1
  have hinv4 : Tendsto (fun n : ℕ => ((4 : ℝ) ^ n)⁻¹) atTop (nhds 0) :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4)).inv_tendsto_atTop
  have hprod : Tendsto (fun n : ℕ =>
      ((4 : ℝ) ^ n)⁻¹ * Real.log (‖φ (orbit c z (2*n))‖ / ‖orbit c z (2*n)‖))
      atTop (nhds 0) := by
    simpa using hinv4.mul hlogr
  -- large orbits and positive `φ`-images
  have hden : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ ‖orbit c z (2*n)‖ := by
    have h := h2n.eventually (hz.eventually_gt 1)
    filter_upwards [h] with n hn using le_of_lt hn
  have hrat1 : ∀ᶠ n : ℕ in atTop,
      (1/2 : ℝ) ≤ ‖φ (orbit c z (2*n))‖ / ‖orbit c z (2*n)‖ :=
    hratio.eventually (eventually_ge_nhds (by norm_num : (1/2 : ℝ) < 1))
  have hnum : ∀ᶠ n : ℕ in atTop, 0 < ‖φ (orbit c z (2*n))‖ := by
    filter_upwards [hrat1, hden] with n hn hd
    have hdpos : 0 < ‖orbit c z (2*n)‖ := by linarith
    have h3 : 0 < (‖φ (orbit c z (2*n))‖ / ‖orbit c z (2*n)‖) * ‖orbit c z (2*n)‖ :=
      mul_pos (by linarith) hdpos
    rwa [div_mul_cancel₀ _ (ne_of_gt hdpos)] at h3
  -- the key asymptotic identity for the even subsequence of `greenSeq`
  have hkey : ∀ᶠ n : ℕ in atTop, greenSeq c z (2*n) =
      Real.log ‖φ z‖ -
        ((4 : ℝ) ^ n)⁻¹ * Real.log (‖φ (orbit c z (2*n))‖ / ‖orbit c z (2*n)‖) := by
    filter_upwards [hden, hnum] with n hdenn hnumn
    have hdne : ‖orbit c z (2*n)‖ ≠ 0 := by
      have : (0 : ℝ) < ‖orbit c z (2*n)‖ := by linarith
      exact ne_of_gt this
    have hnumne : ‖φ (orbit c z (2*n))‖ ≠ 0 := ne_of_gt hnumn
    have hfun : ‖φ (orbit c z (2*n))‖ = ‖φ z‖ ^ (4^n) := by
      rw [h.functional_iterate hz n, norm_pow]
    have hlognum : Real.log ‖φ (orbit c z (2*n))‖ = (4 : ℝ)^n * Real.log ‖φ z‖ := by
      rw [hfun, Real.log_pow, Nat.cast_pow]
      norm_num
    have hlogden : Real.log ‖orbit c z (2*n)‖ = Real.log ‖φ (orbit c z (2*n))‖ -
        Real.log (‖φ (orbit c z (2*n))‖ / ‖orbit c z (2*n)‖) := by
      have h := Real.log_div hnumne hdne
      linarith
    have hpow : ((2 : ℝ) ^ (2*n))⁻¹ = ((4 : ℝ) ^ n)⁻¹ := by
      rw [pow_mul]; norm_num
    rw [greenSeq, hpow,
      Real.posLog_eq_log (by rw [abs_of_nonneg (norm_nonneg _)]; exact hdenn),
      hlogden, hlognum]
    field_simp
  have heven : Tendsto (fun n : ℕ => greenSeq c z (2*n)) atTop (nhds (Real.log ‖φ z‖)) := by
    have h1 : Tendsto (fun n : ℕ => Real.log ‖φ z‖ -
        ((4 : ℝ) ^ n)⁻¹ * Real.log (‖φ (orbit c z (2*n))‖ / ‖orbit c z (2*n)‖))
        atTop (nhds (Real.log ‖φ z‖ - 0)) := tendsto_const_nhds.sub hprod
    simpa using h1.congr' (Filter.EventuallyEq.symm hkey)
  have hsub : Tendsto (fun n : ℕ => greenSeq c z (2*n)) atTop (nhds (greenFun c z)) :=
    hconv.comp h2n
  -- the Green function is `log ‖φ z‖`
  have hEq : greenFun c z = Real.log ‖φ z‖ := tendsto_nhds_unique hsub heven
  have hpos : 0 < ‖φ z‖ := by
    obtain ⟨n, hn⟩ := hnum.exists
    have hfun0 : ‖φ (orbit c z (2*n))‖ = ‖φ z‖ ^ (4^n) := by
      rw [h.functional_iterate hz n, norm_pow]
    have h1 : 0 < ‖φ z‖ ^ (4^n) := by rwa [hfun0] at hn
    have hx0 : ‖φ z‖ ≠ 0 := by
      intro hzero
      rw [hzero, zero_pow (by positivity : 4^n ≠ 0)] at h1
      exact absurd h1 (lt_irrefl 0)
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx0)
  rw [hEq, Real.exp_log hpos]

end Work.ParamRays
