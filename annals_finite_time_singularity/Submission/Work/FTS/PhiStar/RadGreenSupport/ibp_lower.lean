/-
# `Work.FTS.PhiStar.RadGreenSupport.ibp_lower`

The Euler integration by parts behind the explicit radial Green's function
`Work.FTS.PhiStar.Radial.radGreen` (see `Radial/Defs.lean`): for `c` of class `C²` on `(0,∞)`
whose derivatives decay as in `hb`, and with `s := (2m+5)/α`,

  `∫_0^z (α t² c''(t) + (5+α) t c'(t)) · t^{s-1} dt
     = α z^{s+1} c'(z) − 2m z^s c(z) + 2ms ∫_0^z c(t) t^{s-1} dt`.

This is the `0..z` half of the two integration-by-parts identities that turn the Green
representation into the ODE `-α²z²a'' - α(5+α)z a' + λ_m a = c` (`ibp_upper` is the `Ioi z`
half).

Proof: both sides are the evaluation at `z` of the primitive

  `F(t) = α t^{s+1} c'(t) − 2m t^s c(t) + 2ms ∫_0^t c(u) u^{s-1} du`,

because `F'(t)` equals the integrand (uses `α s = 2m+5`), `F(0⁺) = 0` (the derivatives of `c`
are bounded by `A`), and the remaining integral is exactly the last term of the right-hand
side.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.PhiStar.RadGreenSupport.contDiffOn_two_regularity
import Submission.Work.FTS.PhiStar.RadGreenSupport.ioc_bounded_integrable
import Submission.Work.FTS.PhiStar.RadGreenSupport.tendsto_rpow_mul_bounded

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.PhiStar.RadGreenSupport

open MeasureTheory Set Filter

theorem ibp_lower {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hc : ContDiffOn ℝ 2 c (Set.Ioi 0))
    (hb : ∀ k : ℕ, k ≤ 2 → ∀ t : ℝ, 0 < t → |iteratedDeriv k c t| ≤ A / (1 + t ^ (k + 1)))
    {z : ℝ} (hz : 0 < z) :
    ∫ t in (0 : ℝ)..z,
        (α * t ^ 2 * iteratedDeriv 2 c t + (5 + α) * t * deriv c t)
          * t ^ ((2 * (m : ℝ) + 5) / α - 1)
      = α * z ^ ((2 * (m : ℝ) + 5) / α + 1) * deriv c z
        - 2 * (m : ℝ) * z ^ ((2 * (m : ℝ) + 5) / α) * c z
        + 2 * (m : ℝ) * ((2 * (m : ℝ) + 5) / α)
            * ∫ t in (0 : ℝ)..z, c t * t ^ ((2 * (m : ℝ) + 5) / α - 1) := by
  set s : ℝ := (2 * (m : ℝ) + 5) / α with hs
  have hαne : α ≠ 0 := ne_of_gt hα
  have hsdef : α * s = 2 * (m : ℝ) + 5 := by
    rw [hs]
    field_simp
    try ring
  have hnum : 0 < 2 * (m : ℝ) + 5 := by
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hspos : 0 < s := by
    rw [hs]
    exact div_pos hnum hα
  -- ## Elementary bounds from `hb`
  have hc_le : ∀ t : ℝ, 0 < t → |c t| ≤ A / (1 + t) := by
    intro t ht
    simpa only [iteratedDeriv_zero, Nat.zero_add, pow_one] using hb 0 (by norm_num) t ht
  have hc1_le : ∀ t : ℝ, 0 < t → |deriv c t| ≤ A / (1 + t ^ 2) := by
    intro t ht
    simpa only [iteratedDeriv_one] using hb 1 (by norm_num) t ht
  have hc2_le : ∀ t : ℝ, 0 < t → |iteratedDeriv 2 c t| ≤ A / (1 + t ^ 3) := by
    intro t ht
    exact hb 2 le_rfl t ht
  have hdiv_le : ∀ B d : ℝ, 0 ≤ B → 1 ≤ d → B / d ≤ B := by
    intro B d hB hd
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < d)]
    nlinarith [hB, hd]
  have hc_bd : ∀ t : ℝ, 0 < t → |c t| ≤ A := fun t ht =>
    le_trans (hc_le t ht) (hdiv_le A (1 + t) hA (by linarith))
  have hc1_bd : ∀ t : ℝ, 0 < t → |deriv c t| ≤ A := fun t ht =>
    le_trans (hc1_le t ht) (hdiv_le A (1 + t ^ 2) hA (by have := sq_nonneg t; linarith))
  have hc2_bd : ∀ t : ℝ, 0 < t → |iteratedDeriv 2 c t| ≤ A := fun t ht =>
    le_trans (hc2_le t ht) (hdiv_le A (1 + t ^ 3) hA (by have := pow_nonneg ht.le 3; linarith))
  -- ## Regularity of `c`, `c'`, `c''` on `(0,∞)`
  obtain ⟨hcont_c, hcont_d1, hcont_d2, hd_c, hd_dc⟩ := contDiffOn_two_regularity hc
  -- ## The primitive and its derivative
  let F : ℝ → ℝ := fun t => α * (t ^ (s + 1) * deriv c t) + (-(2 * (m : ℝ))) * (t ^ s * c t)
  let G : ℝ → ℝ := fun t =>
    (α * t ^ 2 * iteratedDeriv 2 c t + (5 + α) * t * deriv c t) * t ^ (s - 1)
      - (2 * (m : ℝ) * s) * (c t * t ^ (s - 1))
  have hder : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt F (G t) t := by
    intro t ht
    have ht0 : 0 < t := ht
    have hp1 : HasDerivAt (fun v : ℝ => v ^ (s + 1)) ((s + 1) * t ^ (s + 1 - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht0))
    have hp2 : HasDerivAt (fun v : ℝ => v ^ s) (s * t ^ (s - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht0))
    have hm1 : HasDerivAt (fun v : ℝ => v ^ (s + 1) * deriv c v)
        (((s + 1) * t ^ (s + 1 - 1)) * deriv c t + t ^ (s + 1) * iteratedDeriv 2 c t) t :=
      hp1.mul (hd_dc t ht0)
    have hm2 : HasDerivAt (fun v : ℝ => v ^ s * c v)
        ((s * t ^ (s - 1)) * c t + t ^ s * deriv c t) t :=
      hp2.mul (hd_c t ht0)
    have h3 := (hm1.const_mul α).add (hm2.const_mul (-(2 * (m : ℝ))))
    have hF : HasDerivAt F
        (α * (((s + 1) * t ^ (s + 1 - 1)) * deriv c t + t ^ (s + 1) * iteratedDeriv 2 c t)
          + (-(2 * (m : ℝ))) * ((s * t ^ (s - 1)) * c t + t ^ s * deriv c t)) t := by
      refine h3.congr_of_eventuallyEq ?_
      filter_upwards with y
      simp only [F, Pi.add_apply]
    refine hF.congr_deriv ?_
    have ht1 : t ^ (s + 1 - 1) = t ^ s :=
      congr_arg (fun e : ℝ => t ^ e) (show s + 1 - 1 = s by ring)
    have ht2 : t ^ (s + 1) = t ^ (2 : ℝ) * t ^ (s - 1) := by
      rw [show s + 1 = (2 : ℝ) + (s - 1) by ring, Real.rpow_add ht0]
    have ht3 : t ^ s = t * t ^ (s - 1) := by
      calc t ^ s = t ^ ((1 : ℝ) + (s - 1)) :=
            congr_arg (fun e : ℝ => t ^ e) (show s = (1 : ℝ) + (s - 1) by ring)
        _ = t ^ 1 * t ^ (s - 1) := Real.rpow_add ht0 1 (s - 1)
        _ = t * t ^ (s - 1) := by simp only [Real.rpow_one]
    simp only [G]
    rw [ht1, ht2, ht3]
    rw [show t ^ 2 = t ^ (2 : ℝ) from (Real.rpow_natCast t 2).symm]
    linear_combination (t * t ^ (s - 1) * deriv c t) * hsdef
  -- ## Interval integrability of the two summands
  have hcont_sum : ContinuousOn
      (fun t : ℝ => α * t ^ 2 * iteratedDeriv 2 c t + (5 + α) * t * deriv c t) (Set.Ioi 0) := by
    have h1 : ContinuousOn (fun t : ℝ => α * t ^ 2) (Set.Ioi 0) :=
      (continuousOn_const (c := α)).mul (continuousOn_id.pow 2)
    have h2 : ContinuousOn (fun t : ℝ => (5 + α) * t) (Set.Ioi 0) :=
      (continuousOn_const (c := 5 + α)).mul continuousOn_id
    have h3 : ContinuousOn (fun t : ℝ => α * t ^ 2 * iteratedDeriv 2 c t) (Set.Ioi 0) :=
      h1.mul hcont_d2
    have h4 : ContinuousOn (fun t : ℝ => (5 + α) * t * deriv c t) (Set.Ioi 0) :=
      h2.mul hcont_d1
    exact h3.add h4
  have hbnd_sum : ∀ t : ℝ, 0 < t →
      |α * t ^ 2 * iteratedDeriv 2 c t + (5 + α) * t * deriv c t| ≤ (|α| + |5 + α|) * A := by
    intro t ht
    have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
    have h12 : (0 : ℝ) < 1 + t ^ 2 := by positivity
    have h13 : (0 : ℝ) < 1 + t ^ 3 := by positivity
    have ht_sq_le : t ^ 2 ≤ 1 + t ^ 3 := by
      by_cases h : t ≤ 1
      · have h1 : 0 ≤ t * (1 - t) := mul_nonneg ht.le (by linarith)
        have h2 : 0 ≤ t ^ 3 := pow_nonneg ht.le 3
        nlinarith [h1, h2, h]
      · have h1 : 0 ≤ t ^ 2 * (t - 1) := mul_nonneg (sq_nonneg t) (by linarith [not_le.mp h])
        nlinarith [h1]
    have e1 : t ^ 2 * |iteratedDeriv 2 c t| ≤ A := by
      calc t ^ 2 * |iteratedDeriv 2 c t| ≤ t ^ 2 * (A / (1 + t ^ 3)) :=
            mul_le_mul_of_nonneg_left (hc2_le t ht) ht2
        _ = A * t ^ 2 / (1 + t ^ 3) := by ring
        _ ≤ A := by
            rw [div_le_iff₀ h13]
            exact mul_le_mul_of_nonneg_left ht_sq_le hA
    have e2 : t * |deriv c t| ≤ A := by
      have hle : t ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg (2 * t - 1)]
      calc t * |deriv c t| ≤ t * (A / (1 + t ^ 2)) :=
            mul_le_mul_of_nonneg_left (hc1_le t ht) ht.le
        _ = A * t / (1 + t ^ 2) := by ring
        _ ≤ A := by
            rw [div_le_iff₀ h12]
            exact mul_le_mul_of_nonneg_left hle hA
    have eabs1 : |α * t ^ 2 * iteratedDeriv 2 c t| = |α| * (t ^ 2 * |iteratedDeriv 2 c t|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg ht2]
      ring
    have eabs2 : |(5 + α) * t * deriv c t| = |5 + α| * (t * |deriv c t|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg ht.le]
      ring
    calc |α * t ^ 2 * iteratedDeriv 2 c t + (5 + α) * t * deriv c t|
        ≤ |α * t ^ 2 * iteratedDeriv 2 c t| + |(5 + α) * t * deriv c t| := abs_add_le _ _
      _ = |α| * (t ^ 2 * |iteratedDeriv 2 c t|) + |5 + α| * (t * |deriv c t|) := by
            rw [eabs1, eabs2]
      _ ≤ |α| * A + |5 + α| * A :=
            add_le_add (mul_le_mul_of_nonneg_left e1 (abs_nonneg α))
              (mul_le_mul_of_nonneg_left e2 (abs_nonneg (5 + α)))
      _ = (|α| + |5 + α|) * A := by ring
  have hIA : IntervalIntegrable
      (fun t : ℝ => (α * t ^ 2 * iteratedDeriv 2 c t + (5 + α) * t * deriv c t) * t ^ (s - 1))
      volume (0 : ℝ) z :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le).2
      (ioc_bounded_integrable
        (f := fun t : ℝ => α * t ^ 2 * iteratedDeriv 2 c t + (5 + α) * t * deriv c t)
        (r := s) (z := z) (B := (|α| + |5 + α|) * A) hspos hz
        (mul_nonneg (add_nonneg (abs_nonneg α) (abs_nonneg (5 + α))) hA) hcont_sum hbnd_sum)
  have hIB : IntervalIntegrable (fun t : ℝ => (2 * (m : ℝ) * s) * (c t * t ^ (s - 1)))
      volume (0 : ℝ) z :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le).2
      (ioc_bounded_integrable (f := c) (r := s) (z := z) (B := A) hspos hz hA hcont_c
        hc_bd)).const_mul (2 * (m : ℝ) * s)
  have hInt : IntervalIntegrable G volume (0 : ℝ) z := by
    simpa only [G] using hIA.sub hIB
  -- ## The limit of the primitive at `0⁺` and at `z`
  have hF0 : Tendsto F (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h1 := tendsto_rpow_mul_bounded (f := deriv c) (r := s + 1) (B := A)
      (by linarith) hA hc1_bd
    have h2 := tendsto_rpow_mul_bounded (f := c) (r := s) (B := A) hspos hA hc_bd
    have h3 : Tendsto
        (fun t : ℝ => α * (t ^ (s + 1) * deriv c t) + (-(2 * (m : ℝ))) * (t ^ s * c t))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have h := (Filter.Tendsto.const_mul α h1).add
        (Filter.Tendsto.const_mul (-(2 * (m : ℝ))) h2)
      simpa only [mul_zero, add_zero] using h
    simpa only [F] using h3
  have hFz : Tendsto F (nhdsWithin z (Set.Iio z)) (nhds (F z)) :=
    (hder z hz).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  -- ## The fundamental theorem of calculus
  have hFTC : ∫ t in (0 : ℝ)..z, G t = F z := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hz
      (fun t ht => hder t ht.1) hInt hF0 hFz
    simpa only [sub_zero] using h
  have hsplit : ∫ t in (0 : ℝ)..z, G t
      = (∫ t in (0 : ℝ)..z,
            (α * t ^ 2 * iteratedDeriv 2 c t + (5 + α) * t * deriv c t) * t ^ (s - 1))
        - (2 * (m : ℝ) * s) * (∫ t in (0 : ℝ)..z, c t * t ^ (s - 1)) := by
    simp only [G]
    rw [intervalIntegral.integral_sub hIA hIB, intervalIntegral.integral_const_mul]
  have hfin : (∫ t in (0 : ℝ)..z,
          (α * t ^ 2 * iteratedDeriv 2 c t + (5 + α) * t * deriv c t) * t ^ (s - 1))
      = F z + (2 * (m : ℝ) * s) * (∫ t in (0 : ℝ)..z, c t * t ^ (s - 1)) := by
    rw [hFTC] at hsplit
    linarith [hsplit]
  rw [hfin]
  simp only [F]
  ring

end Work.FTS.PhiStar.RadGreenSupport
