import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.H2.Transport3Aux.power_hardy_boundary
import Submission.Work.FTS.EllipticEst.UopHk.powerHardyFinite

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The weighted Hardy inequality on an interval bounded away from `0`.**

For `c > -1`, `0 < ε < b` and `f` of class `C¹` on `[ε,b]`,

  `∫_ε^b f² x^c ≤ 4/(c+1)² ∫_ε^b (f')² x^{c+2} + 2/(c+1) f(b)² b^{c+1}`.

This is the same inequality as `Work.FTS.H2.Transport3Aux.power_hardy_boundary`, but with the
lower endpoint `0` replaced by `ε > 0`; the only difference is that the lower boundary term
`-f(ε)² ε^{c+1}` (which is non-positive, hence harmless) is kept rather than discarded, and
that no limiting argument at `0` is needed: the fundamental theorem of calculus is applied
directly on `[ε,b]`.

Writing `φ(t) = f(t)² t^{c+1}`, one has `φ'(t) = 2 f f' t^{c+1} + (c+1) f² t^c` on `(ε,b)`, so
`(c+1)∫_ε^b f² t^c = f(b)²b^{c+1} - f(ε)²ε^{c+1} - 2∫_ε^b f f' t^{c+1}`.  The pointwise
weighted arithmetic--geometric mean inequality
`2|f f'| t^{c+1} ≤ (c+1)/2 f² t^c + 2/(c+1) (f')² t^{c+2}` then bounds the cross term. -/
theorem power_hardy_interval {c ε b : ℝ} (hc : -1 < c) (hε : 0 < ε) (hεb : ε < b) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc ε b)) :
    (∫ x in Set.Ioc ε b, (f x) ^ 2 * x ^ c)
      ≤ 4 / (c + 1) ^ 2 * (∫ x in Set.Ioc ε b, (deriv f x) ^ 2 * x ^ (c + 2))
        + 2 / (c + 1) * (f b) ^ 2 * b ^ (c + 1) := by
  have hc1 : 0 < c + 1 := by linarith
  rw [← intervalIntegral.integral_of_le hεb.le, ← intervalIntegral.integral_of_le hεb.le]
  -- ## Step 1: continuity and integrability of the three integrands
  have hcontf : ContinuousOn f (Set.Icc ε b) := hf.continuousOn
  have hdcont : ContinuousOn (derivWithin f (Set.Icc ε b)) (Set.Icc ε b) :=
    hf.continuousOn_derivWithin (uniqueDiffOn_Icc hεb) le_rfl
  have hrpow : ∀ r : ℝ, ContinuousOn (fun t : ℝ => t ^ r) (Set.Icc ε b) := fun r =>
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le hε ht.1)))
  have mkII : ∀ {G : ℝ → ℝ}, ContinuousOn G (Set.Icc ε b) → IntervalIntegrable G volume ε b :=
    fun {G} hG => ContinuousOn.intervalIntegrable (show ContinuousOn G (Set.uIcc ε b) from by
      rw [Set.uIcc_of_le hεb.le]; exact hG)
  -- on `(ε,b]` the derivatives `deriv f` and `derivWithin f (Icc ε b)` may differ only at `b`
  have hb_ae : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), t ≠ b := by
    rw [MeasureTheory.ae_iff]
    simp
  have hae_deriv' : ∀ᵐ t ∂(volume.restrict (Set.Ioc ε b)),
      deriv f t = derivWithin f (Set.Icc ε b) t := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hb_ae] with t htb ht
    have ht' : t ∈ Set.Ioo ε b := ⟨ht.1, lt_of_le_of_ne ht.2 htb⟩
    exact (derivWithin_of_mem_nhds
      (mem_of_superset (Ioo_mem_nhds ht'.1 ht'.2) Set.Ioo_subset_Icc_self)).symm
  have hae_deriv : (fun t : ℝ => deriv f t)
      =ᵐ[volume.restrict (Set.Ioc ε b)] (fun t : ℝ => derivWithin f (Set.Icc ε b) t) :=
    hae_deriv'
  have hI1 : IntervalIntegrable (fun t : ℝ => f t ^ 2 * t ^ c) volume ε b :=
    mkII ((hcontf.pow 2).mul (hrpow c))
  have hI2' : IntervalIntegrable (fun t : ℝ => (derivWithin f (Set.Icc ε b) t) ^ 2 * t ^ (c + 2))
      volume ε b := mkII ((hdcont.pow 2).mul (hrpow (c + 2)))
  have hI2 : IntervalIntegrable (fun t : ℝ => (deriv f t) ^ 2 * t ^ (c + 2)) volume ε b := by
    refine hI2'.congr_ae ?_
    rw [Set.uIoc_of_le hεb.le]
    change ∀ᵐ t ∂(volume.restrict (Set.Ioc ε b)),
      (derivWithin f (Set.Icc ε b) t) ^ 2 * t ^ (c + 2) = (deriv f t) ^ 2 * t ^ (c + 2)
    filter_upwards [hae_deriv'] with t ht
    rw [ht]
  have hI3' : IntervalIntegrable
      (fun t : ℝ => f t * derivWithin f (Set.Icc ε b) t * t ^ (c + 1)) volume ε b :=
    mkII ((hcontf.mul hdcont).mul (hrpow (c + 1)))
  have hI3 : IntervalIntegrable (fun t : ℝ => f t * deriv f t * t ^ (c + 1)) volume ε b := by
    refine hI3'.congr_ae ?_
    rw [Set.uIoc_of_le hεb.le]
    change ∀ᵐ t ∂(volume.restrict (Set.Ioc ε b)),
      f t * derivWithin f (Set.Icc ε b) t * t ^ (c + 1) = f t * deriv f t * t ^ (c + 1)
    filter_upwards [hae_deriv'] with t ht
    rw [ht]
  -- ## Step 2: the fundamental theorem of calculus for `φ t = f t ^ 2 * t ^ (c+1)`
  have hφcont : ContinuousOn (fun s : ℝ => f s ^ 2 * s ^ (c + 1)) (Set.Icc ε b) :=
    (hcontf.pow 2).mul (hrpow (c + 1))
  have hφderiv : ∀ x ∈ Set.Ioo ε b, HasDerivAt (fun s : ℝ => f s ^ 2 * s ^ (c + 1))
      (2 * (f x * deriv f x * x ^ (c + 1)) + (c + 1) * (f x ^ 2 * x ^ c)) x := by
    intro x hx
    have hnhds : Set.Icc ε b ∈ 𝓝 x :=
      mem_of_superset (Ioo_mem_nhds hx.1 hx.2) Set.Ioo_subset_Icc_self
    have hd : HasDerivAt f (deriv f x) x :=
      (hf.contDiffAt hnhds).differentiableAt_one.hasDerivAt
    have h1 : HasDerivAt (fun s : ℝ => f s ^ 2) (2 * f x ^ 1 * deriv f x) x := hd.pow 2
    have h2 : HasDerivAt (fun s : ℝ => s ^ (c + 1)) ((c + 1) * x ^ ((c + 1) - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl (lt_trans hε hx.1).ne')
    have h3 := h1.mul h2
    rw [show (c + 1) - 1 = c by ring] at h3
    refine h3.congr_deriv ?_
    ring
  have hφint : IntervalIntegrable
      (fun t : ℝ => 2 * (f t * deriv f t * t ^ (c + 1)) + (c + 1) * (f t ^ 2 * t ^ c))
      volume ε b := (hI3.const_mul 2).add (hI1.const_mul (c + 1))
  have hFTC : ∫ t in ε..b,
      (2 * (f t * deriv f t * t ^ (c + 1)) + (c + 1) * (f t ^ 2 * t ^ c))
      = f b ^ 2 * b ^ (c + 1) - f ε ^ 2 * ε ^ (c + 1) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hεb.le hφcont hφderiv hφint
  -- ## Step 3: notation
  set A : ℝ := ∫ t in ε..b, f t ^ 2 * t ^ c with hAdef
  set B : ℝ := ∫ t in ε..b, (deriv f t) ^ 2 * t ^ (c + 2) with hBdef
  set S : ℝ := ∫ t in ε..b, f t * deriv f t * t ^ (c + 1) with hSdef
  set L : ℝ := ∫ t in ε..b, |f t * deriv f t * t ^ (c + 1)| with hLdef
  have hsplit : (∫ t in ε..b,
      (2 * (f t * deriv f t * t ^ (c + 1)) + (c + 1) * (f t ^ 2 * t ^ c)))
      = 2 * S + (c + 1) * A := by
    rw [intervalIntegral.integral_add (hI3.const_mul 2) (hI1.const_mul (c + 1)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hSdef, hAdef]
  -- ## Step 4: the identity `(c+1) A = f b ^ 2 * b ^ (c+1) - f ε ^ 2 * ε ^ (c+1) - 2 S`
  have hAB : (c + 1) * A = f b ^ 2 * b ^ (c + 1) - f ε ^ 2 * ε ^ (c + 1) - 2 * S := by
    rw [hsplit] at hFTC
    linarith
  have hSL : |S| ≤ L := by
    rw [hSdef, hLdef]
    exact intervalIntegral.abs_integral_le_integral_abs hεb.le
  -- ## Step 5: the weighted arithmetic--geometric mean inequality
  have hpt : ∀ t ∈ Set.Ioo ε b,
      2 * |f t * deriv f t * t ^ (c + 1)|
        ≤ (c + 1) / 2 * (f t ^ 2 * t ^ c)
          + 2 / (c + 1) * ((deriv f t) ^ 2 * t ^ (c + 2)) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans hε ht.1
    have hta : 0 ≤ t ^ c := Real.rpow_nonneg ht0.le c
    have hpow1 : t ^ (c + 1) = t ^ c * t := by
      rw [Real.rpow_add ht0 c 1, Real.rpow_one]
    have hpow2 : t ^ (c + 2) = t ^ c * t ^ 2 := by
      rw [Real.rpow_add ht0 c 2, Real.rpow_two]
    have hL : |f t * deriv f t * (t ^ c * t)| = (|f t| * |deriv f t| * t) * t ^ c := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hta, abs_of_pos ht0]
      ring
    have hkey : 4 * (c + 1) * (|f t| * |deriv f t| * t)
        ≤ (c + 1) ^ 2 * f t ^ 2 + 4 * (deriv f t) ^ 2 * t ^ 2 := by
      have htwo := two_mul_le_add_sq ((c + 1) * |f t|) (2 * |deriv f t| * t)
      have hfa : |f t| ^ 2 = f t ^ 2 := sq_abs (f t)
      have hga : |deriv f t| ^ 2 = (deriv f t) ^ 2 := sq_abs (deriv f t)
      nlinarith [htwo, hfa, hga]
    have hred : 2 * (|f t| * |deriv f t| * t)
        ≤ (c + 1) / 2 * f t ^ 2 + 2 / (c + 1) * ((deriv f t) ^ 2 * t ^ 2) := by
      have hc2 : (0 : ℝ) < 2 * (c + 1) := by linarith
      refine le_of_mul_le_mul_right ?_ hc2
      have h1 : ((c + 1) / 2 * f t ^ 2 + 2 / (c + 1) * ((deriv f t) ^ 2 * t ^ 2))
          * (2 * (c + 1)) = (c + 1) ^ 2 * f t ^ 2 + 4 * (deriv f t) ^ 2 * t ^ 2 := by
        field_simp
        ring
      have h2 : 2 * (|f t| * |deriv f t| * t) * (2 * (c + 1))
          = 4 * (c + 1) * (|f t| * |deriv f t| * t) := by ring
      rw [h1, h2]
      exact hkey
    rw [hpow1, hpow2, hL]
    have hmul := mul_le_mul_of_nonneg_right hred hta
    nlinarith [hmul]
  -- ## Step 6: integrate the pointwise bound
  have hIL : IntervalIntegrable (fun t : ℝ => 2 * |f t * deriv f t * t ^ (c + 1)|)
      volume ε b := (hI3.abs).const_mul 2
  have hIR : IntervalIntegrable (fun t : ℝ =>
      (c + 1) / 2 * (f t ^ 2 * t ^ c) + 2 / (c + 1) * ((deriv f t) ^ 2 * t ^ (c + 2)))
      volume ε b :=
    (hI1.const_mul ((c + 1) / 2)).add (hI2.const_mul (2 / (c + 1)))
  have hAMGM : 2 * L ≤ (c + 1) / 2 * A + 2 / (c + 1) * B := by
    have h := intervalIntegral.integral_mono_on_of_le_Ioo hεb.le hIL hIR hpt
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hI1.const_mul ((c + 1) / 2)) (hI2.const_mul (2 / (c + 1))),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
    exact h
  -- ## Step 7: finish
  have hstep : (c + 1) / 2 * A ≤ f b ^ 2 * b ^ (c + 1) + 2 / (c + 1) * B := by
    have h1 : -2 * S ≤ 2 * L := by
      have h2 := neg_abs_le S
      linarith
    have hεpow : 0 ≤ f ε ^ 2 * ε ^ (c + 1) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hε.le _)
    nlinarith [hAB, h1, hAMGM, hεpow]
  have hfin : A ≤ 2 / (c + 1) * (f b ^ 2 * b ^ (c + 1)) + 4 / (c + 1) ^ 2 * B := by
    have hc2 : (0 : ℝ) < (c + 1) / 2 := by linarith
    have h1 : A * ((c + 1) / 2) ≤ f b ^ 2 * b ^ (c + 1) + 2 / (c + 1) * B := by linarith
    have h2 := (le_div_iff₀ hc2).2 h1
    have h3 : (f b ^ 2 * b ^ (c + 1) + 2 / (c + 1) * B) / ((c + 1) / 2)
        = 2 / (c + 1) * (f b ^ 2 * b ^ (c + 1)) + 4 / (c + 1) ^ 2 * B := by
      field_simp
      ring
    rw [h3] at h2
    exact h2
  have hgoal : 2 / (c + 1) * (f b ^ 2 * b ^ (c + 1)) + 4 / (c + 1) ^ 2 * B
      = 4 / (c + 1) ^ 2 * B + 2 / (c + 1) * (f b) ^ 2 * b ^ (c + 1) := by ring
  linarith [hfin, hgoal]

end Work.FTS.StrongPersist.N6Trans.SixRoute
