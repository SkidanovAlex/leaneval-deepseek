/-
Copyright: work module for the Elgindi finite-time singularity project.

# Auxiliary estimates for `SpecialTransport`

This file collects the analytic material needed by the proof of Elgindi's Proposition
`SpecialTransport` (§`H2`, tex 1126):

* the elementary `θ`-facts (`sin (2θ) ≥ (4/π) min (θ) (π/2 - θ)` on `Iθ`,
  `intervalIntegrability` of `sin (2θ)^p` for `p > -1`);
* the fundamental theorem of calculus in `θ` for the `θ`-slices of a function which is
  smooth on the open strip and continuous on the closed quadrant (`ftc_pth`), which is
  what turns `f` into `sin (2θ)` times a bounded function;
* the pointwise bounds `ST_f_bounds` on `f`, its `D_z`-derivatives and on the derivatives
  of `f / sin (2θ)`, all in terms of `|∂_θ f|_{𝒲^{4,∞}}`;
* the one-dimensional integration by parts `ibp_lead` which removes the `θ`-derivative
  from the second factor of the leading terms;
* the `L²` product Cauchy–Schwarz estimate `L2Sq_prod_le` for iterated integrals.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.H2.Defs
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.ProductTools
import Submission.Work.Spaces.cs_integral
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.pz_aux
import Submission.Work.Spaces.mixed_mul_eq
import Submission.Work.Spaces.sin_rpow_le_majorant
import Submission.Work.Spaces.integrableOn_majorant_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary `θ`-facts -/

theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sin_two_pos_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- On `Iθ`, `sin (2θ)` dominates `(4/π) · min θ (π/2 - θ)`. -/
theorem sin_two_ge_min (θ : ℝ) (hθ : θ ∈ Spaces.Iθ) :
    (4 / π) * min θ (π / 2 - θ) ≤ Real.sin (2 * θ) := by
  obtain ⟨h0, h1⟩ := hθ
  have hpi := Real.pi_pos
  rcases le_total θ (π / 4) with h | h
  · have hmin : min θ (π / 2 - θ) = θ := by
      refine min_eq_left ?_
      linarith
    rw [hmin]
    have h2 : (2 / π) * (2 * θ) ≤ Real.sin (2 * θ) := by
      refine Real.mul_le_sin (by linarith) ?_
      linarith
    have he : (2 / π) * (2 * θ) = (4 / π) * θ := by ring
    rw [he] at h2; exact h2
  · have hmin : min θ (π / 2 - θ) = π / 2 - θ := by
      refine min_eq_right ?_
      linarith
    rw [hmin]
    have hsin : Real.sin (2 * θ) = Real.sin (2 * (π / 2 - θ)) := by
      rw [show 2 * (π / 2 - θ) = π - 2 * θ by ring, Real.sin_pi_sub]
    rw [hsin]
    have h2 : (2 / π) * (2 * (π / 2 - θ)) ≤ Real.sin (2 * (π / 2 - θ)) := by
      refine Real.mul_le_sin (by linarith) ?_
      linarith
    have he : (2 / π) * (2 * (π / 2 - θ)) = (4 / π) * (π / 2 - θ) := by ring
    rw [he] at h2; exact h2

/-- `sin (2θ)^p` is interval integrable on `[0, π/2]` for `p > -1`. -/
theorem intervalIntegrable_sin_rpow (p : ℝ) (hp : -1 < p) :
    IntervalIntegrable (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) volume 0 (π / 2) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : (0:ℝ) ≤ π / 2)]
  by_cases hp0 : 0 ≤ p
  · -- nonnegative exponent: bounded by `1`
    refine MeasureTheory.Integrable.mono' (MeasureTheory.integrableOn_const
      (s := Set.Icc (0:ℝ) (π/2)) (C := (1:ℝ)) ?_) ?_ ?_
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    · exact ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const p).aestronglyMeasurable
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      have h0 := sin_two_nonneg_Iθ hθ
      rw [Real.norm_of_nonneg (Real.rpow_nonneg h0 p)]
      exact Real.rpow_le_one h0 (Real.sin_le_one _) hp0
  · -- negative exponent: compare with the explicit majorant
    push_neg at hp0
    have hq : 0 < -p := by linarith
    have hmaj := Work.Spaces.integrableOn_majorant_rpow (-p) hq (by linarith)
    refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
    · exact ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const p).aestronglyMeasurable
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      have h0 := sin_two_nonneg_Iθ hθ
      rw [Real.norm_of_nonneg (Real.rpow_nonneg h0 p)]
      have h4 := Work.Spaces.sin_rpow_le_majorant (-p) θ hq hθ
      simpa only [neg_neg] using h4

/-- Any function dominated on `Iθ` by `C · sin (2θ)^p` with `p > -1` is interval integrable
on `[0, π/2]`. -/
theorem intervalIntegrable_of_sin_bound {f : ℝ → ℝ} {C p : ℝ} (hp : -1 < p)
    (hmeas : AEStronglyMeasurable f (volume.restrict (Set.Icc 0 (π / 2))))
    (h : ∀ θ ∈ Spaces.Iθ, |f θ| ≤ C * (Real.sin (2 * θ)) ^ p) :
    IntervalIntegrable f volume 0 (π / 2) := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [Real.pi_pos] : (0:ℝ) ≤ π/2)]
  have hmaj : MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p)
      (Set.Icc 0 (π / 2)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [Real.pi_pos] : (0:ℝ) ≤ π/2)).mp
      (intervalIntegrable_sin_rpow p hp)
  exact MeasureTheory.Integrable.mono' (hmaj.const_mul C) hmeas
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc h)

/-- `sin (2θ)^p → 0` as `θ → 0` from the right, for `p > 0`. -/
theorem tendsto_sin_rpow_zero_right (p : ℝ) (hp : 0 < p) :
    Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) (𝓝[>] 0) (𝓝 0) := by
  have h0p : (0 : ℝ) ^ p = 0 := Real.zero_rpow (ne_of_gt hp)
  have h2 : Tendsto (fun θ : ℝ => 2 * θ) (𝓝[>] 0) (𝓝 0) := by
    have h3 : Tendsto (fun θ : ℝ => 2 * θ) (𝓝 0) (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul tendsto_id : Tendsto (fun θ : ℝ => 2 * θ) (𝓝 0) (𝓝 (2 * 0)))
    exact h3.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun θ : ℝ => (2 * θ) ^ p) (𝓝[>] 0) (𝓝 0) := by
    have hc := (Real.continuousAt_rpow_const (0 : ℝ) p (Or.inr hp.le)).tendsto.comp h2
    simpa [Function.comp_def, h0p] using hc
  refine squeeze_zero' ?_ ?_ h1
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0:ℝ) < π / 4 by positivity)]
      with θ hθ hlt
    exact Real.rpow_nonneg (sin_two_nonneg_Iθ ⟨le_of_lt hθ, by linarith [hlt.2, Real.pi_pos]⟩) p
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0:ℝ) < π / 4 by positivity)]
      with θ hθ hlt
    have hθI : θ ∈ Spaces.Iθ := ⟨le_of_lt hθ, by linarith [hlt.2, Real.pi_pos]⟩
    exact Real.rpow_le_rpow (sin_two_nonneg_Iθ hθI) (Real.sin_le (by linarith [hlt.1])) hp.le

/-- `sin (2θ)^p → 0` as `θ → π/2` from the left, for `p > 0`. -/
theorem tendsto_sin_rpow_zero_left (p : ℝ) (hp : 0 < p) :
    Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) (𝓝[<] (π / 2)) (𝓝 0) := by
  have hcomp : Tendsto (fun θ : ℝ => π / 2 - θ) (𝓝[<] (π / 2)) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h3 : Tendsto (fun θ : ℝ => π / 2 - θ) (𝓝 (π / 2)) (𝓝 0) := by
        simpa using (tendsto_const_nhds.sub tendsto_id :
          Tendsto (fun θ : ℝ => π / 2 - θ) (𝓝 (π / 2)) (𝓝 (π / 2 - π / 2)))
      exact h3.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with θ hθ
      show (0:ℝ) < π / 2 - θ
      have := Set.mem_Iio.mp hθ
      linarith
  have h := (tendsto_sin_rpow_zero_right p hp).comp hcomp
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  simp only [Function.comp_apply]
  rw [show 2 * (π / 2 - θ) = π - 2 * θ by ring, Real.sin_pi_sub]

/-- `θ ↦ sin (2θ)^p` is differentiable at `θ ∈ (0, π/2)` with derivative
`2 cos (2θ) · p · sin (2θ)^(p-1)`. -/
theorem hasDerivAt_sin_rpow (p θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ p)
      (2 * Real.cos (2 * θ) * p * (Real.sin (2 * θ)) ^ (p - 1)) θ := by
  have hs : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
    have h1 : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2:ℝ)
    have h2 := (Real.hasDerivAt_sin (2 * θ)).comp θ h1
    simpa [Function.comp_def, mul_comm] using h2
  have hne : Real.sin (2 * θ) ≠ 0 := ne_of_gt (sin_two_pos_of_Ioo hθ)
  exact hs.rpow_const (p := p) (Or.inl hne)

/-- The derivative of `θ ↦ sin (2θ)^(-e)` on `(0, π/2)`. -/
theorem hasDerivAt_sin_rpow_neg (e θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ (-e))
      (2 * Real.cos (2 * θ) * (-e) * (Real.sin (2 * θ)) ^ (-e - 1)) θ :=
  hasDerivAt_sin_rpow (-e) θ hθ

end Work.FTS.H2
