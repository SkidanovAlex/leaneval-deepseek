import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.H2.DivQ.sqIntervalIntegralLe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A one-sided Poincaré inequality on the angular slice `[0, π/2]`

For a function `u` which is `C²` on the *open* interval `(0, π/2)`, continuous on the closed
interval, and vanishes at the left endpoint `0`, we prove

  `∫_{Iθ} u² ≤ (π/2)² · ∫_{Iθ} (u')²`      (`Iθ = [0, π/2]`),

**without** assuming anything at the right endpoint `π/2` (no Dirichlet condition there, and no
smoothness beyond continuity on `[0, π/2]`).  This is the crude Poincaré estimate used to dominate
the `L²` zero-order angular term by the angular energy.

Route:

* for `θ ∈ (0, π/2)` the fundamental theorem of calculus
  (`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`, applicable because `u` is `C²` on the
  open interval and `u'` is integrable there) gives `u θ = ∫_0^θ u'`;
* hence `|u θ| ≤ ∫_0^θ |u'|`, and Cauchy–Schwarz for the interval integral
  (`Work.FTS.H2.DivQ.sqIntervalIntegralLe`) gives
  `(∫_0^θ |u'|)² ≤ θ · ∫_0^θ (u')² ≤ (π/2) · ∫_{Iθ} (u')²`;
* the resulting bound `(u θ)² ≤ (π/2) · ∫_{Iθ} (u')²` holds for every `θ ∈ (0, π/2)` and also at
  `θ = 0` (where `u = 0`), so it holds almost everywhere on `Iθ`; integrating it
  (`MeasureTheory.setIntegral_mono_on_ae`) gives the claim.

The only point of `Iθ` where the pointwise bound is not available directly is the right endpoint
`π/2`, which is a null set: the bound at that point is never needed.
-/

namespace Work.FTS.EllipticEst.Mine

open MeasureTheory Set Filter
open scoped Real Topology

set_option linter.style.haveILetI false

theorem slice_u_sq_le {u : ℝ → ℝ}
    (hC : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hcont : ContinuousOn u (Set.Icc 0 (Real.pi / 2)))
    (h0 : u 0 = 0)
    (hint : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
        ≤ (Real.pi / 2) ^ 2 * (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2) := by
  have hpi : 0 < Real.pi / 2 := by positivity
  -- energy abbreviation
  set A : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 with hA
  have hA_nonneg : 0 ≤ A := by
    rw [hA]
    exact MeasureTheory.integral_nonneg (fun θ => sq_nonneg (deriv u θ))
  have hM_nonneg : 0 ≤ (Real.pi / 2) * A := mul_nonneg hpi.le hA_nonneg
  -- integrability of `u²` on the slice
  have hu2 : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ :=
    (hcont.pow 2).integrableOn_compact isCompact_Icc
  refine ⟨hu2, ?_⟩
  -- smoothness facts
  have hderivCont : ContinuousOn (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    hC.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hDO : DifferentiableOn ℝ u (Set.Ioo 0 (Real.pi / 2)) :=
    hC.differentiableOn (by norm_num)
  -- ## Step 1: the pointwise bound on the open interval
  have hbound : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (u θ) ^ 2 ≤ (Real.pi / 2) * A := by
    intro θ hθ
    have hθle : (0 : ℝ) ≤ θ := le_of_lt hθ.1
    have hθlt : θ < Real.pi / 2 := hθ.2
    have hIcc_sub : Set.Icc 0 θ ⊆ Work.Spaces.Iθ := fun x hx => ⟨hx.1, hx.2.trans hθlt.le⟩
    have hIoo_sub : Set.Ioo 0 θ ⊆ Set.Ioo 0 (Real.pi / 2) := fun x hx => ⟨hx.1, hx.2.trans hθlt⟩
    have hIoc_sub : Set.Ioc 0 θ ⊆ Work.Spaces.Iθ := fun x hx =>
      ⟨le_of_lt hx.1, hx.2.trans hθlt.le⟩
    have hcont_sub : ContinuousOn u (Set.Icc 0 θ) := hcont.mono hIcc_sub
    have hderiv : ∀ x ∈ Set.Ioo 0 θ, HasDerivAt u (deriv u x) x := fun x hx =>
      hDO.hasDerivAt (isOpen_Ioo.mem_nhds (hIoo_sub hx))
    -- integrability of `(u')²` and of `u'` on `(0, θ]`
    have hg2Ioc : MeasureTheory.IntegrableOn (fun x => (deriv u x) ^ 2) (Set.Ioc 0 θ) :=
      hint.mono_set hIoc_sub
    have hII : IntervalIntegrable (deriv u) volume 0 θ := by
      have hAESM : AEStronglyMeasurable (deriv u) (volume.restrict (Set.Ioc 0 θ)) := by
        have h1 : AEStronglyMeasurable (deriv u) (volume.restrict (Set.Ioo 0 θ)) :=
          (hderivCont.mono hIoo_sub).aestronglyMeasurable measurableSet_Ioo
        rwa [MeasureTheory.restrict_Ioo_eq_restrict_Ioc] at h1
      haveI : IsFiniteMeasure (volume.restrict (Set.Ioc 0 θ)) :=
        ⟨by
          rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Ioc]
          exact ENNReal.ofReal_lt_top⟩
      have hmem : MemLp (deriv u) 2 (volume.restrict (Set.Ioc 0 θ)) :=
        (MeasureTheory.memLp_two_iff_integrable_sq hAESM).mpr hg2Ioc
      have hmem1 : MemLp (deriv u) 1 (volume.restrict (Set.Ioc 0 θ)) :=
        hmem.mono_exponent (by norm_num : (1 : ENNReal) ≤ 2)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hθle).mpr
        (MeasureTheory.memLp_one_iff_integrable.mp hmem1)
    -- the fundamental theorem of calculus
    have hftc : u θ = ∫ x in (0 : ℝ)..θ, deriv u x := by
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
        (f := u) (f' := deriv u) (a := 0) (b := θ) hθle hcont_sub hderiv hII
      rw [h0, sub_zero] at h
      exact h.symm
    have habs : |u θ| ≤ ∫ x in (0 : ℝ)..θ, |deriv u x| := by
      calc |u θ| = |∫ x in (0 : ℝ)..θ, deriv u x| := by rw [hftc]
        _ ≤ ∫ x in (0 : ℝ)..θ, |deriv u x| :=
            intervalIntegral.abs_integral_le_integral_abs (f := deriv u) (a := 0) (b := θ) hθle
    -- Cauchy–Schwarz for the interval integral
    have hCS : (∫ x in (0 : ℝ)..θ, |deriv u x|) ^ 2
        ≤ θ * (∫ x in (0 : ℝ)..θ, (deriv u x) ^ 2) := by
      have hf : IntervalIntegrable (fun x => |deriv u x|) volume 0 θ := hII.abs
      have hf2 : IntervalIntegrable (fun x => |deriv u x| ^ 2) volume 0 θ := by
        refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hθle).mpr ?_
        exact hg2Ioc.congr_fun (fun x _ => (sq_abs (deriv u x)).symm) measurableSet_Ioc
      have h := Work.FTS.H2.DivQ.sqIntervalIntegralLe (fun x => |deriv u x|) hθle hf hf2
      rw [sub_zero] at h
      have hconv : (∫ x in (0 : ℝ)..θ, |deriv u x| ^ 2)
          = ∫ x in (0 : ℝ)..θ, (deriv u x) ^ 2 :=
        intervalIntegral.integral_congr (fun x _ => sq_abs (deriv u x))
      rwa [hconv] at h
    -- comparison with the full slice energy
    have hBA : (∫ x in (0 : ℝ)..θ, (deriv u x) ^ 2) ≤ A := by
      rw [hA, intervalIntegral.integral_of_le (f := fun x => (deriv u x) ^ 2) hθle]
      refine MeasureTheory.setIntegral_mono_set (f := fun x => (deriv u x) ^ 2) hint ?_ ?_
      · filter_upwards with x
        exact sq_nonneg _
      · filter_upwards with x hx
        exact hIoc_sub hx
    have hBnn : 0 ≤ ∫ x in (0 : ℝ)..θ, (deriv u x) ^ 2 :=
      intervalIntegral.integral_nonneg (f := fun x => (deriv u x) ^ 2) hθle
        (fun _ _ => sq_nonneg _)
    calc (u θ) ^ 2 = (|u θ|) ^ 2 := (sq_abs (u θ)).symm
      _ ≤ (∫ x in (0 : ℝ)..θ, |deriv u x|) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg (u θ)) habs 2
      _ ≤ θ * (∫ x in (0 : ℝ)..θ, (deriv u x) ^ 2) := hCS
      _ ≤ (Real.pi / 2) * A := mul_le_mul hθlt.le hBA hBnn hpi.le
  -- ## Step 2: the bound holds almost everywhere on `Iθ` (the bad point `π/2` is null)
  have hpoint : ∀ θ ∈ Work.Spaces.Iθ, θ ≠ Real.pi / 2 → (u θ) ^ 2 ≤ (Real.pi / 2) * A := by
    intro θ hθ hne
    rcases eq_or_lt_of_le hθ.1 with h | h
    · rw [← h, h0]
      simpa using hM_nonneg
    · exact hbound θ ⟨h, lt_of_le_of_ne hθ.2 hne⟩
  have hae : ∀ᵐ θ ∂(volume : Measure ℝ),
      θ ∈ Work.Spaces.Iθ → (u θ) ^ 2 ≤ (Real.pi / 2) * A := by
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_singleton (Real.pi / 2))
    intro θ hθ
    simp only [Set.mem_ofPred_eq, not_imp] at hθ
    by_contra hne
    exact hθ.2 (hpoint θ hθ.1 hne)
  -- ## Step 3: integrate the a.e. bound
  have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => (Real.pi / 2) * A) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const (C := (Real.pi / 2) * A) (by
      rw [Work.Spaces.Iθ, Real.volume_Icc, sub_zero]
      exact ENNReal.ofReal_lt_top.ne)
  have hmono := MeasureTheory.setIntegral_mono_on_ae hu2 hconst measurableSet_Icc hae
  refine hmono.trans_eq ?_
  rw [MeasureTheory.setIntegral_const]
  have hvol : (volume : Measure ℝ).real Work.Spaces.Iθ = Real.pi / 2 := by
    rw [Work.Spaces.Iθ, MeasureTheory.measureReal_def, Real.volume_Icc, sub_zero,
      ENNReal.toReal_ofReal (by positivity)]
  rw [hvol, smul_eq_mul]
  ring

end Work.FTS.EllipticEst.Mine
