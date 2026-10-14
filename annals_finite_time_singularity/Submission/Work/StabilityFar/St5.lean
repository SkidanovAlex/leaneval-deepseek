import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.LWP.BiotSavart.nearField_bound
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Defs
import Submission.Work.StabilityFar.Holder.holderOnWith_of_norm_le
-- ===== merged: Submission.Work.StabilityFar.Decay =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.StabilityFar



/-! ## The support of `∂ₜω` on the open window -/


/-! ## The far-field decay of `u` and `Du` -/





/-! ## The Lipschitz-in-`x` bound for `∂ₜu` -/


end Work.StabilityFar
end
-- ===== merged: Submission.Work.StabilityFar.Decay.biotSavart_sub =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory
open scoped Topology ENNReal

namespace Work.StabilityFar.Decay

/-! ## Integrability of the Biot–Savart integrand -/

/-- For a vorticity `ω` that is ae-strongly-measurable, bounded by `M` and supported in the
closed ball `B(0,R)`, the Biot–Savart integrand `bsK ω x` is Bochner-integrable at every point
`x` — including the points *inside* the support ball, where the kernel `‖x - y‖⁻³` is singular.

The dominating function is `M · ‖x - y‖⁻²` on `B(0,R)`, which is integrable in `ℝ³`
(`integrable_indicator_inv_sq`), and the pointwise bound is `norm_bsK_le_indicator`. -/
lemma integrable_bsK_supported {ω : R3 → R3} {R M : ℝ} (hM : 0 ≤ M) (hω : ∀ y, ‖ω y‖ ≤ M)
    (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : AEStronglyMeasurable ω volume) (x : R3) :
    Integrable (Work.LWP.BiotSavart.bsK ω x) volume :=
  Integrable.mono' (integrable_indicator_inv_sq x hM)
    (Work.LWP.BiotSavart.aestronglyMeasurable_bsK hmeas x)
    (Filter.Eventually.of_forall fun y => norm_bsK_le_indicator hM hω hsupp x y)

/-! ## Linearity of the integrand -/

/-- The Biot–Savart integrand is additive in the vorticity.  After unfolding the definitions this
is the additivity of the cross product in its first slot, transported through the scalar
multiplication by `(‖x - y‖³)⁻¹` and through `WithLp.toLp 2`. -/
lemma bsK_sub (f g : R3 → R3) (x y : R3) :
    Work.LWP.BiotSavart.bsK (f - g) x y
      = Work.LWP.BiotSavart.bsK f x y - Work.LWP.BiotSavart.bsK g x y := by
  simp only [Work.LWP.BiotSavart.bsK, Pi.sub_apply, WithLp.ofLp_sub, map_sub, LinearMap.sub_apply,
    smul_sub, WithLp.toLp_sub]
  abel

/-! ## Additivity of the Biot–Savart operator -/

/-- **Additivity of the Biot–Savart operator.**  `biotSavart` is `(4π)⁻¹` times the Bochner
integral of its integrand; the integrands of `BS(f - g)`, `BS f` and `BS g` differ pointwise by
`bsK_sub`, and the two integrals on the right may be split by `integral_sub` because both
integrands are integrable (`integrable_bsK_supported`).  Dividing the resulting identity by
`4π` is the final `smul_sub`. -/
theorem biotSavart_sub {f g : Work.StabilityFar.R3 → Work.StabilityFar.R3} {R M : ℝ} (hR : 0 ≤ R)
    (hM : 0 ≤ M) (hf : ∀ y, ‖f y‖ ≤ M) (hg : ∀ y, ‖g y‖ ≤ M)
    (hfs : ∀ y, f y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hgs : ∀ y, g y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hfm : MeasureTheory.AEStronglyMeasurable f volume)
    (hgm : MeasureTheory.AEStronglyMeasurable g volume) (x : Work.StabilityFar.R3) :
    Work.LWP.biotSavart (f - g) x = Work.LWP.biotSavart f x - Work.LWP.biotSavart g x := by
  -- `hR` is not needed: it is recorded here only because the statement carries it.
  have _hR : (0 : ℝ) ≤ R := hR
  have hfi : Integrable (Work.LWP.BiotSavart.bsK f x) volume :=
    integrable_bsK_supported hM hf hfs hfm x
  have hgi : Integrable (Work.LWP.BiotSavart.bsK g x) volume :=
    integrable_bsK_supported hM hg hgs hgm x
  rw [Work.LWP.BiotSavart.biotSavart_apply, Work.LWP.BiotSavart.biotSavart_apply,
    Work.LWP.BiotSavart.biotSavart_apply]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => bsK_sub f g x y)]
  rw [MeasureTheory.integral_sub hfi hgi, smul_sub]

end Work.StabilityFar.Decay
end
-- ===== merged: Submission.Work.StabilityFar.Decay.slicesSupported_timeDeriv_window =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.StabilityFar.Decay


end Work.StabilityFar.Decay
end
-- ===== merged: Submission.Work.StabilityFar.St4.isContDiffHolderOn_glue =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.StabilityFar.St4

open Work.StabilityFar Set Filter Topology
open scoped NNReal

set_option autoImplicit false

/-!
## Gluing the core and far `C^{1,α}` estimates

The core region `coreRegion ρ'` (the closed ball of radius `ρ'`) and the far region `farRegion ρ`
(the open exterior of the ball of radius `ρ`) cover the whole space as soon as `ρ ≤ ρ'`.  This
file shows that a function which is `C^{1,α}` on the strip over each of the two regions is
`C^{1,α}` on the whole strip `univ ×ˢ Icc 0 T`.

The only point needing care is that the derivative is taken *within* the set
(`fderivWithin`), so one has to relate `fderivWithin` on the big set to `fderivWithin` on the
two pieces.  This is done by observing that, in the open spatial neighbourhood of a point with
`‖x.1‖ < ρ'` (resp. `ρ < ‖x.1‖`), the full strip agrees with the core (resp. far) strip, so that
`fderivWithin_congr_set` identifies the two derivatives there.  For a pair of points that is *not*
of this kind, the two points are separated by at least `ρ' - ρ`, and the uniform bound obtained
from the two `L^∞` estimates gives the Hölder estimate.
-/

/-- If `‖x‖ < ρ'` then membership in the core strip `coreRegion ρ' ×ˢ Icc 0 T` is, near `x`,
the same as membership in the full strip `univ ×ˢ Icc 0 T`. -/
theorem coreRegion_prod_eventuallyEq {ρ' T : ℝ} {x : R3 × ℝ} (hx : ‖x.1‖ < ρ') :
    coreRegion ρ' ×ˢ Set.Icc 0 T =ᶠ[𝓝 x] Set.univ ×ˢ Set.Icc 0 T := by
  have hr : 0 < ρ' - ‖x.1‖ := by linarith
  have hball : Metric.ball x.1 (ρ' - ‖x.1‖) ⊆ coreRegion ρ' := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    rw [mem_coreRegion]
    have hh := norm_add_le x.1 (z - x.1)
    rw [add_sub_cancel] at hh
    linarith
  have hmem : {p : R3 × ℝ | p.1 ∈ coreRegion ρ'} ∈ 𝓝 x := by
    have h1 : Metric.ball x.1 (ρ' - ‖x.1‖) ∈ 𝓝 x.1 := Metric.ball_mem_nhds x.1 hr
    have h2 : Prod.fst ⁻¹' (Metric.ball x.1 (ρ' - ‖x.1‖)) ∈ 𝓝 x :=
      (continuous_fst.continuousAt (x := x)).preimage_mem_nhds h1
    exact Filter.mem_of_superset h2 (fun p hp => hball hp)
  rw [eventuallyEqSet_iff]
  refine Filter.mem_of_superset hmem (fun p hp => ?_)
  simp only [Set.mem_prod, Set.mem_univ, true_and] at hp ⊢
  exact ⟨fun h => h.2, fun h => ⟨hp, h⟩⟩

/-- If `ρ < ‖x‖` then membership in the far strip `farRegion ρ ×ˢ Icc 0 T` is, near `x`, the
same as membership in the full strip `univ ×ˢ Icc 0 T`. -/
theorem farRegion_prod_eventuallyEq {ρ T : ℝ} {x : R3 × ℝ} (hx : ρ < ‖x.1‖) :
    farRegion ρ ×ˢ Set.Icc 0 T =ᶠ[𝓝 x] Set.univ ×ˢ Set.Icc 0 T := by
  have hr : 0 < ‖x.1‖ - ρ := by linarith
  have hball : Metric.ball x.1 (‖x.1‖ - ρ) ⊆ farRegion ρ := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    rw [mem_farRegion]
    have hh := norm_add_le z (x.1 - z)
    rw [add_sub_cancel] at hh
    rw [norm_sub_rev x.1 z] at hh
    linarith
  have hmem : {p : R3 × ℝ | p.1 ∈ farRegion ρ} ∈ 𝓝 x := by
    have h1 : Metric.ball x.1 (‖x.1‖ - ρ) ∈ 𝓝 x.1 := Metric.ball_mem_nhds x.1 hr
    have h2 : Prod.fst ⁻¹' (Metric.ball x.1 (‖x.1‖ - ρ)) ∈ 𝓝 x :=
      (continuous_fst.continuousAt (x := x)).preimage_mem_nhds h1
    exact Filter.mem_of_superset h2 (fun p hp => hball hp)
  rw [eventuallyEqSet_iff]
  refine Filter.mem_of_superset hmem (fun p hp => ?_)
  simp only [Set.mem_prod, Set.mem_univ, true_and] at hp ⊢
  exact ⟨fun h => h.2, fun h => ⟨hp, h⟩⟩

/-- The `fderivWithin` on the core strip and on the full strip agree at points with `‖x.1‖ < ρ'`. -/
theorem fderivWithin_coreRegion_eq {ρ' T : ℝ} {f : R3 × ℝ → R3} {x : R3 × ℝ}
    (hx : ‖x.1‖ < ρ') :
    fderivWithin ℝ f (coreRegion ρ' ×ˢ Set.Icc 0 T) x
      = fderivWithin ℝ f (Set.univ ×ˢ Set.Icc 0 T) x :=
  fderivWithin_congr_set (coreRegion_prod_eventuallyEq (T := T) hx)

/-- The `fderivWithin` on the far strip and on the full strip agree at points with `ρ < ‖x.1‖`. -/
theorem fderivWithin_farRegion_eq {ρ T : ℝ} {f : R3 × ℝ → R3} {x : R3 × ℝ}
    (hx : ρ < ‖x.1‖) :
    fderivWithin ℝ f (farRegion ρ ×ˢ Set.Icc 0 T) x
      = fderivWithin ℝ f (Set.univ ×ˢ Set.Icc 0 T) x :=
  fderivWithin_congr_set (farRegion_prod_eventuallyEq (T := T) hx)

/-- **Geometry of the two-region cover.**  If `ρ < ρ'` and two points of `R3 × ℝ` are closer than
`ρ' - ρ`, then they are either both inside the ball of radius `ρ'` or both outside the ball of
radius `ρ`.  This is what allows the two Hölder estimates to be glued at small scales. -/
theorem dist_lt_dichotomy {ρ ρ' : ℝ} (h : ρ < ρ') {x y : R3 × ℝ}
    (hd : dist x y < ρ' - ρ) :
    (‖x.1‖ < ρ' ∧ ‖y.1‖ < ρ') ∨ (ρ < ‖x.1‖ ∧ ρ < ‖y.1‖) := by
  by_contra hcon
  rw [not_or, not_and, not_and] at hcon
  obtain ⟨ha, hb⟩ := hcon
  have ha1 : ‖x.1‖ < ρ' → ρ' ≤ ‖y.1‖ := fun h1 => not_lt.mp (ha h1)
  have hb1 : ρ < ‖x.1‖ → ‖y.1‖ ≤ ρ := fun h1 => not_lt.mp (hb h1)
  have hdist : ‖x.1 - y.1‖ ≤ dist x y := by
    rw [Prod.dist_eq, dist_eq_norm]; exact le_max_left _ _
  by_cases hxlt : ‖x.1‖ < ρ'
  · by_cases hxgt : ρ < ‖x.1‖
    · have : ρ' ≤ ρ := le_trans (ha1 hxlt) (hb1 hxgt)
      linarith
    · have hy : ρ' ≤ ‖y.1‖ := ha1 hxlt
      have hxle : ‖x.1‖ ≤ ρ := le_of_not_gt hxgt
      have hle : ρ' - ρ ≤ ‖x.1 - y.1‖ := by
        have hh := norm_add_le x.1 (y.1 - x.1)
        rw [add_sub_cancel] at hh
        rw [norm_sub_rev y.1 x.1] at hh
        linarith
      linarith
  · have hxge : ρ' ≤ ‖x.1‖ := le_of_not_gt hxlt
    have hxgt : ρ < ‖x.1‖ := lt_of_lt_of_le h hxge
    have hy : ‖y.1‖ ≤ ρ := hb1 hxgt
    have hle : ρ' - ρ ≤ ‖x.1 - y.1‖ := by
      have hh := norm_add_le y.1 (x.1 - y.1)
      rw [add_sub_cancel] at hh
      linarith
    linarith

/-- **`ContDiffOn` on the covering strips glues.**  The two strips are not open, so
`ContDiffOn.union_of_isOpen` does not apply; instead one uses that near every point of the full
strip one of the two pieces already coincides (as a set) with the full strip, which is exactly the
local characterisation `contDiffWithinAt_iff_contDiffOn_nhds`. -/
theorem contDiffOn_union_strip {ρ ρ' T : ℝ} (h : ρ < ρ') {f : R3 × ℝ → R3}
    (hcore : ContDiffOn ℝ 1 f (coreRegion ρ' ×ˢ Set.Icc 0 T))
    (hfar : ContDiffOn ℝ 1 f (farRegion ρ ×ˢ Set.Icc 0 T)) :
    ContDiffOn ℝ 1 f (Set.univ ×ˢ Set.Icc 0 T) := by
  intro x hx
  rw [contDiffWithinAt_iff_contDiffOn_nhds (by simp : (1 : WithTop ℕ∞) ≠ ↑(⊤ : ℕ∞))]
  by_cases hlt : ‖x.1‖ < ρ'
  · set r : ℝ := (ρ' - ‖x.1‖) / 2 with hrdef
    have hr : 0 < r := by rw [hrdef]; linarith
    have hball : Metric.ball x.1 r ⊆ coreRegion ρ' := by
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      rw [mem_coreRegion]
      have hh := norm_add_le x.1 (z - x.1)
      rw [add_sub_cancel] at hh
      rw [hrdef] at hz
      linarith
    refine ⟨(Set.univ ×ˢ Set.Icc 0 T) ∩ (Metric.ball x.1 r ×ˢ Set.univ), ?_, ?_⟩
    · rw [nhdsWithin, Filter.mem_inf_iff]
      refine ⟨Metric.ball x.1 r ×ˢ Set.univ, ?_, Set.univ ×ˢ Set.Icc 0 T, ?_, ?_⟩
      · rw [nhds_prod_eq]
        exact Filter.prod_mem_prod (Metric.ball_mem_nhds x.1 hr) Filter.univ_mem
      · rw [Filter.mem_principal]
        rintro p (rfl | hp)
        · exact hx
        · exact hp
      · rw [inter_comm]
    · apply hcore.mono
      rintro p ⟨⟨-, hp2⟩, hp1, -⟩
      exact ⟨hball hp1, hp2⟩
  · have hgt : ρ < ‖x.1‖ := lt_of_lt_of_le h (le_of_not_gt hlt)
    set r : ℝ := (‖x.1‖ - ρ) / 2 with hrdef
    have hr : 0 < r := by rw [hrdef]; linarith
    have hball : Metric.ball x.1 r ⊆ farRegion ρ := by
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      rw [mem_farRegion]
      have hh := norm_add_le z (x.1 - z)
      rw [add_sub_cancel] at hh
      rw [norm_sub_rev x.1 z] at hh
      rw [hrdef] at hz
      linarith
    refine ⟨(Set.univ ×ˢ Set.Icc 0 T) ∩ (Metric.ball x.1 r ×ˢ Set.univ), ?_, ?_⟩
    · rw [nhdsWithin, Filter.mem_inf_iff]
      refine ⟨Metric.ball x.1 r ×ˢ Set.univ, ?_, Set.univ ×ˢ Set.Icc 0 T, ?_, ?_⟩
      · rw [nhds_prod_eq]
        exact Filter.prod_mem_prod (Metric.ball_mem_nhds x.1 hr) Filter.univ_mem
      · rw [Filter.mem_principal]
        rintro p (rfl | hp)
        · exact hx
        · exact hp
      · rw [inter_comm]
    · apply hfar.mono
      rintro p ⟨⟨-, hp2⟩, hp1, -⟩
      exact ⟨hball hp1, hp2⟩

/-- **Core + far ⟹ the whole strip.**  If `f` is `C^{1,α}` on the strip over the closed ball of
radius `ρ'` and on the strip over the exterior of the ball of radius `ρ`, with `ρ < ρ'`, then `f`
is `C^{1,α}` on the whole strip `univ ×ˢ Icc 0 T`. -/
theorem isContDiffHolderOn_glue {α : NNReal} {f : Work.StabilityFar.R3 × ℝ → Work.StabilityFar.R3}
    {ρ ρ' T : ℝ} (hρ : 0 < ρ) (h : ρ < ρ')
    (hcore : IsContDiffHolderOn ℝ α f (Work.StabilityFar.coreRegion ρ' ×ˢ Set.Icc 0 T))
    (hfar : IsContDiffHolderOn ℝ α f (Work.StabilityFar.farRegion ρ ×ˢ Set.Icc 0 T)) :
    IsContDiffHolderOn ℝ α f (Set.univ ×ˢ Set.Icc 0 T) := by
  have _ : 0 < ρ' := lt_trans hρ h
  obtain ⟨hcdC, hbddC, hholderC⟩ := hcore
  obtain ⟨hcdD, hbddD, hholderD⟩ := hfar
  obtain ⟨C1, hC1⟩ := hholderC
  obtain ⟨C2, hC2⟩ := hholderD
  obtain ⟨N1, hN1⟩ := isBounded_iff_forall_norm_le.mp hbddC
  obtain ⟨N2, hN2⟩ := isBounded_iff_forall_norm_le.mp hbddD
  set M0 : ℝ := max (max N1 0) (max N2 0) with hM0def
  have hM0nonneg : 0 ≤ M0 := by
    rw [hM0def]
    exact le_trans (le_max_right N1 0) (le_max_left _ _)
  have hbdC : ∀ z ∈ coreRegion ρ' ×ˢ Set.Icc 0 T,
      ‖fderivWithin ℝ f (coreRegion ρ' ×ˢ Set.Icc 0 T) z‖ ≤ M0 := by
    intro z hz
    refine le_trans (hN1 _ (mem_image_of_mem _ hz)) ?_
    rw [hM0def]
    exact le_trans (le_max_left N1 0) (le_max_left _ _)
  have hbdD : ∀ z ∈ farRegion ρ ×ˢ Set.Icc 0 T,
      ‖fderivWithin ℝ f (farRegion ρ ×ˢ Set.Icc 0 T) z‖ ≤ M0 := by
    intro z hz
    refine le_trans (hN2 _ (mem_image_of_mem _ hz)) ?_
    rw [hM0def]
    exact le_trans (le_max_left N2 0) (le_max_right _ _)
  have hUS : ∀ x ∈ (Set.univ ×ˢ Set.Icc 0 T : Set (R3 × ℝ)), ‖x.1‖ < ρ' →
      fderivWithin ℝ f (Set.univ ×ˢ Set.Icc 0 T) x
        = fderivWithin ℝ f (coreRegion ρ' ×ˢ Set.Icc 0 T) x := by
    intro x _ hx
    exact (fderivWithin_coreRegion_eq (T := T) hx).symm
  have hVS : ∀ x ∈ (Set.univ ×ˢ Set.Icc 0 T : Set (R3 × ℝ)), ρ < ‖x.1‖ →
      fderivWithin ℝ f (Set.univ ×ˢ Set.Icc 0 T) x
        = fderivWithin ℝ f (farRegion ρ ×ˢ Set.Icc 0 T) x := by
    intro x _ hx
    exact (fderivWithin_farRegion_eq (T := T) hx).symm
  have hbddS : ∀ x ∈ (Set.univ ×ˢ Set.Icc 0 T : Set (R3 × ℝ)),
      ‖fderivWithin ℝ f (Set.univ ×ˢ Set.Icc 0 T) x‖ ≤ M0 := by
    intro x hx
    by_cases hlt : ‖x.1‖ < ρ'
    · rw [hUS x hx hlt]
      exact hbdC x ⟨mem_coreRegion.mpr (le_of_lt hlt), hx.2⟩
    · have hgt : ρ < ‖x.1‖ := lt_of_lt_of_le h (le_of_not_gt hlt)
      rw [hVS x hx hgt]
      exact hbdD x ⟨mem_farRegion.mpr hgt, hx.2⟩
  set dg : ℝ := (ρ' - ρ) / 2 with hdgdef
  have hdg : 0 < dg := by rw [hdgdef]; linarith
  set K : ℝ := max (max (C1 : ℝ) (C2 : ℝ)) (2 * M0 / dg ^ (α : ℝ)) with hKdef
  have hKnonneg : 0 ≤ K := by
    rw [hKdef]
    exact le_trans (le_trans (NNReal.coe_nonneg C1) (le_max_left _ _)) (le_max_left _ _)
  have hholder : HolderOn α (fderivWithin ℝ f (Set.univ ×ˢ Set.Icc 0 T))
      (Set.univ ×ˢ Set.Icc 0 T) := by
    refine ⟨Real.toNNReal K, ?_⟩
    refine Work.StabilityFar.Holder.holderOnWith_of_norm_le (C := Real.toNNReal K) (r := α) ?_
    intro x hx y hy
    rw [Real.coe_toNNReal K hKnonneg]
    by_cases hd : dist x y < ρ' - ρ
    · rcases dist_lt_dichotomy h hd with ⟨hxlt, hylt⟩ | ⟨hxgt, hygt⟩
      · rw [hUS x hx hxlt, hUS y hy hylt]
        have hxC : x ∈ coreRegion ρ' ×ˢ Set.Icc 0 T :=
          ⟨mem_coreRegion.mpr (le_of_lt hxlt), hx.2⟩
        have hyC : y ∈ coreRegion ρ' ×ˢ Set.Icc 0 T :=
          ⟨mem_coreRegion.mpr (le_of_lt hylt), hy.2⟩
        have hle := hC1.dist_le hxC hyC
        rw [dist_eq_norm] at hle
        refine le_trans hle ?_
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg dist_nonneg _)
        rw [hKdef]
        exact le_trans (le_max_left _ _) (le_max_left _ _)
      · rw [hVS x hx hxgt, hVS y hy hygt]
        have hxD : x ∈ farRegion ρ ×ˢ Set.Icc 0 T :=
          ⟨mem_farRegion.mpr hxgt, hx.2⟩
        have hyD : y ∈ farRegion ρ ×ˢ Set.Icc 0 T :=
          ⟨mem_farRegion.mpr hygt, hy.2⟩
        have hle := hC2.dist_le hxD hyD
        rw [dist_eq_norm] at hle
        refine le_trans hle ?_
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg dist_nonneg _)
        rw [hKdef]
        exact le_trans (le_max_right _ _) (le_max_left _ _)
    · have hlarge : ρ' - ρ ≤ dist x y := le_of_not_gt hd
      have hd2 : dg ≤ dist x y := by rw [hdgdef]; linarith
      have hbnd2 : ‖fderivWithin ℝ f (Set.univ ×ˢ Set.Icc 0 T) x
          - fderivWithin ℝ f (Set.univ ×ˢ Set.Icc 0 T) y‖ ≤ 2 * M0 := by
        calc ‖fderivWithin ℝ f (Set.univ ×ˢ Set.Icc 0 T) x
              - fderivWithin ℝ f (Set.univ ×ˢ Set.Icc 0 T) y‖
            ≤ ‖fderivWithin ℝ f (Set.univ ×ˢ Set.Icc 0 T) x‖
              + ‖fderivWithin ℝ f (Set.univ ×ˢ Set.Icc 0 T) y‖ := norm_sub_le _ _
          _ ≤ M0 + M0 := add_le_add (hbddS x hx) (hbddS y hy)
          _ = 2 * M0 := by ring
      have hdgpow : dg ^ (α : ℝ) ≤ dist x y ^ (α : ℝ) :=
        Real.rpow_le_rpow (le_of_lt hdg) hd2 (by positivity)
      have h2M0 : 2 * M0 ≤ K * dg ^ (α : ℝ) := by
        have hdpos : 0 < dg ^ (α : ℝ) := Real.rpow_pos_of_pos hdg _
        have hle : 2 * M0 / dg ^ (α : ℝ) ≤ K := by
          rw [hKdef]; exact le_max_right _ _
        calc 2 * M0 = (2 * M0 / dg ^ (α : ℝ)) * dg ^ (α : ℝ) :=
              (div_mul_cancel₀ (2 * M0) (ne_of_gt hdpos)).symm
          _ ≤ K * dg ^ (α : ℝ) := mul_le_mul_of_nonneg_right hle (le_of_lt hdpos)
      calc ‖fderivWithin ℝ f (Set.univ ×ˢ Set.Icc 0 T) x
            - fderivWithin ℝ f (Set.univ ×ˢ Set.Icc 0 T) y‖
          ≤ 2 * M0 := hbnd2
        _ ≤ K * dg ^ (α : ℝ) := h2M0
        _ ≤ K * dist x y ^ (α : ℝ) := mul_le_mul_of_nonneg_left hdgpow hKnonneg
  have hbdd : IsBoundedFunOn (fderivWithin ℝ f (Set.univ ×ˢ Set.Icc 0 T))
      (Set.univ ×ˢ Set.Icc 0 T) :=
    isBounded_iff_forall_norm_le.mpr ⟨M0, fun z hz => by
      simp only [Set.mem_image] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      exact hbddS x hx⟩
  exact ⟨contDiffOn_union_strip h hcdC hcdD, hbdd, hholder⟩

end Work.StabilityFar.St4
end
-- ===== merged: Submission.Work.StabilityFar.St5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology NNReal ENNReal

set_option autoImplicit false

namespace Work.StabilityFar

/-- A pointwise lower bound for one slice of the vorticity gives a lower bound for the `L^∞`-norm
`vortLInf u t = ⨆ₓ ‖ω(x,t)‖`, provided the supremum is honest (`BddAbove`).  This is the form in
which the construction's data (a point where the profile `F_* + g` is large) is fed into `St5`. -/
theorem vortLInf_lower_of_exists {u : R3 → ℝ → R3} {t c : ℝ}
    (hbdd : BddAbove (Set.range (fun x : R3 => ‖vorticity (fun y => u y t) x‖)))
    (h : ∃ x : R3, c ≤ ‖vorticity (fun y => u y t) x‖) :
    c ≤ Work.LWP.vortLInf u t :=
  h.elim (fun x hx => le_trans hx (le_ciSup hbdd x))

/-- **`St5`.**  If the `L^∞`-norm of the vorticity dominates `c/(T*-t)` on `[0,T*)`, then the BKM
integral `bkm u t = ∫₀ᵗ ‖ω(·,s)‖_∞ ds` diverges as `t → T*⁻`. -/
theorem bkm_divergence_of_vortLinfLower {u : R3 → ℝ → R3} {T c : ℝ} (hT : 0 < T) (hc : 0 < c)
    (h : VortLinfLower u T c)
    (hint : ∀ t ∈ Set.Ico 0 T, IntervalIntegrable (Work.LWP.vortLInf u) volume 0 t) :
    Filter.Tendsto (Work.LWP.bkm u) (𝓝[<] T) Filter.atTop :=
  BKM.bkm_tendsto_atTop_of_linf_lower hT hc h hint

/-- **`St5` at the physical blow-up time `1`**, in the exact shape of `theorem_1`'s last
clause. -/
theorem bkm_divergence_at_one {u : R3 → ℝ → R3} {c : ℝ} (hc : 0 < c)
    (h : VortLinfLower u 1 c)
    (hint : ∀ t ∈ Set.Ico 0 1, IntervalIntegrable (Work.LWP.vortLInf u) volume 0 t) :
    Filter.Tendsto (fun t => ∫ s in 0..t, ⨆ x, ‖vorticity (fun y => u y s) x‖) (𝓝[<] 1)
      Filter.atTop := by
  have h1 := bkm_divergence_of_vortLinfLower (u := u) (T := (1 : ℝ)) (c := c) one_pos hc h hint
  have h2 : Work.LWP.bkm u = fun t => ∫ s in 0..t, ⨆ x, ‖vorticity (fun y => u y s) x‖ :=
    funext (fun t => rfl)
  rw [h2] at h1
  exact h1

/-! ## The `St5` lower bound from the self-similar ansatz

The paper's construction represents the vorticity by the self-similar ansatz
`ω(x,t) = λ̄(t)^{-1}·F(z,θ)` with `F = F_* + g`, `λ̄(t) = (T*-t)Λ(t)`.  Two ingredients then give
the `L^∞` lower bound consumed by `St5`:

* `Work.StabilityFar.Profile.exists_Fstar_add_ge`: the profile `F_* + g` is `≥ c₀α` somewhere in the
  domain as soon as `‖g‖_∞ ≤ c₀α/2` (with `Linf_H2`, `‖g‖_∞ ≤ 100√10·Cα^{3/2} ≤ c₀α/2`);
* the upper bound `Λ ≤ 2` of the bootstrap, i.e. `λ̄(t) ≤ 2(T*-t)`.

The lemma below packages the (elementary) step from those two to `VortLinfLower u T* (c₀α/2)`. -/

/-- **The `St5` lower bound from the ansatz.**  If at every time `t < T*` there is a point `x` with
`c₀α ≤ λ̄(t)·‖ω(x,t)‖` (the self-similar ansatz, read in the physical space, with the profile bound
`c₀α ≤ |F_* + g|` of `Profile.exists_Fstar_add_ge`), and if the modulation obeys
`0 < λ̄(t) ≤ 2(T*-t)`, then the vorticity sup-norm dominates `c₀α/(2(T*-t))`. -/
theorem vortLinfLower_of_ansatz {u : R3 → ℝ → R3} {T c₀ α : ℝ} {lam : ℝ → ℝ}
    (hlam_pos : ∀ t ∈ Set.Ico 0 T, 0 < lam t)
    (hlam_le : ∀ t ∈ Set.Ico 0 T, lam t ≤ 2 * (T - t)) (hc₀ : 0 < c₀) (hα : 0 < α)
    (hbdd : ∀ t ∈ Set.Ico 0 T,
      BddAbove (Set.range (fun x : R3 => ‖vorticity (fun y => u y t) x‖)))
    (hansatz : ∀ t ∈ Set.Ico 0 T, ∃ x : R3, c₀ * α ≤ lam t * ‖vorticity (fun y => u y t) x‖) :
    VortLinfLower u T (c₀ * α / 2) := by
  intro t ht
  obtain ⟨x, hx⟩ := hansatz t ht
  have h1 : c₀ * α / 2 / (T - t) ≤ ‖vorticity (fun y => u y t) x‖ := by
    have hTt : (0 : ℝ) < T - t := by linarith [ht.2]
    rw [div_le_iff₀ hTt]
    have h2 : c₀ * α ≤ lam t * ‖vorticity (fun y => u y t) x‖ := hx
    have h3 : lam t * ‖vorticity (fun y => u y t) x‖
        ≤ 2 * (T - t) * ‖vorticity (fun y => u y t) x‖ :=
      mul_le_mul_of_nonneg_right (hlam_le t ht) (norm_nonneg _)
    linarith
  exact vortLInf_lower_of_exists (u := u) (t := t) (c := c₀ * α / 2 / (T - t))
    (hbdd t ht) ⟨x, h1⟩

end Work.StabilityFar
end
