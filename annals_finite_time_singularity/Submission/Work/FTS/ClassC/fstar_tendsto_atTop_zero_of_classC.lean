import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.ClassC.TailDefs
import Submission.Work.FTS.ClassC.zTail_lintegral_le_HkSq
import Submission.Work.FTS.ClassC.zTail_hardy

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Vanishing of the angular moment `F_* g` at `z = ∞`.**  For a profile `g` which is
`C^∞` on the open quadrant, honestly in `ℋ⁷` and decaying in `z` at every angle
`θ ∈ Iθ = [0,π/2]`, the angular moment `F_* g z = ∫_θ g z θ sin θ cos²θ` tends to `0` as
`z → ∞`.

Route.  Fix `θ ∈ (0,π/2)`.  The radial Hardy inequality (`Work.FTS.H2.HQ.HardyZQ`, packaged as
`zTail_hardy`) bounds the *value* `(g z θ)²` uniformly in `z > 0` by the weighted `L²`-mass of
the radial derivative,

  `(g z θ)² ≤ zTailR g θ`,   `zTailR g θ = (∫⁻_{s ∈ Iz} ofReal ((D_z g(s,θ))² w(s)²)).toReal`,

and `HkMem α 7 g` together with Tonelli (`zTail_lintegral_le_HkSq`) gives
`∫⁻_θ zTail g θ ≤ ofReal (HkSq α 7 g) < ∞`.  Hence `zTailR g` is an integrable function of `θ`
with `1 + zTailR g` dominating `θ ↦ g z θ · sin θ cos²θ` for all `z > 0`; the pointwise decay
`hdec` gives the a.e. pointwise convergence, and dominated convergence
(`MeasureTheory.tendsto_integral_filter_of_dominated_convergence`) yields the claim. -/
theorem fstar_tendsto_atTop_zero_of_classC {α : ℝ} {g : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hreg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmem : Work.Spaces.HkMem α 7 g)
    (hdec : ∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => g z θ) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun z => Work.Elliptic.Fstar g z) Filter.atTop (nhds 0) := by
  -- (0) the a.e. set where the angle is interior
  have hIθmem : MeasurableSet Work.Spaces.Iθ := by simp [Work.Spaces.Iθ]
  have hIoo_restrict : volume.restrict (Set.Ioo (0 : ℝ) (π / 2))
      = volume.restrict Work.Spaces.Iθ :=
    Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := π / 2))
  have hθae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
    rw [← hIoo_restrict]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  -- (1) the lintegral bound `∫⁻_θ zTail g θ ≤ ofReal (HkSq α 7 g)`
  have hlin : (∫⁻ θ in Work.Spaces.Iθ, zTail g θ)
      ≤ ENNReal.ofReal (Work.Spaces.HkSq α 7 g) :=
    zTail_lintegral_le_HkSq hreg hmem (by norm_num)
  have htop : (∫⁻ θ in Work.Spaces.Iθ, zTail g θ) ≠ ⊤ :=
    ne_top_of_lt (lt_of_le_of_lt hlin ENNReal.ofReal_lt_top)
  -- (2) measurability of the tail weight
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => (Work.Spaces.Dz g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2)
      (Work.FTS.EllipticEst.Q0) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dz g p.1 p.2)
        (Work.FTS.EllipticEst.Q0) := (hreg.Dz).continuousOn
    have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        (Work.FTS.EllipticEst.Q0) := by
      simp only [Work.Spaces.w]
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
        (continuousOn_fst.pow 2) (fun p hp => ?_)
      exact pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
    exact (h1.pow 2).mul (h2.pow 2)
  have haesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.Dz g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  have hjoint : AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal
        ((Work.Spaces.Dz g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    haesm.aemeasurable.ennreal_ofReal
  have hmeasT : AEMeasurable (zTail g) (volume.restrict Work.Spaces.Iθ) :=
    hjoint.lintegral_prod_left'
  have hmeasR : AEMeasurable (zTailR g) (volume.restrict Work.Spaces.Iθ) :=
    ENNReal.measurable_toReal.comp_aemeasurable hmeasT
  -- (3) `zTail g` is finite a.e.
  have haefin : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), zTail g θ ≠ ⊤ :=
    (MeasureTheory.ae_lt_top' hmeasT htop).mono fun θ h => ne_of_lt h
  -- (4) `1 + zTailR g` is integrable
  have hbound_lin : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (zTailR g θ)) ≠ ⊤ :=
    ne_top_of_le_ne_top htop (lintegral_mono fun θ => ENNReal.ofReal_toReal_le)
  have haesmR : AEStronglyMeasurable (zTailR g) (volume.restrict Work.Spaces.Iθ) :=
    hmeasR.aestronglyMeasurable
  have hintT : MeasureTheory.Integrable (zTailR g) (volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable haesmR
      (Filter.Eventually.of_forall fun θ => zTailR_nonneg g θ)).mp hbound_lin
  have hInt1 : MeasureTheory.Integrable (fun _ : ℝ => (1 : ℝ))
      (volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.integrable_const_iff]
    right
    refine ⟨?_⟩
    rw [MeasureTheory.Measure.restrict_apply_univ]
    show volume Work.Spaces.Iθ < ⊤
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hInt : MeasureTheory.Integrable (fun θ => 1 + zTailR g θ)
      (volume.restrict Work.Spaces.Iθ) := hInt1.add hintT
  -- (5) dominated convergence
  have hF_meas : ∀ᶠ z in Filter.atTop,
      AEStronglyMeasurable (fun θ => g z θ * Work.Elliptic.sinCos2 θ)
        (volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with z hz
    have h1 : ContinuousOn (fun θ : ℝ => g z θ) (Set.Ioo (0 : ℝ) (π / 2)) :=
      (hreg.curry_θ hz).continuousOn
    have h2 : ContinuousOn (fun θ : ℝ => Work.Elliptic.sinCos2 θ) (Set.Ioo (0 : ℝ) (π / 2)) := by
      unfold Work.Elliptic.sinCos2
      exact (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn
    exact (hIoo_restrict ▸ ((h1.mul h2).aestronglyMeasurable measurableSet_Ioo))
  have hsin1 : ∀ θ : ℝ, |Work.Elliptic.sinCos2 θ| ≤ 1 := by
    intro θ
    unfold Work.Elliptic.sinCos2
    rw [abs_mul]
    have h2 : |Real.cos θ ^ 2| ≤ 1 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_one_iff_abs_le_one (Real.cos θ)).mpr (Real.abs_cos_le_one θ)
    calc |Real.sin θ| * |Real.cos θ ^ 2| ≤ 1 * 1 :=
          mul_le_mul (Real.abs_sin_le_one θ) h2 (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have habs_le : ∀ a : ℝ, |a| ≤ a ^ 2 + 1 := by
    intro a
    nlinarith [sq_nonneg (|a| - 1 / 2), sq_abs a]
  have hbound : ∀ᶠ z in Filter.atTop,
      ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        ‖g z θ * Work.Elliptic.sinCos2 θ‖ ≤ 1 + zTailR g θ := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with z hz
    filter_upwards [haefin, hθae] with θ hfin hθ
    have hg : (g z θ) ^ 2 ≤ zTailR g θ := zTail_hardy hreg hdec hθ hfin z hz
    rw [Real.norm_eq_abs, abs_mul]
    calc |g z θ| * |Work.Elliptic.sinCos2 θ|
        ≤ ((g z θ) ^ 2 + 1) * 1 :=
          mul_le_mul (habs_le (g z θ)) (hsin1 θ) (abs_nonneg _) (by positivity)
      _ ≤ 1 + zTailR g θ := by nlinarith
  have hlim : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto (fun z => g z θ * Work.Elliptic.sinCos2 θ) Filter.atTop (nhds (0 : ℝ)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hIθmem] with θ hθ
    have h := (hdec θ hθ).mul_const (Work.Elliptic.sinCos2 θ)
    simpa using h
  have hDCT := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict Work.Spaces.Iθ) (l := Filter.atTop)
    (F := fun z θ => g z θ * Work.Elliptic.sinCos2 θ) (f := fun _ => (0 : ℝ))
    (bound := fun θ => 1 + zTailR g θ) hF_meas hbound hInt hlim
  simpa [Work.Elliptic.Fstar] using hDCT

end

end Work.FTS.ClassC
