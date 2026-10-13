import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.ThShiftAEMeasurable
import Submission.Work.FTS.StrongEps.JepsHkMem.lintegral_thShift_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The product bound for the angular shift `lintegral_thShift_le`

`JepsHkMem.lintegral_thShift_le` bounds the *angular* lintegral of a shifted profile:

  `∫⁻_{θ ∈ Iθ} U (thShift θ p) ≤ e^{3|p|} ∫⁻_{θ ∈ Iθ} U θ`     (`Iθ = [0, π/2]`).

Here we integrate the same inequality in `p` over the shift interval `[-ε, ε]`.  Since the
inequality is *uniform in* `θ` (`thShift` acts on `θ` alone), Fubini on the product measure
gives, for every `Measurable U`,

  `∫⁻_{(θ,p) ∈ Iθ × [-ε,ε]} U (thShift θ p) ≤ e^{3ε} · (2ε) · ∫⁻_{θ ∈ Iθ} U θ`.

## Proof

1. **Fubini.** `MeasureTheory.lintegral_prod_symm` turns the integral over
   `(volume.restrict Iθ).prod (volume.restrict [-ε,ε])` into `∫⁻ p, ∫⁻ θ ∈ Iθ, …`.  The required
   a.e. measurability of the uncurried integrand is
   `Measurable.aemeasurable.comp_aemeasurable` applied to
   `FstarJepsSmoothAux.aemeasurable_thShift_prod` (the angular shift is a.e. continuous on the
   conull set `{θ ∈ (0,π/2)}` of `Iθ`).

2. **Pointwise-a.e. bound in `p`.**  For a.e. `p` (namely for `p ∈ [-ε,ε]`, where `|p| ≤ ε`)
   the inner integral is `≤ ofReal (e^{3|p|}) · J ≤ ofReal (e^{3ε}) · J`
   (`J := ∫⁻ θ ∈ Iθ, U θ`).

3. **Integration in `p`.**  The bound is a constant in `p`, so
   `∫⁻ p, C * J = C * J * μ([-ε,ε]) = C * J * ofReal (2ε)`, and
   `ofReal (e^{3ε}) * ofReal (2ε) = ofReal (e^{3ε} · 2ε)`.

`hε` is not needed: the statement also holds for `ε ≤ 0` (the shift interval is then empty and
`2ε ≤ 0` makes the constant `ofReal (…) = 0`).
-/

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux

theorem LintegralProdThShiftLe {ε : ℝ} (hε : 0 < ε) {U : ℝ → ENNReal} (hU : Measurable U) :
    (∫⁻ x : ℝ × ℝ, U (Work.FTS.StrongEps.thShift x.1 x.2)
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
          (MeasureTheory.volume.restrict (Set.Icc (-ε) ε))))
      ≤ ENNReal.ofReal (Real.exp (3 * ε) * (2 * ε)) * ∫⁻ θ in Work.Spaces.Iθ, U θ := by
  have _hε := hε
  classical
  -- a.e. measurability of the uncurried integrand, from `aemeasurable_thShift_prod`
  have hAEM : AEMeasurable (fun z : ℝ × ℝ => U (Work.FTS.StrongEps.thShift z.1 z.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
        (MeasureTheory.volume.restrict (Set.Icc (-ε) ε))) := by
    simpa only [Function.comp_def] using
      hU.aemeasurable.comp_aemeasurable
        (Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.aemeasurable_thShift_prod (ε := ε))
  -- Fubini on the product measure
  have hswap : (∫⁻ z : ℝ × ℝ, U (Work.FTS.StrongEps.thShift z.1 z.2)
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
          (MeasureTheory.volume.restrict (Set.Icc (-ε) ε))))
      = ∫⁻ p, (∫⁻ θ in Work.Spaces.Iθ, U (Work.FTS.StrongEps.thShift θ p))
          ∂(MeasureTheory.volume.restrict (Set.Icc (-ε) ε)) :=
    MeasureTheory.lintegral_prod_symm
      (fun z : ℝ × ℝ => U (Work.FTS.StrongEps.thShift z.1 z.2)) hAEM
  rw [hswap]
  set J : ENNReal := ∫⁻ θ in Work.Spaces.Iθ, U θ with hJ
  set C : ENNReal := ENNReal.ofReal (Real.exp (3 * ε)) with hC
  -- the pointwise-a.e. bound in `p`
  have hinner : ∀ᵐ p ∂(MeasureTheory.volume.restrict (Set.Icc (-ε) ε)),
      (∫⁻ θ in Work.Spaces.Iθ, U (Work.FTS.StrongEps.thShift θ p)) ≤ C * J := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with p hp
    have habs : |p| ≤ ε := abs_le.mpr hp
    calc (∫⁻ θ in Work.Spaces.Iθ, U (Work.FTS.StrongEps.thShift θ p))
        ≤ ENNReal.ofReal (Real.exp (3 * |p|)) * J :=
          Work.FTS.StrongEps.JepsHkMem.lintegral_thShift_le U p
      _ ≤ C * J := by
          rw [hC]
          exact mul_le_mul_of_nonneg_right
            (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))) zero_le
  calc ∫⁻ p, (∫⁻ θ in Work.Spaces.Iθ, U (Work.FTS.StrongEps.thShift θ p))
        ∂(MeasureTheory.volume.restrict (Set.Icc (-ε) ε))
      ≤ ∫⁻ p, C * J ∂(MeasureTheory.volume.restrict (Set.Icc (-ε) ε)) :=
        MeasureTheory.lintegral_mono_ae hinner
    _ = C * J * ENNReal.ofReal (2 * ε) := by
        rw [MeasureTheory.lintegral_const, MeasureTheory.Measure.restrict_apply_univ,
          Real.volume_Icc, show ε - (-ε) = 2 * ε by ring]
    _ = ENNReal.ofReal (Real.exp (3 * ε) * (2 * ε)) * J := by
        rw [hC, ENNReal.ofReal_mul (Real.exp_nonneg _)]
        ac_rfl

end Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux
