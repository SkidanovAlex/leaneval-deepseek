import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel
import Submission.Work.BoseKinLoc.Momentum.memLp_kinFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.PortSmallB.kinFTSqLintegralOne`

The unweighted (`p`-mass) Plancherel estimate for the corpus's `p`-convention kinetic Fourier
transform `kinFT F p = ∫_y e^{−i⟪p,y⟫}F(y)dy`: for a `C¹` compactly supported real `u`,

`∫⁻_p ‖kinFT u p‖² ≤ (2π)³ · ∫_x u(x)²`,

i.e. the `L²`-Plancherel identity `∫_p ‖kinFT F p‖² = (2π)³ ∫_x ‖F x‖²` (the `L¹ ∩ L²` version
`Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel`) combined with the passage from the Bochner
integral to the `ℝ≥0∞`-valued integral (`ofReal_integral_eq_lintegral_ofReal`).  The `C¹` +
compact-support hypotheses give `F = (u : ℝ³ → ℂ) ∈ L¹ ∩ L²`, and
`Work.BoseKinLoc.Momentum.memLp_kinFT` makes `p ↦ ‖kinFT F p‖²` integrable, so the `ofReal`
conversion is legitimate.

This is the (unweighted) sibling of `kinFTEnergyLintegralOne` (where the `p`-integrand carries a
factor `‖p‖²` and the right-hand side the full gradient energy).
-/

noncomputable section

open MeasureTheory
open scoped Topology Real

namespace Work.BoseB1Cube.PortSmallB

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

theorem kinFTSqLintegralOne {u : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hu : ContDiff ℝ 1 u) (hcs : HasCompactSupport u) {C : ℝ}
    (hC : (∫ z : EuclideanSpace ℝ (Fin 3), u z ^ 2) ≤ C) :
    (∫⁻ p : EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (u z : ℂ)) p‖ ^ 2))
      ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3 * C) := by
  -- `F = (u : ℝ³ → ℂ)` is continuous, compactly supported, hence `L¹ ∩ L²`.
  have hcont : Continuous (fun z : E3 => (u z : ℂ)) := Complex.continuous_ofReal.comp hu.continuous
  have hcsC : HasCompactSupport (fun z : E3 => (u z : ℂ)) :=
    hcs.comp_left (by simp : ((0 : ℝ) : ℂ) = 0)
  have hint : Integrable (fun z : E3 => (u z : ℂ)) :=
    hcont.integrable_of_hasCompactSupport hcsC
  have hmlp : MemLp (fun z : E3 => (u z : ℂ)) 2 := hcont.memLp_of_hasCompactSupport hcsC
  -- Plancherel for `L¹ ∩ L²`: `∫_p ‖kinFT F p‖² = (2π)³ ∫_x ‖F x‖²`.
  have hpl := Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel hint hmlp
  -- Integrability of the `p`-integrand, needed for the `ofReal` ↔ `lintegral` conversion.
  have hInt : Integrable (fun p : E3 =>
      ‖Submission.BoseGases.kinFT (fun z : E3 => (u z : ℂ)) p‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm
      (Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable hint).aestronglyMeasurable).mp
      (Work.BoseKinLoc.Momentum.memLp_kinFT hint hmlp)
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
    (Filter.Eventually.of_forall (fun p => sq_nonneg _))]
  -- It remains to compare the two real integrals.
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hpl]
  have hnorm : (∫ x : E3, ‖(fun z : E3 => (u z : ℂ)) x‖ ^ 2) = ∫ x, u x ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    show ‖((u x : ℝ) : ℂ)‖ ^ 2 = u x ^ 2
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  rw [hnorm]
  exact mul_le_mul_of_nonneg_left hC (by positivity)

end Work.BoseB1Cube.PortSmallB
