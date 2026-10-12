import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.chiSmallB_eq_zero_of_volume_dlBox_eq_zero
import Submission.Work.BoseFixB1S.corrPlanchMarg
import Submission.Work.BoseFixB1S.kineticCruxParsed
import Submission.Work.BoseFixB1S.weightedPlancherelKinFT
import Submission.Work.BoseFixB1S.win.chiSmallB_kinFT_decay
import Submission.Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel
import Submission.Work.LocRepoint.chiSmallB_sq_integral_u
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S.CubeWindow

open MeasureTheory

set_option maxHeartbeats 1000000

/-- **Per-box Plancherel at the cube cutoff.**  For `0 < ℓ`, `0 < d`, smooth `w` and every `u`,
the `p`-space mass of the cut state `z ↦ χ_{B(u)}(z)·w(z)` is `(2π)³` times its `x`-space `L²`
mass:

`∫_p ‖bsPsi (χ_{B(u)}·w) p‖² = (2π)³ ∫_z χ_{B(u)}(z)²·w(z)²`.

Unlike the ball twin (`Work.BoseFixB1S.integral_bsPsi_chiB_mul_sq`, which uses the Schwartz
Plancherel `Work.BSKinetic.plancherel_pconv`), the sliding cube cut-off `chiSmallB M ℓ d u` is
only `C^{M-1}` and *not* smooth, so `plancherel_pconv` does not apply.  What is needed instead is
only that the cut state be continuous with compact support, hence `L¹ ∩ L²`, and for those the
`L¹∩L²` Plancherel `Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel` applies:

* `chiSmallB M ℓ d u` is continuous (`chiSmallB_continuous`), bounded by its big-box factor
  (`chiSmallB_support_big_box`), and compactly supported (`chiSmallB_hasCompactSupport`, whose
  support is contained in the ball of radius `ℓ/2`);
* so `z ↦ χ_{B(u)}(z)·w(z)` is continuous with compact support (`hw.continuous`), as is its
  complexification, which is therefore `Integrable` and `MemLp 2`. -/
lemma integral_bsPsi_chiSmallB_mul_sq (M : ℕ) (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    {w : EuclideanSpace ℝ (Fin 3) → ℝ} (hw : ContDiff ℝ (⊤ : ENat) w)
    (u : EuclideanSpace ℝ (Fin 3)) :
    (∫ p : EuclideanSpace ℝ (Fin 3), ‖Work.BSKinetic.Decomp.bsPsi (fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiSmallB M ℓ d u z * w z) p‖ ^ 2)
      = (2 * Real.pi) ^ 3 * (∫ z : EuclideanSpace ℝ (Fin 3),
          (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2 * (w z) ^ 2) := by
  have hcont : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiSmallB M ℓ d u z * w z) :=
    (Work.BoseFixB1S.chiSmallB_continuous hM ℓ d u).mul hw.continuous
  have hcs : HasCompactSupport (fun z : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiSmallB M ℓ d u z * w z) :=
    (Submission.BoseGases.chiSmallB_hasCompactSupport hM hℓ u).mul_right
  have hFcont : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      ((Submission.BoseGases.chiSmallB M ℓ d u z * w z : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hcont
  have hFcs : HasCompactSupport (fun z : EuclideanSpace ℝ (Fin 3) =>
      ((Submission.BoseGases.chiSmallB M ℓ d u z * w z : ℝ) : ℂ)) :=
    hcs.comp_left (show ((0 : ℝ) : ℂ) = 0 from rfl)
  have hpl := Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel
    (hFcont.integrable_of_hasCompactSupport hFcs)
    (hFcont.memLp_of_hasCompactSupport hFcs : MeasureTheory.MemLp _ 2 MeasureTheory.volume)
  rw [show (∫ p : EuclideanSpace ℝ (Fin 3), ‖Work.BSKinetic.Decomp.bsPsi
        (fun z : EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.chiSmallB M ℓ d u z * w z) p‖ ^ 2)
      = (2 * Real.pi) ^ 3 * (∫ x : EuclideanSpace ℝ (Fin 3),
          ‖(fun z : EuclideanSpace ℝ (Fin 3) =>
            ((Submission.BoseGases.chiSmallB M ℓ d u z * w z : ℝ) : ℂ)) x‖ ^ 2) from by
      simpa only [Work.BSKinetic.Decomp.bsPsi] using hpl]
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  show ‖(((Submission.BoseGases.chiSmallB M ℓ d u z * w z : ℝ)) : ℂ)‖ ^ 2 = _
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
  ring

/-- **Plancherel/partition at the cube cutoff**: for a smooth `w`, if the `u`-marginal
`u ↦ ∫_z χ_{B(u)}(z)²w(z)²` is integrable and its `u`-integral collapses to `∫_z χ(x/ℓ)²w(z)²`
(the pointwise partition `∫_u χ_{B(u)}(z)² du = χ(z/ℓ)²`), then the `p`-space marginal
`u ↦ ∫_p ‖bsPsi (χ_{B(u)}·w) p‖²` is integrable and its `u`-integral is `(2π)³` times the same
`x`-space mass.  Cube twin of `Work.BoseFixB1S.corrPlanchMarg`; the per-`u` identity goes through
the `L¹∩L²` Plancherel `Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel` (the window is only
`C^{M-1}`, not smooth). -/
theorem planchMargCube (M : ℕ) (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {w : EuclideanSpace ℝ (Fin 3) → ℝ} (hw : ContDiff ℝ (⊤ : ENat) w)
    (hint : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) => ∫ z : EuclideanSpace ℝ (Fin 3),
      (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2 * (w z) ^ 2))
    (heq : (∫ u : EuclideanSpace ℝ (Fin 3), ∫ z : EuclideanSpace ℝ (Fin 3),
        (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2 * (w z) ^ 2)
      = ∫ z : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chiScale ℓ z) ^ 2 * (w z) ^ 2) :
    MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) => ∫ p : EuclideanSpace ℝ (Fin 3),
        ‖Work.BSKinetic.Decomp.bsPsi (fun z : EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.chiSmallB M ℓ d u z * w z) p‖ ^ 2)
      ∧ (∫ u : EuclideanSpace ℝ (Fin 3), ∫ p : EuclideanSpace ℝ (Fin 3),
            ‖Work.BSKinetic.Decomp.bsPsi (fun z : EuclideanSpace ℝ (Fin 3) =>
              Submission.BoseGases.chiSmallB M ℓ d u z * w z) p‖ ^ 2)
        = (2 * Real.pi) ^ 3 *
            (∫ z : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chiScale ℓ z) ^ 2 * (w z) ^ 2) := by
  have hpoint : ∀ u : EuclideanSpace ℝ (Fin 3),
      (∫ p : EuclideanSpace ℝ (Fin 3), ‖Work.BSKinetic.Decomp.bsPsi (fun z : EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.chiSmallB M ℓ d u z * w z) p‖ ^ 2)
        = (2 * Real.pi) ^ 3 * (∫ z : EuclideanSpace ℝ (Fin 3),
            (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2 * (w z) ^ 2) :=
    fun u => integral_bsPsi_chiSmallB_mul_sq M hM hℓ hw u
  refine ⟨?_, ?_⟩
  · exact (hint.const_mul ((2 * Real.pi) ^ 3)).congr
      (Filter.Eventually.of_forall fun u => (hpoint u).symm)
  · have hfuneq : (fun u : EuclideanSpace ℝ (Fin 3) => ∫ p : EuclideanSpace ℝ (Fin 3),
          ‖Work.BSKinetic.Decomp.bsPsi (fun z : EuclideanSpace ℝ (Fin 3) =>
            Submission.BoseGases.chiSmallB M ℓ d u z * w z) p‖ ^ 2)
        = fun u : EuclideanSpace ℝ (Fin 3) => (2 * Real.pi) ^ 3 *
            (∫ z : EuclideanSpace ℝ (Fin 3),
              (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2 * (w z) ^ 2) := funext hpoint
    rw [hfuneq, MeasureTheory.integral_const_mul, heq]

end Work.BoseFixB1S.CubeWindow
