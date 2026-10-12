import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Decomp.bsShift_L2_tendsto
import Submission.Work.BoseKinLoc.Gap.gapBare_eq_expand
import Submission.Work.BoseKinLoc.Gap.integral_lamBox_eq_acube
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Kinetic.gapWord_measurable`

**The gap word `u ↦ bℓ⁻² ‖Q_{Λ(u)}ψ‖²_{Λ(u)}` is a.e. strongly measurable in the translation
parameter `u`** (FS `eq:DefT`'s second piece as a function of the box position).

## Proof

The mean-free box mass expands as the variance over the moving box
(`Work.BoseKinLoc.Gap.gapBare_eq_expand`),
`gapBare ℓ u ψ = ∫_{Λ(u)} ψ² − ℓ³·(bsMean ℓ u ψ)²`, and the box mass is `ℓ³` times the box mean
of `ψ²` (`Work.BoseKinLoc.Gap.integral_lamBox_eq_acube`), so

`gapBare ℓ u ψ = ℓ³·bsMean ℓ u (ψ²) − ℓ³·(bsMean ℓ u ψ)²`.

Both box means are continuous in `u` for a continuous, compactly supported `ψ`
(`Work.BSKinetic.Decomp.continuous_bsMean`), hence so is `u ↦ gapBare ℓ u ψ`, and a continuous
function is a.e. strongly measurable.  The prefactor `bℓ⁻²` is a constant.
-/

noncomputable section

open MeasureTheory
open scoped Topology Real ENNReal

namespace Work.BoseKinLoc.Kinetic

open Submission.BoseGases
open Work.BSKinetic

/-- The mean-free box mass is continuous in the translation parameter. -/
theorem continuous_gapBare {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Continuous (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.gapBare ℓ u ψ) := by
  -- `ψ²` is smooth with compact support
  have hψ2_cd : ContDiff ℝ (⊤ : ENat) (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z) ^ 2) := by
    simpa [pow_two] using hψ.mul hψ
  have hψ2_cs : HasCompactSupport (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z) ^ 2) :=
    hcs.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num : (0 : ℝ) ^ 2 = 0)
  -- the two box means are continuous in `u`
  have hcontB : Continuous (fun u : EuclideanSpace ℝ (Fin 3) => bsMean ℓ u ψ) :=
    Work.BSKinetic.Decomp.continuous_bsMean hψ.continuous hcs
  have hcontB2 : Continuous
      (fun u : EuclideanSpace ℝ (Fin 3) => bsMean ℓ u (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z) ^ 2)) :=
    Work.BSKinetic.Decomp.continuous_bsMean hψ2_cd.continuous hψ2_cs
  -- the box mass is `ℓ³` times the box mean of `ψ²`
  have hboxmass : ∀ u : EuclideanSpace ℝ (Fin 3),
      (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z) ^ 2)
        = ℓ ^ 3 * bsMean ℓ u (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z) ^ 2) := by
    intro u
    rw [Work.BoseKinLoc.Gap.integral_lamBox_eq_acube ℓ hℓ (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z) ^ 2) u,
      bsMean]
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 3 hℓ.ne'), one_mul]
  have hfun : (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.gapBare ℓ u ψ)
      = fun u : EuclideanSpace ℝ (Fin 3) =>
          ℓ ^ 3 * bsMean ℓ u (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z) ^ 2)
            - ℓ ^ 3 * (bsMean ℓ u ψ) ^ 2 := by
    funext u
    rw [Work.BoseKinLoc.Gap.gapBare_eq_expand ℓ hℓ ψ hψ u, hboxmass u]
  rw [hfun]
  exact ((continuous_const.mul hcontB2).sub (continuous_const.mul (hcontB.pow 2)))

theorem gapWord_measurable {ℓ b : ℝ} (hℓ : 0 < ℓ) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    MeasureTheory.AEStronglyMeasurable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.gapWord ℓ b u ψ) := by
  have hbare : MeasureTheory.AEStronglyMeasurable
      (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.gapBare ℓ u ψ) :=
    (continuous_gapBare hℓ hψ hcs).aestronglyMeasurable
  have hword : (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.gapWord ℓ b u ψ)
      = fun u : EuclideanSpace ℝ (Fin 3) =>
          (b * ℓ ^ (-2 : ℤ)) * Work.BoseKinLoc.gapBare ℓ u ψ := by
    funext u
    rfl
  rw [hword]
  exact hbare.const_mul _

end Work.BoseKinLoc.Kinetic
