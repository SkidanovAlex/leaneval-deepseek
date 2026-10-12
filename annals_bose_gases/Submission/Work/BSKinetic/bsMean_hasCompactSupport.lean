import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BSKinetic.Decomp.bsMean_eq_zero_of_far
import Submission.Work.BSKinetic.Decomp.exists_radius_eq_zero_of_hasCompactSupport
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BSKinetic.bsMean_hasCompactSupport`

The moving-box mean

    `bsMean ℓ u ψ = (ℓ³)⁻¹ ∫_{acube ℓ} ψ (ℓ•u + z) dz`

is *localised* in the shift `u`: for `ℓ > 0` and `ψ` compactly supported it vanishes as soon as
the moving box `Λ(u) = ℓu + acube ℓ` has left the support of `ψ`, hence `u ↦ bsMean ℓ u ψ` is
itself compactly supported.

Concretely, `ψ` vanishes outside the ball of radius `Rψ ≥ 0`
(`exists_radius_eq_zero_of_hasCompactSupport`).  If `Rψ + ℓ ≤ ℓ‖u‖` then every point `ℓu + z` of
the moving box (`z ∈ acube ℓ`, so `‖z‖ ≤ ℓ`) satisfies `‖ℓu + z‖ ≥ ℓ‖u‖ − ℓ ≥ Rψ`, whence
`bsMean ℓ u ψ = 0` (`bsMean_eq_zero_of_far`).  Thus the support of `u ↦ bsMean ℓ u ψ` is contained
in the closed ball of radius `(Rψ + ℓ)/ℓ`, a compact set.  (Smoothness of `ψ` is not needed: the
argument uses only the pointwise vanishing of `ψ` far away.)

## Main result

* `bsMean_hasCompactSupport`
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The moving-box mean is compactly supported in the shift.**  For `ℓ > 0` and `ψ` smooth of
compact support, the function `u ↦ bsMean ℓ u ψ` has compact support: it vanishes once the moving
box `Λ(u) = ℓu + acube ℓ` is clear of the support of `ψ`, i.e. for `‖u‖ ≥ (Rψ + ℓ)/ℓ`. -/
theorem bsMean_hasCompactSupport {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    HasCompactSupport (fun u : EuclideanSpace ℝ (Fin 3) => Work.BSKinetic.bsMean ℓ u ψ) := by
  -- `ψ` vanishes outside the ball of radius `R`
  obtain ⟨R, _hR0, hψzero⟩ := Decomp.exists_radius_eq_zero_of_hasCompactSupport hcs
  -- it suffices to show that the support is contained in a large compact ball
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : ℝ³) ((R + ℓ) / ℓ)) ?_
  rw [Function.support_subset_iff]
  intro u hu
  rw [Metric.mem_closedBall, dist_zero_right]
  -- if `u` were outside that ball, the moving box would miss the support of `ψ`
  by_contra hle
  have hlt : (R + ℓ) / ℓ < ‖u‖ := lt_of_not_ge hle
  have hmul : ℓ * ((R + ℓ) / ℓ) < ℓ * ‖u‖ := mul_lt_mul_of_pos_left hlt hℓ
  have hℓR : ℓ * ((R + ℓ) / ℓ) = R + ℓ := by field_simp
  have hfar : R + ℓ ≤ ℓ * ‖u‖ := by rw [← hℓR]; exact le_of_lt hmul
  exact hu (Decomp.bsMean_eq_zero_of_far hℓ hψzero hfar)

end Work.BSKinetic
