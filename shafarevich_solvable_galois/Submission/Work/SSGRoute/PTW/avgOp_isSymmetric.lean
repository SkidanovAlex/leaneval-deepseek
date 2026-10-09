import Mathlib
import Submission.Work.SSGRoute.PTW.RegularRep
import Submission.Work.SSGRoute.PTW.avgOp_regRep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The averaging operator is self-adjoint

For a compact Hausdorff topological group `Q` with a left-invariant probability measure `μ`
(the Haar probability measure), the averaging operator

`avgOp ξ = ∫ g, |regRep g ξ⟩⟨regRep g ξ| dμ(g)`

on `L²(Q, μ)` is self-adjoint (symmetric): `⟪avgOp ξ x, y⟫ = ⟪x, avgOp ξ y⟫`.

Each integrand `rankOneOp (regRep g ξ) (regRep g ξ)` is self-adjoint, and the (conjugate-)linear
functionals `v ↦ ⟪v, y⟫`, `v ↦ ⟪x, v⟫` commute with the Bochner integral.
-/

set_option linter.style.haveILetI false

namespace Work.SSGRoute.PTW

open MeasureTheory Filter Metric
open scoped Topology InnerProductSpace ENNReal ComplexConjugate

variable {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q]
  [T2Space Q] [MeasurableSpace Q] [BorelSpace Q] {μ : Measure Q}
  [Measure.IsMulLeftInvariant μ] [IsProbabilityMeasure μ] [IsLocallyFiniteMeasure μ]
  [μ.InnerRegularCompactLTTop]

/-- The vector-valued integrand `g ↦ ⟪regRep g ξ, x⟫ • regRep g ξ` of `avgOp ξ x` is Bochner
integrable: it is continuous on the compact space `Q` and `μ` is a finite measure. -/
theorem integrable_avgOp_integrand (ξ x : Lp ℂ 2 μ) :
    Integrable (fun g : Q => inner ℂ (regRep (μ := μ) g ξ) x • regRep (μ := μ) g ξ) μ := by
  haveI : IsFiniteMeasureOnCompacts μ :=
    ⟨fun K _ => lt_of_le_of_lt (measure_mono (Set.subset_univ K))
      (IsFiniteMeasure.measure_univ_lt_top (μ := μ))⟩
  refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
  have h1 : Continuous fun g : Q => regRep (μ := μ) g ξ := continuous_regRep_apply (μ := μ) ξ
  have h2 : Continuous fun g : Q => (inner ℂ (regRep (μ := μ) g ξ) x : ℂ) :=
    Continuous.inner (𝕜 := ℂ) h1 continuous_const
  exact h2.smul h1

/-- The conjugate-linear functional `v ↦ ⟪v, y⟫` commutes with the Bochner integral:
`⟪∫ g, f g, y⟫ = ∫ g, ⟪f g, y⟫`. -/
theorem inner_integral {f : Q → Lp ℂ 2 μ} (hf : Integrable f μ) (y : Lp ℂ 2 μ) :
    inner ℂ (∫ g, f g ∂μ) y = ∫ g, inner ℂ (f g) y ∂μ := by
  calc inner ℂ (∫ g, f g ∂μ) y
      = starRingEnd ℂ (inner ℂ y (∫ g, f g ∂μ)) :=
        (inner_conj_symm (𝕜 := ℂ) (x := ∫ g, f g ∂μ) (y := y)).symm
    _ = starRingEnd ℂ (∫ g, inner ℂ y (f g) ∂μ) := by
        rw [integral_inner (𝕜 := ℂ) hf y]
    _ = ∫ g, starRingEnd ℂ (inner ℂ y (f g)) ∂μ := by rw [integral_conj]
    _ = ∫ g, inner ℂ (f g) y ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun g => ?_)
        exact inner_conj_symm (𝕜 := ℂ) (x := f g) (y := y)

/-- `avgOp ξ = ∫ g, |regRep g ξ⟩⟨regRep g ξ|` is a self-adjoint operator: each integrand
`rankOneOp a a` is self-adjoint (`⟪rankOneOp a a x, y⟫ = ⟪x, rankOneOp a a y⟫`), and the inner
product commutes with the Bochner integral.  Useful API: `avgOp_regRep.lean` (`avgOp_apply`),
`RegularRep.lean` (`rankOneOp_apply`, `integrable_rankOneOp` in `avgOp_regRep.lean`),
`ContinuousLinearMap.integral_apply`, `MeasureTheory.integral_inner`. -/
theorem avgOp_isSymmetric {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q] {μ : MeasureTheory.Measure Q}
    [MeasureTheory.Measure.IsMulLeftInvariant μ] [MeasureTheory.IsProbabilityMeasure μ]
    [MeasureTheory.IsLocallyFiniteMeasure μ] [MeasureTheory.Measure.InnerRegularCompactLTTop μ]
    (ξ : MeasureTheory.Lp ℂ 2 μ) :
    ((Work.SSGRoute.PTW.avgOp (μ := μ) ξ : MeasureTheory.Lp ℂ 2 μ →L[ℂ] MeasureTheory.Lp ℂ 2 μ) :
        MeasureTheory.Lp ℂ 2 μ →ₗ[ℂ] MeasureTheory.Lp ℂ 2 μ).IsSymmetric := by
  intro x y
  change inner ℂ (avgOp (μ := μ) ξ x) y = inner ℂ x (avgOp (μ := μ) ξ y)
  rw [avgOp_apply (μ := μ) ξ x, avgOp_apply (μ := μ) ξ y,
    inner_integral (integrable_avgOp_integrand ξ x) y,
    ← integral_inner (𝕜 := ℂ) (integrable_avgOp_integrand ξ y) x]
  have hpt : ∀ g : Q,
      inner ℂ (inner ℂ (regRep (μ := μ) g ξ) x • regRep (μ := μ) g ξ) y =
        inner ℂ x (inner ℂ (regRep (μ := μ) g ξ) y • regRep (μ := μ) g ξ) := by
    intro g
    rw [inner_smul_left, inner_smul_right,
      ← inner_conj_symm (x := x) (y := regRep (μ := μ) g ξ)]
    ring
  exact integral_congr_ae (Eventually.of_forall hpt)

end Work.SSGRoute.PTW
