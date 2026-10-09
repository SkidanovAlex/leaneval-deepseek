import Mathlib
import Submission.Work.SSGRoute.PTW.RegularRep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The averaging operator intertwines the regular representation

For a compact Hausdorff topological group `Q` with a left-invariant probability measure `μ`
(the Haar probability measure), the averaging operator

`avgOp ξ = ∫ g, |regRep g ξ⟩⟨regRep g ξ| dμ(g)`

on `L²(Q, μ)` commutes with the (left) regular representation:

`avgOp ξ (regRep h η) = regRep h (avgOp ξ η)`.

This is the intertwining property of the averaging operator used in the spectral-theoretic
proof that the regular representation of a compact group separates points.

The proof follows the change of variables `g ↦ h⁻¹ g` (legal because `μ` is left invariant),
together with the fact that `regRep h` is unitary (it preserves the inner product) and
continuous linear, hence commutes with the Bochner integral.
-/

set_option linter.style.haveILetI false

namespace Work.SSGRoute.PTW

open MeasureTheory Filter Metric
open scoped Topology InnerProductSpace ENNReal

variable {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q]
  [T2Space Q] [MeasurableSpace Q] [BorelSpace Q] {μ : Measure Q}
  [Measure.IsMulLeftInvariant μ] [IsProbabilityMeasure μ] [IsLocallyFiniteMeasure μ]
  [μ.InnerRegularCompactLTTop]

/-- `regRep h` is an isometry, hence antilipschitz with constant `1`.  This lets us commute it
with the Bochner integral without any integrability assumption
(`ContinuousLinearMap.integral_comp_comm'`). -/
theorem antilipschitz_regRep (h : Q) : AntilipschitzWith 1 (regRep (μ := μ) h) := by
  refine AntilipschitzWith.of_le_mul_dist (fun x y => ?_)
  simp only [NNReal.coe_one, one_mul]
  rw [regRep_apply, regRep_apply, DomMulAct.dist_smul_Lp]

/-- `regRep h` is unitary: it preserves the inner product. -/
theorem inner_regRep_apply (h : Q) (a b : Lp ℂ 2 μ) :
    inner ℂ (regRep (μ := μ) h a) (regRep (μ := μ) h b) = inner ℂ a b :=
  (LinearMap.norm_map_iff_inner_map_map (regRep (μ := μ) h)).mp
    (fun x => norm_regRep_apply h x) a b

/-- `regRep h` commutes with the Bochner integral. -/
theorem regRep_integral (h : Q) (F : Q → Lp ℂ 2 μ) :
    regRep (μ := μ) h (∫ g, F g ∂μ) = ∫ g, regRep (μ := μ) h (F g) ∂μ := by
  rw [← ContinuousLinearMap.integral_comp_comm' (regRep (μ := μ) h) (antilipschitz_regRep h) F]

/-- **The change of variables identity.**  After the substitution `g ↦ h⁻¹ g` the inner product
`⟪regRep (h⁻¹ g) ξ, η⟫` becomes `⟪regRep g ξ, regRep h η⟫`. -/
theorem inner_regRep_inv_mul (h g : Q) (ξ η : Lp ℂ 2 μ) :
    inner ℂ (regRep (μ := μ) (h⁻¹ * g) ξ) η =
      inner ℂ (regRep (μ := μ) g ξ) (regRep (μ := μ) h η) := by
  have h1 : regRep (μ := μ) h (regRep (μ := μ) (h⁻¹ * g) ξ) = regRep (μ := μ) g ξ := by
    rw [← regRep_mul_apply, mul_inv_cancel_left]
  rw [← inner_regRep_apply h (regRep (μ := μ) (h⁻¹ * g) ξ) η, h1]

/-- The operator-valued integrand `g ↦ |regRep g ξ⟩⟨regRep g ξ|` is Bochner integrable
(continuous on the compact space `Q`, with values in a normed space). -/
theorem integrable_rankOneOp (ξ : Lp ℂ 2 μ) :
    Integrable (fun g : Q =>
      rankOneOp (μ := μ) (regRep (μ := μ) g ξ) (regRep (μ := μ) g ξ)) μ := by
  haveI : IsFiniteMeasureOnCompacts μ :=
    ⟨fun K _ => lt_of_le_of_lt (measure_mono (Set.subset_univ K))
      (IsFiniteMeasure.measure_univ_lt_top (μ := μ))⟩
  refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
  rw [show (fun g : Q => rankOneOp (μ := μ) (regRep (μ := μ) g ξ) (regRep (μ := μ) g ξ))
      = fun g : Q => InnerProductSpace.rankOne ℂ (regRep (μ := μ) g ξ)
          (regRep (μ := μ) g ξ) from by
        funext g; rw [rankOneOp, InnerProductSpace.rankOne]; rfl]
  have h1 : Continuous (fun g : Q =>
      (ContinuousLinearMap.smulRightL ℂ (Lp ℂ 2 μ) (Lp ℂ 2 μ))
        (innerSL ℂ (regRep (μ := μ) g ξ))) :=
    (ContinuousLinearMap.smulRightL ℂ (Lp ℂ 2 μ) (Lp ℂ 2 μ)).continuous.comp
      ((innerSL ℂ).continuous.comp (continuous_regRep_apply ξ))
  have h2 : Continuous (fun g : Q => (regRep (μ := μ) g ξ : Lp ℂ 2 μ)) :=
    continuous_regRep_apply ξ
  have h3 := (IsBoundedBilinearMap.continuous isBoundedBilinearMap_apply).comp (h1.prodMk h2)
  refine h3.congr ?_
  intro g
  rw [InnerProductSpace.rankOne_def]
  rfl

/-- Unfolding the averaging operator on a vector. -/
theorem avgOp_apply (ξ : Lp ℂ 2 μ) (η : Lp ℂ 2 μ) :
    avgOp (μ := μ) ξ η =
      ∫ g, inner ℂ (regRep (μ := μ) g ξ) η • regRep (μ := μ) g ξ ∂μ := by
  rw [avgOp]
  rw [ContinuousLinearMap.integral_apply (integrable_rankOneOp (μ := μ) ξ) η]
  refine integral_congr_ae (Eventually.of_forall (fun g => ?_))
  simp [rankOneOp_apply]

/-- **The averaging operator intertwines the regular representation.** -/
theorem avgOp_regRep {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q] {μ : MeasureTheory.Measure Q}
    [MeasureTheory.Measure.IsMulLeftInvariant μ] [MeasureTheory.IsProbabilityMeasure μ]
    [MeasureTheory.IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    (ξ : MeasureTheory.Lp ℂ 2 μ) (h : Q) (η : MeasureTheory.Lp ℂ 2 μ) :
    Work.SSGRoute.PTW.avgOp (μ := μ) ξ (Work.SSGRoute.PTW.regRep (μ := μ) h η) =
      Work.SSGRoute.PTW.regRep (μ := μ) h (Work.SSGRoute.PTW.avgOp (μ := μ) ξ η) := by
  calc avgOp (μ := μ) ξ (regRep (μ := μ) h η)
      = ∫ g, inner ℂ (regRep (μ := μ) g ξ) (regRep (μ := μ) h η) •
          regRep (μ := μ) g ξ ∂μ :=
          avgOp_apply ξ (regRep h η)
    _ = ∫ g, inner ℂ (regRep (μ := μ) (h⁻¹ * g) ξ) η • regRep (μ := μ) g ξ ∂μ := by
          refine integral_congr_ae (Eventually.of_forall (fun g => ?_))
          simp only [inner_regRep_inv_mul]
    _ = ∫ g, inner ℂ (regRep (μ := μ) g ξ) η • regRep (μ := μ) (h * g) ξ ∂μ := by
          rw [← integral_mul_left_eq_self (fun y =>
            inner ℂ (regRep (μ := μ) y ξ) η • regRep (μ := μ) (h * y) ξ) h⁻¹]
          simp only [mul_inv_cancel_left]
    _ = ∫ g, regRep (μ := μ) h
          (inner ℂ (regRep (μ := μ) g ξ) η • regRep (μ := μ) g ξ) ∂μ := by
          refine integral_congr_ae (Eventually.of_forall (fun g => ?_))
          simp only [ContinuousLinearMap.map_smul, ← regRep_mul_apply]
    _ = regRep (μ := μ) h
          (∫ g, inner ℂ (regRep (μ := μ) g ξ) η • regRep (μ := μ) g ξ ∂μ) :=
          (regRep_integral h _).symm
    _ = regRep (μ := μ) h (avgOp (μ := μ) ξ η) := by rw [avgOp_apply]

end Work.SSGRoute.PTW
