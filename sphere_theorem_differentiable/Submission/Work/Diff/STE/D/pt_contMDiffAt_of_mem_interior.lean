import Mathlib
import Submission.Work.Diff.STE.B3.Comp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the chart parametrisation `pt i` on the interior of the chart target

`Work.Diff.STE.B3Data.pt i z = (extChartAt I (x₀ i)).symm (flatToE (x₀ i) z)` is the point of `M`
with flat coordinate `z` in the chart at `x₀ i`.  Since `flatToE (x₀ i)` is affine (hence `C^∞`)
and the inverse extended chart `(extChartAt I (x₀ i)).symm` is `C^∞` on its target
(`contMDiffOn_extChartAt_symm`), the composite is `C^∞` at `z` as soon as `z` is such that
`flatToE (x₀ i) z` lies in the *interior* of the chart target — the interior (rather than the
target itself) is what is needed because `(extChartAt I x).target` is not open for a model with
boundary; this is the reason the request is stated without `[I.Boundaryless]`.
-/

open scoped ContDiff

namespace Work.Diff.STE.D

/-- `flatToE x₀` is `C^∞`: it is the affine map `z ↦ equivFun.symm (equivFun ((extChartAt I x₀) x₀)
+ z)`. -/
lemma contDiff_flatToE {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (x₀ : M) :
    ContDiff ℝ ∞ (Work.Diff.STE.flatToE (I := I) x₀) := by
  have h1 : ContDiff ℝ ∞ (fun z : Fin (Module.finrank ℝ E) → ℝ =>
      (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀) + z) :=
    contDiff_const.add contDiff_id
  have h2 : ContDiff ℝ ∞ (fun w : Fin (Module.finrank ℝ E) → ℝ =>
      (Module.finBasis ℝ E).equivFun.symm w) :=
    (((Module.finBasis ℝ E).equivFun.symm :
        (Fin (Module.finrank ℝ E) → ℝ) ≃ₗ[ℝ] E) :
        (Fin (Module.finrank ℝ E) → ℝ) →ₗ[ℝ] E).toContinuousLinearMap.contDiff
  exact h2.comp h1

theorem pt_contMDiffAt_of_mem_interior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ)
    (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ i) z ∈
      interior ((extChartAt I (D.x₀ i)).target)) :
    ContMDiffAt (modelWithCornersSelf ℝ (Fin (Module.finrank ℝ E) → ℝ)) I
      ((⊤ : ENat) : WithTop ENat) (D.pt i) z := by
  -- smoothness of the inverse extended chart on its target
  have h1 : ContMDiffAt (modelWithCornersSelf ℝ E) I ∞
      (↑(extChartAt I (D.x₀ i)).symm) (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) :=
    (contMDiffOn_extChartAt_symm (I := I) (n := ∞) (D.x₀ i)).contMDiffAt
      (Filter.mem_of_superset (isOpen_interior.mem_nhds hz) interior_subset)
  -- smoothness of the affine flat coordinate
  have h2 : ContMDiffAt (modelWithCornersSelf ℝ (Fin (Module.finrank ℝ E) → ℝ))
      (modelWithCornersSelf ℝ E) ∞ (Work.Diff.STE.flatToE (I := I) (D.x₀ i)) z :=
    contMDiffAt_iff_contDiffAt.mpr
      ((contDiff_flatToE (I := I) (M := M) (D.x₀ i)).contDiffAt)
  exact h1.comp z h2

end Work.Diff.STE.D
