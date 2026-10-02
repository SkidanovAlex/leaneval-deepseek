import Mathlib
import Submission.Work.ThomBordism.CofAtlas.Signs
import Submission.Work.ThomBordism.CofAtlas.Structure
import Submission.Work.ThomBordism.CofAtlas.newIsManifold

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The boundary of the corrected chart structure on the coframed level set

`Work.ThomBordism.CofAtlas.newChartedSpace D` puts the charts
`newChart D x = ((lvlChart x) ≫ₕ (reflectMap x)).restr (src x)` on the coframed level set
`D.S.Pre`: the `Lvl` chart at `x`, post-composed with the reflection of the half-space whenever
that makes the chart positively oriented relative to the framing.

This file identifies the *boundary* of the resulting manifold with the boundary of `M`:

* the extended `newChart x`, evaluated at `x`, has zeroth coordinate `chartEps D.S x`
  (`newChart_extend_apply_coord`); the reflection `reflectLin D x` fixes the zeroth coordinate and
  the `Lvl` chart at its centre sends `x` to `chartEps D.S x • e₀ 8`;
* `(𝓡∂ 9).boundary` is read in the chart, `IsBoundaryPoint x ↔ (extChartAt (𝓡∂ 9) x x) 0 = 0`, and
  the zeroth coordinate is exactly what says whether the underlying point lies on the boundary of
  the ambient manifold `M` (`Lvl.Setup.chartEps_eq_zero_iff`).

The result `newBoundary` is one of the two structural inputs (together with
`IsManifold`, proved in `newIsManifold`) of the final theorem
`Work.ThomBordism.levelSet_positiveAtlas_of_coframing`.
-/

namespace Work.ThomBordism.CofAtlas

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter ModelWithCorners
open Work.PTGeometric
open Work.PTGeometric.Lvl

set_option linter.style.haveILetI false

variable {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) ((⊤ : ENat) : WithTop ENat) M]

/-- **The zeroth coordinate of the corrected chart at its centre.**  The extended `newChart x`
evaluated at `x` has zeroth coordinate `chartEps D.S x`, i.e. the sign of the level function at
`x`; this is what makes the boundary of the corrected chart structure the boundary of `M`. -/
theorem newChart_extend_apply_coord (D : Cof k n M) (x : D.S.Pre) :
    ((𝓡∂ 9) (D.newChart x x)).ofLp 0 = D.S.chartEps x := by
  have hlv : (𝓡∂ 9) (D.lvlChart x x) = D.S.chartFun x x := by
    show (𝓡∂ 9) (Lvl.Setup.chartAt D.S x x) = _
    rw [Lvl.Setup.chartAt_apply_of_mem D.S x (D.mem_chartSource_self x)]
    rfl
  rw [newChart_apply, reflectMap_coord, hlv, reflectLin_coord_zero]
  rw [Lvl.Setup.chartFun_self D.S x]
  simp [PiLp.smul_apply, Work.Surgery.e₀_apply_zero]

theorem newBoundary
    {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) ((⊤ : ENat) : WithTop ENat) M]
    (D : Work.ThomBordism.CofAtlas.Cof k n M) :
    letI : ChartedSpace (EuclideanHalfSpace 9) D.S.Pre :=
      Work.ThomBordism.CofAtlas.newChartedSpace D
    (modelWithCornersEuclideanHalfSpace 9).boundary D.S.Pre =
      {x : D.S.Pre | (x : M) ∈
        (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M} := by
  letI : ChartedSpace (EuclideanHalfSpace 9) D.S.Pre :=
    Work.ThomBordism.CofAtlas.newChartedSpace D
  ext x
  rw [Set.mem_ofPred_eq]
  show (𝓡∂ 9).IsBoundaryPoint x ↔
    (x : M) ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M
  rw [ModelWithCorners.isBoundaryPoint_iff,
    frontier_range_modelWithCornersEuclideanHalfSpace, Set.mem_ofPred_eq,
    extChartAt_coe, Function.comp_apply]
  have hchart : chartAt (EuclideanHalfSpace 9) x = D.newChart x := rfl
  rw [hchart, newChart_extend_apply_coord, eq_comm, Lvl.Setup.chartEps_eq_zero_iff]

end Work.ThomBordism.CofAtlas
