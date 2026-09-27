import Mathlib
import Submission.Work.Geo.Radial.ChartImage

namespace Work.Geo.Radial

open Set Metric
open Work.Geo.Radial

/-- The choice-based inverse `chartInv c` of a cube chart is continuous on the chart image
`c.toFun '' openCube 1`. -/
theorem continuousOn_chartInv {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c : PL.CubeChart n M) : ContinuousOn (chartInv c) (chartImage c) := by
  let f : PL.openCube (n := n) 1 → M := (PL.openCube (n := n) 1).domRestrict c.toFun
  have hf : IsOpenMap f := c.emb.isOpenMap
  have hmem : ∀ p : M, chartInv c p ∈ PL.openCube (n := n) 1 := by
    intro p
    by_cases hp : p ∈ chartImage c
    · exact chartInv_mem c hp
    · rw [chartInv_of_notMem c hp]
      simp [PL.openCube]
  let finv : M → PL.openCube (n := n) 1 := fun p => ⟨chartInv c p, hmem p⟩
  have hleft : Function.LeftInverse finv f := by
    intro x
    apply Subtype.ext
    show chartInv c (f x) = x.val
    have hfx : f x = c.toFun x.val := rfl
    rw [hfx, chartInv_apply c x.2]
  have hcont : ContinuousOn finv (Set.range f) :=
    hf.continuousOn_range_of_leftInverse hleft
  have hrange : Set.range f = chartImage c := Set.range_domRestrict _ _
  rw [hrange] at hcont
  have hcomp := continuous_subtype_val.comp_continuousOn hcont
  simpa [finv, Function.comp_def] using hcomp

end Work.Geo.Radial
