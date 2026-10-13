import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXT.AgmonND.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The pointwise derivative of `agmonF v`

`agmonF v x = x * (v x * w x) ^ 2` with `w x = (1 + x) ^ 2 / x ^ 2`.  On `(0, ∞)` this is
`(v x) ^ 2 * (1 + x) ^ 4 / x ^ 3`, and differentiating that rational expression gives the
function `agmonFderiv v v'` whenever `v` has derivative `v'` on `(0, ∞)`.
-/

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.AgmonND

theorem hasDerivAt_agmonF {v v' : ℝ → ℝ}
    (hderiv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt v (v' x) x) :
    ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.FTS_RegExport.RXT.agmonF v)
        (Work.FTS_RegExport.RXT.agmonFderiv v v' x) x := by
  intro x hx
  have hx0 : 0 < x := hx
  have hxne : x ≠ 0 := ne_of_gt hx0
  have h1x : (1 : ℝ) + x ≠ 0 := by positivity
  -- On a neighbourhood of `x > 0`, `agmonF v` is the rational function `v²(1+y)⁴/y³`.
  have hev : Work.FTS_RegExport.RXT.agmonF v =ᶠ[𝓝 x]
      fun y : ℝ => (v y) ^ 2 * (1 + y) ^ 4 / y ^ 3 := by
    filter_upwards [isOpen_Ioi.mem_nhds hx0] with y hy
    have hyne : y ≠ 0 := ne_of_gt hy
    simp only [Work.FTS_RegExport.RXT.agmonF, Work.Spaces.w]
    field_simp
  have hv2 : HasDerivAt (fun y : ℝ => (v y) ^ 2) (2 * v x * v' x) x := by
    have h := (hderiv x hx).pow 2
    convert h using 1 <;> ring
  have h1xy : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    have h := (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)
    convert h using 1
    · funext y; simp
    · simp
  have hp : HasDerivAt (fun y : ℝ => (1 + y) ^ 4) (4 * (1 + x) ^ 3) x := by
    have h := h1xy.pow 4
    convert h using 1 <;> ring
  have hden : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    have h := (hasDerivAt_id x).pow 3
    convert h using 1
    · funext y; rfl
    · simp
  have hnum : HasDerivAt (fun y : ℝ => (v y) ^ 2 * (1 + y) ^ 4)
      (2 * v x * v' x * (1 + x) ^ 4 + (v x) ^ 2 * (4 * (1 + x) ^ 3)) x := by
    have h := hv2.mul hp
    convert h using 1 <;> ring
  have hq := hnum.div hden (pow_ne_zero 3 hxne)
  refine (hev.hasDerivAt_iff).mpr ?_
  convert hq using 1
  rw [Work.FTS_RegExport.RXT.agmonFderiv]
  simp only [Work.Spaces.w]
  field_simp <;> ring

end Work.FTS_RegExport.RXT.AgmonND
