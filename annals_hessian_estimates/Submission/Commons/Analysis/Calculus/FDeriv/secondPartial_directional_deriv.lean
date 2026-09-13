import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder

open scoped Topology

namespace Commons.Analysis.Calculus.FDeriv

theorem secondPartial_directional_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {s : Set E} {x : E}
    (hs : IsOpen s) (hx : x ∈ s) (hu : ContDiffOn ℝ 3 u s) (a b w : E) :
    fderiv ℝ (fun y => (iteratedFDeriv ℝ 2 u y) ![a, b]) x w =
      (iteratedFDeriv ℝ 3 u x) ![w, a, b] := by
  have hxmem : s ∈ 𝓝 x := hs.mem_nhds hx
  have huAt : ContDiffAt ℝ 3 u x := hu.contDiffAt hxmem
  have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ 2 u) x :=
    (huAt.iteratedFDeriv_right (i := 2) (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h1 : fderiv ℝ (fun y => (iteratedFDeriv ℝ 2 u y) ![a, b]) x w
      = (fderiv ℝ (iteratedFDeriv ℝ 2 u) x w) ![a, b] :=
    fderiv_continuousMultilinear_apply_const_apply hdiff ![a, b] w
  have h2 : (iteratedFDeriv ℝ 3 u x) ![w, a, b]
      = (fderiv ℝ (iteratedFDeriv ℝ 2 u) x w) ![a, b] := by
    rw [iteratedFDeriv_succ_apply_left (n := 2) (m := ![w, a, b])]
    simp
  rw [h1, h2]

end Commons.Analysis.Calculus.FDeriv