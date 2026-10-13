import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollSmooth

theorem slice_dd_cont {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    {a x : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hx : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ContinuousOn (deriv (deriv f)) (Set.uIcc a x) := by
  have hT : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have h1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hf.deriv_of_isOpen hT (by norm_num)
  have h2 : ContinuousOn (deriv (deriv f)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    h1.continuousOn_deriv_of_isOpen hT (by norm_num)
  refine h2.mono ?_
  intro y hy
  rw [Set.mem_uIcc] at hy
  rcases hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
  · exact ⟨lt_of_lt_of_le ha.1 hy1, lt_of_le_of_lt hy2 hx.2⟩
  · exact ⟨lt_of_lt_of_le hx.1 hy1, lt_of_le_of_lt hy2 ha.2⟩

end Work.FTS.EllSol.EllPkgAux.MollSmooth
