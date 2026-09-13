import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic

namespace Commons.Analysis.Calculus.FDeriv

theorem iteratedFDeriv_directional_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {s : Set E} {x : E} (hs : IsOpen s) (hx : x ∈ s) {n : ℕ}
    (hu : ContDiffOn ℝ (n + 1) u s) (m : Fin n → E) (w : E) :
    fderiv ℝ (fun y => (iteratedFDeriv ℝ n u y) m) x w =
      (iteratedFDeriv ℝ (n + 1) u x) (Fin.cons w m) := by
  have hf : ContDiffAt ℝ (n + 1) u x := hu.contDiffAt (hs.mem_nhds hx)
  have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ n u) x :=
    (hf.iteratedFDeriv_right (m := 1) (i := n) (by rw [add_comm]))
      |>.differentiableAt (by norm_num)
  rw [fderiv_continuousMultilinear_apply_const_apply hdiff m w]
  rw [iteratedFDeriv_succ_apply_left (𝕜 := ℝ) (f := u) (x := x) (Fin.cons w m)]
  simp

end Commons.Analysis.Calculus.FDeriv