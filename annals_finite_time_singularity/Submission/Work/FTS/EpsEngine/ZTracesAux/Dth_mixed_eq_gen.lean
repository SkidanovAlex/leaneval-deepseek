import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine.ZTracesAux

theorem Dth_mixed_eq_gen {f : ℝ → ℝ → ℝ} {N : ℕ}
    (hF : ContDiffOn ℝ N (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (b a : ℕ) (hab : a + b + 1 ≤ N) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ = Work.Spaces.mixed b (a + 1) f z θ := by
  have hy : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ⟩
  -- `f` is `C^{a+b+1}` on `Q0`, hence `D_θ^a f` is `C^{b+1}` there
  have hab2 : (b + 1 + a : ℕ) ≤ N := by omega
  have h1 : ContDiffOn ℝ (b + 1 + a) (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
    hF.of_le (Nat.cast_le.mpr hab2)
  have hfin : ContDiffOn ℝ (b + 1) (Function.uncurry (Work.Spaces.DthIter a f))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.contDiffOn_uncurry_DthIter_shift
      Work.FTS.EllipticEst.isOpen_Q0 a (b + 1) h1
  -- Clairaut at the finite order: `D_θ` commutes with `D_z^b`
  have hpt := (Work.FTS_RegExport.C4.Dth_DzIter_comm_fin b
      Work.FTS.EllipticEst.isOpen_Q0 hfin) hy
  rw [show Work.Spaces.mixed b a f
      = Work.Spaces.DzIter b (Work.Spaces.DthIter a f) from rfl]
  rw [show Work.Spaces.mixed b (a + 1) f
      = Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter a f)) from rfl]
  simpa only [Function.uncurry] using hpt

end Work.FTS.EpsEngine.ZTracesAux
