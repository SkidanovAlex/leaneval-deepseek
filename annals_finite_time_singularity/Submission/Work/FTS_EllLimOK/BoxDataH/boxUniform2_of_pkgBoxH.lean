import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_EllLimOK.BoxDataH.BoxUniform
import Submission.Work.FTS_EllLimOK.RulingELF

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.BoxDataH

theorem boxUniform2_of_pkgBoxH {α : ℝ} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hbox : Work.FTS_EllLimOK.RulingELF.PkgBoxH α E)
    {a b B : ℝ} (ha : 0 < a) (hab : a < b) {fn : ℕ → Work.FTS.Galerkin.Fn}
    (hclass : ∀ n, Work.FTS.ClassC.ClassC α (fn n))
    (hB : ∀ n, Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ B) :
    Work.FTS_EllLimOK.BoxDataH.BoxUniform2 a b (fun n z θ => E (fn n) z θ) := by
  obtain ⟨K, β, hK, hβ, hb⟩ := hbox a b ha hab.le
  refine ⟨K * max B 0 + 1, β, hβ, ?_, ?_, ?_⟩
  · intro n
    exact (hb (fn n) (hclass n)).1
  · intro n k hk p hp
    have h2 : Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ max B 0 := le_trans (hB n) (le_max_left _ _)
    have hle : K * Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ K * max B 0 :=
      mul_le_mul_of_nonneg_left h2 hK.le
    calc ‖iteratedFDerivWithin ℝ k (Function.uncurry (E (fn n))) (cbox a b) p‖
        ≤ K * Work.FTS.StrongGlobal.Xn6 α (fn n) := (hb (fn n) (hclass n)).2.1 hab k hk p hp
      _ ≤ K * max B 0 := hle
      _ ≤ K * max B 0 + 1 := by linarith
  · intro n p hp q hq
    have h2 : Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ max B 0 := le_trans (hB n) (le_max_left _ _)
    have hr : (0 : ℝ) ≤ ‖p - q‖ ^ β := Real.rpow_nonneg (norm_nonneg _) _
    have hle : K * Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ K * max B 0 :=
      mul_le_mul_of_nonneg_left h2 hK.le
    calc ‖iteratedFDerivWithin ℝ 2 (Function.uncurry (E (fn n))) (cbox a b) p
          - iteratedFDerivWithin ℝ 2 (Function.uncurry (E (fn n))) (cbox a b) q‖
        ≤ K * Work.FTS.StrongGlobal.Xn6 α (fn n) * ‖p - q‖ ^ β :=
          (hb (fn n) (hclass n)).2.2 hab p hp q hq
      _ ≤ (K * max B 0) * ‖p - q‖ ^ β := mul_le_mul_of_nonneg_right hle hr
      _ ≤ (K * max B 0 + 1) * ‖p - q‖ ^ β := mul_le_mul_of_nonneg_right (by linarith) hr

end Work.FTS_EllLimOK.BoxDataH
