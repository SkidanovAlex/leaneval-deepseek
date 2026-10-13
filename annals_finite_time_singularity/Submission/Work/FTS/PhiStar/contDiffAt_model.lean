import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.Model

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar

/-- The radial profile `φ(z) = 2z/(1+z)²` is `C^n` at every `z ≠ -1` (in particular on `z > 0`),
since it is a quotient of polynomials with non-vanishing denominator. -/
theorem contDiffAt_phiR {n : ℕ} {z : ℝ} (hz : -1 < z) :
    ContDiffAt ℝ n Work.FTS.VocabO.phiR z := by
  show ContDiffAt ℝ n (fun z : ℝ => 2 * z / (1 + z) ^ 2) z
  have hden : (1 + z) ^ 2 ≠ 0 := by
    have : 1 + z ≠ 0 := by linarith
    positivity
  exact ((contDiffAt_const (c := (2 : ℝ))).mul contDiffAt_id).div
    (((contDiffAt_const (c := (1 : ℝ))).add contDiffAt_id).pow 2) hden

theorem contDiffAt_model {α : ℝ} {Gz ψ : ℝ → ℝ} {z θ : ℝ} (n : ℕ) (hz : 0 < z)
    (hG : ContDiffAt ℝ n Gz z) (hψ : ContDiffAt ℝ n ψ θ) :
    ContDiffAt ℝ n (Function.uncurry (Work.FTS.PhiStar.Model α Gz ψ)) (z, θ) := by
  have hphi : ContDiffAt ℝ n Work.FTS.VocabO.phiR z := contDiffAt_phiR (by linarith)
  show ContDiffAt ℝ n (fun p : ℝ × ℝ =>
    Gz p.1 * Real.sin (2 * p.2) + α * Work.FTS.VocabO.phiR p.1 * ψ p.2) (z, θ)
  have hsin : ContDiffAt ℝ n (fun p : ℝ × ℝ => Real.sin (2 * p.2)) (z, θ) :=
    (((contDiffAt_const (c := (2 : ℝ))).mul contDiffAt_snd)).sin
  have h1 : ContDiffAt ℝ n (fun p : ℝ × ℝ => Gz p.1 * Real.sin (2 * p.2)) (z, θ) :=
    (hG.comp (z, θ) contDiffAt_fst).mul hsin
  have h2 : ContDiffAt ℝ n (fun p : ℝ × ℝ => α * Work.FTS.VocabO.phiR p.1 * ψ p.2) (z, θ) :=
    ((contDiffAt_const (c := α)).mul (hphi.comp (z, θ) contDiffAt_fst)).mul
      (hψ.comp (z, θ) contDiffAt_snd)
  exact h1.add h2

end Work.FTS.PhiStar
