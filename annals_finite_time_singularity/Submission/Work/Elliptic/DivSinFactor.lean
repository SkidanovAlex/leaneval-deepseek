import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.Spaces.Gamma_WlInf

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

open Work.Spaces

/-- `D_z` commutes with division by a function of `θ` alone: the factor `1/s(θ)` is a
constant as far as the `z`-derivative is concerned. -/
lemma Dz_div_const (F : ℝ → ℝ → ℝ) (s : ℝ → ℝ) (z θ : ℝ) :
    Dz (fun z θ => F z θ / s θ) z θ = Dz F z θ / s θ := by
  simp only [Dz, pz]
  rw [deriv_div_const]
  ring

theorem DivSinFactor (Φ : ℝ → ℝ → ℝ) (j : ℕ) (z θ : ℝ)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DzIter j (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ
      = Work.Spaces.DzIter j Φ z θ / Real.sin (2 * θ) := by
  have hfun : Work.Spaces.DzIter j (fun z θ => Φ z θ / Real.sin (2 * θ))
      = fun z θ => Work.Spaces.DzIter j Φ z θ / Real.sin (2 * θ) := by
    induction j with
    | zero => rfl
    | succ n ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
      funext z θ
      exact Dz_div_const (Work.Spaces.DzIter n Φ) (fun θ => Real.sin (2 * θ)) z θ
  exact congrFun (congrFun hfun z) θ

end Work.Elliptic
