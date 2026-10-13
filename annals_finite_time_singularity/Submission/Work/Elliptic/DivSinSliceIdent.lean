import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Elliptic.DivSinDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Iterated `D_θ` of a function of `θ` alone

`D_θ f = sin(2θ) ∂_θ f` (`Work.Spaces.Dth`), where `∂_θ` differentiates the second
variable while the first (`z`) is held fixed.  If `f z θ = g θ` does not depend on `z`,
then `D_θ f z θ = sin(2θ) · g'(θ) = Dth1 g θ`; iterating gives the identity below.
It is the observation that makes `h ↦ h / sin(2θ)` a legitimate "angular quotient":
the one-dimensional operator `Dth1` of `DivisionBySin` computes exactly the iterated
`D_θ`-derivatives of the two-variable function `(z,θ) ↦ h θ / sin(2θ)`. -/

/-- Iterated `D_θ` of a function of `θ` alone agrees with the iterated one-dimensional
operator `Dth1`. -/
theorem DthIter_const (i : ℕ) (g : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DthIter i (fun _ θ' => g θ') z θ = Dth1Iter i g θ := by
  induction i generalizing z θ with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth, Dth1Iter_succ, Dth1]
      congr 1
      exact congrArg (fun f => deriv f θ) (funext fun θ' => ih z θ')

/-- The `i`-th `D_θ`-derivative (in the two-variable sense of `Work.Spaces.DthIter`) of the
angular quotient `(z,θ) ↦ h θ / sin(2θ)` is the `i`-th `Dth1`-derivative of the
one-dimensional quotient `SinQ h`. -/
theorem DivSinSliceIdent (h : ℝ → ℝ) (i : ℕ) (z θ : ℝ)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DthIter i (fun z θ => h θ / Real.sin (2 * θ)) z θ
      = Work.Elliptic.Dth1Iter i (Work.Elliptic.SinQ h) θ := by
  have hfun : (fun θ' : ℝ => h θ' / Real.sin (2 * θ')) = SinQ h := rfl
  rw [← hfun]
  exact DthIter_const i (fun θ' => h θ' / Real.sin (2 * θ')) z θ

end Work.Elliptic
