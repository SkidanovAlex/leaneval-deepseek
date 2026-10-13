/-
Copyright: work module for the Elgindi finite-time singularity project.

# `D_θ^i` applied to a product `g(z) · u(θ)`

The operator `D_θ = sin(2θ) ∂_θ` differentiates only in the angular variable, so
multiplication by a function of `z` alone passes straight through all its iterates:

`D_θ^i (g(z) u(θ)) = g(z) · D_θ^i u(θ)`.

The righthand side is stated with the (constant in `z`) extension `θ ↦ u θ` of `u`
evaluated at `z = 0`, which is legitimate because `D_θ^i` of a function of `θ` alone
does not depend on `z`.

At fixed `z` the slice of `D_θ` is the derivation `Lop u θ = sin(2θ) u'(θ)`, and
`DthIter n f z = Lop^[n] (θ ↦ f z θ)` (`Work.Spaces.DthIter_eq_iterate_Lop`).
The whole content is then that `Lop^[n]` (hence every `D_θ`-iterate) commutes with
multiplication by a constant, which is unconditional because `deriv` is scalar
homogeneous without any differentiability hypothesis (`deriv_const_mul_field`).
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.RCLike.Basic
import Submission.Work.FTS.EllipticEst.GbarSetup
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.DthIter_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## Iterates of `Lop` commute with constant factors -/

/-- Every iterate of `Lop` commutes with multiplication by a constant. -/
lemma Lop_iter_const_mul_angular (c : ℝ) (u : ℝ → ℝ) (i : ℕ) :
    Work.Spaces.Lop^[i] (fun θ => c * u θ) = fun θ => c * Work.Spaces.Lop^[i] u θ := by
  induction i with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      funext θ
      simp only [Work.Spaces.Lop]
      rw [deriv_const_mul_field (u := c) (v := Work.Spaces.Lop^[n] u) (x := θ)]
      ring

/-! ## The main identity -/

theorem DthIter_mul_of_angular (i : ℕ) (g u : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DthIter i (fun z θ => g z * u θ) z θ
      = g z * (Work.Spaces.DthIter i (fun _ θ' => u θ') 0 θ) := by
  have h1 : Work.Spaces.DthIter i (fun z θ => g z * u θ) z θ
      = Work.Spaces.Lop^[i] (fun θ' => g z * u θ') θ := by
    have h := congrFun (Work.Spaces.DthIter_eq_iterate_Lop i (fun z θ => g z * u θ) z) θ
    simpa using h
  have h2 : Work.Spaces.DthIter i (fun _ θ' => u θ') 0 θ
      = Work.Spaces.Lop^[i] u θ := by
    have h := congrFun (Work.Spaces.DthIter_eq_iterate_Lop i (fun _ θ' => u θ') 0) θ
    simpa using h
  rw [h1, h2]
  exact congrFun (Lop_iter_const_mul_angular (g z) u i) θ

end Work.FTS.EllipticEst
