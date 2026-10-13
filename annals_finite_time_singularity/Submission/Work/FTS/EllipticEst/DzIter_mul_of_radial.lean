/-
Copyright: work module for the Elgindi finite-time singularity project.

# `D_z^j` on a separated (radial × angular) product

The paper's radial operator is `D_z = z ∂_z`, acting on functions of `(z, θ)`.  On a
*separated* function `(z, θ) ↦ g(z) · u(θ)` — the shape of every term in which the angular
profile is factored out, e.g. `Ḡ(z) sin 2θ` — the operator only sees the `z`-variable and
becomes the one-variable operator `rDz g z = z ∂_z g` of `GbarSetup`:

* `Dz_radial_mul`:  `D_z (g(z)·u(θ)) = (rDz g)(z) · u(θ)`,
* `DzIter_radial_mul` (iterated):  `D_z^j (g(z)·u(θ)) = (rDzIter j g)(z) · u(θ)`,

and the requested lemma `DzIter_mul_of_radial` is the pointwise form of the second.

The proof of the one-step statement is the product rule with the constant factor `u θ`.  No
differentiability hypothesis is needed: Mathlib's `deriv` is `0` at points where the
function is not differentiable, and `A(·)·c` fails to be differentiable at `z` exactly when
`A` does (for `c ≠ 0`), so the identity holds unconditionally — see `deriv_mul_radial`.
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.RCLike.Basic
import Submission.Work.FTS.EllipticEst.GbarSetup
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## The one-variable product rule, without differentiability hypotheses -/

/-- `deriv (A · c) z = deriv A z * c` for a constant `c`, with no differentiability
hypothesis: `deriv_mul_const_field` is stated unconditionally, the convention being that
`deriv` is `0` where the function is not differentiable. -/
theorem deriv_mul_radial (A : ℝ → ℝ) (c z : ℝ) :
    deriv (fun z' => A z' * c) z = deriv A z * c :=
  deriv_mul_const_field (u := A) c

/-! ## `D_z` on a separated product -/

/-- `D_z (g(z)·u(θ)) = (rDz g)(z) · u(θ)`: the operator `D_z = z∂_z` sees only the
`z`-variable and the radial factor becomes the one-variable operator `rDz`. -/
theorem Dz_radial_mul (g u : ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => g z * u θ) = fun z θ => rDz g z * u θ := by
  funext z θ
  simp only [Work.Spaces.Dz, Work.Spaces.pz, rDz]
  rw [deriv_mul_radial (A := g) (u θ)]
  ring

/-- Iterated form of `Dz_radial_mul`: `D_z^j (g(z)·u(θ)) = (rDzIter j g)(z) · u(θ)`. -/
theorem DzIter_radial_mul (j : ℕ) (g u : ℝ → ℝ) :
    Work.Spaces.DzIter j (fun z θ => g z * u θ)
      = fun z θ => rDzIter j g z * u θ := by
  induction j with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DzIter_succ, ih, rDzIter_succ]
      exact Dz_radial_mul (rDzIter n g) u

/-! ## The requested pointwise form -/

theorem DzIter_mul_of_radial (j : ℕ) (g u : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DzIter j (fun z θ => g z * u θ) z θ
      = Work.FTS.EllipticEst.rDzIter j g z * u θ :=
  congrFun (congrFun (DzIter_radial_mul j g u) z) θ

end Work.FTS.EllipticEst
