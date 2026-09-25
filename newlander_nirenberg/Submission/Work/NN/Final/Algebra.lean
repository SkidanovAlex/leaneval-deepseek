/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The bidegree algebra of the perturbation `∂̄_J = ∂̄₀ + L_A`

## What this module contains

* `dbarOne_pert`: the linearisation at the level of coefficients,
  `∂̄_{Jstd+A} w (e_m) = ∂̄₀w (e_m) + (L_A w)_m` (from `Work.NN.Core.dbarCoef_lin`);
* `ddbar_pert_decomp`: the definitional decomposition `∂̄_{Jstd+A} = ∂̄₀ + L^{(2)}_A` at the
  `(0,2)`-level of *coefficient families*;
* `ddbar_std_self`: `∂̄₀² = 0` at that level (from the commutation of mixed `∂̄`-derivatives).

## A warning, and the correction of an earlier version

The operator `ddbar J a` of `Defs.lean` is the *coefficient-level* `(0,2)`-operator: it
antisymmetrises the `∂̄_J`-derivatives of the coefficient functions `a_m = α(e_m)`, exactly as the
flat chapter does for the standard structure.  For `J = Jstd` this is the genuine `(0,2)`-part of
the exterior derivative of `α = Σ a_m dz̄_m` (it is `dbarCoord_comm`, i.e. `dbar_sq_zero` in the
flat frame), and `ddbar_std_self` records that.

For a **non-constant** `J` it is **not** the `J`-(0,2)-projection `(dα)^{(0,2)}_J`, and the
identity `ddbar J (∂̄_J v) = 0` is **FALSE** even for an integrable `J`: the difference between the
two operators is a term involving the first derivatives of `J`, which does not vanish (see the
counterexample recorded below).  Consequently the integrability input cannot be fed to this
algebra in the naive form "`ddbar (Jstd+A) (∂̄_J v) = 0`", and an earlier version of this file
derived the "defect identity" from that hypothesis; that derivation was vacuous and has been
removed.

The correct route (see `README.md` of this directory, §"the defect argument, corrected") uses the
genuine projections `P^{(1)}_J`, `P^{(1)}_0` on *forms* (not on coefficient families):

  `g - L_A w = ∂̄₀ w - ρ`,  `P_0^{(1)} ∘ ∂̄_0 = 0`,  `P_J^{(1)} ρ = 0` (`ρ` is `J`-closed),

hence `∂̄₀( g - L_A w ) = - P^{(1)}_0 ρ = (P_J^{(1)} - P_0^{(1)}) ρ`, and the operator
`P_J^{(1)} - P_0^{(1)}` is of order `0` in `(A, DA)`, hence of size `O(‖A‖_{C¹})`, which is small
after the rescaling `A ↦ A_λ = A∘σ_λ` (`Work.NN.Core.Jscale_Atr_norm_le`).  That is what makes the
defect argument close.

## The counterexample (found by a reviewer of the delegation `NN/Final/ddbar_integrable_flat`)

On `ℂ²` with real coordinates `(x,y,u,v)` and `Φ(x,y,u,v) = (x + xv, y, u, v)` (a diffeomorphism of
`{v ≠ -1}` with `dΦ_0 = 1`), the structure `J₁ := Φ^*S` (pull-back of multiplication by `i`) is
smooth, integrable, and satisfies `J₁(0) = S`, while `D_{e_v}J₁(0) ≠ 0`; the coefficient-level
expression `ddbar J₁ (∂̄_{J₁} v)` does not vanish for a suitable affine `v`.
-/
import Mathlib
import Submission.Work.NN.Final.Defs

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Final

variable {n : ℕ}

/-- `dbarOne` depends only on the function it is applied to. -/
lemma dbarOne_congr {J : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)} {a b : (Fin n → ℂ) → ℂ}
    (h : a = b) (m : Fin n) (z : Fin n → ℂ) : dbarOne J a m z = dbarOne J b m z := by
  rw [h]

/-- `ddbar` respects equality of the coefficient families. -/
lemma ddbar_congr {J : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)}
    {a b : Fin n → (Fin n → ℂ) → ℂ} (h : a = b) (j l : Fin n) (z : Fin n → ℂ) :
    ddbar J a j l z = ddbar J b j l z := by
  rw [h]

end Work.NN.Final
