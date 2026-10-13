/-
Copyright: work module for the Elgindi finite-time singularity project.

# Setup for the `H^k` estimate of `Ḡ · sin 2θ` (paper Lemma `HardyInequality4`)

This module collects the vocabulary shared by the proof of

  `Work.FTS.EllipticEst.Gbar_Hk_fts`:
`|Ḡ(α,F) · sin 2θ|_{H^k} ≤ C_k |F|_{H^k}` for `0 < α ≤ 1`, `C_k` independent of `α`,

where `Ḡ(α,F)(z) = -(3/(4α)) z^{-5/α} ∫_0^z s^{(5-α)/α} F_*(s) ds` is the singular term of
Elgindi's §'Elliptic Regularity Estimates'.

## The three gadgets

* `bet α = 5/α` and `HarOp β g z = z^{-β} ∫_0^z s^{β-1} g(s) ds`: the weighted Hardy operator
  of which `Ḡ` is a constant multiple — `Gbar_eq_HarOp`.  The point of the *Hardy form* is
  that it is uniformly (in `α`) bounded on the weighted `L²` space with weight
  `w(z) = (1+z)²/z²`: the sharp constant of the Hardy inequality is `O(1/β²) = O(α²)` and
  cancels the explicit `1/α` in front of `Ḡ`.
* `rDz g z = z ∂_z g` and its iterates `rDzIter`: the one-variable version of `D_z`, so that
  `D_z^j (g(z) h(θ)) = (rDzIter j g)(z) · h(θ)` (`DzIter_mul_of_radial`).
* `sinIter i θ = D_θ^i (sin 2θ)`: the angular profile of `D_θ^i` applied to `Ḡ(z) sin 2θ`.

The one analytic input that the refinement of `D_z^j Ḡ` needs is the *commutation* of the
Hardy operator with `D_z`: `HarOp_comm` below (`D_z (HarOp β h)(z) = -β · HarOp β h z + h z`,
equivalently `D_z` commutes with `HarOp` when written in the averaged form); it is proved by
integration by parts on `[0,z]`, for which the function `h` must be `C¹` on `[0,z]`.
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.PsiStar_zero
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The Hardy operator of `Ḡ` -/

/-- `β = 5/α`, the exponent of `Ḡ` (the larger indicial root of the associated Euler
equation). -/
def bet (α : ℝ) : ℝ := 5 / α

/-- The weighted Hardy operator `HarOp β g z = z^{-β} ∫_0^z s^{β-1} g(s) ds`, of which
`Gbar α F` is `-(3/(4α)) · HarOp (5/α) (F_*)`. -/
def HarOp (β : ℝ) (g : ℝ → ℝ) (z : ℝ) : ℝ :=
  z ^ (-β) * ∫ s in (0 : ℝ)..z, s ^ (β - 1) * g s

/-- `Gbar α F` is `-(3/(4α))` times the Hardy operator applied to `F_*(F)`. -/
theorem Gbar_eq_HarOp (α : ℝ) (hα : α ≠ 0) (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.Gbar α F z
      = -(3 / (4 * α)) * HarOp (bet α) (fun s => Work.Elliptic.Fstar F s) z := by
  have hexp : (5 - α) / α = 5 / α - 1 := (div_sub_one hα).symm
  simp only [Work.Elliptic.Gbar, bet, HarOp]
  rw [intervalIntegral.integral_congr (fun s _ => by rw [hexp])]
  ring

/-! ## The one-variable `D_z`-operator and its iterates -/

/-- The one-variable version `g ↦ z ∂_z g` of the paper's `D_z`. -/
def rDz (g : ℝ → ℝ) : ℝ → ℝ := fun z => z * deriv g z

/-- Iterated `rDz`. -/
def rDzIter : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, g => g
  | n + 1, g => rDz (rDzIter n g)

@[simp] theorem rDzIter_zero (g : ℝ → ℝ) : rDzIter 0 g = g := rfl

@[simp] theorem rDzIter_succ (n : ℕ) (g : ℝ → ℝ) :
    rDzIter (n + 1) g = rDz (rDzIter n g) := rfl

theorem rDz_const_mul (c : ℝ) (g : ℝ → ℝ) :
    rDz (fun z => c * g z) = fun z => c * rDz g z := by
  funext z
  simp only [rDz, deriv_const_mul_field]
  ring

/-! ## The angular profile of `D_θ^i (sin 2θ)` -/

/-- `D_θ^i (sin 2θ)`, as a function of the angle.  This is the angular profile of
`D_z^j D_θ^i (Ḡ(z) sin 2θ)`. -/
def sinIter (i : ℕ) (θ : ℝ) : ℝ :=
  Work.Spaces.DthIter i (fun _ θ' => Real.sin (2 * θ')) 0 θ

theorem sinIter_zero (θ : ℝ) : sinIter 0 θ = Real.sin (2 * θ) := by
  simp [sinIter]

end Work.FTS.EllipticEst
