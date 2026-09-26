import Mathlib
import Submission.Work.Smooth.Morse.ParamDeriv
import Submission.Work.Smooth.Morse.Immersion.hasFDerivAt_torusMap
import Submission.Work.Smooth.Morse.Immersion.torusDeriv_injective

/-!
# The surface `ψ(standard torus)` is a smoothly immersed surface

Let `ψ` be a diffeomorphism of `ℝ³` and `param ψ p = ψ (torusMap p.1 p.2)` the parametrisation
of the surface `F = ψ(standard torus)`.  This file proves item 1 of the smooth chapter of the
Pardon project: `param ψ` is an **immersion**, i.e. its derivative is injective at every
parameter point,

`IsImmersion ψ := ∀ p, Function.Injective (fderiv ℝ (param ψ) p)`.

The parametrisation is the composition of the torus parametrisation `p ↦ torusMap p.1 p.2` with
the diffeomorphism `ψ` (read as a map `ℝ³ → ℝ³`), so its derivative at `p` is the composition

`fderiv ℝ (param ψ) p = (fderiv ℝ ψ (torusMap p.1 p.2)) ∘L torusDeriv p`

(chain rule; `hasFDerivAt_torusMap` identifies the derivative of the torus parametrisation with
`torusDeriv`, whose component lemmas live in `Submission.Work.Smooth.Morse.ParamDeriv`).  Both
factors are injective:

* `torusDeriv p` is injective because the two columns `dtheta p` and `dphi p` are linearly
  independent (`torusDeriv_injective`), i.e. the standard torus of revolution is immersed;
* `fderiv ℝ ψ x` is injective because `ψ` is a diffeomorphism: differentiating the identity
  `ψ.invFun ∘ ψ = id` with the chain rule gives
  `(fderiv ℝ ψ.invFun (ψ x)) ∘L (fderiv ℝ ψ x) = 1`, a left inverse of `fderiv ℝ ψ x`.

A composition of injective linear maps is injective, which is `isImmersion`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Work.Smooth.Morse

namespace Work.Smooth.Morse.Immersion

noncomputable section

/-! ## The derivative of a diffeomorphism is injective -/

/-- **The derivative of a diffeomorphism of `ℝ³` is injective.**  Differentiating the identity
`ψ.invFun ∘ ψ = id` with the chain rule gives a left inverse
`fderiv ℝ ψ.invFun (ψ x)` of `fderiv ℝ ψ x`. -/
theorem fderiv_diffeo_injective (ψ : Submission.Diffeo) (x : R3) :
    Function.Injective (fderiv ℝ (ψ : R3 → R3) x) := by
  have hψdiff : DifferentiableAt ℝ (ψ : R3 → R3) x :=
    (ψ.smooth_toFun.differentiable (by simp)).differentiableAt
  have hinvdiff : DifferentiableAt ℝ (ψ.invFun : R3 → R3) (ψ x) :=
    (ψ.smooth_invFun.differentiable (by simp)).differentiableAt
  -- differentiating `ψ.invFun ∘ ψ = id` gives `fderiv ψ.invFun (ψ x) ∘L fderiv ψ x = 1`
  have hcomp : (fderiv ℝ (ψ.invFun : R3 → R3) (ψ x)).comp (fderiv ℝ (ψ : R3 → R3) x)
      = ContinuousLinearMap.id ℝ R3 := by
    have h1 : fderiv ℝ (fun y : R3 => ψ.invFun (ψ y)) x
        = (fderiv ℝ (ψ.invFun : R3 → R3) (ψ x)).comp (fderiv ℝ (ψ : R3 → R3) x) :=
      (hinvdiff.hasFDerivAt.comp x hψdiff.hasFDerivAt).fderiv
    have h2 : (fun y : R3 => ψ.invFun (ψ y)) = id := funext ψ.left_inv
    rw [← h1, h2, fderiv_id]
  intro u v huv
  have key : ∀ w : R3, fderiv ℝ (ψ.invFun : R3 → R3) (ψ x)
      (fderiv ℝ (ψ : R3 → R3) x w) = w := by
    intro w
    have hw := congrArg (fun (L : R3 →L[ℝ] R3) => L w) hcomp
    simpa using hw
  rw [← key u, ← key v, huv]

/-! ## The derivative of the parametrisation -/

/-- **Chain rule for the parametrisation**: the derivative of `param ψ` at `p` is the composition
of the derivative of `ψ` at `torusMap p.1 p.2` with the derivative `torusDeriv p` of the torus
parametrisation. -/
theorem fderiv_param (ψ : Submission.Diffeo) (p : ℝ × ℝ) :
    fderiv ℝ (param ψ) p
      = (fderiv ℝ (ψ : R3 → R3) (Work.Core.torusMap p.1 p.2)).comp (torusDeriv p) := by
  have hψdiff : DifferentiableAt ℝ (ψ : R3 → R3) (Work.Core.torusMap p.1 p.2) :=
    (ψ.smooth_toFun.differentiable (by simp)).differentiableAt
  exact (hψdiff.hasFDerivAt.comp p (hasFDerivAt_torusMap p)).fderiv

/-- A composition of injective continuous linear maps is injective. -/
theorem injective_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : E →L[ℝ] R3} {M : R3 →L[ℝ] R3} (hM : Function.Injective M)
    (hL : Function.Injective L) : Function.Injective (M.comp L) := by
  intro a b hab
  exact hL (hM (by simpa [ContinuousLinearMap.comp_apply] using hab))

/-- **Item 1 of the smooth chapter: `F = ψ(standard torus)` is a smoothly immersed surface.**
The derivative of the parametrisation `p ↦ ψ (torusMap p.1 p.2)` is injective at every parameter
point: it is the composition of the injective derivatives `torusDeriv p` (the torus of revolution
is immersed) and `fderiv ℝ ψ (torusMap p.1 p.2)` (a diffeomorphism has invertible derivative). -/
theorem isImmersion (ψ : Submission.Diffeo) : Work.Smooth.Morse.IsImmersion ψ := by
  intro p
  rw [fderiv_param ψ p]
  exact injective_comp (fderiv_diffeo_injective ψ (Work.Core.torusMap p.1 p.2))
    (torusDeriv_injective p)

end

end Work.Smooth.Morse.Immersion
