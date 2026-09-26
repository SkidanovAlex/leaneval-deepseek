import Mathlib
import Submission.Work.Smooth.Morse.ParamDeriv
import Submission.Work.Smooth.Morse.Immersion.hasFDerivAt_torusMap
import Submission.Work.Smooth.Morse.Immersion.torusDeriv_injective
import Submission.Work.Smooth.Morse.Immersion.isImmersion

/-!
# `F = ψ(standard torus)` is a smoothly immersed surface (item 1)

The parametrisation `(θ,φ) ↦ ψ (torusMap θ φ)` of the surface of the challenge is an immersion:
its derivative at `(θ,φ)` is the derivative of `ψ` at `torusMap θ φ` composed with the derivative
`torusDeriv` of the standard torus parametrisation, the latter having the two independent columns
`dtheta`, `dphi` (`Work.Smooth.Morse.Immersion.torusDeriv_injective`), and the former being
injective because `ψ` is a diffeomorphism.

The two ingredient lemmas are in sub-files of `Submission/Work/Smooth/Morse/Immersion/`; this file
assembles them and records the derivative formula.

## Main results

* `Work.Smooth.Morse.fderiv_diffeomorphism_injective` — the derivative of a diffeomorphism of
  `ℝ³` is injective;
* `Work.Smooth.Morse.fderiv_param` — the chain rule for the parametrisation of `F`;
* `Work.Smooth.Morse.isImmersion` — `IsImmersion ψ` (item 1);
* `Work.Smooth.Morse.isImmersion_torusMap` — the standard torus parametrisation is an immersion.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Morse

noncomputable section

/-- **The derivative of a diffeomorphism of `ℝ³` is injective.**  The derivative of the inverse,
composed with it, is the derivative of the identity. -/
theorem fderiv_diffeomorphism_injective (ψ : Submission.Diffeo) (x : R3) :
    Function.Injective (fderiv ℝ (ψ : R3 → R3) x) := by
  have hψ : HasFDerivAt (ψ : R3 → R3) (fderiv ℝ (ψ : R3 → R3) x) x :=
    (ψ.smooth_toFun.hasStrictFDerivAt (by simp)).hasFDerivAt
  have hinv : HasFDerivAt (ψ.invFun) (fderiv ℝ ψ.invFun (ψ x)) (ψ x) :=
    (ψ.smooth_invFun.hasStrictFDerivAt (by simp)).hasFDerivAt
  have hcomp : HasFDerivAt (fun y : R3 => ψ.invFun (ψ y))
      ((fderiv ℝ ψ.invFun (ψ x)).comp (fderiv ℝ (ψ : R3 → R3) x)) x := hinv.comp x hψ
  have hid : (fun y : R3 => ψ.invFun (ψ y)) = id := funext fun y => ψ.left_inv y
  rw [hid] at hcomp
  have hone : (fderiv ℝ ψ.invFun (ψ x)).comp (fderiv ℝ (ψ : R3 → R3) x) =
      ContinuousLinearMap.id ℝ R3 := hcomp.unique (hasFDerivAt_id x)
  intro u v huv
  have h : (fderiv ℝ ψ.invFun (ψ x)) ((fderiv ℝ (ψ : R3 → R3) x) u) = u := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
      congrArg (fun (L : R3 →L[ℝ] R3) => L u) hone
  have h' : (fderiv ℝ ψ.invFun (ψ x)) ((fderiv ℝ (ψ : R3 → R3) x) v) = v := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
      congrArg (fun (L : R3 →L[ℝ] R3) => L v) hone
  rw [huv] at h
  exact h.symm.trans h'

/-- **The chain rule for the parametrisation of the surface**: the derivative of
`p ↦ ψ (torusMap p.1 p.2)` is the derivative of `ψ` composed with `torusDeriv`. -/
theorem fderiv_param (ψ : Submission.Diffeo) (p : ℝ × ℝ) :
    fderiv ℝ (param ψ) p =
      (fderiv ℝ (ψ : R3 → R3) (Work.Core.torusMap p.1 p.2)).comp (torusDeriv p) := by
  have hmap : param ψ =
      (ψ : R3 → R3) ∘ (fun q : ℝ × ℝ => Work.Core.torusMap q.1 q.2) := rfl
  have hd1 : DifferentiableAt ℝ (ψ : R3 → R3) (Work.Core.torusMap p.1 p.2) :=
    (ψ.smooth_toFun.differentiable (by simp)).differentiableAt
  have hd2 : DifferentiableAt ℝ (fun q : ℝ × ℝ => Work.Core.torusMap q.1 q.2) p :=
    (Work.Smooth.Morse.Immersion.hasFDerivAt_torusMap p).differentiableAt
  rw [hmap, fderiv_comp p hd1 hd2,
    (Work.Smooth.Morse.Immersion.hasFDerivAt_torusMap p).fderiv]

/-- **Item 1: the surface of the challenge is a smoothly immersed surface.** -/
theorem isImmersion (ψ : Submission.Diffeo) : IsImmersion ψ :=
  Work.Smooth.Morse.Immersion.isImmersion ψ

/-- The standard torus of revolution is an immersed surface. -/
theorem isImmersion_torusMap (p : ℝ × ℝ) :
    Function.Injective (fderiv ℝ (fun q : ℝ × ℝ => Work.Core.torusMap q.1 q.2) p) := by
  rw [(Work.Smooth.Morse.Immersion.hasFDerivAt_torusMap p).fderiv]
  exact Work.Smooth.Morse.Immersion.torusDeriv_injective p

end

end Work.Smooth.Morse
