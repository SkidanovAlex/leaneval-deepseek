import Mathlib
import ChallengeDeps
import Submission.Work.Core.Torus

/-!
# The smooth structure of the challenge's surface

The challenge provides the knot class through an *ambient isotopy* `Φ` of `ℝ³`, i.e. a smooth
one-parameter family of diffeomorphisms (`ChallengeDeps.AmbientIsotopy`, with `ContDiff` data for
both `Φ.H t` and `Φ.Hinv t`).  In particular the map `Φ.Hinv 1` is a **diffeomorphism** of `ℝ³`,
and the surface of the challenge

`F = ψ(F_standard)`,   `ψ = Φ.Hinv 1`,

is a smoothly embedded torus of revolution in `ℝ³`, not merely a topological torus.
This file puts that structure at the disposal of the later stages of the proof: a structure
`Submission.Diffeo` for diffeomorphisms of `ℝ³`, the special element `psiDiffeo Φ`, and the
smoothness of the parametrisation `(x, y) ↦ ψ (torusMap x y)` of `F`.

Everything downstream that needs transversality (Sard), the implicit function theorem, gradient
flows, or Morse theory can (and should) be stated in terms of `Diffeo` rather than in terms of
an arbitrary homeomorphism `R3 ≃ₜ R3`.

## Main definitions

* `Submission.Diffeo` — a diffeomorphism of `ℝ³`, with its inverse, both `C^∞`;
* `Submission.Diffeo.toHomeomorph` — the underlying homeomorphism (for use with the topological
  API of `Work.CoreTopology`);
* `Submission.psiDiffeo Φ` — the diffeomorphism `Φ.Hinv 1` of the ambient isotopy `Φ`;
* `Submission.psiHomeo Φ` — the same map as a homeomorphism (`Submission.psiDiffeo Φ`'s
  `toHomeomorph`), kept for compatibility with the topological part of the development.

## Main results

* `Submission.Diffeo.injective`, `Submission.Diffeo.surjective`;
* `Submission.contDiff_torusMap` — the standard torus of revolution is a `C^∞` (immersed)
  surface: `(θ, φ) ↦ torusMap θ φ` is smooth;
* `Submission.contDiff_paramDiffeo` — `(θ, φ) ↦ ψ (torusMap θ φ)` is smooth for a
  diffeomorphism `ψ`.
-/

namespace Submission

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

/-- **A diffeomorphism of `ℝ³`**: a bijection which is smooth together with its inverse. -/
structure Diffeo where
  /-- the forward map -/
  toFun : R3 → R3
  /-- the inverse map -/
  invFun : R3 → R3
  /-- the forward map is smooth -/
  smooth_toFun : ContDiff ℝ (⊤ : ℕ∞) toFun
  /-- the inverse map is smooth -/
  smooth_invFun : ContDiff ℝ (⊤ : ℕ∞) invFun
  /-- the inverse is a left inverse -/
  left_inv : ∀ x : R3, invFun (toFun x) = x
  /-- the inverse is a right inverse -/
  right_inv : ∀ x : R3, toFun (invFun x) = x

namespace Diffeo

instance : CoeFun Diffeo (fun _ => R3 → R3) := ⟨Diffeo.toFun⟩

@[simp] theorem toFun_apply (φ : Diffeo) (x : R3) : φ.toFun x = φ x := rfl

theorem injective (φ : Diffeo) : Function.Injective φ := by
  intro x y h
  have h' := congrArg φ.invFun h
  simpa [φ.left_inv] using h'

theorem surjective (φ : Diffeo) : Function.Surjective φ :=
  fun y => ⟨φ.invFun y, φ.right_inv y⟩

theorem continuous (φ : Diffeo) : Continuous φ := φ.smooth_toFun.continuous

theorem continuous_invFun (φ : Diffeo) : Continuous φ.invFun := φ.smooth_invFun.continuous

/-- The underlying homeomorphism of `ℝ³`. -/
def toHomeomorph (φ : Diffeo) : R3 ≃ₜ R3 where
  toFun := φ.toFun
  invFun := φ.invFun
  left_inv := φ.left_inv
  right_inv := φ.right_inv
  continuous_toFun := φ.continuous
  continuous_invFun := φ.continuous_invFun

@[simp] theorem toHomeomorph_apply (φ : Diffeo) (x : R3) : φ.toHomeomorph x = φ x := rfl

@[simp] theorem toHomeomorph_symm_apply (φ : Diffeo) (x : R3) :
    φ.toHomeomorph.symm x = φ.invFun x := rfl

/-- The inverse diffeomorphism. -/
def symm (φ : Diffeo) : Diffeo where
  toFun := φ.invFun
  invFun := φ.toFun
  smooth_toFun := φ.smooth_invFun
  smooth_invFun := φ.smooth_toFun
  left_inv := φ.right_inv
  right_inv := φ.left_inv

@[simp] theorem symm_apply (φ : Diffeo) (x : R3) : φ.symm x = φ.invFun x := rfl

@[simp] theorem symm_toFun (φ : Diffeo) : φ.symm.toFun = φ.invFun := rfl

@[simp] theorem symm_invFun (φ : Diffeo) : φ.symm.invFun = φ.toFun := rfl

theorem symm_symm (φ : Diffeo) : φ.symm.symm = φ := by
  cases φ; rfl

@[simp] theorem symm_apply_apply (φ : Diffeo) (x : R3) : φ.symm (φ x) = x := φ.left_inv x

@[simp] theorem apply_symm_apply (φ : Diffeo) (x : R3) : φ (φ.symm x) = x := φ.right_inv x

end Diffeo

/-- **The diffeomorphism `Φ.Hinv 1` of the ambient isotopy `Φ`.**  This is the map which carries
the standard torus of revolution to the surface of the challenge. -/
def psiDiffeo (Φ : AmbientIsotopy) : Diffeo where
  toFun := fun x => Φ.Hinv 1 x
  invFun := fun x => Φ.H 1 x
  smooth_toFun :=
    Φ.smooth_inv.comp (f := fun x : R3 => ((1 : ℝ), x)) (by fun_prop)
  smooth_invFun :=
    Φ.smooth.comp (f := fun x : R3 => ((1 : ℝ), x)) (by fun_prop)
  left_inv := fun x => Φ.inv_right 1 x
  right_inv := fun x => Φ.inv_left 1 x

@[simp] theorem psiDiffeo_apply (Φ : AmbientIsotopy) (x : R3) :
    psiDiffeo Φ x = Φ.Hinv 1 x := rfl

@[simp] theorem psiDiffeo_symm_apply (Φ : AmbientIsotopy) (x : R3) :
    (psiDiffeo Φ).symm x = Φ.H 1 x := rfl

@[simp] theorem psiDiffeo_invFun (Φ : AmbientIsotopy) :
    (psiDiffeo Φ).invFun = fun x => Φ.H 1 x := rfl

/-- The diffeomorphism `Φ.Hinv 1` of `ℝ³`, as a homeomorphism.  This is the form in which the
topological part of the development (`Work.CoreTopology`, `Work.InnermostDisk`, ...) consumes
the surface of the challenge. -/
def psiHomeo (Φ : AmbientIsotopy) : R3 ≃ₜ R3 := (psiDiffeo Φ).toHomeomorph

@[simp] theorem psiHomeo_apply (Φ : AmbientIsotopy) (x : R3) : psiHomeo Φ x = Φ.Hinv 1 x := rfl

@[simp] theorem psiHomeo_symm_apply (Φ : AmbientIsotopy) (x : R3) :
    (psiHomeo Φ).symm x = Φ.H 1 x := rfl

/-- **The standard torus of revolution is a smooth immersed surface**:
`(θ, φ) ↦ torusMap θ φ` is `C^∞`. -/
theorem contDiff_torusMap :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => Work.Core.torusMap p.1 p.2) := by
  unfold Work.Core.torusMap
  rw [contDiff_piLp]
  intro i
  fin_cases i <;> simp <;> fun_prop

/-- **The parametrisation of the surface of the challenge is smooth**: for a diffeomorphism `ψ`
of `ℝ³`, the map `(θ, φ) ↦ ψ (torusMap θ φ)` is `C^∞`. -/
theorem contDiff_paramDiffeo (ψ : Diffeo) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => ψ (Work.Core.torusMap p.1 p.2)) :=
  ψ.smooth_toFun.comp contDiff_torusMap

end

end Submission
