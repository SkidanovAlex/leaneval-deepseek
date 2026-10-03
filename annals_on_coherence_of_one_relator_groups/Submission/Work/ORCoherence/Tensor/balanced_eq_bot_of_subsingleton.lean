import Mathlib
import Submission.Work.ORCoherence.Defs
import Submission.Work.ORCoherence.Map
import Submission.Work.ORCoherence.Tensor.balanced_injective_tmul_one_finsupp

namespace Work.ORCoherence.Tensor

open Work.ORCoherence

/-- Coefficientwise application of a ring homomorphism `f : R →+* S` to a finitely
supported function `X →₀ R`, as a `ℤ`-linear map. -/
noncomputable def coeffMap {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (X : Type*) :
    (X →₀ R) →ₗ[ℤ] (X →₀ S) :=
  (Finsupp.mapRange.addMonoidHom (f : R →+ S)).toIntLinearMap

theorem coeffMap_apply {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (X : Type*)
    (u : X →₀ R) (x : X) : coeffMap f X u x = f (u x) := rfl

theorem coeffMap_injective {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (hf : Function.Injective f) (X : Type*) : Function.Injective (coeffMap f X) := by
  intro u v huv
  ext x
  refine hf ?_
  have := congrArg (fun w : X →₀ S => w x) huv
  rwa [coeffMap_apply, coeffMap_apply] at this

theorem coeffMap_smul {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (X : Type*)
    (r : R) (u : X →₀ R) : coeffMap f X (r • u) = f r • coeffMap f X u := by
  ext x
  simp only [coeffMap_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [map_mul]

theorem balanced_eq_bot_of_subsingleton {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (hf : Function.Injective f) (X : Type*) (W : Submodule R (X →₀ R))
    (hW : Subsingleton (Balanced f W)) : W = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro u hu
  let φ : W →ₗ[ℤ] (X →₀ S) := (coeffMap f X).comp (W.subtype.restrictScalars ℤ)
  have hφ : ∀ (r : R) (w : W), f r • φ w = φ (r • w) := by
    intro r w
    have h1 : ((r • w : W) : X →₀ R) = r • (w : X →₀ R) := Submodule.coe_smul r w
    show f r • coeffMap f X (w : X →₀ R) = coeffMap f X ((r • w : W) : X →₀ R)
    rw [h1, coeffMap_smul]
  have hzero : φ ⟨u, hu⟩ = 0 := by
    have h : Balanced.tmul f (1 : S) (⟨u, hu⟩ : W) = 0 := Subsingleton.elim _ _
    have h2 := congrArg (Balanced.lift f φ hφ) h
    simpa using h2
  have he : coeffMap f X u = 0 := by
    have h3 : φ ⟨u, hu⟩ = coeffMap f X u := rfl
    rw [h3] at hzero
    exact hzero
  exact (coeffMap_injective f hf X) (by rw [he, map_zero])

end Work.ORCoherence.Tensor
