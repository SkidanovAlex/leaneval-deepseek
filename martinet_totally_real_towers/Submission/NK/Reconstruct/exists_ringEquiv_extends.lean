import Mathlib
import Submission.NK.Reconstruct.exists_tauStar

/-!
# Extending an automorphism of a finite normal level to the ambient separable closure

Let `Ω` be a separable closure of `ℚ` and `L ⊆ Ω` a finite *normal* (equivalently, in
characteristic zero, Galois) intermediate field.  Then every `ℚ`-algebra automorphism `τ` of `L`
extends to a ring automorphism `θ` of `Ω` which preserves `L` *as a set* and whose restriction to
`L` is `τ`.

The construction is the standard one: `Ω/ℚ` is Galois (Mathlib's
`IsSepClosure.isGalois`), so — since `L/ℚ` is normal — the automorphism `τ` lifts along
`AlgEquiv.restrictNormalHom`; concretely we take `σ = AlgEquiv.liftNormal Ω τ ∈ Gal(Ω/ℚ)`, whose
restriction to `L` is `τ` by `AlgEquiv.liftNormal_commutes`.  That lemma already gives the
pointwise statement `σ x = (τ ⟨x, _⟩ : Ω)` for `x ∈ L`, from which `σ L = L` (hence the
"preserves `L`" clause) follows: `σ` carries `L` into `L`, and the reverse inclusion is
obtained by applying `σ` to `τ⁻¹ y` for `y ∈ L`, together with injectivity of `σ`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.Reconstruct

/-- **Extension of an automorphism of a finite normal level.**  For `L ⊆ Ω` a finite normal
intermediate field of a separable closure `Ω` of `ℚ` and `τ ∈ Gal(L/ℚ)`, there is a ring
automorphism `θ` of `Ω` which preserves `L` setwise and restricts to `τ` on `L`. -/
theorem exists_ringEquiv_extends {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsSepClosure ℚ Ω]
    (L : IntermediateField ℚ Ω) [FiniteDimensional ℚ L] [Normal ℚ L]
    (τ : Gal(↥L/ℚ)) :
    ∃ θ : Ω ≃+* Ω, (∀ x : Ω, x ∈ L ↔ θ x ∈ L) ∧ ∀ x : ↥L, θ (x : Ω) = ((τ x : ↥L) : Ω) := by
  -- `Ω` is Galois over `ℚ`, since it is a separable closure.
  haveI : Normal ℚ Ω := inferInstance
  -- Lift `τ` to an automorphism `σ` of `Ω` over `ℚ`.
  let σ : Gal(Ω/ℚ) := τ.liftNormal Ω
  -- The lifted automorphism restricts to `τ` on `L`.
  have hpt : ∀ x : ↥L, σ (x : Ω) = ((τ x : ↥L) : Ω) := fun x => τ.liftNormal_commutes Ω x
  refine ⟨σ.toRingEquiv, ?_, fun x => hpt x⟩
  intro x
  constructor
  · -- `x ∈ L → σ x ∈ L`: the value is the image of `τ x` under the inclusion `L ↪ Ω`.
    intro hx
    change σ x ∈ L
    rw [hpt ⟨x, hx⟩]
    exact (τ ⟨x, hx⟩).2
  · -- `σ x ∈ L → x ∈ L`: apply `hpt` to `τ⁻¹ (σ x)` and use injectivity of `σ`.
    intro hx
    let y : ↥L := τ.symm ⟨σ x, hx⟩
    have hy : σ (y : Ω) = σ x := by
      rw [hpt y]
      simp [y]
    have hyx : (y : Ω) = x := σ.injective hy
    rw [← hyx]
    exact y.2

end NK.Reconstruct
