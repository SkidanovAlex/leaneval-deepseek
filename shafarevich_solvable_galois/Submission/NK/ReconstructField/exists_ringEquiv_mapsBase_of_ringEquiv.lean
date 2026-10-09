import Mathlib
import Submission.NK.Mine.NeukirchUchidaAPI
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Extending a base-field isomorphism to the separable closures

This file proves `NK.ReconstructField.exists_ringEquiv_mapsBase_of_ringEquiv`: a
ring isomorphism `τ : K₁ ≃+* K₂` of number fields extends to a ring isomorphism
`σ : K₂' ≃+* K₁'` of their separable closures which maps the embedded copy of
`K₂` onto the embedded copy of `K₁` (`Submission.NeukirchUchida.MapsBase`) and
which restricts to `τ⁻¹` on the embedded base field.

The two ingredients are completely elementary and hold for *arbitrary* fields:

* transporting an algebra structure across an isomorphism of the base rings
  preserves separability (`algebra_isSeparable_of_ringEquiv`), hence preserves
  being a separable closure (`isSepClosure_of_isSepClosed_of_ringEquiv`);
* two separable closures of a field are isomorphic, and any such isomorphism is
  the identity on the base (`IsSepClosure.equiv`).
-/

set_option linter.style.haveILetI false

namespace NK.ReconstructField

/-- **Separability is invariant under a change of the base field along a ring isomorphism.**
Let `A` be a separable algebra over the field `K₁`, and let `K₂` act on `A` through the
isomorphism `e : K₁ ≃+* K₂` composed with the structure map of `A` over `K₁`
(i.e. `algebraMap K₂ A = algebraMap K₁ A ∘ e.symm`).  Then `A` is separable over `K₂`. -/
lemma algebra_isSeparable_of_ringEquiv {K₁ K₂ A : Type*} [Field K₁] [Field K₂] [Field A]
    [Algebra K₁ A] [Algebra K₂ A] [Algebra.IsSeparable K₁ A] (e : K₁ ≃+* K₂)
    (h : algebraMap K₂ A = (algebraMap K₁ A).comp e.symm.toRingHom) :
    Algebra.IsSeparable K₂ A := by
  haveI hInt : Algebra.IsIntegral K₁ A := ⟨fun x => Algebra.IsSeparable.isIntegral K₁ x⟩
  have hcomp : (algebraMap K₂ A).comp (e : K₁ →+* K₂) =
      (RingEquiv.refl A : A ≃+* A).toRingHom.comp (algebraMap K₁ A) := by
    rw [h]
    ext a
    simp [RingHom.comp_apply]
  refine ⟨fun x => ?_⟩
  have hmin : Polynomial.map (e : K₁ →+* K₂) (minpoly K₁ x) = minpoly K₂ x :=
    minpoly.map_eq_of_equiv_equiv (f := e) (g := RingEquiv.refl A) hcomp x
  show (minpoly K₂ x).Separable
  rw [← hmin]
  exact Polynomial.Separable.map (Algebra.IsSeparable.isSeparable K₁ x) (f := (e : K₁ →+* K₂))

/-- **Separable closures are stable under a change of the base field along a ring
isomorphism.**  If `A` is a separable closure of `K₁` and `K₂` acts on `A` through
`e : K₁ ≃+* K₂` (i.e. `algebraMap K₂ A = algebraMap K₁ A ∘ e.symm`), then `A` is a
separable closure of `K₂`. -/
lemma isSepClosure_of_isSepClosed_of_ringEquiv {K₁ K₂ A : Type*} [Field K₁] [Field K₂]
    [Field A] [Algebra K₁ A] [Algebra K₂ A] [IsSepClosure K₁ A] (e : K₁ ≃+* K₂)
    (h : algebraMap K₂ A = (algebraMap K₁ A).comp e.symm.toRingHom) :
    IsSepClosure K₂ A :=
  ⟨IsSepClosure.sep_closed K₁, algebra_isSeparable_of_ringEquiv e h⟩

/-- **Extending a base-field isomorphism to the separable closures.**  Let `K₁`, `K₂` be number
fields with separable closures `K₁'`, `K₂'` and let `τ : K₁ ≃+* K₂` be a base-field isomorphism.
Then `τ` extends to a ring isomorphism `σ : K₂' ≃+* K₁'` of the separable closures which maps the
embedded copy of `K₂` *onto* the embedded copy of `K₁` (i.e. `MapsBase`) and which on the base is
`τ⁻¹`.

Concretely: `K₁'` is a separable closure of `K₂` for the algebra structure `K₂ → K₁'` given by
`algebraMap K₁ K₁' ∘ τ⁻¹`, and `IsSepClosure.equiv` compares it with `K₂'`. -/
theorem exists_ringEquiv_mapsBase_of_ringEquiv
    {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] (τ : K₁ ≃+* K₂) :
    ∃ σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ x : K₁, σ (algebraMap K₂ K₂' (τ x)) = algebraMap K₁ K₁' x := by
  -- Regard `K₁'` as a `K₂`-algebra via `τ⁻¹`; it is then a separable closure of `K₂`.
  letI : Algebra K₂ K₁' := ((algebraMap K₁ K₁').comp τ.symm.toRingHom).toAlgebra
  haveI hsep : Algebra.IsSeparable K₂ K₁' :=
    algebra_isSeparable_of_ringEquiv τ (RingHom.algebraMap_toAlgebra _)
  haveI : IsSepClosure K₂ K₁' :=
    isSepClosure_of_isSepClosed_of_ringEquiv τ (RingHom.algebraMap_toAlgebra _)
  -- Compare the two separable closures of `K₂`.
  let σ₀ : K₂' ≃ₐ[K₂] K₁' := IsSepClosure.equiv K₂ K₂' K₁'
  refine ⟨σ₀.toRingEquiv, ?_, ?_⟩
  · -- `σ₀` maps `i₂(K₂)` onto `i₁(K₁)`.
    rw [Submission.NeukirchUchida.MapsBase]
    ext y
    constructor
    · intro hy
      obtain ⟨z, hz, hzy⟩ := Subring.mem_map.mp hy
      obtain ⟨a, rfl⟩ := hz
      rw [← hzy]
      refine RingHom.mem_range.mpr ⟨τ.symm a, ?_⟩
      have h2 : σ₀.toRingEquiv.toRingHom (algebraMap K₂ K₂' a) = algebraMap K₂ K₁' a := by
        simpa using σ₀.commutes a
      rw [h2]
      simp [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
    · intro hy
      obtain ⟨b, hb⟩ := hy
      refine Subring.mem_map.mpr
        ⟨algebraMap K₂ K₂' (τ b), RingHom.mem_range.mpr ⟨τ b, rfl⟩, ?_⟩
      rw [← hb]
      have h2 : σ₀.toRingEquiv.toRingHom (algebraMap K₂ K₂' (τ b)) =
          algebraMap K₂ K₁' (τ b) := by
        simpa using σ₀.commutes (τ b)
      rw [h2]
      simp [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
  · -- On the base, `σ₀` is `τ⁻¹`.
    intro x
    have h1 : σ₀.toRingEquiv (algebraMap K₂ K₂' (τ x)) = algebraMap K₂ K₁' (τ x) := by
      simpa using σ₀.commutes (τ x)
    have h2 : algebraMap K₂ K₁' (τ x) = algebraMap K₁ K₁' x := by
      show algebraMap K₁ K₁' (τ.symm (τ x)) = algebraMap K₁ K₁' x
      simp
    simpa [RingEquiv.toRingHom] using h1.trans h2

end NK.ReconstructField
