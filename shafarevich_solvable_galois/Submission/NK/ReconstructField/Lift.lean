import Submission.NK.ReconstructField.Basic
import Submission.NK.ReconstructField.exists_ringEquiv_mapsBase_of_ringEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The lift of a base-field isomorphism to the separable closures, and its Galois twists

`NK.ReconstructField.exists_ringEquiv_mapsBase_of_ringEquiv` shows that every base-field
isomorphism `τ : K₁ ≃+* K₂` lifts to an isomorphism `K₂' ≃+* K₁'` of the separable closures mapping
the embedded `K₂` onto the embedded `K₁`.  This file chooses such a lift and shows that its Galois
twists (`h ↦ liftTwist h`, precomposition with `h ∈ Gal(K₂'/K₂)`) are exactly the MapsBase
isomorphisms `K₂' ≃+* K₁'` restricting to `τ⁻¹` on the base.

This is what allows the reconstruction input `NK.ReconstructField.ReconstructionInput` to be
stated as a condition on a **base-field** isomorphism `τ` and a Galois twist `h`, rather than as the
assertion of the existence of a field isomorphism of the separable closures.

The type arguments `K₁ K₂ K₁' K₂'` are explicit (as in `IsSepClosure.equiv`), since they cannot be
inferred from `τ` alone.
-/

set_option linter.unusedVariables false

namespace NK.ReconstructField

/-- **The chosen lift of a base-field isomorphism to the separable closures**: a ring isomorphism
`K₂' ≃+* K₁'` mapping the embedded copy of `K₂` onto that of `K₁` and restricting to `τ⁻¹` on the
base. -/
noncomputable def liftBase (K₁ : Type*) [Field K₁] (K₂ : Type*) [Field K₂]
    (K₁' : Type*) [Field K₁'] (K₂' : Type*) [Field K₂'] [NumberField K₁] [NumberField K₂]
    [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (τ : K₁ ≃+* K₂) : K₂' ≃+* K₁' :=
  (exists_ringEquiv_mapsBase_of_ringEquiv (K₁ := K₁) (K₂ := K₂) (K₁' := K₁') (K₂' := K₂') τ).choose

/-- The lift maps the embedded copy of `K₂` onto that of `K₁`. -/
theorem liftBase_mapsBase (K₁ : Type*) [Field K₁] (K₂ : Type*) [Field K₂]
    (K₁' : Type*) [Field K₁'] (K₂' : Type*) [Field K₂'] [NumberField K₁] [NumberField K₂]
    [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (τ : K₁ ≃+* K₂) :
    Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂')
      (liftBase K₁ K₂ K₁' K₂' τ) :=
  (exists_ringEquiv_mapsBase_of_ringEquiv (K₁ := K₁) (K₂ := K₂) (K₁' := K₁') (K₂' := K₂')
    τ).choose_spec.1

/-- The lift restricts to `τ⁻¹` on the embedded base field. -/
theorem liftBase_apply_base (K₁ : Type*) [Field K₁] (K₂ : Type*) [Field K₂]
    (K₁' : Type*) [Field K₁'] (K₂' : Type*) [Field K₂'] [NumberField K₁] [NumberField K₂]
    [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (τ : K₁ ≃+* K₂) (x : K₁) :
    liftBase K₁ K₂ K₁' K₂' τ (algebraMap K₂ K₂' (τ x)) = algebraMap K₁ K₁' x :=
  (exists_ringEquiv_mapsBase_of_ringEquiv (K₁ := K₁) (K₂ := K₂) (K₁' := K₁') (K₂' := K₂')
    τ).choose_spec.2 x

/-- **A Galois twist of the lift**: precomposition with `h ∈ Gal(K₂'/K₂)`. -/
noncomputable def liftTwist (K₁ : Type*) [Field K₁] (K₂ : Type*) [Field K₂]
    (K₁' : Type*) [Field K₁'] (K₂' : Type*) [Field K₂'] [NumberField K₁] [NumberField K₂]
    [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (τ : K₁ ≃+* K₂) (h : Gal(K₂'/K₂)) : K₂' ≃+* K₁' :=
  h.toRingEquiv.trans (liftBase K₁ K₂ K₁' K₂' τ)

theorem liftTwist_apply (K₁ : Type*) [Field K₁] (K₂ : Type*) [Field K₂]
    (K₁' : Type*) [Field K₁'] (K₂' : Type*) [Field K₂'] [NumberField K₁] [NumberField K₂]
    [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (τ : K₁ ≃+* K₂) (h : Gal(K₂'/K₂)) (x : K₂') :
    liftTwist K₁ K₂ K₁' K₂' τ h x = liftBase K₁ K₂ K₁' K₂' τ (h x) := rfl

/-- Every Galois twist of the lift restricts to `τ⁻¹` on the embedded base field. -/
theorem liftTwist_apply_base (K₁ : Type*) [Field K₁] (K₂ : Type*) [Field K₂]
    (K₁' : Type*) [Field K₁'] (K₂' : Type*) [Field K₂'] [NumberField K₁] [NumberField K₂]
    [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (τ : K₁ ≃+* K₂) (h : Gal(K₂'/K₂)) (x : K₁) :
    liftTwist K₁ K₂ K₁' K₂' τ h (algebraMap K₂ K₂' (τ x)) = algebraMap K₁ K₁' x := by
  rw [liftTwist_apply, AlgEquiv.commutes, liftBase_apply_base]

/-- Every Galois twist of the lift is MapsBase. -/
theorem liftTwist_mapsBase (K₁ : Type*) [Field K₁] (K₂ : Type*) [Field K₂]
    (K₁' : Type*) [Field K₁'] (K₂' : Type*) [Field K₂'] [NumberField K₁] [NumberField K₂]
    [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (τ : K₁ ≃+* K₂) (h : Gal(K₂'/K₂)) :
    Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂')
      (liftTwist K₁ K₂ K₁' K₂' τ h) := by
  rw [Submission.NeukirchUchida.MapsBase]
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, hxz⟩ := Subring.mem_map.mp hz
    obtain ⟨b, rfl⟩ := RingHom.mem_range.mp hx
    refine RingHom.mem_range.mpr ⟨τ.symm b, ?_⟩
    rw [← hxz]
    conv_rhs => rw [← RingEquiv.apply_symm_apply τ b]
    exact (liftTwist_apply_base K₁ K₂ K₁' K₂' τ h (τ.symm b)).symm
  · intro hz
    obtain ⟨a, rfl⟩ := RingHom.mem_range.mp hz
    exact Subring.mem_map.mpr ⟨algebraMap K₂ K₂' (τ a), RingHom.mem_range.mpr ⟨τ a, rfl⟩,
      liftTwist_apply_base K₁ K₂ K₁' K₂' τ h a⟩

/-- **Every lift of `τ` is a Galois twist of the chosen one.**  If `σ : K₂' ≃+* K₁'` restricts to
`τ⁻¹` on the base, then `σ = liftTwist τ h` for the Galois element `h := (liftBase)⁻¹ ∘ σ`. -/
theorem eq_liftTwist_of_apply_base (K₁ : Type*) [Field K₁] (K₂ : Type*) [Field K₂]
    (K₁' : Type*) [Field K₁'] (K₂' : Type*) [Field K₂'] [NumberField K₁] [NumberField K₂]
    [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    {τ : K₁ ≃+* K₂} {σ : K₂' ≃+* K₁'}
    (hbase : ∀ x : K₁, σ (algebraMap K₂ K₂' (τ x)) = algebraMap K₁ K₁' x) :
    ∃ h : Gal(K₂'/K₂), σ = liftTwist K₁ K₂ K₁' K₂' τ h := by
  have hfix : ∀ b : K₂,
      (liftBase K₁ K₂ K₁' K₂' τ).symm (σ (algebraMap K₂ K₂' b)) = algebraMap K₂ K₂' b := by
    intro b
    have h₁ : σ (algebraMap K₂ K₂' b) = algebraMap K₁ K₁' (τ.symm b) := by
      have := hbase (τ.symm b)
      rwa [RingEquiv.apply_symm_apply] at this
    rw [h₁, ← liftBase_apply_base K₁ K₂ K₁' K₂' τ (τ.symm b), RingEquiv.symm_apply_apply,
      RingEquiv.apply_symm_apply]
  refine ⟨AlgEquiv.ofRingEquiv (f := σ.trans (liftBase K₁ K₂ K₁' K₂' τ).symm) (by
    intro a
    show (liftBase K₁ K₂ K₁' K₂' τ).symm (σ (algebraMap K₂ K₂' a)) = algebraMap K₂ K₂' a
    exact hfix a), ?_⟩
  ext x
  show σ x = liftBase K₁ K₂ K₁' K₂' τ ((σ.trans (liftBase K₁ K₂ K₁' K₂' τ).symm) x)
  rw [RingEquiv.trans_apply, RingEquiv.apply_symm_apply]

end NK.ReconstructField
