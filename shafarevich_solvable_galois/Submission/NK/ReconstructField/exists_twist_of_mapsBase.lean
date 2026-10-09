import Mathlib
import Submission.NK.ReconstructField.Input
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Every `MapsBase` isomorphism of the separable closures is a Galois twist of a lift

`NK.ReconstructField.liftTwist` (file `Submission/Work/ReconstructField/Lift.lean`) produces, from
a base-field isomorphism `τ : K₁ ≃+* K₂` and a Galois element `h ∈ Gal(K₂'/K₂)`, a `MapsBase` ring
isomorphism `K₂' ≃+* K₁'`; `NK.ReconstructField.eq_liftTwist_of_apply_base` shows conversely that
*every* `MapsBase` isomorphism restricting to a fixed isomorphism on the base is such a twist.

This file removes the last hypothesis of that converse: a `MapsBase` isomorphism `σ : K₂' ≃+* K₁'`
already *induces* a base-field isomorphism, since `MapsBase` says that `σ` carries the embedded copy
of `K₂` onto the embedded copy of `K₁`.  The induced isomorphism is
`NK.ReconstructField.baseRingEquiv_of_mapsBase`, and its inverse is then a base-field isomorphism
`τ : K₁ ≃+* K₂` whose chosen lifts are exactly (up to a Galois twist) `σ`.

Consequently the σ-free reconstruction input `NK.ReconstructField.ReconstructionInput` is
equivalent to its σ-based form `NK.ReconstructField.ReconstructionInputSigma`.
-/

namespace NK.ReconstructField

/-- **The base-field isomorphism induced by a `MapsBase` isomorphism of the separable closures.**

If `σ : K₂' ≃+* K₁'` carries the embedded copy of `K₂` onto the embedded copy of `K₁`
(`Submission.NeukirchUchida.MapsBase`), then it induces a ring isomorphism `ρ : K₂ ≃+* K₁`
characterized by `σ (algebraMap K₂ K₂' x) = algebraMap K₁ K₁' (ρ x)`.

The construction is the one forced by the situation: `σ (algebraMap K₂ K₂' x)` lies in the range of
`algebraMap K₁ K₁'`, whose injectivity makes the witness `ρ x` unique; additivity and multiplicativity
of `x ↦ ρ x` follow from those of `σ` together with the injectivity of `algebraMap K₁ K₁'`, and
surjectivity from `mapsBase_mem_symm`. -/
lemma baseRingEquiv_of_mapsBase
    {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [Algebra K₁ K₁'] [Algebra K₂ K₂'] (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ) :
    ∃ ρ : K₂ ≃+* K₁, ∀ x : K₂, σ (algebraMap K₂ K₂' x) = algebraMap K₁ K₁' (ρ x) := by
  have hinj₁ : Function.Injective (algebraMap K₁ K₁') := RingHom.injective _
  have hinj₂ : Function.Injective (algebraMap K₂ K₂') := RingHom.injective _
  -- Every `σ (algebraMap K₂ K₂' x)` lies in the range of `algebraMap K₁ K₁'`.
  have hmem : ∀ x : K₂, σ (algebraMap K₂ K₂' x) ∈ (algebraMap K₁ K₁').range := fun x =>
    Submission.NeukirchUchida.mapsBase_mem _ _ hσ (RingHom.mem_range.mpr ⟨x, rfl⟩)
  -- The induced function, well defined because `algebraMap K₁ K₁'` is injective.
  let ρf : K₂ → K₁ := fun x => Classical.choose (RingHom.mem_range.mp (hmem x))
  have hρf : ∀ x : K₂, algebraMap K₁ K₁' (ρf x) = σ (algebraMap K₂ K₂' x) := fun x =>
    Classical.choose_spec (RingHom.mem_range.mp (hmem x))
  have hρf_inj : Function.Injective ρf := by
    intro x y hxy
    apply hinj₂
    apply σ.injective
    rw [← hρf x, ← hρf y, hxy]
  have hρf_surj : Function.Surjective ρf := by
    intro y
    -- `σ.symm (algebraMap K₁ K₁' y)` already lies in the embedded copy of `K₂`.
    obtain ⟨z, hz⟩ := RingHom.mem_range.mp (Submission.NeukirchUchida.mapsBase_mem_symm _ _ hσ
      (RingHom.mem_range.mpr ⟨y, rfl⟩))
    exact ⟨z, hinj₁ (by rw [hρf z, hz, RingEquiv.apply_symm_apply])⟩
  -- `ρf` is a ring homomorphism, by injectivity of `algebraMap K₁ K₁'`.
  let f : K₂ →+* K₁ :=
    { toFun := ρf
      map_one' := hinj₁ (by simp only [hρf, map_one])
      map_mul' := fun x y => hinj₁ (by simp only [hρf, map_mul])
      map_zero' := hinj₁ (by simp only [hρf, map_zero])
      map_add' := fun x y => hinj₁ (by simp only [hρf, map_add]) }
  refine ⟨RingEquiv.ofBijective f ⟨hρf_inj, hρf_surj⟩, ?_⟩
  intro x
  change σ (algebraMap K₂ K₂' x) = algebraMap K₁ K₁' (f x)
  rw [show f x = ρf x from rfl]
  exact (hρf x).symm

/-- **Every MapsBase isomorphism of the separable closures is the Galois twist of a lift of a
base-field isomorphism.**

Let `σ : K₂' ≃+* K₁'` map the embedded copy of `K₂` onto the embedded copy of `K₁`
(`MapsBase`).  Then `σ = liftTwist τ h` for the base-field isomorphism `τ : K₁ ≃+* K₂` induced by
`σ` on the base and some `h ∈ Gal(K₂'/K₂)`.  Consequently the σ-free reconstruction input
`NK.ReconstructField.ReconstructionInput` is equivalent to its σ-based form
`NK.ReconstructField.ReconstructionInputSigma`.

Proof route: `MapsBase` says that `σ` carries `(algebraMap K₂ K₂').range` onto
`(algebraMap K₁ K₁').range`, so for every `x : K₂` there is a unique `y : K₁` with
`σ (algebraMap K₂ K₂' x) = algebraMap K₁ K₁' y`; the map `x ↦ y` is a ring isomorphism `K₂ ≃+* K₁`,
and taking `τ` to be its inverse we get `σ (algebraMap K₂ K₂' (τ x)) = algebraMap K₁ K₁' x`, so
`NK.ReconstructField.eq_liftTwist_of_apply_base` applies. -/
theorem exists_twist_of_mapsBase
    {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ) :
    ∃ (τ : K₁ ≃+* K₂) (h : Gal(K₂'/K₂)), σ = liftTwist K₁ K₂ K₁' K₂' τ h := by
  obtain ⟨ρ, hρ⟩ := baseRingEquiv_of_mapsBase σ hσ
  -- On the base, `σ` restricts to `ρ⁻¹ = τ`.
  have hbase : ∀ x : K₁, σ (algebraMap K₂ K₂' (ρ.symm x)) = algebraMap K₁ K₁' x := by
    intro x
    have h := hρ (ρ.symm x)
    rwa [RingEquiv.apply_symm_apply] at h
  exact ⟨ρ.symm, eq_liftTwist_of_apply_base K₁ K₂ K₁' K₂' hbase⟩

end NK.ReconstructField
