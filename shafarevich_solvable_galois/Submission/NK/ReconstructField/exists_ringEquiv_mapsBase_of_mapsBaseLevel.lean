import Mathlib.NumberTheory.NumberField.Basic
import Submission.NK.Reconstruct.Transport
import Submission.NK.ReconstructField.exists_ringEquiv_mapsBase_of_ringEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Extending a base-compatible level isomorphism to the separable closures

`NK.Reconstruct.MapsBaseLevel L₁ L₂ τ` says that a ring isomorphism `τ : ↥L₁ ≃+* ↥L₂` of two
finite levels of the separable closures `K₁' ⊇ L₁ / K₁` and `K₂' ⊇ L₂ / K₂` carries the embedded
copy of `K₁` into the embedded copy of `K₂` and vice versa.

This file proves that such a `τ` is the restriction of a ring isomorphism `σ : K₂' ≃+* K₁'` of the
separable closures which maps the embedded copy of `K₂` *onto* the embedded copy of `K₁`
(`Submission.NeukirchUchida.MapsBase`) and which on `L₂` is exactly `τ⁻¹`.

The proof is a reduction to `NK.ReconstructField.exists_ringEquiv_mapsBase_of_ringEquiv` applied
with the two *levels* `↥L₁`, `↥L₂` as the base fields: since `K₁'` (resp. `K₂'`) is separably
closed and separable over `L₁` (resp. `L₂`), it is a separable closure of `↥L₁` (resp. `↥L₂`), and
the ring isomorphism `τ` of the bases extends to the separable closures.  The only extra input is
`MapsBaseLevel`, which is what identifies `σ` as a map of `K₂` onto `K₁` (rather than merely of `L₂`
onto `L₁`).
-/

set_option linter.style.haveILetI false

namespace NK.ReconstructField

theorem exists_ringEquiv_mapsBase_of_mapsBaseLevel {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂]
    [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (L₁ : IntermediateField K₁ K₁') (L₂ : IntermediateField K₂ K₂') [FiniteDimensional K₁ L₁]
    [NumberField ↥L₁] [NumberField ↥L₂] (τ : ↥L₁ ≃+* ↥L₂)
    (hτ : NK.Reconstruct.MapsBaseLevel L₁ L₂ τ) :
    ∃ σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ x : ↥L₂, σ (x : K₂') = ((τ.symm x : ↥L₁) : K₁') := by
  -- `K₁'` is a separable closure of `L₁`, `K₂'` one of `L₂`.
  haveI hsc₁ : IsSepClosure ↥L₁ K₁' :=
    ⟨IsSepClosure.sep_closed K₁, IntermediateField.isSeparable_tower_top K₁ L₁⟩
  haveI hsc₂ : IsSepClosure ↥L₂ K₂' :=
    ⟨IsSepClosure.sep_closed K₂, IntermediateField.isSeparable_tower_top K₂ L₂⟩
  -- Extend the base isomorphism `τ` of the levels to the separable closures.
  obtain ⟨σ, _hσmap, hσ⟩ :=
    exists_ringEquiv_mapsBase_of_ringEquiv (K₁ := ↥L₁) (K₂ := ↥L₂)
      (K₁' := K₁') (K₂' := K₂') τ
  -- `hσ : ∀ x : ↥L₁, σ (algebraMap ↥L₂ K₂' (τ x)) = algebraMap ↥L₁ K₁' x`.
  -- On the level `L₂`, `σ` is the inverse of `τ`.
  have key : ∀ z : ↥L₂, σ (algebraMap ↥L₂ K₂' z) = (τ.symm z : ↥L₁) := by
    intro z
    have h := hσ (τ.symm z)
    rw [RingEquiv.apply_symm_apply] at h
    simpa using h
  have key' : ∀ b : K₂, σ (algebraMap K₂ K₂' b) = (τ.symm (algebraMap K₂ ↥L₂ b) : ↥L₁) := by
    intro b
    simpa using key (algebraMap K₂ ↥L₂ b)
  refine ⟨σ, ?_, ?_⟩
  · -- `σ` maps the embedded `K₂` onto the embedded `K₁`.
    rw [Submission.NeukirchUchida.MapsBase]
    refine le_antisymm ?_ ?_
    · -- `σ(i₂(K₂)) ⊆ i₁(K₁)`: `τ⁻¹` carries `K₂` into `K₁` (`hτ.2`).
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Subring.mem_map.mp hx
      obtain ⟨b, rfl⟩ := RingHom.mem_range.mp hy
      obtain ⟨c, hc⟩ := hτ.2 b
      refine RingHom.mem_range.mpr ⟨c, ?_⟩
      change (algebraMap K₁ K₁') c = σ (algebraMap K₂ K₂' b)
      rw [key' b, hc]
      simp
    · -- `i₁(K₁) ⊆ σ(i₂(K₂))`: `τ` carries `K₁` into `K₂` (`hτ.1`).
      intro x hx
      obtain ⟨a, rfl⟩ := RingHom.mem_range.mp hx
      obtain ⟨c, hc⟩ := hτ.1 a
      refine Subring.mem_map.mpr
        ⟨algebraMap K₂ K₂' c, RingHom.mem_range.mpr ⟨c, rfl⟩, ?_⟩
      change σ (algebraMap K₂ K₂' c) = (algebraMap K₁ K₁') a
      rw [key' c, ← hc]
      simp
  · -- On `L₂`, `σ` is `τ⁻¹`.
    intro x
    simpa using key x

end NK.ReconstructField
