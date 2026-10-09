import Mathlib
import Submission.NK.Reconstruct.InnerTwist
import Submission.NK.Reconstruct.comap_placeMap_eq_of_realizesPlaceMap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A realizing `σ` from a conjugating `σ₀` with inner obstruction

Let `K₁, K₂` be number fields with separable closures `K₁', K₂'`, let
`ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` be an isomorphism of absolute Galois groups and
`a : LocalCorrespondence ϕ` its (group-theoretically defined) local correspondence.  Suppose a
base-field-mapping isomorphism `σ₀ : K₂' ≃+* K₁'` is known, and that the obstruction
`Φ_{σ₀} ∘ ϕ⁻¹` (where `Φ_{σ₀} = conjHomEquiv hσ₀`) is inner, `Φ_{σ₀} ∘ ϕ⁻¹ = MulAut.conj k`
for some `k ∈ Gal(K₂'/K₂)`.

The *inner-twist reduction* (`NK.Reconstruct.conjugates_trans_of_conj_normal`) then exhibits an
explicit `MapsBase` isomorphism realizing `ϕ` as a conjugation, namely
`σ := k.toRingEquiv.trans σ₀`, and `NK.Reconstruct.comap_placeMap_eq_of_conjugates` — reproduced
here in-line so that this file rests only on stable modules — shows that this `σ` realizes the
place correspondence `a.placeMap` as well.  This is precisely the structure field
`GoodLocalCorrespondence.sigma` together with `sigma_mapsBase` and `sigma_realizes`.
-/

namespace NK.Reconstruct

open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The twist realizing an inner obstruction realizes the place correspondence.**  If `σ₀` is a
base-field-mapping isomorphism and `Φ_{σ₀} ∘ ϕ⁻¹ = MulAut.conj k`, then `σ := k.toRingEquiv.trans σ₀`
is a base-field-mapping isomorphism inducing `ϕ` by conjugation and realizing the local
correspondence `a.placeMap` of `ϕ`. -/
theorem exists_realizing_sigma_of_conj_normal {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂]
    [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} (a : LocalCorrespondence ϕ) {σ₀ : K₂' ≃+* K₁'}
    (hσ₀ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ₀)
    (k : Gal(K₂'/K₂))
    (h : ϕ.symm.trans (Submission.NeukirchUchida.conjHomEquiv hσ₀) = MulAut.conj k) :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁')
        (algebraMap K₂ K₂') σ ∧
      ∀ A : FinitePlaceOf K₁ K₁', (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1 := by
  -- the inner-twist reduction: `σ := k.toRingEquiv.trans σ₀` maps the bases onto each other
  -- and conjugates to `ϕ`
  have hconj : Submission.NeukirchUchida.Conjugates (k.toRingEquiv.trans σ₀) ϕ :=
    conjugates_trans_of_conj_normal (σ₀ := σ₀) (hσ₀ := hσ₀) k h
  obtain ⟨hbase, hconjeq⟩ := hconj
  refine ⟨k.toRingEquiv.trans σ₀, hbase, fun A => ?_⟩
  -- `ϕ` *is* the conjugation isomorphism induced by `σ`
  have hhom : (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
      (Submission.NeukirchUchida.conjHomEquiv hbase :
        Gal(K₁'/K₁) →* Gal(K₂'/K₂)) := by
    ext g x
    change (ϕ g).toRingEquiv x =
      (Submission.NeukirchUchida.conj hbase g).toRingEquiv x
    rw [hconjeq g, Submission.NeukirchUchida.conj_toRingEquiv hbase g]
  -- the decomposition group of `a.placeMap A` is that of the place transported by `σ`
  have hD : Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂')
        (a.placeMap A).1 =
      Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂')
        (A.1.comap (k.toRingEquiv.trans σ₀ : K₂' →+* K₁')) := by
    rw [← a.map_decomp A, hhom,
      ← map_conjHomEquiv_decompositionGroup hbase A.1]
  -- rigidity of places: a place over a finite prime is determined by its decomposition group
  have hBC : (a.placeMap A).1 = A.1.comap (k.toRingEquiv.trans σ₀ : K₂' →+* K₁') :=
    Submission.NeukirchUchida.decompositionGroup_injective (K₁ := K₂) (K₁' := K₂')
      (a.placeMap A).2 (comap_sigma_comap_ne_top hbase A.2) hD
  rw [hBC]
  exact comap_symm_comap_eq (k.toRingEquiv.trans σ₀) A.1

end NK.Reconstruct
