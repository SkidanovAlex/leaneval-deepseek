import Submission.NK.ReconstructField.Basic
import Submission.NeukirchUchida.PlaceSystem
import Submission.NK.Reconstruct.InnerTwist
import Submission.NK.Reconstruct.comap_placeMap_eq_of_realizesPlaceMap
import Submission.Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime

/-!
# Rigidity of the place system

The place system of the separable closure `K₁'` of a number field `K₁` — the family of places over
the finite primes, with its `Gal(K₁'/K₁)`-action — is *rigid*: it has no non-trivial
Galois-equivariant automorphism.  Consequently the place map of a group isomorphism `ϕ` is
**unique** (`NK.ReconstructField.placeEquiv_ext`): given `ϕ`, there is at most one equivariant
bijection of the place systems of `K₁'` and `K₂'` compatible with `ϕ`.

This is the "fibre" rigidity that underlies the correspondence of *primes at finite levels*
(CoNF XII §12.2): a fibre of the place system over a prime of the base field is a transitive
`Gal`-set whose equivariant self-bijections are trivial, because the decomposition groups are
self-normalising (`NK.ReconstructField.normalizer_decompositionGroup_finitePlace`, i.e.
CoNF (12.1.3)/(12.1.4), that a place is determined by its decomposition group).

The mathematical content is exactly the *freeness* of the place system as a structure, and it is an
unconditional theorem about the pair `(K₁, K₁')` alone: no hypothesis on a second field, on `ϕ`, or
on the existence of a realizing field isomorphism of the separable closures is used.
-/

set_option linter.unusedVariables false

namespace NK.ReconstructField

open NK.Reconstruct

open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **A decomposition group of a place over a finite prime is self-normalising**
(CoNF XII (12.1.3)/(12.1.4), "only if" half of Neukirch's local characterisation (12.1.9)).

The general form in `Submission.NeukirchUchida.PlaceSystem.normalizer_decompositionGroup` is stated
for places cut out by a height-one prime `p` of `𝓞 K₁`; every place of `K₁'` over a finite prime is
of that form, which is the content of the bookkeeping below. -/
theorem normalizer_decompositionGroup_finitePlace (A : NK.Reconstruct.FinitePlaceOf K₁ K₁') :
    Subgroup.normalizer (Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A.1) =
      Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A.1 := by
  obtain ⟨P, hP⟩ :=
    Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
      (A.1.comap (algebraMap K₁ K₁')) A.2
      (Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top _ A.2)
  exact Submission.NeukirchUchida.normalizer_decompositionGroup P A.1 hP

/-- **The place system is rigid**: a `Gal(K₁'/K₁)`-equivariant bijection of the places of `K₁'`
over the finite primes of `K₁` is the identity.

The proof is the fibre argument: for an equivariant `Φ`, an element `w` of the decomposition group
of a place `B` lies in the decomposition group of `Φ B` (because `Φ B = Φ (w • B) = w • Φ B`), and
applying the same argument to `Φ⁻¹` gives the converse inclusion; the two decomposition groups are
equal, so the places are equal by `Submission.NeukirchUchida.decompositionGroup_injective`. -/
theorem placeEquiv_ext {Φ Φ' : NK.Reconstruct.FinitePlaceOf K₁ K₁' ≃
    NK.Reconstruct.FinitePlaceOf K₁ K₁'}
    (hΦ : ∀ (g : Gal(K₁'/K₁)) (A : NK.Reconstruct.FinitePlaceOf K₁ K₁'),
      Φ (NK.Reconstruct.placeSmul g A) = NK.Reconstruct.placeSmul g (Φ A))
    (hΦ' : ∀ (g : Gal(K₁'/K₁)) (A : NK.Reconstruct.FinitePlaceOf K₁ K₁'),
      Φ' (NK.Reconstruct.placeSmul g A) = NK.Reconstruct.placeSmul g (Φ' A)) :
    Φ = Φ' := by
  -- equivariance of `β := Φ' ∘ Φ⁻¹`
  have hβ : ∀ (g : Gal(K₁'/K₁)) (B : NK.Reconstruct.FinitePlaceOf K₁ K₁'),
      Φ' (Φ.symm (NK.Reconstruct.placeSmul g B)) =
        NK.Reconstruct.placeSmul g (Φ' (Φ.symm B)) := by
    intro g B
    have h1 : Φ.symm (NK.Reconstruct.placeSmul g B) =
        NK.Reconstruct.placeSmul g (Φ.symm B) := by
      apply Φ.injective
      rw [Equiv.apply_symm_apply, hΦ, Equiv.apply_symm_apply]
    rw [h1, hΦ']
  -- equivariance of the inverse of `β`
  have hβ' : ∀ (g : Gal(K₁'/K₁)) (C : NK.Reconstruct.FinitePlaceOf K₁ K₁'),
      Φ (Φ'.symm (NK.Reconstruct.placeSmul g C)) =
        NK.Reconstruct.placeSmul g (Φ (Φ'.symm C)) := by
    intro g C
    have h1 : Φ'.symm (NK.Reconstruct.placeSmul g C) =
        NK.Reconstruct.placeSmul g (Φ'.symm C) := by
      apply Φ'.injective
      rw [Equiv.apply_symm_apply, hΦ', Equiv.apply_symm_apply]
    rw [h1, hΦ]
  have key : ∀ B : NK.Reconstruct.FinitePlaceOf K₁ K₁', Φ' (Φ.symm B) = B := by
    intro B
    have hle : Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') B.1 ≤
        Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁')
          (Φ' (Φ.symm B)).1 := by
      intro w hw
      have hwB : NK.Reconstruct.placeSmul w B = B :=
        Subtype.ext (MulAction.mem_stabilizer_iff.mp hw)
      have hstep : Φ' (Φ.symm B) = Φ' (Φ.symm (NK.Reconstruct.placeSmul w B)) := by rw [hwB]
      rw [hβ w B] at hstep
      exact MulAction.mem_stabilizer_iff.mpr (Subtype.ext_iff.mp hstep).symm
    have hge : Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁')
          (Φ' (Φ.symm B)).1 ≤
        Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') B.1 := by
      intro w hw
      have hws : NK.Reconstruct.placeSmul w (Φ' (Φ.symm B)) = Φ' (Φ.symm B) :=
        Subtype.ext (MulAction.mem_stabilizer_iff.mp hw)
      have hstep : Φ (Φ'.symm (Φ' (Φ.symm B))) =
          Φ (Φ'.symm (NK.Reconstruct.placeSmul w (Φ' (Φ.symm B)))) := by rw [hws]
      rw [hβ' w (Φ' (Φ.symm B))] at hstep
      rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply] at hstep
      exact MulAction.mem_stabilizer_iff.mpr (Subtype.ext_iff.mp hstep).symm
    exact Subtype.ext (Submission.NeukirchUchida.decompositionGroup_injective B.2
      (Φ' (Φ.symm B)).2 (le_antisymm hle hge)).symm
  refine Equiv.ext fun B => ?_
  simpa using (key (Φ B)).symm

/-- **The place map of a group isomorphism is unique.**  Two `ϕ`-equivariant bijections of the place
systems of `K₁'` and `K₂'` over the finite primes coincide: the composite `Φ' ∘ Φ⁻¹` is
`Gal(K₂'/K₂)`-equivariant, and `placeEquiv_ext` (rigidity of the place system) forces it to be the
identity.

Consequently the local correspondence of CoNF (12.1.9) — when it exists — is *canonical*: given
`ϕ`, there is at most one place map satisfying `placeMap (g • A) = ϕ g • placeMap A`.  The freedom
in the reconstruction therefore never lies in the place map, but in the question whether it is
induced by a field isomorphism. -/
theorem placeMap_unique {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}
    {Φ Φ' : NK.Reconstruct.FinitePlaceOf K₁ K₁' ≃ NK.Reconstruct.FinitePlaceOf K₂ K₂'}
    (hΦ : ∀ (g : Gal(K₁'/K₁)) (A : NK.Reconstruct.FinitePlaceOf K₁ K₁'),
      Φ (NK.Reconstruct.placeSmul g A) = NK.Reconstruct.placeSmul₂ (ϕ g) (Φ A))
    (hΦ' : ∀ (g : Gal(K₁'/K₁)) (A : NK.Reconstruct.FinitePlaceOf K₁ K₁'),
      Φ' (NK.Reconstruct.placeSmul g A) = NK.Reconstruct.placeSmul₂ (ϕ g) (Φ' A)) :
    Φ = Φ' := by
  -- `Ψ := Φ' ∘ Φ⁻¹` is equivariant, so by `placeEquiv_ext` it is the identity
  have hid : ∀ (g : Gal(K₂'/K₂)) (B : NK.Reconstruct.FinitePlaceOf K₂ K₂'),
      (Equiv.refl _) (NK.Reconstruct.placeSmul₂ g B) = NK.Reconstruct.placeSmul₂ g ((Equiv.refl _) B) :=
    fun g B => rfl
  have hΨ : ∀ (g : Gal(K₂'/K₂)) (B : NK.Reconstruct.FinitePlaceOf K₂ K₂'),
      (Φ.symm.trans Φ') (NK.Reconstruct.placeSmul₂ g B) =
        NK.Reconstruct.placeSmul₂ g ((Φ.symm.trans Φ') B) := by
    intro g B
    have h1 : Φ.symm (NK.Reconstruct.placeSmul₂ g B) =
        NK.Reconstruct.placeSmul (ϕ.symm g) (Φ.symm B) := by
      apply Φ.injective
      rw [Equiv.apply_symm_apply, hΦ, MulEquiv.apply_symm_apply]
      rw [Equiv.apply_symm_apply]
    rw [Equiv.trans_apply, h1, hΦ', Equiv.trans_apply, MulEquiv.apply_symm_apply]
  have := placeEquiv_ext (Φ := Φ.symm.trans Φ') (Φ' := Equiv.refl _) hΨ hid
  refine Equiv.ext fun A => ?_
  have h := Equiv.congr_fun this (Φ A)
  rw [Equiv.trans_apply] at h
  have h2 : Φ' (Φ.symm (Φ A)) = Φ A := by simpa using h
  have h3 : Φ' A = Φ A := by rwa [Equiv.symm_apply_apply] at h2
  exact h3.symm

/-- **Non-vacuity of the rigidity of the place system** (`NK.Reconstruct.PlaceRigidity`): every
place-system-preserving automorphism of `Gal(K₂'/K₂)` coming from a field automorphism of `K₂'`
which preserves the embedded copy of `K₂` *does* preserve the family of decomposition groups of the
places over the finite primes.  (That family is exactly the hypothesis of the rigidity statement,
so the class of automorphisms to which it applies is non-empty and contains the field-theoretic
ones.) -/
theorem placePreserving_conjHomEquiv (c : K₂' ≃+* K₂')
    (hc : Submission.NeukirchUchida.MapsBase (algebraMap K₂ K₂') (algebraMap K₂ K₂') c) :
    ∀ B : ValuationSubring K₂', B.comap (algebraMap K₂ K₂') ≠ ⊤ →
      ∃ B' : ValuationSubring K₂', B'.comap (algebraMap K₂ K₂') ≠ ⊤ ∧
        (Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂') B).map
            ((Submission.NeukirchUchida.conjHomEquiv hc : Gal(K₂'/K₂) ≃* Gal(K₂'/K₂)) :
              Gal(K₂'/K₂) →* Gal(K₂'/K₂)) =
          Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂') B' := by
  intro B hB
  exact ⟨B.comap (c : K₂' →+* K₂'), NK.Reconstruct.comap_sigma_comap_ne_top hc hB,
    NK.Reconstruct.map_conjHomEquiv_decompositionGroup hc B⟩

end NK.ReconstructField
