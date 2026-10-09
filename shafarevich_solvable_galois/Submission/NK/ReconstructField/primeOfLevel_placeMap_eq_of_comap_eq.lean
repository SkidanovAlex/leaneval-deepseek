import Mathlib
import Submission.NK.ReconstructField.All
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false

namespace NK.ReconstructField

open scoped Pointwise

/-- **Well-definedness of the level prime `primeOfLevel` attached to a place through the local
correspondence `a`.**

If two places `A`, `A'` of `K₁'` over finite primes have the same trace on a finite normal level
`L ⊆ K₁'` (i.e. they lie over the same prime of `𝓞 L`), then the primes of the corresponding level
`levelMap ϕ L` cut out by the corresponding places `a.placeMap A`, `a.placeMap A'` of `K₂'` agree.

The proof is the transitivity of the Galois action on the places of `K₁'` above a fixed place of
`L` (`Commons.FieldTheory.Galois.exists_restrictScalars_smul_eq_of_comap_eq`): there is a
`σ ∈ Gal(K₁'/K₁)` fixing `L` pointwise with `A = σ • A'`.  By the Galois equivariance
`a.map_smul` of the place correspondence, `a.placeMap A = (ϕ σ) • a.placeMap A'`, and since `σ`
fixes `L`, the element `ϕ σ` fixes `levelMap ϕ L` pointwise; hence the two places have the same
trace on `levelMap ϕ L`, and `primeOfLevel_spec` together with the injectivity of
`valuationSubringAtPrime` gives the claim. -/
theorem primeOfLevel_placeMap_eq_of_comap_eq
    {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ L)]
    [NumberField ↥(NK.Reconstruct.levelMap ϕ L)]
    (A A' : NK.Reconstruct.FinitePlaceOf K₁ K₁')
    (h : A.1.comap (algebraMap ↥L K₁') = A'.1.comap (algebraMap ↥L K₁')) :
    NK.Reconstruct.primeOfLevel (a.placeMap A).1 (NK.Reconstruct.levelMap ϕ L)
        (NK.Reconstruct.comap_level_ne_top (a.placeMap A).2 (NK.Reconstruct.levelMap ϕ L)) =
      NK.Reconstruct.primeOfLevel (a.placeMap A').1 (NK.Reconstruct.levelMap ϕ L)
        (NK.Reconstruct.comap_level_ne_top (a.placeMap A').2 (NK.Reconstruct.levelMap ϕ L)) := by
  -- Transitivity of the Galois action on the places above a fixed place of `L`: some
  -- `σ ∈ Gal(K₁'/K₁)` fixing `L` pointwise carries `A'` onto `A`.
  obtain ⟨σ, hσL, hσcomap⟩ :=
    Commons.FieldTheory.Galois.exists_restrictScalars_smul_eq_of_comap_eq
      (K := K₁) (K' := K₁') L A'.1 A.1 (NK.Reconstruct.comap_level_ne_top A'.2 L) h.symm
  -- Equivalently, `A = σ • A'` as valuation subrings.
  have hsmul : (σ : Gal(K₁'/K₁)) • A'.1 = A.1 := by
    rw [← hσcomap]
    ext x
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      AlgEquiv.smul_def]
    rfl
  have hplace : NK.Reconstruct.placeSmul σ A' = A := by
    apply Subtype.ext
    rw [NK.Reconstruct.placeSmul_val]
    exact hsmul
  -- Galois equivariance of the place correspondence.
  have hkey : a.placeMap A = NK.Reconstruct.placeSmul₂ (ϕ σ) (a.placeMap A') := by
    rw [← hplace]
    exact a.map_smul σ A'
  have hval : (a.placeMap A).1 = (ϕ σ) • (a.placeMap A').1 := by
    rw [congrArg Subtype.val hkey, NK.Reconstruct.placeSmul₂_val]
  -- `σ` fixes `L`, so `ϕ σ` fixes `levelMap ϕ L` pointwise.
  have hfix : ∀ x : ↥(NK.Reconstruct.levelMap ϕ L), (ϕ σ) (x : K₂') = (x : K₂') := by
    intro x
    exact (NK.Reconstruct.mem_levelMap_iff (ϕ := ϕ) (L := L) (x := (x : K₂'))).mp x.2 σ hσL
  -- Hence the two places have the same trace on `levelMap ϕ L`.
  have hcomap : (a.placeMap A).1.comap (algebraMap ↥(NK.Reconstruct.levelMap ϕ L) K₂') =
      (a.placeMap A').1.comap (algebraMap ↥(NK.Reconstruct.levelMap ϕ L) K₂') := by
    rw [hval]
    ext x
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    have h' : (ϕ σ)⁻¹ • (algebraMap ↥(NK.Reconstruct.levelMap ϕ L) K₂' x)
        = algebraMap ↥(NK.Reconstruct.levelMap ϕ L) K₂' x := by
      rw [AlgEquiv.smul_def]
      have := congrArg (⇑((ϕ σ)⁻¹ : Gal(K₂'/K₂))) (hfix x)
      simpa using this.symm
    rw [h']
  -- `primeOfLevel` is determined by the trace of the place on the level.
  exact Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
    ((NK.Reconstruct.primeOfLevel_spec (a.placeMap A).1 (NK.Reconstruct.levelMap ϕ L)
        (NK.Reconstruct.comap_level_ne_top (a.placeMap A).2 (NK.Reconstruct.levelMap ϕ L))).symm.trans
      (hcomap.trans
        (NK.Reconstruct.primeOfLevel_spec (a.placeMap A').1 (NK.Reconstruct.levelMap ϕ L)
          (NK.Reconstruct.comap_level_ne_top (a.placeMap A').2 (NK.Reconstruct.levelMap ϕ L)))))

end NK.ReconstructField
