import Mathlib
import Submission.NK.ReconstructField.Basic
import Submission.NK.Reconstruct.PlaceCorrespondence
import Submission.NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.ReconstructField

open IsDedekindDomain

open scoped Pointwise

/-- **The completely split primes at corresponding levels** (step 2 of the reconstruction, the
"prime correspondence at finite levels").

Let `ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` be a homeomorphic isomorphism with local correspondence `a`
(CoNF (12.1.9)), and let `L ⊆ K₁'` be a finite normal level which is a number field, with image
level `L₂ = levelMap ϕ L` (the fixed field of `ϕ(Gal(K₁'/L))`).  Then a prime `p` of `K₁` splits
completely in `L` if and only if its image `a.primeMap p` splits completely in `L₂`.

Proof route (using only `(A)`): for a place `A` of `K₁'` over `p`, the decomposition group `D_A` is
contained in `Gal(K₁'/L)` if and only if `p` splits completely in `L`
(`NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely`); applying this criterion to
`(K₁,L,A)` and to `(K₂, levelMap ϕ L, a.placeMap A)` — whose prime below is `a.primeMap p` by
`a.primeMap_spec` — the claim reduces to `D_A ≤ L.fixingSubgroup ↔ ϕ(D_A) ≤ ϕ(L.fixingSubgroup)`,
which follows from `a.map_decomp`, `NK.Reconstruct.fixingSubgroup_levelMap` and injectivity of
`ϕ`. -/
theorem splitsCompletely_levelMap_iff
    {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ L)]
    [NumberField ↥(NK.Reconstruct.levelMap ϕ L)] :
    ∀ p : NK.Chebotarev.PrimeIdeal K₁,
      NK.ReconstructField.SplitsCompletely K₁ ↥L p ↔
        NK.ReconstructField.SplitsCompletely K₂ ↥(NK.Reconstruct.levelMap ϕ L)
          (a.primeMap p) := by
  classical
  intro p
  -- A place of `K₁'` lying over the prime `p`.
  set A : NK.Reconstruct.FinitePlaceOf K₁ K₁' :=
    Submission.NeukirchUchida.placeOver (K₁ := K₁) (K₁' := K₁') p with hA
  have hAspec : A.1.comap (algebraMap K₁ K₁') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₁ p :=
    Submission.NeukirchUchida.placeOver_spec (K₁ := K₁) (K₁' := K₁') p
  -- The prime of `K₁` below `A` is `p`.
  have hprime : Submission.NeukirchUchida.primeOf A.1 A.2 = p :=
    Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (by
      rw [← Submission.NeukirchUchida.primeOf_spec A.1 A.2, hAspec])
  -- The prime of `K₂` below `placeMap A` is `primeMap p`.
  have hBspec : (a.placeMap A).1.comap (algebraMap K₂ K₂') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₂ (a.primeMap p) := by
    rw [← hprime, a.primeMap_spec A]
    exact Submission.NeukirchUchida.primeOf_spec (a.placeMap A).1 (a.placeMap A).2
  -- The criterion of `stabilizer_le_fixingSubgroup_iff_splitCompletely` at the two levels.
  have hcrit₁ := NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely
    (K := K₁) (K' := K₁') (N := L) p A.1 hAspec
  have hcrit₂ := NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely
    (K := K₂) (K' := K₂') (N := NK.Reconstruct.levelMap ϕ L) (a.primeMap p)
    (a.placeMap A).1 hBspec
  -- The decomposition groups correspond under `ϕ`.
  have hmap : (MulAction.stabilizer Gal(K₁'/K₁) A.1).map
      (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
      MulAction.stabilizer Gal(K₂'/K₂) (a.placeMap A).1 := a.map_decomp A
  -- The fixing subgroup of the image level is the image of the fixing subgroup.
  have hfix : (NK.Reconstruct.levelMap ϕ L).fixingSubgroup =
      L.fixingSubgroup.map (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) :=
    NK.Reconstruct.fixingSubgroup_levelMap hϕ L
  -- Containment in the fixing subgroup is transported along the multiplicative equivalence `ϕ`.
  have hstab : (MulAction.stabilizer Gal(K₁'/K₁) A.1 ≤ L.fixingSubgroup) ↔
      (MulAction.stabilizer Gal(K₂'/K₂) (a.placeMap A).1 ≤
        (NK.Reconstruct.levelMap ϕ L).fixingSubgroup) := by
    rw [hfix, ← hmap]
    exact (Subgroup.map_le_map_iff_of_injective ϕ.injective).symm
  exact hcrit₁.symm.trans (hstab.trans hcrit₂)

end NK.ReconstructField
