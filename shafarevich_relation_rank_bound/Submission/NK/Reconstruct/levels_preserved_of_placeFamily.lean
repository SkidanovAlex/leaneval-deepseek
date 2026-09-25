import Mathlib
import Submission.NK.Reconstruct.eq_of_splitPrimes_eq
import Submission.NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely
import Submission.NK.Reconstruct.eq_of_stabilizer_le_fixingSubgroup
import Submission.NK.Reconstruct.LevelMap
import Submission.NK.Reconstruct.agreesOnLevels_of_map_decompositionGroup
import Submission.Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top
import Submission.Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped Pointwise

namespace NK.Reconstruct

/-- **A continuous prime-fixing place-preserving automorphism of `G_K` preserves every finite
Galois level.**  If `ψ : Gal(K'/K) ≃* Gal(K'/K)` is a *homeomorphism* (which is the case for every
obstruction arising in this development, `ϕ` satisfying `IsHomeomorph`) and maps the decomposition
group of every place `B` of `K'` over a prime of `K` onto the decomposition group of a place `B'` of
`K'` *over the same prime of `K` as `B`*, then for every finite Galois number-field level `L ⊆ K'`
the image of `Gal(K'/L)` under `ψ` is again `Gal(K'/L)`.

Route: continuity gives that `(L.fixingSubgroup).map ψ` is closed (an image of an open subgroup
under a homeomorphism), hence is the fixing subgroup of a finite Galois level `L'`.  Then fix a
prime `p`; `hplace` makes `ψ` permute the places over `p` surjectively, and for a place `B` over `p`,
`p` splits completely in `L` iff `MulAction.stabilizer Gal(K'/K) B ≤ L.fixingSubgroup`
(`NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely`); applying `ψ` turns this into
the same statement for `L'` and the place `B'` over the *same* `p`, so `L` and `L'` have the same
completely split primes and `NK.Reconstruct.eq_of_splitPrimes_eq` (Bauer) gives `L' = L`.

**Sharpness.**  Neither the continuity nor the prime-fixing clause can be dropped: continuity is
needed because the image of an open subgroup under a non-continuous automorphism need not be closed
(the sibling `Submission.NeukirchUchida.GaloisIso.exists_finite_fixingSubgroup_map` carries the same
hypothesis), and prime-fixing is needed by the `K = ℚ(i)` counterexample recorded in
`Submission/Work/Reconstruct/PlaceRigidity.lean`, where a place-preserving automorphism permutes the
primes of `K` and sends `Gal(K'/L)` to `Gal(K'/c(L))`.  Hence this is the prime-fixing half of the
reduction of `NK.Reconstruct.PlaceRigidity` to a finite-level statement; the prime-permuting case
is the `Aut(K)`-twist, which must be factored out. -/
theorem levels_preserved_of_placeFamily {K : Type*} [Field K] [NumberField K]
    {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']
    (ψ : Gal(K'/K) ≃* Gal(K'/K)) (hψ : IsHomeomorph ψ)
    (hplace : ∀ B : ValuationSubring K', B.comap (algebraMap K K') ≠ ⊤ →
      ∃ B' : ValuationSubring K', B'.comap (algebraMap K K') ≠ ⊤ ∧
        B'.comap (algebraMap K K') = B.comap (algebraMap K K') ∧
        (Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') B).map
            (ψ : Gal(K'/K) →* Gal(K'/K)) =
          Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') B')
    (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L] :
    (L.fixingSubgroup).map (ψ : Gal(K'/K) →* Gal(K'/K)) = L.fixingSubgroup := by
  classical
  -- The image of the level `L` under the Galois correspondence attached to `ψ`: its fixing
  -- subgroup is `ψ(Gal(K'/L))`.
  obtain ⟨L', hfd', hnorm', hnf', hfix⟩ : ∃ L' : IntermediateField K K',
      FiniteDimensional K L' ∧ Normal K L' ∧ NumberField ↥L' ∧
        L'.fixingSubgroup = (L.fixingSubgroup).map (ψ : Gal(K'/K) →* Gal(K'/K)) :=
    ⟨NK.Reconstruct.levelMap ψ L, NK.Reconstruct.finiteDimensional_levelMap hψ L,
      NK.Reconstruct.normal_levelMap hψ L, NK.Reconstruct.numberField_levelMap hψ L,
      NK.Reconstruct.fixingSubgroup_levelMap hψ L⟩
  haveI := hfd'
  haveI := hnorm'
  haveI := hnf'
  -- Every place over a finite prime `p` of `K` detects the same splitting behaviour in `L` and
  -- in `L'`.
  have hpres : ∀ B : ValuationSubring K', B.comap (algebraMap K K') ≠ ⊤ →
      (MulAction.stabilizer Gal(K'/K) B ≤ L.fixingSubgroup ↔
        MulAction.stabilizer Gal(K'/K) B ≤ L'.fixingSubgroup) := by
    intro B hB
    obtain ⟨B', _hB'ne, hB'comap, hψmap⟩ := hplace B hB
    have hψmap' : (MulAction.stabilizer Gal(K'/K) B).map (ψ : Gal(K'/K) →* Gal(K'/K)) =
        MulAction.stabilizer Gal(K'/K) B' := hψmap
    -- the prime of `K` below `B`
    obtain ⟨p, hp⟩ :=
      Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
        (B.comap (algebraMap K K')) hB
        (Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top _ hB)
    have hB'p : B'.comap (algebraMap K K') =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p :=
      hB'comap.trans hp
    -- the dictionary, at the level `L` and at the level `L'`
    have dL := NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely
      (K := K) (K' := K') (N := L) p B hp
    have dL' := NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely
      (K := K) (K' := K') (N := L') p B hp
    have dB' := NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely
      (K := K) (K' := K') (N := L') p B' hB'p
    -- `ψ` carries the stabiliser of `B` to that of `B'` and `Gal(K'/L)` to `Gal(K'/L')`
    have core : MulAction.stabilizer Gal(K'/K) B ≤ L.fixingSubgroup ↔
        MulAction.stabilizer Gal(K'/K) B' ≤ L'.fixingSubgroup := by
      have h1 := (NK.Reconstruct.subgroup_map_le_map_iff_of_injective
        (ψ : Gal(K'/K) →* Gal(K'/K)) ψ.injective
        (X := MulAction.stabilizer Gal(K'/K) B) (Y := L.fixingSubgroup))
      rw [hψmap', ← hfix] at h1
      exact h1.symm
    have hmid : ((p.asIdeal.primesOver (NumberField.RingOfIntegers ↥L)).ncard =
          Module.finrank K ↥L) ↔
        ((p.asIdeal.primesOver (NumberField.RingOfIntegers ↥L')).ncard =
          Module.finrank K ↥L') := by
      rw [← dL, ← dB']
      exact core
    exact dL.trans (hmid.trans dL'.symm)
  have hLL' : L = L' :=
    NK.Reconstruct.eq_of_stabilizer_le_fixingSubgroup (K := K) (K' := K') hpres
  rw [← hLL'] at hfix
  exact hfix.symm

end NK.Reconstruct
