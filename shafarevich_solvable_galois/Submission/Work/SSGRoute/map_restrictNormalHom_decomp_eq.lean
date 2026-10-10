import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.InfInertiaClosureDefs
import Submission.Work.SSGRoute.decomp_mod_inertia_cyclic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open scoped Pointwise NumberField

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-! ## Auxiliary lemmas (replayed from `decomp_mod_inertia_cyclic.lean`) -/

/-- **The two descriptions of the automorphism of `𝓞 L` induced by `τ` agree**: the restriction of
a `k`-automorphism to the ring of integers is `galRestrict`, so `MulSemiringAction.toRingHom` of
the Galois action on `𝓞 L` is the ring hom induced by `galRestrict`. -/
private theorem galRestrict_coe_eq_toRingHom {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (τ : L ≃ₐ[K] L) :
    (galRestrict (𝓞 K) K L (𝓞 L) τ : 𝓞 L →+* 𝓞 L) =
      MulSemiringAction.toRingHom (L ≃ₐ[K] L) (𝓞 L) τ := by
  ext y
  rw [MulSemiringAction.toRingHom_apply]
  change algebraMap (𝓞 L) L (((galRestrict (𝓞 K) K L (𝓞 L)) τ) y) =
    algebraMap (𝓞 L) L (τ • y)
  rw [algebraMap_galRestrict_apply, algebraMap.smul']
  rfl

/-- **The stabiliser of a prime is the set of elements fixing its induced place**: the ideal
action on `P.asIdeal` agrees with `placeSmul`. -/
private theorem placeSmul_eq_iff_smul_asIdeal {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (τ : L ≃ₐ[K] L) :
    Submission.NeukirchUchida.Local.placeSmul τ P = P ↔ τ • P.asIdeal = P.asIdeal := by
  constructor
  · intro h
    have h2 : Ideal.map (galRestrict (𝓞 K) K L (𝓞 L) τ : 𝓞 L →+* 𝓞 L) P.asIdeal = P.asIdeal := by
      conv_rhs => rw [← congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h]
      rw [Submission.NeukirchUchida.Local.placeSmul_asIdeal]
    rw [Ideal.pointwise_smul_def, ← galRestrict_coe_eq_toRingHom]
    exact h2
  · intro h
    apply IsDedekindDomain.HeightOneSpectrum.ext
    rw [Submission.NeukirchUchida.Local.placeSmul_asIdeal]
    rw [Ideal.pointwise_smul_def, ← galRestrict_coe_eq_toRingHom] at h
    exact h

/-- **The stabiliser of a prime ideal is contained in the stabiliser of its valuation ring.** -/
private theorem stabilizer_asIdeal_le_stabilizer_valuationSubringAtPrime {K L : Type*} [Field K]
    [Field L] [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    MulAction.stabilizer (L ≃ₐ[K] L) P.asIdeal ≤
      MulAction.stabilizer (L ≃ₐ[K] L)
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L P) := by
  intro τ hτ
  rw [MulAction.mem_stabilizer_iff] at hτ ⊢
  have hmap : Ideal.map (galRestrict (𝓞 K) K L (𝓞 L) τ : 𝓞 L →+* 𝓞 L) P.asIdeal = P.asIdeal := by
    rw [galRestrict_coe_eq_toRingHom, ← Ideal.pointwise_smul_def]
    exact hτ
  exact Commons.NumberTheory.RamificationInertia.smul_valuationSubringAtPrime_eq_map_galRestrict
    P P τ hmap.symm

/-- **The stabiliser of the valuation ring of a prime is contained in the stabiliser of the
prime ideal.** -/
private theorem stabilizer_valuationSubringAtPrime_le_stabilizer_asIdeal {K L : Type*} [Field K]
    [Field L] [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    MulAction.stabilizer (L ≃ₐ[K] L)
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L P) ≤
      MulAction.stabilizer (L ≃ₐ[K] L) P.asIdeal := by
  intro τ hτ
  rw [MulAction.mem_stabilizer_iff] at hτ ⊢
  have h1 : τ ∈ Submission.NeukirchUchida.Local.decompositionSubgroup (K := K) P :=
    (Submission.NeukirchUchida.Local.mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup
      P τ).mp hτ
  rw [Submission.NeukirchUchida.Local.mem_decompositionSubgroup] at h1
  exact (placeSmul_eq_iff_smul_asIdeal P τ).mp h1

/-- **The restriction of the decomposition group of `B` to a finite normal level is the
decomposition group of the trace of `B` on that level.** -/
private theorem map_restrictNormalHom_decomp_eq_stabilizer {B : ValuationSubring Ω}
    (hB : SSGRoute.IsFinPlace k B)
    (L : IntermediateField k Ω) [FiniteDimensional k L] [Normal k L] :
    (SSGRoute.decomp k B).map (AlgEquiv.restrictNormalHom L) =
      MulAction.stabilizer (↥L ≃ₐ[k] ↥L) (B.comap (algebraMap ↥L Ω)) := by
  apply le_antisymm
  · rintro τ ⟨σ, hσ, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hσ
    rw [← Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul B σ L, hσ]
  · intro τ hτ
    obtain ⟨σ, hσ, hres⟩ := Commons.FieldTheory.Galois.exists_mem_stabilizer_restrictNormalHom_eq
      (F := k) (K' := Ω) B hB L τ hτ
    exact ⟨σ, hσ, hres⟩

/-- **The restriction to a finite normal level maps the decomposition group of `A` onto the
decomposition group of the level prime.**

ROUTE (the general-`k` form of the *proved* private lemma
`map_restrictNormalHom_decomp_eq_stabilizer` in
`Submission/Work/SSGRoute/decomp_mod_inertia_cyclic.lean`, which is the template; the same argument
also appears in Step 1 of the main proof of `Submission/Work/SSGRoute/levelSub_commutator_and_generator.lean`).

* Forward: for `δ ∈ decomp k A` one has `δ • A = A`, hence
  `restrictNormalHom M δ • (A.comap (algebraMap ↥M Ω)) = A.comap (algebraMap ↥M Ω)` by
  `Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul`; use
  `NK.Reconstruct.primeOfLevel_spec` (`A.comap (algebraMap ↥M Ω) = valuationSubringAtPrime ↥M P`)
  together with the two inclusions between the stabiliser of `valuationSubringAtPrime ↥M P` and
  the stabiliser of `P.asIdeal`
  (`Submission.NeukirchUchida.Local.mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup`,
  `Submission.NeukirchUchida.Local.placeSmul_asIdeal`, or replay the short private lemmas
  `stabilizer_asIdeal_le_stabilizer_valuationSubringAtPrime`,
  `stabilizer_valuationSubringAtPrime_le_stabilizer_asIdeal` from `decomp_mod_inertia_cyclic.lean`).
* Backward: for `τ` in the stabiliser of `P.asIdeal`, apply
  `Commons.FieldTheory.Galois.exists_mem_stabilizer_restrictNormalHom_eq` to lift `τ` to
  `δ ∈ decomp k A` with `restrictNormalHom M δ = τ`. -/
theorem map_restrictNormalHom_decomp_eq (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) (M : IntermediateField k Ω) [FiniteDimensional k M]
    [Normal k M] [NumberField ↥M] :
    (SSGRoute.decomp k A).map (AlgEquiv.restrictNormalHom M) =
      Work.SSGRoute.levelDecompAt k Ω A hA M := by
  haveI hMgal : IsGalois k ↥M :=
    Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  rw [map_restrictNormalHom_decomp_eq_stabilizer (B := A) hA M]
  rw [show Work.SSGRoute.levelDecompAt k Ω A hA M =
      MulAction.stabilizer (↥M ≃ₐ[k] ↥M) (levelPrime k Ω A hA M).asIdeal from rfl]
  have hspecA : A.comap (algebraMap ↥M Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M (levelPrime k Ω A hA M) :=
    NK.Reconstruct.primeOfLevel_spec A M (NK.Reconstruct.comap_level_ne_top hA M)
  rw [hspecA]
  exact le_antisymm
    (stabilizer_valuationSubringAtPrime_le_stabilizer_asIdeal (K := k) (L := ↥M)
      (levelPrime k Ω A hA M))
    (stabilizer_asIdeal_le_stabilizer_valuationSubringAtPrime (K := k) (L := ↥M)
      (levelPrime k Ω A hA M))

end Work.SSGRoute
