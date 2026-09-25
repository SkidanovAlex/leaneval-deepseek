import Mathlib
import Submission.NK.NUV2.LC.RouteB.level_kills_aux
import Submission.NK.HassePrinciple.map_levelRestrict_stabSubgroup
import Submission.NK.GlobalCFT.Place
import Submission.NK.HassePrinciple.IndexInput
import Submission.NK.NUV2.LC.RouteB.stabilizerOfFiniteEqValuationSubring
import Submission.Commons.RingTheory.Valuation.exists_mem_stabilizer_restrictNormalHom_eq_of_isGalois
import Submission.Commons.RingTheory.Valuation.mem_stabilizer_valuationSubring_iff
import Submission.Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top
import Submission.Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top
import Submission.NK.HassePrinciple.UnitsLevel

/-!
# The stabiliser of a finite place of a level lies in the image of the local level group

Let `V ≤ Gal(K'/K)` be a subgroup containing `Gal(K'/L)` for a finite Galois intermediate field
`L`, and let `q` be a finite place of `L`, cut out on `L` by a place `A` of `K'`
(`A.1.comap (algebraMap ↥L K') = 𝒪_{L,q}`, the hypothesis `hA`).  Then

`levelGroupEquiv V L : LevelGroup V L ≃* Gal(L/(L ⊓ K'^V))`

identifies the level group with the Galois group of the level extension, and the *arithmetic*
statement proved here is that the stabiliser of the place `q` in `Gal(L/(L ⊓ K'^V))` is contained
in the image of the local level group `(V ⊓ D_A)/...` under `localInclHom`.

Equivalently: every automorphism of `L` over `L ⊓ K'^V` fixing the place `q` is the restriction of
an element of `V` in the decomposition group `D_A` of the place `A` of `K'`.

The proof is the classical "decomposition groups surject onto the decomposition group of the
restriction": since `γ` fixes the place `q`, it stabilises the valuation ring `𝒪_{L,q} = A ∩ L`
(`stabilizerOfFiniteEqValuationSubring`, applied over the base field `L ⊓ K'^V`), hence its scalar
restriction to `K` stabilises `A ∩ L`; by the surjectivity of the restriction map on decomposition
groups (`Commons.RingTheory.Valuation.exists_mem_stabilizer_restrictNormalHom_eq_of_isGalois`) some
`σ ∈ D_A` restricts to it, and `σ` is corrected into `V` by an element of `Gal(K'/L) ≤ V`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace NK.NUV2.LC.RouteB

open scoped Pointwise

theorem levelGroupEquiv_symm_mem_range_localInclHom {K K' : Type} [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsSepClosure K K']
    (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')
    (hF : L.fixingSubgroup ≤ V)
    (A : NK.BrauerTwist.OverFinitePrime K K')
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (hA : A.1.comap (algebraMap ↥L K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L q)
    (γ : MulAction.stabilizer (↥L ≃ₐ[↥(levelBase (K := K) V L)] ↥L)
        (NK.GlobalCFT.Place.ofFinite q)) :
    ∃ δ : NK.BrauerHasse.LocalLevelGroup V A.1 L,
      NK.BrauerHasse.localInclHom V A.1 L δ =
        (levelGroupEquiv (K := K) (K' := K') V L).symm
          (γ : ↥L ≃ₐ[↥(levelBase (K := K) V L)] ↥L) := by
  obtain ⟨σ, hσmem⟩ := γ
  -- `γ` fixes the valuation ring `𝒪_{L,q}`, over the base field `L ⊓ K'^V`.
  have hσV : σ ∈ MulAction.stabilizer (↥L ≃ₐ[↥(levelBase (K := K) V L)] ↥L)
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L q) := by
    have h := hσmem
    rw [stabilizerOfFiniteEqValuationSubring (K := ↥(levelBase (K := K) V L)) (L := ↥L) q] at h
    exact h
  -- Its scalar restriction to `K` fixes `A ∩ L`.
  have hσK : AlgEquiv.restrictScalars K σ ∈ MulAction.stabilizer (↥L ≃ₐ[K] ↥L)
      (A.1.comap (algebraMap ↥L K')) := by
    rw [hA]
    rw [Commons.RingTheory.Valuation.mem_stabilizer_valuationSubring_iff]
    intro x
    rw [Commons.RingTheory.Valuation.mem_stabilizer_valuationSubring_iff] at hσV
    exact hσV x
  -- `A` is a genuine place of `K'` over a finite prime of `K`.
  have hC : A.1.comap (algebraMap K K') ≠ ⊤ := by
    intro htop
    have hAtop : A.1 = ⊤ :=
      Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top A.1
        (F := K) (K' := K') inferInstance htop
    have h2 : A.1.comap (algebraMap ↥L K') = ⊤ := by
      rw [hAtop]
      ext x
      simp [ValuationSubring.mem_comap]
    rw [hA] at h2
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top q h2
  -- Surjectivity of the restriction map on decomposition groups: lift to `σ' ∈ D_A`.
  obtain ⟨σ', hσ'stab, hσ'res⟩ :=
    Commons.RingTheory.Valuation.exists_mem_stabilizer_restrictNormalHom_eq_of_isGalois
      (F := K) (E := K') A.1 hC (L : IntermediateField K K')
      (AlgEquiv.restrictScalars K σ) hσK
  -- `σ` fixes the base field `levelBase = L ⊓ K'^V`, so it is the restriction of some `v ∈ V`.
  have hσfix : AlgEquiv.restrictScalars K σ ∈ (levelBase (K := K) V L).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    exact σ.commutes ⟨y, hy⟩
  have hrange : (levelBase (K := K) V L).fixingSubgroup =
      (NK.HassePrinciple.levelRestrictHom V L).range := by
    rw [NK.HassePrinciple.levelRestrictHom_range]
    exact IntermediateField.fixingSubgroup_fixedField
      (H := V.map (NK.HassePrinciple.levelRestrict L))
  obtain ⟨v, hv⟩ := hrange ▸ hσfix
  -- Correct `σ'` into `V` by `v`: both restrict to `γ` on `L`.
  have hσ'V : σ' ∈ V := by
    have hmem : σ' * (v : Gal(K'/K))⁻¹ ∈ L.fixingSubgroup := by
      rw [FiniteGaloisIntermediateField.mem_fixingSubgroup_iff]
      rw [map_mul, map_inv, hσ'res]
      have hv' : (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') (L : IntermediateField K K'))
          (v : Gal(K'/K)) = AlgEquiv.restrictScalars K σ := hv
      rw [hv', mul_inv_cancel]
    have hsplit : σ' = (σ' * (v : Gal(K'/K))⁻¹) * (v : Gal(K'/K)) := by group
    rw [hsplit]
    exact V.mul_mem (hF hmem) v.2
  -- The class of `σ'` in the local level group is the required preimage.
  have hcomp : NK.HassePrinciple.levelGroupRestrictHom V L
      (NK.BrauerHasse.localInclHom V A.1 L
        (QuotientGroup.mk (⟨σ', ⟨hσ'V, hσ'stab⟩⟩ : ↥(V ⊓ NK.BrauerHasse.stabSubgroup A.1)))) =
      AlgEquiv.restrictScalars K σ := by
    rw [NK.BrauerHasse.localInclHom, QuotientGroup.map_mk]
    rw [NK.HassePrinciple.levelGroupRestrictHom_mk]
    exact hσ'res
  have hgoal : levelGroupEquiv (K := K) (K' := K') V L
      (NK.BrauerHasse.localInclHom V A.1 L
        (QuotientGroup.mk (⟨σ', ⟨hσ'V, hσ'stab⟩⟩ : ↥(V ⊓ NK.BrauerHasse.stabSubgroup A.1)))) = σ := by
    apply AlgEquiv.ext
    intro x
    rw [levelGroupEquiv_apply]
    rw [hcomp]
    rfl
  refine ⟨QuotientGroup.mk (⟨σ', ⟨hσ'V, hσ'stab⟩⟩ : ↥(V ⊓ NK.BrauerHasse.stabSubgroup A.1)), ?_⟩
  show NK.BrauerHasse.localInclHom V A.1 L
      (QuotientGroup.mk (⟨σ', ⟨hσ'V, hσ'stab⟩⟩ : ↥(V ⊓ NK.BrauerHasse.stabSubgroup A.1))) =
    (levelGroupEquiv (K := K) (K' := K') V L).symm σ
  rw [← hgoal, MulEquiv.symm_apply_apply]

end NK.NUV2.LC.RouteB
