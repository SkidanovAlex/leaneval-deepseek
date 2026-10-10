import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.SSGRoute.GrunwaldEscapeCore.isGalois_adjoin_kummerRoot
import Submission.Work.SSGRoute.ZDataMup.ideleArtin_ideleOfPrime_of_unramified
import Submission.Work.SSGRoute.myv2.NormCorr
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.myv2

open IntermediateField Polynomial

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem kummerSubfield_data_correction
    (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (E : IntermediateField ↥K Ω) [FiniteDimensional ↥K E] [IsGalois ↥K E]
    (𝔭 : NK.Chebotarev.PrimeIdeal ↥K)
    (c : (↥K)ˣ) (hcE : NK.LocalAnabelian.kummerField (K' := Ω) p c ≤ E) :
    ∃ (F : IntermediateField ↥K ↥E) (_ : FiniteDimensional ↥K F) (_ : Normal ↥K F)
      (_ : NumberField ↥F) (_ : IsMulCommutative (↥F ≃ₐ[↥K] ↥F)) (γ : (↥E)ˣ),
      γ ^ p = Units.map (algebraMap ↥K ↥E) c ∧ (γ : ↥E) ∈ F ∧
      NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭)
        (Units.mk0 (ζ ^ (p * (p - 1) / 2))
          (pow_ne_zero _ (hζ.ne_zero (Fact.out : p.Prime).ne_zero)) * c) ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥F)
          (NK.GlobalCFT.Place.ofFinite 𝔭) := by
  classical
  have hp' : p.Prime := Fact.out
  have hpne : p ≠ 0 := hp'.ne_zero
  have hζne : ζ ≠ 0 := hζ.ne_zero hpne
  haveI hKn : NumberField ↥K := inferInstance
  -- a `p`-th root of `c` in `Ω` (it lies in `E` by hypothesis)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap ↥K Ω (c : ↥K)) (n := p) hp'.pos
  have hαmem : α ∈ NK.LocalAnabelian.kummerField (K' := Ω) p c :=
    NK.LocalAnabelian.mem_kummerField_of_pow_eq hα
  have hαE : α ∈ E := hcE hαmem
  let αE : ↥E := ⟨α, hαE⟩
  have hαEpow : αE ^ p = algebraMap ↥K ↥E (c : ↥K) := by
    apply (IntermediateField.val E).injective
    simp only [map_pow]
    exact hα
  have hαE0 : αE ≠ 0 := by
    intro h
    rw [h, zero_pow hpne] at hαEpow
    exact ((algebraMap ↥K ↥E).injective.ne (Units.ne_zero c)) hαEpow.symm
  let γ : (↥E)ˣ := Units.mk0 αE hαE0
  have hγpow : γ ^ p = Units.map (algebraMap ↥K ↥E) c := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.coe_map]
    show αE ^ p = algebraMap ↥K ↥E (c : ↥K)
    exact hαEpow
  by_cases hc : c ∈ NK.LocalAnabelian.powSubgroup p ↥K
  · -- `c` is a `p`-th power in `↥K`: take `F = ⊥`
    obtain ⟨d, hd⟩ : ∃ d : (↥K)ˣ, d ^ p = c := by
      rw [NK.LocalAnabelian.powSubgroup, MonoidHom.mem_range] at hc
      obtain ⟨d, hd⟩ := hc
      exact ⟨d, by rwa [powMonoidHom_apply] at hd⟩
    haveI hFfd : FiniteDimensional ↥K (⊥ : IntermediateField ↥K ↥E) :=
      FiniteDimensional.of_finrank_pos (by rw [IntermediateField.finrank_bot]; norm_num)
    haveI hFgal : IsGalois ↥K (⊥ : IntermediateField ↥K ↥E) := inferInstance
    haveI hFn : Normal ↥K (⊥ : IntermediateField ↥K ↥E) := IsGalois.to_normal
    haveI hFnf : NumberField ↥(⊥ : IntermediateField ↥K ↥E) := inferInstance
    refine ⟨⊥, hFfd, hFn, hFnf, ?_, Units.map (algebraMap ↥K ↥E) d, ?_, ?_, ?_⟩
    · exact inferInstance
    · rw [← map_pow, hd]
    · rw [IntermediateField.mem_bot]
      exact ⟨(d : ↥K), by simp⟩
    · -- the corrected element is a norm from the trivial extension
      have hznz : ζ ^ (p * (p - 1) / 2) ≠ 0 := pow_ne_zero _ hζne
      have hy0 : ζ ^ (p * (p - 1) / 2) * (c : ↥K) ≠ 0 := mul_ne_zero hznz (Units.ne_zero c)
      have hfree : Module.Free ↥K (↥(⊥ : IntermediateField ↥K ↥E)) :=
        Module.Free.of_divisionRing (K := ↥K) (V := ↥(⊥ : IntermediateField ↥K ↥E))
      have hnorm : (Algebra.norm ↥K)
          (algebraMap ↥K (↥(⊥ : IntermediateField ↥K ↥E))
            (ζ ^ (p * (p - 1) / 2) * (c : ↥K))) =
          ζ ^ (p * (p - 1) / 2) * (c : ↥K) := by
        rw [Algebra.norm_algebraMap, IntermediateField.finrank_bot, pow_one]
      let u : (↥(⊥ : IntermediateField ↥K ↥E))ˣ :=
        Units.mk0 (algebraMap ↥K (↥(⊥ : IntermediateField ↥K ↥E))
            (ζ ^ (p * (p - 1) / 2) * (c : ↥K)))
          ((algebraMap ↥K (↥(⊥ : IntermediateField ↥K ↥E))).injective.ne hy0)
      have hη : Units.map (Algebra.norm ↥K) u =
          Units.mk0 (ζ ^ (p * (p - 1) / 2))
            (pow_ne_zero _ (hζ.ne_zero (Fact.out : p.Prime).ne_zero)) * c := by
        apply Units.ext
        rw [Units.coe_map]
        show (Algebra.norm ↥K)
          (algebraMap ↥K (↥(⊥ : IntermediateField ↥K ↥E))
            (ζ ^ (p * (p - 1) / 2) * (c : ↥K))) =
          ↑(Units.mk0 (ζ ^ (p * (p - 1) / 2))
            (pow_ne_zero _ (hζ.ne_zero (Fact.out : p.Prime).ne_zero)) * c)
        rw [hnorm]
        simp
      rw [← hη]
      exact Work.SSGRoute.GrunwaldEscapeCore.mem_localNormSubgroup_algebra_norm
        (K := ↥K) (L := ↥(⊥ : IntermediateField ↥K ↥E)) 𝔭 u
  · -- `c` is not a `p`-th power in `↥K`: take `F = ↥K⟮αE⟯`
    let F : IntermediateField ↥K ↥E := IntermediateField.adjoin ↥K ({αE} : Set ↥E)
    have hgal4 :=
      Work.SSGRoute.GrunwaldEscapeCore.isGalois_adjoin_kummerRoot p ζ hζ c γ hγpow hc
    have hgal : IsGalois ↥K F := hgal4.1
    have hdeg : Module.finrank ↥K F = p := hgal4.2
    haveI hFfd : FiniteDimensional ↥K F :=
      FiniteDimensional.of_finrank_pos (by rw [hdeg]; exact hp'.pos)
    haveI hFgal : IsGalois ↥K F := hgal
    haveI hFn : Normal ↥K F := IsGalois.to_normal
    haveI hFnf : NumberField ↥F := inferInstance
    haveI hFcomm : IsMulCommutative (↥F ≃ₐ[↥K] ↥F) := by
      have hcard : Nat.card (↥F ≃ₐ[↥K] ↥F) = p := by
        have h2 := IsGalois.card_aut_eq_finrank ↥K ↥F
        rwa [hdeg] at h2
      haveI : IsCyclic (↥F ≃ₐ[↥K] ↥F) := isCyclic_of_prime_card hcard
      exact IsCyclic.isMulCommutative
    let aF : ↥F := ⟨αE, IntermediateField.mem_adjoin_simple_self ↥K αE⟩
    have hαF : aF ^ p = algebraMap ↥K ↥F (c : ↥K) := by
      apply (IntermediateField.val F).injective
      simp only [map_pow]
      show αE ^ p = algebraMap ↥K ↥E (c : ↥K)
      exact hαEpow
    have hint : IsIntegral ↥K aF :=
      IsIntegral.of_pow hp'.pos (by rw [hαF]; exact isIntegral_algebraMap)
    have hirk : Irreducible (Polynomial.X ^ p - Polynomial.C (c : ↥K)) :=
      X_pow_sub_C_irreducible_of_prime hp' (fun b hb => hc (by
        rw [NK.LocalAnabelian.powSubgroup, MonoidHom.mem_range]
        refine ⟨Units.mk0 b ?_, ?_⟩
        · rintro rfl
          rw [zero_pow hpne] at hb
          exact Units.ne_zero c hb.symm
        · rw [powMonoidHom_apply]; apply Units.ext
          rw [Units.val_pow_eq_pow_val]
          exact hb))
    have hroot : aeval aF (Polynomial.X ^ p - Polynomial.C (c : ↥K)) = 0 := by
      rw [aeval_def, eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, sub_eq_zero]
      exact hαF
    have hmin : minpoly ↥K aF = Polynomial.X ^ p - Polynomial.C (c : ↥K) :=
      (minpoly.eq_of_irreducible_of_monic hirk hroot (monic_X_pow_sub_C _ hpne)).symm
    have hfr1 : Module.finrank ↥K ↥(IntermediateField.adjoin ↥K ({aF} : Set ↥F)) = p := by
      rw [IntermediateField.adjoin.finrank hint, hmin, natDegree_X_pow_sub_C]
    have htop : Module.finrank ↥K ↥(⊤ : IntermediateField ↥K ↥F) = p := by
      rw [(IntermediateField.topEquiv (F := ↥K) (E := ↥F)).toLinearEquiv.finrank_eq, hdeg]
    have hgen : IntermediateField.adjoin ↥K ({aF} : Set ↥F) = ⊤ := by
      haveI : FiniteDimensional ↥K ↥(⊤ : IntermediateField ↥K ↥F) :=
        FiniteDimensional.of_finrank_pos (by rw [htop]; exact hp'.pos)
      refine IntermediateField.eq_of_le_of_finrank_eq le_top ?_
      rw [hfr1, htop]
    refine ⟨F, hFfd, hFn, hFnf, hFcomm, γ, hγpow, ?_, ?_⟩
    · show αE ∈ F
      exact IntermediateField.mem_adjoin_simple_self ↥K αE
    · exact Work.SSGRoute.N2v2.mem_localNormSubgroup_of_kummerRoot_correction
        p ζ hζ c aF hαF hgen hdeg 𝔭

end Work.SSGRoute.myv2
