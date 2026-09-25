import Mathlib
import Submission.NK.NUV2.LC.RouteB.Defs
import Submission.NK.NUV2.LC.RouteB.localLevelGroup_top_unramified
import Submission.NK.NUV2.LC.RouteB.h2_map_eq_zero_of_surj_cyclic_dvd_ker
import Submission.NK.NUV2.LC.RouteB.exists_cyclotomic_level_dvd_inertiaDeg
import Submission.NK.NUV2.LC.RouteB.hasseSurjOfTopAux
import Submission.NK.HeckeL.Basic.finite_setOf_not_isUnramifiedIn

/-! # Finite support at an open `μ_p`-level (Route B, node S2)

A class of `H²(U, Z/p)` (`U` open in `Gal(K'/K)`, fixing a primitive `p`-th root of unity) has
non-zero localisation only at the places over finitely many primes of `K`.

## Route

* `finite_support_top` — the **`⊤`-case over an arbitrary number field** `F`: a class of
  `H²(Gal(K'/F), Z/p)` is ramified at only finitely many primes.  The proof is the elementary
  cycle argument: represent the class at a finite level `L` (`x = ofLevel L a`); at a prime `𝔭`
  *unramified* in `L/K` the local level group is the decomposition group `D_𝔮`, cyclic of order
  `f(𝔮|𝔭)`; enlarging the level cyclotomically to `L' = L(ζ_m)` (`m = N𝔮^p - 1`) multiplies the
  local group order by a multiple of `p`, and the inflation `H²(Z/f, Z/p) → H²(Z/fp, Z/p)` along
  a surjection of cyclic groups whose kernel has order divisible by `p` is zero
  (`h2_map_eq_zero_of_surj_cyclic_dvd_ker`).  Hence every prime unramified in `L` is unramified
  for the class, and the ramified primes form a finite set
  (`NK.HeckeL.Basic.finite_setOf_not_isUnramifiedIn`).
* the reduction of the general open `U` to the `⊤`-case over the fixed field `K'^U`, using the
  proved local transport `NK.NUV2.LC.RouteB.HTO.LocPhi` (`hasseSurjOfTopAux`): the localisation
  commutes with the transport and the transport is injective.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NK.NUV2.LC.RouteB

open IsDedekindDomain

variable {F K' : Type} [Field F] [NumberField F] [Field K'] [Algebra F K'] [IsSepClosure F K']

/-- **The localisation of a level class vanishes at every prime unramified in the level.** -/
theorem loc_ofLevel_eq_zero_of_isUnramified (p : ℕ) (hp : p.Prime)
    (L : FiniteGaloisIntermediateField F K')
    (a : NK.BrauerHasse.LevelH2 (K := F) (K' := K') p (⊤ : Subgroup Gal(K'/F)) L)
    (A : NK.BrauerHasse.OverFinitePrime F K')
    (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (hA : A.1.comap (algebraMap F K') =
      HeightOneSpectrum.valuationSubringAtPrime F 𝔭)
    (hunr : NK.HeckeL.IsUnramifiedIn (K := F) (L := ↥(L : IntermediateField F K')) 𝔭) :
    NK.BrauerHasse.H2Profinite.loc p (⊤ : Subgroup Gal(K'/F))
      (NK.BrauerHasse.H2Profinite.ofLevel L a) A = 0 := by
  obtain ⟨L', hLL', hunr', 𝔮, 𝔴, h𝔮, h𝔴, hdiv⟩ :=
    exists_cyclotomic_level_dvd_inertiaDeg p hp L A 𝔭 hA hunr
  -- the transition map on the local level groups
  set φ : NK.BrauerHasse.LocalLevelGroup (⊤ : Subgroup Gal(K'/F)) A.1 L' →*
      NK.BrauerHasse.LocalLevelGroup (⊤ : Subgroup Gal(K'/F)) A.1 L :=
    NK.BrauerHasse.localLevelQuotHom (⊤ : Subgroup Gal(K'/F)) A.1 hLL' with hφdef
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
    exact ⟨QuotientGroup.mk' _ x, by simp [hφdef, NK.BrauerHasse.localLevelQuotHom]⟩
  haveI hfL' : Fintype (NK.BrauerHasse.LocalLevelGroup (⊤ : Subgroup Gal(K'/F)) A.1 L') :=
    Fintype.ofFinite _
  haveI hfL : Fintype (NK.BrauerHasse.LocalLevelGroup (⊤ : Subgroup Gal(K'/F)) A.1 L) :=
    Fintype.ofFinite _
  have hcyc := (localLevelGroup_top_unramified L' A 𝔭 𝔴 hA h𝔴 hunr').1
  have hcardL := (localLevelGroup_top_unramified L A 𝔭 𝔮 hA h𝔮 hunr).2
  have hcardL' := (localLevelGroup_top_unramified L' A 𝔭 𝔴 hA h𝔴 hunr').2
  -- the cardinality of the kernel
  have hker : Nat.card (MonoidHom.ker φ) *
      Nat.card (NK.BrauerHasse.LocalLevelGroup (⊤ : Subgroup Gal(K'/F)) A.1 L) =
      Nat.card (NK.BrauerHasse.LocalLevelGroup (⊤ : Subgroup Gal(K'/F)) A.1 L') :=
    calc Nat.card (MonoidHom.ker φ) *
          Nat.card (NK.BrauerHasse.LocalLevelGroup (⊤ : Subgroup Gal(K'/F)) A.1 L)
        = Nat.card (MonoidHom.ker φ) * Nat.card ↥(MonoidHom.range φ) := by
          rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
      _ = Nat.card (MonoidHom.ker φ) * (MonoidHom.ker φ).index := by
          rw [Subgroup.index_ker]
      _ = Nat.card (NK.BrauerHasse.LocalLevelGroup (⊤ : Subgroup Gal(K'/F)) A.1 L') :=
          Subgroup.card_mul_index _
  have hpos : 0 < 𝔮.asIdeal.inertiaDeg (NumberField.RingOfIntegers F) :=
    Ideal.inertiaDeg_pos _ _
  have hmul : Nat.card (MonoidHom.ker φ) * 𝔮.asIdeal.inertiaDeg (NumberField.RingOfIntegers F) =
      𝔴.asIdeal.inertiaDeg (NumberField.RingOfIntegers F) := by
    rw [← hcardL, hker, hcardL']
  have hkerdvd : p ∣ Nat.card (MonoidHom.ker φ) := by
    refine Nat.dvd_of_mul_dvd_mul_right hpos ?_
    rw [hmul]
    exact hdiv
  haveI : Fact p.Prime := ⟨hp⟩
  have hkill := h2_map_eq_zero_of_surj_cyclic_dvd_ker p hcyc φ hsurj hkerdvd
    ((NK.BrauerHasse.locLevel p (⊤ : Subgroup Gal(K'/F)) A.1 L) a)
  -- conclude
  rw [NK.BrauerHasse.H2Profinite.loc_ofLevel_apply]
  rw [← NK.BrauerHasse.LocalH2.ofLevel_levelMap p (⊤ : Subgroup Gal(K'/F)) A.1 hLL'
    ((NK.BrauerHasse.locLevel p (⊤ : Subgroup Gal(K'/F)) A.1 L) a)]
  have hkill' : (NK.BrauerHasse.localLevelMap p (⊤ : Subgroup Gal(K'/F)) A.1 hLL')
      ((NK.BrauerHasse.locLevel p (⊤ : Subgroup Gal(K'/F)) A.1 L) a) = 0 := hkill
  rw [hkill']
  exact NK.BrauerHasse.local_ofLevel_zero p A.1 L'

/-- **The ⊤-case: finite support over an arbitrary number field `F`.** -/
theorem finite_support_top (p : ℕ) (hp : p.Prime)
    (x : NK.BrauerHasse.H2Profinite (K := F) (K' := K') p (⊤ : Subgroup Gal(K'/F))) :
    {𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers F) |
      ∃ A : NK.BrauerHasse.OverFinitePrime F K',
        A.1.comap (algebraMap F K') = HeightOneSpectrum.valuationSubringAtPrime F 𝔮 ∧
        NK.BrauerHasse.H2Profinite.loc p (⊤ : Subgroup Gal(K'/F)) x A ≠ 0}.Finite := by
  obtain ⟨L, a, rfl⟩ := NK.BrauerHasse.H2Profinite.ofLevel_surjective x
  refine Set.Finite.subset
    (NK.HeckeL.Basic.finite_setOf_not_isUnramifiedIn (K := F)
      (L := ↥(L : IntermediateField F K'))) ?_
  intro 𝔭 h𝔭
  rintro hunr
  obtain ⟨A, hA, hne⟩ := h𝔭
  exact hne (loc_ofLevel_eq_zero_of_isUnramified p hp L a A 𝔭 hA hunr)


section Reduction

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- The local transport sends the zero class to the zero class. -/
lemma LocPhi_zero (U : Subgroup Gal(K'/K)) (hUcl : IsClosed (U : Set Gal(K'/K)))
    (hUopen : IsOpen (U : Set Gal(K'/K))) [hsc : IsSepClosure ↥(NK.NUV2.LC.RouteB.fixedFieldOf U) K']
    (p : ℕ) (A : ValuationSubring K') :
    NK.NUV2.LC.RouteB.HTO.LocPhi U hUcl hUopen p A
      (0 : NK.BrauerHasse.LocalH2 (K := K) (K' := K') p U A) = 0 := by
  have h : (0 : NK.BrauerHasse.LocalH2 (K := K) (K' := K') p U A) =
      NK.BrauerHasse.H2Profinite.ofLevel (⊥ : FiniteGaloisIntermediateField K K')
        (0 : NK.BrauerHasse.LocalLevelH2 (K := K) (K' := K') p U A ⊥) := rfl
  rw [h, NK.NUV2.LC.RouteB.HTO.LocPhi_ofLevel']
  show NK.BrauerHasse.LocalH2.ofLevel (K := ↥(NK.NUV2.LC.RouteB.fixedFieldOf U))
      (K' := K') (p := p) (⊤ : Subgroup Gal(K'/↥(NK.NUV2.LC.RouteB.fixedFieldOf U))) A
      (NK.NUV2.LC.RouteB.HTO.flev U hUcl hUopen (⊥ : FiniteGaloisIntermediateField K K'))
      ((NK.BrauerHasse.H2.map (p := p)
        (NK.NUV2.LC.RouteB.HTO.localIso U hUcl hUopen A (⊥ : FiniteGaloisIntermediateField K K')).symm.toMonoidHom).hom
          (0 : NK.BrauerHasse.LocalLevelH2 (K := K) (K' := K') p U A ⊥)) = 0
  rw [map_zero]
  exact NK.BrauerHasse.local_ofLevel_zero p A _

/-- **Reduction of the target to the `⊤`-case over the fixed field.** -/
theorem finite_support_isMuOpen (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) {K K' : Type} [Field K]
    [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K'] (ζ : K')
    (hζ : IsPrimitiveRoot ζ p) (U : Subgroup Gal(K'/K))
    (hU : NK.NUV2.LC.RouteB.IsMuOpen (K := K) (K' := K') ζ U)
    (x : NK.BrauerHasse.H2Profinite (K := K) (K' := K') p U) :
    {𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K) |
      ∃ A : NK.BrauerHasse.OverFinitePrime K K',
        A.1.comap (algebraMap K K') = HeightOneSpectrum.valuationSubringAtPrime K 𝔭 ∧
        NK.BrauerHasse.H2Profinite.loc p U x A ≠ 0}.Finite := by
  have hUopen : IsOpen (U : Set Gal(K'/K)) := hU.1
  have hUcl : IsClosed (U : Set Gal(K'/K)) := Subgroup.isClosed_of_isOpen U hUopen
  haveI hfd : FiniteDimensional K ↥(NK.NUV2.LC.RouteB.fixedFieldOf U) :=
    NK.NUV2.LC.RouteB.finiteDimensional_fixedField U hUopen
  haveI hnf : NumberField ↥(NK.NUV2.LC.RouteB.fixedFieldOf U) := inferInstance
  haveI hsc : IsSepClosure ↥(NK.NUV2.LC.RouteB.fixedFieldOf U) K' :=
    NK.NUV2.LC.RouteB.isSepClosure_fixedField U
  set y : NK.BrauerHasse.H2Profinite (K := ↥(NK.NUV2.LC.RouteB.fixedFieldOf U)) (K' := K')
      p (⊤ : Subgroup Gal(K'/↥(NK.NUV2.LC.RouteB.fixedFieldOf U))) :=
    NK.NUV2.LC.HT.Phi p (NK.NUV2.LC.RouteB.HTO.tdata U hUcl hUopen) x with hy
  have hfin : ({𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers
        ↥(NK.NUV2.LC.RouteB.fixedFieldOf U)) |
      ∃ A : NK.BrauerHasse.OverFinitePrime ↥(NK.NUV2.LC.RouteB.fixedFieldOf U) K',
        A.1.comap (algebraMap ↥(NK.NUV2.LC.RouteB.fixedFieldOf U) K') =
            HeightOneSpectrum.valuationSubringAtPrime ↥(NK.NUV2.LC.RouteB.fixedFieldOf U) 𝔮 ∧
        NK.BrauerHasse.H2Profinite.loc p
          (⊤ : Subgroup Gal(K'/↥(NK.NUV2.LC.RouteB.fixedFieldOf U))) y A ≠ 0} : Set _).Finite :=
    finite_support_top p hp y
  refine Set.Finite.subset
    (hfin.image (fun 𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers
        ↥(NK.NUV2.LC.RouteB.fixedFieldOf U)) =>
      (⟨Ideal.under (NumberField.RingOfIntegers K) 𝔮.asIdeal,
        Ideal.IsPrime.under _ 𝔮.asIdeal, Ideal.under_ne_bot _ 𝔮.ne_bot⟩ :
          HeightOneSpectrum (NumberField.RingOfIntegers K)))) ?_
  intro 𝔭 h𝔭
  obtain ⟨A, hA, hloc⟩ := h𝔭
  set 𝔮F : HeightOneSpectrum (NumberField.RingOfIntegers
      ↥(NK.NUV2.LC.RouteB.fixedFieldOf U)) :=
    Submission.NeukirchUchida.Local.placeOf 𝔭 A.1 hA (NK.NUV2.LC.RouteB.fixedFieldOf U)
      with h𝔮F
  have h𝔮F' : A.1.comap (algebraMap ↥(NK.NUV2.LC.RouteB.fixedFieldOf U) K') =
      HeightOneSpectrum.valuationSubringAtPrime ↥(NK.NUV2.LC.RouteB.fixedFieldOf U) 𝔮F :=
    Submission.NeukirchUchida.Local.comap_eq_valuationSubringAtPrime_placeOf _ _ _ _
  refine ⟨𝔮F, ?_, ?_⟩
  · refine ⟨⟨A.1, NK.NUV2.LC.RouteB.comap_fixedField_ne_top U A.1 A.2⟩, h𝔮F', ?_⟩
    intro h0
    have h0' : NK.NUV2.LC.RouteB.HTO.LocPhi U hUcl hUopen p A.1
        (NK.BrauerHasse.H2Profinite.loc p U x A) = 0 := by
      rw [show NK.BrauerHasse.H2Profinite.loc p U x A =
          NK.BrauerHasse.H2Profinite.loc p U x
            (⟨A.1, A.2⟩ : NK.BrauerHasse.OverFinitePrime K K') from rfl,
        NK.NUV2.LC.RouteB.HTO.LocPhi_loc U hUcl hUopen p A.1 A.2 x]
      exact h0
    exact hloc (NK.NUV2.LC.RouteB.HTO.LocPhi_injective U hUcl hUopen p A.1 (by
      rw [h0', LocPhi_zero U hUcl hUopen p A.1]))
  · -- the prime of `K` below `𝔮F` is `𝔭`
    show (⟨Ideal.under (NumberField.RingOfIntegers K) 𝔮F.asIdeal,
      Ideal.IsPrime.under _ 𝔮F.asIdeal, Ideal.under_ne_bot _ 𝔮F.ne_bot⟩ :
        HeightOneSpectrum (NumberField.RingOfIntegers K)) = 𝔭
    have h2 : (HeightOneSpectrum.valuationSubringAtPrime
        ↥(NK.NUV2.LC.RouteB.fixedFieldOf U) 𝔮F).comap
        (algebraMap K ↥(NK.NUV2.LC.RouteB.fixedFieldOf U)) =
        HeightOneSpectrum.valuationSubringAtPrime K 𝔭 := by
      rw [← h𝔮F']
      rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq K
        ↥(NK.NUV2.LC.RouteB.fixedFieldOf U) K']
      exact hA
    have h3 : (HeightOneSpectrum.valuationSubringAtPrime
        ↥(NK.NUV2.LC.RouteB.fixedFieldOf U) 𝔮F).comap
        (algebraMap K ↥(NK.NUV2.LC.RouteB.fixedFieldOf U)) =
        HeightOneSpectrum.valuationSubringAtPrime K
          (⟨Ideal.under (NumberField.RingOfIntegers K) 𝔮F.asIdeal,
            Ideal.IsPrime.under _ 𝔮F.asIdeal, Ideal.under_ne_bot _ 𝔮F.ne_bot⟩ :
              HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
      Commons.RingTheory.Valuation.comap_valuationSubringAtPrime
        (⟨Ideal.under (NumberField.RingOfIntegers K) 𝔮F.asIdeal,
          Ideal.IsPrime.under _ 𝔮F.asIdeal, Ideal.under_ne_bot _ 𝔮F.ne_bot⟩ :
            HeightOneSpectrum (NumberField.RingOfIntegers K)) 𝔮F (Ideal.LiesOver.mk rfl)
    exact (Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := K)
      (h2.symm.trans h3)).symm

end Reduction

end NK.NUV2.LC.RouteB
