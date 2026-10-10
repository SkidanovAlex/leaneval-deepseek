import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.CycLevel.stabilizer_ofFinite_eq_decompositionSubgroup
import Submission.Work.SSGRoute.inertiaSub_image_eq_levelInertia
import Submission.Work.SSGRoute.levelInertia_index_eq_inertiaDeg
import Submission.Work.SSGRoute.levelSub_comap_index_eq_inertiaDeg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A cyclic degree-`p` level which is unramified and inert at a prescribed place

Given a continuous additive character `χ : G_k → ZMod p` which vanishes on the inertia subgroup
`I_A` of a finite place `A` and is non-zero on the decomposition group `D_A`, we construct a finite
Galois level `M ⊆ Ω`, cyclic of degree `p` over `k`, in which every prime above the place `Q` of `k`
below `A` is unramified (`e = 1`) and inert (`f = p`).

The level is the fixed field of `ker χ`: `ker χ` is an open (hence closed) normal subgroup of
`G_k = Gal(Ω/k)`, so `Gal(M/k) ≅ G_k ⧸ ker χ ≅ ZMod p`.  The inertia of `M` at the prime below `A`
is the image of `I_A` (`Work.SSGRoute.inertiaSub_image_eq_levelInertia`), hence trivial because `χ`
vanishes on `I_A`; the decomposition group is the image of `D_A`
(`Work.SSGRoute.range_restrictNormalHom_eq_stabilizer`), hence all of `Gal(M/k)` because `χ` is
non-zero on `D_A`.  Therefore the fundamental identity
(`Work.SSGRoute.levelInertia_index_eq_inertiaDeg`) gives `f = p` and
`e = |I| = 1`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open scoped Pointwise NumberField

namespace Work.SSGRoute.Sha2Lib

open _root_.SSGRoute

theorem unramified_inert_level_of_character (p : ℕ) [Fact p.Prime]
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (A : ValuationSubring Ω)
    (hA : A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k Q)
    (χ : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hadd : ∀ a b : Ω ≃ₐ[k] Ω, χ (a * b) = χ a + χ b)
    (hcont : SSGRoute.IsLocConstOn ⊤ χ)
    (hinn : ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ Work.SSGRoute.inertiaSub k Ω A → χ σ = 0)
    (hne : ∃ σ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k A ∧ χ σ ≠ 0) :
    ∃ (M : IntermediateField k Ω) (_ : NumberField ↥M)
      (_ : FiniteDimensional k ↥M) (_ : IsGalois k ↥M),
      IsCyclic (↥M ≃ₐ[k] ↥M) ∧ Nat.card (↥M ≃ₐ[k] ↥M) = p ∧
      ∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥M),
        w.asIdeal.LiesOver Q.asIdeal →
          w.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 ∧
          w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) = p := by
  classical
  haveI hGalΩ : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  haveI hNormΩ : Normal k Ω := IsAlgClosure.normal k Ω
  have hAf : SSGRoute.IsFinPlace k A := by
    change A.comap (algebraMap k Ω) ≠ ⊤
    rw [hA]
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top Q
  -- ## 0. `χ` as a homomorphism
  have hχ1 : χ 1 = 0 := by
    have h := hadd 1 1
    rw [mul_one] at h
    have h2 : χ 1 + 0 = χ 1 + χ 1 := by rw [add_zero]; exact h
    exact (add_left_cancel h2).symm
  let χhom : (Ω ≃ₐ[k] Ω) →* Multiplicative (ZMod p) :=
    { toFun := fun σ => Multiplicative.ofAdd (χ σ)
      map_one' := by rw [hχ1]; rfl
      map_mul' := fun a b => by rw [hadd a b]; rfl }
  have hχhom_apply : ∀ σ, (χhom σ).toAdd = χ σ := fun σ => rfl
  -- ## 1. `ker χ` is open
  obtain ⟨U, hUopen, hU⟩ := hcont
  have hUker : U ≤ χhom.ker := by
    intro u hu
    rw [MonoidHom.mem_ker]
    have h := hU 1 trivial u hu trivial
    rw [one_mul, hχ1] at h
    exact h
  have hkeropen : IsOpen ((χhom.ker : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) :=
    Subgroup.isOpen_mono hUker hUopen
  have hkerclosed : IsClosed ((χhom.ker : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) :=
    Subgroup.isClosed_of_isOpen _ hkeropen
  -- ## 2. the level
  let H : ClosedSubgroup (Ω ≃ₐ[k] Ω) := ⟨χhom.ker, hkerclosed⟩
  let M : IntermediateField k Ω := IntermediateField.fixedField χhom.ker
  have hMfix : M.fixingSubgroup = χhom.ker := by
    show (IntermediateField.fixedField H.1).fixingSubgroup = H.1
    exact InfiniteGalois.fixingSubgroup_fixedField H
  haveI hMgal : IsGalois k ↥M :=
    IsGalois.of_fixedField_normal_subgroup (K := k) (L := Ω) χhom.ker
  have hMfd : FiniteDimensional k ↥M := by
    rw [← InfiniteGalois.isOpen_iff_finite M, hMfix]
    exact hkeropen
  haveI : FiniteDimensional k ↥M := hMfd
  haveI hMnf : NumberField ↥M :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField M
  -- ## 3. `Gal(M/k) ≅ ZMod p`
  have hχsurj : Function.Surjective χhom := by
    obtain ⟨δ, _hδD, hδχ⟩ := hne
    have hδ1 : χhom δ ≠ 1 := by
      intro h
      apply hδχ
      have := congrArg Multiplicative.toAdd h
      simpa [hχhom_apply] using this
    have hne_bot : Subgroup.zpowers (χhom δ) ≠ ⊥ := by
      intro h
      have : χhom δ ∈ (⊥ : Subgroup (Multiplicative (ZMod p))) := by
        rw [← h]; exact Subgroup.mem_zpowers _
      exact hδ1 (by simpa using this)
    have hcard : Nat.card (Multiplicative (ZMod p)) = p := by
      rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p),
        Nat.card_eq_fintype_card, ZMod.card]
    have htop : Subgroup.zpowers (χhom δ) = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      have hdvd : Nat.card (Subgroup.zpowers (χhom δ)) ∣ Nat.card (Multiplicative (ZMod p)) :=
        Subgroup.card_subgroup_dvd_card _
      rw [hcard] at hdvd
      have h1 : 1 < Nat.card (Subgroup.zpowers (χhom δ)) := by
        by_contra hcon
        push Not at hcon
        have hpos : 0 < Nat.card (Subgroup.zpowers (χhom δ)) := Nat.card_pos
        exact hne_bot (Subgroup.card_eq_one.mp (by omega))
      rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with h | h
      · omega
      · rw [h, hcard]
    intro y
    have hy : y ∈ Subgroup.zpowers (χhom δ) := by rw [htop]; exact Subgroup.mem_top y
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ⟨δ ^ n, by rw [map_zpow, hn]⟩
  let eGal : (↥M ≃ₐ[k] ↥M) ≃* Multiplicative (ZMod p) :=
    (InfiniteGalois.normalAutEquivQuotient H).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective χhom hχsurj)
  have hcardM : Nat.card (↥M ≃ₐ[k] ↥M) = p := by
    rw [Nat.card_congr eGal.toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p),
      Nat.card_eq_fintype_card, ZMod.card]
  have hcycM : IsCyclic (↥M ≃ₐ[k] ↥M) := by
    have hcyc : IsCyclic (Multiplicative (ZMod p)) := by
      refine isCyclic_iff_exists_zpowers_eq_top.mpr ⟨Multiplicative.ofAdd 1, ?_⟩
      rw [Subgroup.eq_top_iff']
      intro y
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨((y.toAdd).val : ℤ), ?_⟩
      apply Multiplicative.ext
      rw [toAdd_zpow, toAdd_ofAdd, zsmul_eq_mul, mul_one, Int.cast_natCast,
        ZMod.natCast_zmod_val]
    exact isCyclic_of_surjective (eGal.symm : Multiplicative (ZMod p) →* (↥M ≃ₐ[k] ↥M))
      eGal.symm.surjective
  -- ## 4. the level prime, its inertia and decomposition group
  let P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥M) :=
    Work.SSGRoute.levelPrime k Ω A hAf M
  have hPliesQ : P.asIdeal.LiesOver Q.asIdeal := by
    have h1 : P.asIdeal.LiesOver (Submission.NeukirchUchida.primeOf A hAf).asIdeal :=
      NK.ResidueFrob.primeOfLevel_liesOver (K := k) (K' := Ω) ⟨A, hAf⟩ M
    have h2 : Submission.NeukirchUchida.primeOf A hAf = Q :=
      Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
        (by rw [← Submission.NeukirchUchida.primeOf_spec A hAf, hA])
    rwa [h2] at h1
  haveI hPliesI : P.asIdeal.LiesOver Q.asIdeal := hPliesQ
  haveI hPprime : P.asIdeal.IsPrime := P.isPrime
  haveI hQprime : Q.asIdeal.IsPrime := Q.isPrime
  -- the inertia of `M` at `P` is trivial
  have hIbot : Work.SSGRoute.levelInertiaAt k Ω A hAf M = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro τ hτ
    have hτ' : τ ∈ (Work.SSGRoute.inertiaSub k Ω A).map (AlgEquiv.restrictNormalHom M) := by
      rw [inertiaSub_image_eq_levelInertia k Ω A hAf M]
      exact hτ
    obtain ⟨σ, hσ, hστ⟩ := Subgroup.mem_map.mp hτ'
    have hσker : σ ∈ χhom.ker := by
      rw [MonoidHom.mem_ker]
      apply Multiplicative.ext
      rw [hχhom_apply, toAdd_one]
      exact hinn σ hσ
    rw [← hMfix] at hσker
    rw [← hστ]
    exact MonoidHom.mem_ker.mp (by rw [IntermediateField.restrictNormalHom_ker]; exact hσker)
  -- the decomposition group of `M` at `P` is everything
  have hDtop : Work.SSGRoute.levelDecompAt k Ω A hAf M = ⊤ := by
    obtain ⟨δ, hδD, hδχ⟩ := hne
    have hδ1 : AlgEquiv.restrictNormalHom M δ ≠ 1 := by
      intro h
      apply hδχ
      have hker : δ ∈ (AlgEquiv.restrictNormalHom M).ker := by
        rw [MonoidHom.mem_ker]; exact h
      rw [IntermediateField.restrictNormalHom_ker] at hker
      rw [hMfix] at hker
      have h2 := congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp hker)
      simpa [hχhom_apply] using h2
    have hmem : AlgEquiv.restrictNormalHom M δ ∈ Work.SSGRoute.levelDecompAt k Ω A hAf M := by
      show AlgEquiv.restrictNormalHom M δ ∈
        MulAction.stabilizer (↥M ≃ₐ[k] ↥M) (Work.SSGRoute.levelPrime k Ω A hAf M).asIdeal
      rw [← Work.SSGRoute.range_restrictNormalHom_eq_stabilizer A hAf M]
      exact ⟨⟨δ, hδD⟩, rfl⟩
    have hne_bot : Work.SSGRoute.levelDecompAt k Ω A hAf M ≠ ⊥ := by
      intro h
      have : AlgEquiv.restrictNormalHom M δ ∈ (⊥ : Subgroup (↥M ≃ₐ[k] ↥M)) := by
        rw [← h]; exact hmem
      exact hδ1 (by simpa using this)
    apply Subgroup.eq_top_of_card_eq
    have hdvd : Nat.card (Work.SSGRoute.levelDecompAt k Ω A hAf M) ∣
        Nat.card (↥M ≃ₐ[k] ↥M) := Subgroup.card_subgroup_dvd_card _
    rw [hcardM] at hdvd
    have h1 : 1 < Nat.card (Work.SSGRoute.levelDecompAt k Ω A hAf M) := by
      by_contra hcon
      push Not at hcon
      have hpos : 0 < Nat.card (Work.SSGRoute.levelDecompAt k Ω A hAf M) := Nat.card_pos
      exact hne_bot (Subgroup.card_eq_one.mp (by omega))
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with h | h
    · omega
    · rw [h, hcardM]
  -- ## 5. `e = 1` and `f = p` at the level prime
  haveI hperf : PerfectField Q.asIdeal.ResidueField :=
    Commons.NumberTheory.NumberField.perfectField_residueField_heightOneSpectrum Q
  have hind : ((Work.SSGRoute.levelInertiaAt k Ω A hAf M).subgroupOf
      (Work.SSGRoute.levelDecompAt k Ω A hAf M)).index =
      P.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) :=
    Work.SSGRoute.levelInertia_index_eq_inertiaDeg k Ω A hAf M
  have hfind : P.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) = p := by
    rw [← hind, hIbot, hDtop, Subgroup.bot_subgroupOf, Subgroup.index_bot,
      Nat.card_congr (Subgroup.topEquiv :
        (⊤ : Subgroup (↥M ≃ₐ[k] ↥M)) ≃* (↥M ≃ₐ[k] ↥M)).toEquiv, hcardM]
  have heind : P.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := by
    have hcard_in : Nat.card (P.asIdeal.inertia (↥M ≃ₐ[k] ↥M)) =
        Q.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers ↥M) :=
      Ideal.card_inertia_eq_ramificationIdxIn (G := ↥M ≃ₐ[k] ↥M) Q.asIdeal P.asIdeal
    have hrIn : Q.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers ↥M) =
        P.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) :=
      Ideal.ramificationIdxIn_eq_ramificationIdx Q.asIdeal P.asIdeal (↥M ≃ₐ[k] ↥M)
    have hbot : P.asIdeal.inertia (↥M ≃ₐ[k] ↥M) = ⊥ := hIbot
    have h1 : Nat.card (P.asIdeal.inertia (↥M ≃ₐ[k] ↥M)) = 1 :=
      Subgroup.card_eq_one.mpr hbot
    rw [← hrIn, ← hcard_in, h1]
  refine ⟨M, hMnf, hMfd, hMgal, hcycM, hcardM, ?_⟩
  -- ## 6. all primes above `Q`
  intro w hw
  haveI hwI : w.asIdeal.LiesOver Q.asIdeal := hw
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup Q.asIdeal P.asIdeal w.asIdeal
    (↥M ≃ₐ[k] ↥M)
  have h1 : w.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) =
      P.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) := by
    rw [← hσ, Ideal.ramificationIdx_smul]
  have h2 : w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) =
      P.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := by
    rw [← hσ, Ideal.inertiaDeg_smul]
  exact ⟨by rw [h1, heind], by rw [h2, hfind]⟩

end Work.SSGRoute.Sha2Lib
