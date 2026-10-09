import Mathlib
import Submission.NK.CFTLib.ARL.AuxField
import Submission.NK.CFTLib.ARL.auxField_arith
import Submission.NK.CFTLib.ARL.AuxFieldBase
import Submission.NK.CFTLib.ARL.inertiaDeg_one_isFrobAtPrime_one
import Submission.NK.CFTLib.ARL.disjoint_restrictScalars_adjoin_zeta
import Submission.NK.CFTLib.ARL.isFrobAtPrime_zeta
import Submission.NK.CFTLib.ARL.auxField_construction
import Submission.NK.Chebotarev.Basic
import Submission.NK.Chebotarev.IsFrobAtRestrictNormalHom
import Submission.NK.FieldTheory.Galois.exists_prod_restrictNormalHom_of_card
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Artin's lemma: existence of the auxiliary field (multi-prime form)

This module proves `NK.CFTLib.ARL.auxField_exists_B`: for a finite cyclic extension `L/K` of
number fields and `m > 0`, the auxiliary-field hypothesis `NK.CFTLib.ARL.AuxFieldHyp K L m` of
Artin's lemma (Lang, *Algebraic Number Theory*, Ch. X §2; Childress, *CFT*, Lemma 2.8) holds.

The construction is the one described in `Submission/Work/CFTLib/ARL/NOTES_artin_lemma_and_transfer.md`:
`M = q₀·∏q𝔭` is chosen so that `(ZMod M)ˣ` contains a prime `ℓ` whose relations with the norms
`N𝔭` are controlled (`NK.CFTLib.ARL.auxField_arith`); inside `Ω = L(ζ_M)`,
`Gal(Ω/K) ≃ Gal(L/K) × Gal(K(ζ_M)/K)`, and for each `𝔭 ∈ s` one takes
`E_𝔭 = Ω^{H𝔭}` for `H𝔭 = ⟨δ, Φ𝔭⟩`, where `δ` has `L`-component a generator of `Gal(L/K)` and
`K(ζ_M)`-component the automorphism `ζ ↦ ζ^ℓ`, while `Φ𝔭` is a Frobenius element at `𝔭`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace NK.CFTLib.ARL

/-- In a cyclotomic extension of level `M`, the standard primitive `M`-th root of unity generates
the whole field over the base. -/
theorem isCyclotomicExtension_adjoin_eq_top {K L : Type*} [Field K] [Field L] [Algebra K L]
    (M : ℕ) [NeZero M] [IsCyclotomicExtension {M} K L] :
    IntermediateField.adjoin K
      ({IsCyclotomicExtension.zeta M K L} : Set L) = ⊤ := by
  have htop : IsCyclotomicExtension {M} K ↥(⊤ : IntermediateField K L) :=
    IsCyclotomicExtension.equiv (S := {M}) (A := K) (B := L)
      (C := ↥(⊤ : IntermediateField K L)) (IntermediateField.topEquiv.symm)
  have h := (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin M K L
    (⊤ : IntermediateField K L) (IsCyclotomicExtension.zeta_spec M K L)).mp htop
  exact h.symm

theorem auxField_exists_B (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (m : ℕ) (hm : 0 < m) : NK.CFTLib.ARL.AuxFieldHyp K L m := by
  classical
  intro s hs S hS
  -- ## Part 0: a generator of the Galois group
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  -- ## Part 1: the arithmetic input
  set a : s → ℕ := fun 𝔭 => Ideal.absNorm (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal with ha
  have ha_gt : ∀ i : s, 1 < a i := by
    intro 𝔭
    haveI : (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal.IsMaximal :=
      Ring.DimensionLEOne.maximalOfPrime (𝔭 : NK.Chebotarev.PrimeIdeal K).ne_bot
        (𝔭 : NK.Chebotarev.PrimeIdeal K).isPrime
    haveI hfin : Finite (𝓞 K ⧸ (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal) :=
      Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum _
    haveI : Fintype (𝓞 K ⧸ (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal) := Fintype.ofFinite _
    haveI : Field (𝓞 K ⧸ (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal) := Ideal.Quotient.field _
    have h : a 𝔭 = Nat.card (𝓞 K ⧸ (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal) := by
      rw [ha]
      simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [h, Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  set Bnd : ℕ := max (max m (max (NumberField.discr K).natAbs (NumberField.discr L).natAbs))
      ((Finset.univ.sup a) + 1) with hBnd
  set T : Finset ℕ := ((Finset.range (Bnd + 1)).filter Nat.Prime) ∪ S with hT
  have hTprime : ∀ p ∈ T, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact (Finset.mem_filter.mp h).2
    · exact hS p h
  obtain ⟨M, hMne, ℓ, hℓprime, hM_avoid, hM_cop_a, hℓ_cop_M, hrel⟩ :=
    auxField_arith (Module.finrank K L) Module.finrank_pos a ha_gt T hTprime
  haveI : NeZero M := hMne
  have hm_Bnd : m ≤ Bnd := by
    rw [hBnd]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hdK_Bnd : (NumberField.discr K).natAbs ≤ Bnd := by
    rw [hBnd]
    refine le_trans (le_max_left _ _) (le_trans (le_max_right m _) (le_max_left _ _))
  have hdL_Bnd : (NumberField.discr L).natAbs ≤ Bnd := by
    rw [hBnd]
    refine le_trans (le_max_right _ _)
      (le_trans (le_max_right m _) (le_max_left _ _))
  have hmemT : ∀ p : ℕ, p.Prime → p ≤ Bnd → p ∈ T := fun p hp hple =>
    Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hple), hp⟩)
  have hM_coprime_m : M.Coprime m := by
    refine Nat.coprime_of_dvd (fun p hp hpdvdM hpdvdm => ?_)
    exact hM_avoid p (hmemT p hp (le_trans (Nat.le_of_dvd hm hpdvdm) hm_Bnd)) hpdvdM
  have hM_avoidS : ∀ p ∈ S, ¬ p ∣ M := fun p hp => hM_avoid p (Finset.mem_union_right _ hp)
  have hM_absNorm : ∀ p : ℕ, p.Prime → p ∣ M → ∀ 𝔭 ∈ s, ¬ p ∣ Ideal.absNorm 𝔭.asIdeal := by
    intro p hp hpdvd 𝔭 h𝔭 hpdvd𝔭
    have hc : Nat.Coprime (a ⟨𝔭, h𝔭⟩) M := hM_cop_a ⟨𝔭, h𝔭⟩
    have h1 : p ∣ a ⟨𝔭, h𝔭⟩ := by
      rw [ha]
      simpa using hpdvd𝔭
    have h2 : p ∣ (a ⟨𝔭, h𝔭⟩).gcd M := Nat.dvd_gcd h1 hpdvd
    rw [hc.gcd_eq_one] at h2
    exact hp.not_dvd_one h2
  have hM_discrL : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ (NumberField.discr L).natAbs := by
    intro p hp hpdvd hpd
    have hple : p ≤ (NumberField.discr L).natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr (NumberField.discr_ne_zero L)) hpd
    exact hM_avoid p (hmemT p hp (le_trans hple hdL_Bnd)) hpdvd
  have hM_discrK : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ (NumberField.discr K).natAbs := by
    intro p hp hpdvd hpd
    have hple : p ≤ (NumberField.discr K).natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr (NumberField.discr_ne_zero K)) hpd
    exact hM_avoid p (hmemT p hp (le_trans hple hdK_Bnd)) hpdvd
  have hM_not_mem : ∀ 𝔭 ∈ s, (M : 𝓞 K) ∉ 𝔭.asIdeal := by
    intro 𝔭 h𝔭 hmem
    have hge := ha_gt ⟨𝔭, h𝔭⟩
    have hcop : Nat.Coprime (Ideal.absNorm (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal) M := by
      have h := hM_cop_a ⟨𝔭, h𝔭⟩
      rw [ha] at h
      simpa using h
    have hle : Ideal.span {((M : ℕ) : 𝓞 K)} ≤ (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal :=
      Ideal.span_le.mpr (by simpa using hmem)
    have hdvd : Ideal.absNorm (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal ∣ M ^ Module.finrank ℤ (𝓞 K) := by
      have h := Ideal.absNorm_dvd_absNorm_of_le hle
      rw [Ideal.absNorm_span_singleton, Algebra.norm_natCast, Int.natAbs_pow,
        Int.natAbs_natCast] at h
      exact h
    have h2 : Nat.Coprime (Ideal.absNorm (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal)
        (M ^ Module.finrank ℤ (𝓞 K)) := hcop.pow_right _
    have hone : Ideal.absNorm (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal = 1 :=
      Nat.Coprime.eq_one_of_dvd h2 hdvd
    have hge' : 1 < Ideal.absNorm (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal := by
      rw [ha] at hge
      simpa using hge
    omega
  refine ⟨M, hMne, hM_coprime_m, hM_avoidS, hM_absNorm, ?_, ?_⟩
  · -- the cyclotomic part meets the image of `L` in `K`
    exact disjoint_restrictScalars_adjoin_zeta M hM_discrL
  · -- the auxiliary field of Artin's lemma
    have hrel' : ∀ 𝔭 ∈ s, ∀ u v : ℕ,
        ((ℓ : ZMod M)) ^ u * (((Ideal.absNorm 𝔭.asIdeal : ℕ)) : ZMod M) ^ v = 1 →
          Module.finrank K L ∣ u ∧ Module.finrank K L ∣ v := by
      intro 𝔭 h𝔭 u v huv
      refine hrel ⟨𝔭, h𝔭⟩ u v ?_
      simpa [ha] using huv
    obtain ⟨E, hE, hEp⟩ :=
      auxField_construction K L m hm s S M ℓ hℓprime hM_coprime_m hM_avoidS hℓ_cop_M
        hM_absNorm hM_discrK hM_discrL hM_not_mem hrel'
    exact ⟨E, hE, hEp⟩

end NK.CFTLib.ARL
