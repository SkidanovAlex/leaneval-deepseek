import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Submission.Work.SSGRoute.ZDataMup.CycleDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Artin's lemma at a cycle (ideal modulus)

Artin's lemma (Lang, *ANT*, X §2; Childress, *CFT*, Lemma 2.8) is the auxiliary-field input of the
proof that `ker ψ ⊆ P(m)·𝔑(m)`; in this workspace it is packaged as the hypothesis
`NK.CFTLib.ARL.AuxFieldHyp K L m` of `NK.CFTLib.ARLTransfer.kernelLe_of_auxField`, and proved for
every natural-number modulus `m > 0` in `NK.CFTLib.ARL.auxField_exists_B`.

For the *cycle* (ideal-modulus) form of the transfer the modulus is replaced by a cycle `c`
(`CycleDefs.lean`); the natural-number modulus enters `AuxFieldHyp` only through

* the hypothesis that the primes of `s` are prime to it (`∀ 𝔭 ∈ s, (m : 𝓞 K) ∉ 𝔭.asIdeal`, which is
  *unused* in the proof of `auxField_exists_B`), and
* the conclusion that the auxiliary modulus `M` is coprime to it (`M.Coprime m`),

both of which say "avoid the (finitely many) rational primes below the primes of the modulus".
For a cycle the corresponding condition is "no prime dividing `M` lies below a prime of `c`",
i.e. `M.Coprime (∏_{𝔮 ∈ c.supp} N𝔮)`.  Since the construction of `auxField_exists_B` only feeds the
rational primes below the modulus into the set `T` of primes to avoid, the cycle version follows by
the same argument with `m` replaced by the product of the norms of the primes of `c`.

## Contents

* `Cycle.normProd` — the product of the absolute norms of the primes of a cycle;
* `Cycle.AuxFieldHyp K L c` — Artin's lemma's auxiliary-field hypothesis at the cycle `c`;
* `Cycle.auxField_exists` — it holds for every cycle `c`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace Work.SSGRoute.ZDataMup

namespace Cycle

variable {K : Type} [Field K] [NumberField K]

/-- **The product of the absolute norms of the primes of a cycle.**  A cycle is "avoided" by a
natural number `M` exactly when `M` is coprime to this rational number. -/
noncomputable def normProd (c : Cycle K) : ℕ :=
  ∏ 𝔮 ∈ c.supp, Ideal.absNorm 𝔮.asIdeal

theorem normProd_ne_zero (c : Cycle K) : c.normProd ≠ 0 := by
  rw [normProd, Finset.prod_ne_zero_iff]
  intro 𝔮 _
  exact (Ideal.absNorm_ne_zero_iff 𝔮.asIdeal).mpr
    (Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum 𝔮)

/-- **Artin's lemma's auxiliary-field hypothesis at a cycle `c`** (the cycle analogue of
`NK.CFTLib.ARL.AuxFieldHyp K L m`): for every finite set `s` of primes of `K` *outside* `c` and
every finite set `S` of rational primes there are an `M ≥ 1` whose prime divisors do not lie below
any prime of `c` (the cycle analogue of "`M` coprime to `m`"), not divisible by any prime of `S`,
and not dividing any `N𝔭` (`𝔭 ∈ s`), together with a subfield `E ⊆ L(ζ_M)` with `L ∩ K(ζ_M) = K`
and `E ∩ L = K`, such that for every `𝔭 ∈ s` there is a subfield `E𝔭 ≤ E` with
`E𝔭·ℚ(ζ_M) = L(ζ_M)` and `𝔭` splitting completely in `E𝔭/K`. -/
def AuxFieldHyp (L : Type) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (c : Cycle K) : Prop :=
  ∀ (s : Finset (NK.Chebotarev.PrimeIdeal K)) (hs : ∀ 𝔭 ∈ s, 𝔭 ∉ c.supp)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime),
    ∃ (M : ℕ) (_ : NeZero M),
      M.Coprime c.normProd ∧ (∀ p ∈ S, ¬ p ∣ M) ∧
      (∀ p : ℕ, p.Prime → p ∣ M → ∀ 𝔭 ∈ s, ¬ p ∣ Ideal.absNorm 𝔭.asIdeal) ∧
      Disjoint ((⊥ : IntermediateField L (CyclotomicField M L)).restrictScalars K)
        (IntermediateField.adjoin K
          ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} :
            Set (CyclotomicField M L))) ∧
      ∃ E : IntermediateField K (CyclotomicField M L),
        Disjoint E ((⊥ : IntermediateField L (CyclotomicField M L)).restrictScalars K) ∧
        (∀ 𝔭 ∈ s, ∃ E𝔭 : IntermediateField K (CyclotomicField M L),
          E𝔭 ≤ E ∧
          (E𝔭.restrictScalars ℚ) ⊔ (IntermediateField.adjoin ℚ
            ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} :
              Set (CyclotomicField M L))) = ⊤ ∧
          NK.Chebotarev.IsFrobAtPrime (K := K) (L := ↥E𝔭) 𝔭 1)

/-- **Artin's lemma at a cycle**: the auxiliary-field hypothesis holds for every cycle `c`. -/
theorem auxField_exists (L : Type) [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (c : Cycle K) : AuxFieldHyp (K := K) L c := by
  classical
  intro s _hs S hS
  -- the bound given by the rational primes below the primes of the cycle
  set Pc : ℕ := c.normProd with hPcdef
  have hPcne : Pc ≠ 0 := by rw [hPcdef]; exact normProd_ne_zero c
  have hPcpos : 0 < Pc := Nat.pos_of_ne_zero hPcne
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
  set Bnd : ℕ := max (max (NumberField.discr K).natAbs (NumberField.discr L).natAbs)
      ((Finset.univ.sup a) + 1) with hBnd
  set T : Finset ℕ := ((Finset.range (Bnd + 1)).filter Nat.Prime) ∪ S ∪
      ((Finset.range (Pc + 1)).filter Nat.Prime) with hT
  have hTprime : ∀ p ∈ T, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact (Finset.mem_filter.mp h).2
      · exact hS p h
    · exact (Finset.mem_filter.mp h).2
  have hn : 0 < Module.finrank K L := Module.finrank_pos
  obtain ⟨M, hMne, ℓ, hℓprime, hM_avoid, hM_cop_a, hℓ_cop_M, hrel⟩ :=
    NK.CFTLib.ARL.auxField_arith (n := Module.finrank K L) (hn := hn) (ι := ↥s)
      (a := a) (ha := ha_gt) (T := T) (hT := hTprime)
  haveI : NeZero M := hMne
  -- ## Part 2: the auxiliary modulus is coprime to the primes of the cycle
  have hdK_Bnd : (NumberField.discr K).natAbs ≤ Bnd := by
    rw [hBnd]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hdL_Bnd : (NumberField.discr L).natAbs ≤ Bnd := by
    rw [hBnd]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hmemT : ∀ p : ℕ, p.Prime → p ≤ Bnd → p ∈ T := fun p hp hple =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hple), hp⟩))
  have hmemTc : ∀ p : ℕ, p.Prime → p ≤ Pc → p ∈ T := fun p hp hple =>
    Finset.mem_union_right _ (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hple), hp⟩)
  have hM_cop_c : M.Coprime c.normProd := by
    rw [← hPcdef]
    refine Nat.coprime_of_dvd (fun p hp hpdvdM hpdvdPc => ?_)
    exact hM_avoid p (hmemTc p hp (Nat.le_of_dvd hPcpos hpdvdPc)) hpdvdM
  have hM_avoidS : ∀ p ∈ S, ¬ p ∣ M :=
    fun p hp => hM_avoid p (Finset.mem_union_left _
      (Finset.mem_union_right _ hp))
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
    have hdvd : Ideal.absNorm (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal ∣
        M ^ Module.finrank ℤ (𝓞 K) := by
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
    rw [hone] at hge'
    exact absurd hge' (lt_irrefl 1)
  refine ⟨M, hMne, hM_cop_c, hM_avoidS, hM_absNorm, ?_, ?_⟩
  · exact NK.CFTLib.ARL.disjoint_restrictScalars_adjoin_zeta M hM_discrL
  · have hrel' : ∀ 𝔭 ∈ s, ∀ u v : ℕ,
        ((ℓ : ZMod M)) ^ u * (((Ideal.absNorm 𝔭.asIdeal : ℕ)) : ZMod M) ^ v = 1 →
          Module.finrank K L ∣ u ∧ Module.finrank K L ∣ v := by
      intro 𝔭 h𝔭 u v huv
      refine hrel ⟨𝔭, h𝔭⟩ u v ?_
      simpa [ha] using huv
    obtain ⟨E, hE, hEp⟩ :=
      NK.CFTLib.ARL.auxField_construction K L 1 one_pos s S M ℓ hℓprime
        (Nat.coprime_one_right M) hM_avoidS hℓ_cop_M hM_absNorm hM_discrK hM_discrL hM_not_mem hrel'
    exact ⟨E, hE, hEp⟩

end Cycle

end Work.SSGRoute.ZDataMup
