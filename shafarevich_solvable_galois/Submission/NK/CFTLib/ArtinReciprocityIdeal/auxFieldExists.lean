import Mathlib.Computability.Reduce
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Submission.NK.CFTLib.ARL.AuxField
import Submission.NK.CFTLib.ARL.auxField_arith
import Submission.NK.CFTLib.ARL.inertiaDeg_one_isFrobAtPrime_one
import Submission.NK.ChebotarevGeneral.isFrobAtPrime_under_of_isFrobAt
import Submission.NK.NUV2.ARL.Gap.conductor_crux.AuxFrob
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Artin's lemma: existence of the auxiliary field (multi-prime form)

This module proves `NK.CFTLib.ARL.AuxFieldHyp K L m` for a finite **cyclic** extension `L/K` of
number fields and every `m > 0`: Artin's lemma in the form needed by the transfer argument of the
ideal-theoretic reciprocity law (`NK.CFTLib.ARL.kernelLe_of_auxField_B`).

For a finite set `s` of primes of `K` prime to `(m)` and a finite set `S` of rational primes we
produce a modulus `M` (coprime to `m`, avoiding `S` and the norms `N𝔭`, `𝔭 ∈ s`) together with, in
`Ω = L(ζ_M)`:

* the auxiliary field `E = Ω^H`, where `H = ⋂_{𝔭 ∈ s} H_𝔭` and
  `H_𝔭 = Ψ⁻¹(K0_𝔭)` for the explicit subgroup
  `K0_𝔭 = {(sA^{a + t_𝔭 c}, bu^a·au_𝔭^c) : a, c ∈ ℤ} ≤ Gal(A/K) × (ℤ/M)ˣ`
  of the product `Gal(Ω/K) ≃ Gal(A/K) × (ℤ/M)ˣ` (`NK.NUV2.ARL.Gap.conductor_crux.AuxPsiEquiv`),
  where `sA` is a generator of `Gal(A/K) ≅ Gal(L/K)`, `F_𝔭` is a Frobenius at a prime `𝔓_𝔭 | 𝔭` of
  `Ω`, `AuxPhi1 F_𝔭 = sA^{t_𝔭}`, `au_𝔭 = χ(F_𝔭) = N𝔭` and `bu = ℓ` is the auxiliary prime class
  provided by the arithmetic input `NK.CFTLib.ARL.auxField_arith`;
* the individual fields `E_𝔭 = Ω^{H_𝔭} ≤ E`.

The three properties are then:

* `E ∩ L = K`: the element `ψ⁻¹(sA, bu) ∈ K0_𝔭` lies in every `H_𝔭`, hence in `H`, and its
  `A`-component `sA` generates `Gal(A/K)` (`hK0sA`, `hJmem`, `hEA`);
* `E_𝔭 · ℚ(ζ_M) = Ω`: the key arithmetic input `hK0key` — if `bu^a au_𝔭^c = 1` then
  `ℓ^a N𝔭^c = 1` in `ℤ/M`, whence `n ∣ a` and `n ∣ c` by the orthogonality relation of
  `auxField_arith`, so `sA^{a + t_𝔭 c} = 1` (`hEB`);
* `𝔭` splits completely in `E_𝔭/K`: `F_𝔭 ∈ H_𝔭` fixes `E_𝔭`, so the residue degree of
  `𝔓_𝔭 ∩ E_𝔭` over `𝔭` is `1` (`NK.ChebotarevGeneral.inertiaDeg_under_eq_one`) and the identity
  is a Frobenius (`NK.CFTLib.ARL.inertiaDeg_one_isFrobAtPrime_one`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace NK.CFTLib.ArtinReciprocityIdeal

open NK.NUV2.ARL.Gap.conductor_crux

/-- **The arithmetic input of the auxiliary-field construction.**  For a number field extension
`L/K` (with `n > 0` given, so that it may be instantiated at `n = [L : K]`), a modulus `m > 0`, a
finite set `s` of primes of `K`, and a finite set `S` of rational primes, there are `M > 0`, a
rational prime `ℓ` and units `ℓ, N𝔭 ∈ (ℤ/M)ˣ` such that

* `M` is coprime to `m`, avoids `S`, avoids the norms `N𝔭` (`𝔭 ∈ s`) and the discriminant of `L`;
* `(M) ⊄ 𝔭` for `𝔭 ∈ s`, `ℓ ∤ M`;
* `n ∣ ord ℓ` and `n ∣ ord(N𝔭)`;
* the orthogonality relation `ℓ^u·N𝔭^v = 1 ⟹ n ∣ u ∧ n ∣ v` holds for every `𝔭 ∈ s`. -/
theorem exists_auxModulus {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m)
    (s : Finset (NK.Chebotarev.PrimeIdeal K))
    (hs : ∀ 𝔭 ∈ s, (m : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∃ (M : ℕ) (_ : NeZero M) (ℓ : ℕ), ℓ.Prime ∧ M.Coprime m ∧ (∀ p ∈ S, ¬ p ∣ M) ∧
      (∀ p : ℕ, p.Prime → p ∣ M → ∀ 𝔭 ∈ s, ¬ p ∣ Ideal.absNorm 𝔭.asIdeal) ∧
      (∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ (NumberField.discr L).natAbs) ∧
      ¬ ℓ ∣ M ∧
      (∀ 𝔭 ∈ s, (M : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal) ∧
      n ∣ orderOf ((ℓ : ZMod M)) ∧
      (∀ 𝔭 ∈ s, n ∣ orderOf (((Ideal.absNorm 𝔭.asIdeal : ℕ) : ZMod M))) ∧
      (∀ 𝔭 ∈ s, ∀ u v : ℕ, (ℓ : ZMod M) ^ u * ((Ideal.absNorm 𝔭.asIdeal : ℕ) : ZMod M) ^ v = 1 →
        n ∣ u ∧ n ∣ v) := by
  classical
  -- ## the family of norms (with one spare index carrying a unit of `ℤ/M`)
  let a : Option s → ℕ := fun i => match i with
    | none => 2
    | some 𝔭 => Ideal.absNorm 𝔭.1.asIdeal
  have ha_gt : ∀ i : Option s, 1 < a i := by
    rintro (_ | 𝔭)
    · show 1 < 2
      norm_num
    · exact one_lt_absNorm_aux 𝔭.1
  -- ## the finite set of bad primes
  set Bnd : ℕ := max (max m (max (NumberField.discr K).natAbs (NumberField.discr L).natAbs))
      ((Finset.univ.sup a) + 1) with hBnd
  set T : Finset ℕ := ((Finset.range (Bnd + 1)).filter Nat.Prime) ∪ S with hT
  have hTprime : ∀ p ∈ T, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact (Finset.mem_filter.mp h).2
    · exact hS p h
  obtain ⟨M, hMne, ℓ, hℓprime, hMavoid, hMcop_a, hℓnotM, hrel⟩ :=
    NK.CFTLib.ARL.auxField_arith n hn a ha_gt T hTprime
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
    exact hMavoid p (hmemT p hp (le_trans (Nat.le_of_dvd hm hpdvdm) hm_Bnd)) hpdvdM
  have hM_avoidS : ∀ p ∈ S, ¬ p ∣ M := fun p hp => hMavoid p (Finset.mem_union_right _ hp)
  have hM_absNorm : ∀ p : ℕ, p.Prime → p ∣ M → ∀ 𝔭 ∈ s, ¬ p ∣ Ideal.absNorm 𝔭.asIdeal := by
    intro p hp hpdvd 𝔭 h𝔭 hpdvd𝔭
    have hc : Nat.Coprime (a (some ⟨𝔭, h𝔭⟩)) M := hMcop_a (some ⟨𝔭, h𝔭⟩)
    have h1 : p ∣ a (some ⟨𝔭, h𝔭⟩) := hpdvd𝔭
    have h2 : p ∣ (a (some ⟨𝔭, h𝔭⟩)).gcd M := Nat.dvd_gcd h1 hpdvd
    rw [hc.gcd_eq_one] at h2
    exact hp.not_dvd_one h2
  have hM_discrL : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ (NumberField.discr L).natAbs := by
    intro p hp hpdvd hpd
    have hple : p ≤ (NumberField.discr L).natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr (NumberField.discr_ne_zero L)) hpd
    exact hMavoid p (hmemT p hp (le_trans hple hdL_Bnd)) hpdvd
  have hM_not_mem : ∀ 𝔭 ∈ s, (M : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal := by
    intro 𝔭 h𝔭
    exact natCast_notMem_of_not_dvd_absNorm M 𝔭 (fun p hp hpM => hM_absNorm p hp hpM 𝔭 h𝔭)
  -- ## the order relations
  have hn_ordℓ : n ∣ orderOf ((ℓ : ZMod M)) := by
    have h := hrel none (orderOf ((ℓ : ZMod M))) 0 (by rw [pow_orderOf_eq_one, pow_zero, mul_one])
    exact h.1
  have hn_ordN : ∀ 𝔭 ∈ s, n ∣ orderOf (((Ideal.absNorm 𝔭.asIdeal : ℕ) : ZMod M)) := by
    intro 𝔭 h𝔭
    have h := hrel (some ⟨𝔭, h𝔭⟩) 0 (orderOf (((Ideal.absNorm 𝔭.asIdeal : ℕ) : ZMod M)))
      (by rw [pow_zero, one_mul, pow_orderOf_eq_one])
    exact h.2
  have hrel' : ∀ 𝔭 ∈ s, ∀ u v : ℕ,
      (ℓ : ZMod M) ^ u * ((Ideal.absNorm 𝔭.asIdeal : ℕ) : ZMod M) ^ v = 1 → n ∣ u ∧ n ∣ v := by
    intro 𝔭 h𝔭 u v huv
    exact hrel (some ⟨𝔭, h𝔭⟩) u v huv
  exact ⟨M, hMne, ℓ, hℓprime, hM_coprime_m, hM_avoidS, hM_absNorm, hM_discrL, hℓnotM,
    hM_not_mem, hn_ordℓ, hn_ordN, hrel'⟩

/-- The auxiliary subgroup `K0 𝔭 ≤ Gal(A/K) × (ℤ/M)ˣ` of the product decomposition, the elements
`(sA ^ (a + t 𝔭 * c), bu ^ a * au 𝔭 ^ c)` with `a c : ℤ`.  This is the group whose inverse image
under `AuxPsiEquiv` is the fixing subgroup of the individual auxiliary field `E𝔭`. -/
def auxK0 {K L : Type} [Field K] [Field L] [Algebra K L] (M : ℕ)
    (sA : ↥(AuxA K L M) ≃ₐ[K] ↥(AuxA K L M)) (bu : (ZMod M)ˣ)
    {ι : Type} (t : ι → ℤ) (au : ι → (ZMod M)ˣ) (𝔭 : ι) :
    Subgroup ((↥(AuxA K L M) ≃ₐ[K] ↥(AuxA K L M)) × (ZMod M)ˣ) where
  carrier := {x | ∃ a c : ℤ, x = (sA ^ (a + t 𝔭 * c), bu ^ a * au 𝔭 ^ c)}
  mul_mem' := by
    rintro x y ⟨a, c, rfl⟩ ⟨a', c', rfl⟩
    refine ⟨a + a', c + c', ?_⟩
    refine Prod.ext ?_ ?_
    · show sA ^ (a + t 𝔭 * c) * sA ^ (a' + t 𝔭 * c') = sA ^ ((a + a') + t 𝔭 * (c + c'))
      rw [← zpow_add]
      congr 1
      ring
    · show bu ^ a * au 𝔭 ^ c * (bu ^ a' * au 𝔭 ^ c') = bu ^ (a + a') * au 𝔭 ^ (c + c')
      rw [mul_mul_mul_comm, ← zpow_add, ← zpow_add]
  one_mem' := by
    refine ⟨0, 0, ?_⟩
    refine Prod.ext ?_ ?_
    · show (1 : ↥(AuxA K L M) ≃ₐ[K] ↥(AuxA K L M)) = sA ^ (0 + t 𝔭 * 0)
      rw [mul_zero, add_zero, zpow_zero]
    · show (1 : (ZMod M)ˣ) = bu ^ (0 : ℤ) * au 𝔭 ^ (0 : ℤ)
      rw [zpow_zero, zpow_zero, one_mul]
  inv_mem' := by
    rintro x ⟨a, c, rfl⟩
    refine ⟨-a, -c, ?_⟩
    refine Prod.ext ?_ ?_
    · show (sA ^ (a + t 𝔭 * c))⁻¹ = sA ^ ((-a) + t 𝔭 * (-c))
      rw [← zpow_neg]
      congr 1
      ring
    · show (bu ^ a * au 𝔭 ^ c)⁻¹ = bu ^ (-a) * au 𝔭 ^ (-c)
      rw [mul_inv, zpow_neg, zpow_neg]

/-- **Artin's lemma: the auxiliary-field hypothesis.**  For a finite cyclic extension `L/K` of
number fields and every `m > 0` the hypothesis `NK.CFTLib.ARL.AuxFieldHyp K L m` holds. -/
theorem auxFieldExists (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (m : ℕ) (hm : 0 < m) : NK.CFTLib.ARL.AuxFieldHyp K L m := by
  classical
  intro s hs S hS
  -- ## Step 0: a generator of the cyclic group `Gal(L/K)`
  obtain ⟨σ₀, hσ₀⟩ := IsCyclic.exists_generator (α := (L ≃ₐ[K] L))
  have hnpos : 0 < Nat.card (L ≃ₐ[K] L) := by
    rw [IsGalois.card_aut_eq_finrank K L]; exact Module.finrank_pos
  -- ## Step 1: the arithmetic data
  obtain ⟨M, hMne, ℓ, hℓprime, hMcop, hMS, hMa, hMdisc, hℓM, hMmem, hordℓ, hordN, hrel⟩ :=
    exists_auxModulus (K := K) (L := L) (Nat.card (L ≃ₐ[K] L)) hnpos m hm s hs S hS
  haveI : NeZero M := hMne
  -- ## Step 2: the product decomposition `Gal(Ω/K) ≃ Gal(A/K) × (ℤ/M)ˣ`
  have hdisjAB : Disjoint (AuxA K L M) (AuxB K L M) :=
    disjoint_iff.mpr (AuxA_inf_AuxB_eq_bot (K := K) (L := L) M hMdisc)
  set Ψ := AuxPsiEquiv (K := K) (L := L) M hMdisc with hΨdef
  have hPsi_fst : ∀ γ : (CyclotomicField M L) ≃ₐ[K] (CyclotomicField M L),
      (Ψ γ).1 = AuxPhi1 M γ := fun γ => by rw [hΨdef]; exact AuxPsi_fst M γ
  have hPsi_snd : ∀ γ : (CyclotomicField M L) ≃ₐ[K] (CyclotomicField M L),
      (Ψ γ).2 = AuxChi M γ := fun γ => by rw [hΨdef]; exact AuxPsi_snd M γ
  set sA : ↥(AuxA K L M) ≃ₐ[K] ↥(AuxA K L M) :=
    AlgEquiv.autCongr (AuxA_algEquiv (K := K) (L := L) M) σ₀ with hsAdef
  have hsAgen : ∀ y : ↥(AuxA K L M) ≃ₐ[K] ↥(AuxA K L M), y ∈ Subgroup.zpowers sA := by
    intro y
    rw [Subgroup.mem_zpowers_iff]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      (hσ₀ ((AlgEquiv.autCongr (AuxA_algEquiv (K := K) (L := L) M)).symm y))
    refine ⟨k, ?_⟩
    calc sA ^ k = AlgEquiv.autCongr (AuxA_algEquiv (K := K) (L := L) M) (σ₀ ^ k) :=
          (map_zpow (AlgEquiv.autCongr (AuxA_algEquiv (K := K) (L := L) M)) σ₀ k).symm
      _ = AlgEquiv.autCongr (AuxA_algEquiv (K := K) (L := L) M)
            ((AlgEquiv.autCongr (AuxA_algEquiv (K := K) (L := L) M)).symm y) := by rw [hk]
      _ = y := MulEquiv.apply_symm_apply _ y
  have hsAord : orderOf sA = Nat.card (L ≃ₐ[K] L) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hsAgen]
    haveI := AuxA_isGalois (K := K) (L := L) M
    haveI := AuxA_finiteDimensional (K := K) (L := L) M
    rw [IsGalois.card_aut_eq_finrank K ↥(AuxA K L M), AuxA_finrank (K := K) (L := L) M,
      IsGalois.card_aut_eq_finrank K L]
  -- ## Step 3: the Frobenius data at each prime of `s`
  haveI hisG : IsGalois K (CyclotomicField M L) :=
    NK.CFTLib.ARL.isGalois_cyclotomicField_over_base (K := K) M
  have hex : ∀ 𝔭 : s, ∃ (𝔓 : NK.Chebotarev.PrimeIdeal (CyclotomicField M L))
      (F : (CyclotomicField M L) ≃ₐ[K] (CyclotomicField M L)),
      𝔓.asIdeal.LiesOver 𝔭.1.asIdeal ∧ NK.Chebotarev.IsFrobAt 𝔓 F := by
    intro 𝔭
    obtain ⟨𝔓, h𝔓⟩ := Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
      (K := K) (L := CyclotomicField M L) 𝔭.1
    obtain ⟨F, hF⟩ := NK.Chebotarev.exists_isFrobAt (K := K) (L := CyclotomicField M L) 𝔭.1 𝔓 h𝔓
    exact ⟨𝔓, F, h𝔓, hF⟩
  choose 𝔓 F h𝔓 hF using hex
  have hFζ : ∀ 𝔭 : s, F 𝔭 (AuxZeta L M) = (AuxZeta L M) ^ (Ideal.absNorm 𝔭.1.asIdeal) := fun 𝔭 =>
    AuxZeta_frob_pow (K := K) (L := L) M 𝔭.1 (F 𝔭) (𝔓 𝔭) (h𝔓 𝔭) (hF 𝔭) (fun p hp hpM => hMa p hp hpM 𝔭.1 𝔭.2)
  have hχF : ∀ 𝔭 : s,
      (((AuxChi M (F 𝔭) : (ZMod M)ˣ) : ZMod M)) = (Ideal.absNorm 𝔭.1.asIdeal : ZMod M) :=
    fun 𝔭 => AuxChi_eq_absNorm (K := K) (L := L) M 𝔭.1 (F 𝔭) (hFζ 𝔭)
  have hg0 : ∀ 𝔭 : s, ∃ t : ℤ, AuxPhi1 M (F 𝔭) = sA ^ t := fun 𝔭 =>
    (Subgroup.mem_zpowers_iff.mp (hsAgen (AuxPhi1 M (F 𝔭)))).imp (fun t ht => ht.symm)
  choose t ht using hg0
  -- ## the units `bu = ℓ` and `au 𝔭 = N𝔭`
  have hℓcop : ℓ.Coprime M := (Nat.Prime.coprime_iff_not_dvd hℓprime).mpr hℓM
  set bu : (ZMod M)ˣ := ZMod.unitOfCoprime ℓ hℓcop with hbudef
  have hbucoe : (bu : ZMod M) = (ℓ : ZMod M) := ZMod.coe_unitOfCoprime ℓ hℓcop
  set au : s → (ZMod M)ˣ := fun 𝔭 => AuxChi M (F 𝔭) with haudef
  have hcardpos : 0 < Nat.card ((ZMod M)ˣ) := Finite.card_pos_iff.mpr ⟨(1 : (ZMod M)ˣ)⟩
  have hbupos : 0 < orderOf bu := Nat.pos_of_dvd_of_pos (orderOf_dvd_natCard bu) hcardpos
  have haupos : ∀ 𝔭 : s, 0 < orderOf (au 𝔭) := fun 𝔭 =>
    Nat.pos_of_dvd_of_pos (orderOf_dvd_natCard (au 𝔭)) hcardpos
  have hnu : ∀ 𝔭 : s, Nat.card (L ≃ₐ[K] L) ∣ orderOf (au 𝔭) := by
    intro 𝔭
    rw [← orderOf_units]
    show Nat.card (L ≃ₐ[K] L) ∣ orderOf ((AuxChi M (F 𝔭) : (ZMod M)ˣ) : ZMod M)
    rw [hχF 𝔭]
    exact hordN 𝔭.1 𝔭.2
  have hnb : Nat.card (L ≃ₐ[K] L) ∣ orderOf bu := by
    rw [← orderOf_units, hbucoe]
    exact hordℓ
  -- ## Step 4: the subgroups `K0 𝔭`
  set K0 : s → Subgroup ((↥(AuxA K L M) ≃ₐ[K] ↥(AuxA K L M)) × (ZMod M)ˣ) :=
    fun 𝔭 => auxK0 M sA bu t au 𝔭 with hK0def
  -- ## Step 5: the key arithmetic point
  have hK0key : ∀ 𝔭 : s, ∀ x ∈ K0 𝔭, x.2 = 1 → x.1 = 1 := by
    rintro 𝔭 x ⟨a, c, rfl⟩ h2
    have h2' : au 𝔭 ^ c * bu ^ a = 1 := by rw [mul_comm]; exact h2
    set a' : ℕ := (a % (orderOf bu : ℤ)).toNat with ha'def
    set c' : ℕ := (c % (orderOf (au 𝔭) : ℤ)).toNat with hc'def
    have hc'e : au 𝔭 ^ c = au 𝔭 ^ (c' : ℤ) := by
      have hmod : au 𝔭 ^ (c % (orderOf (au 𝔭) : ℤ)) = au 𝔭 ^ c := zpow_mod_orderOf (au 𝔭) c
      have hz : (c' : ℤ) = c % (orderOf (au 𝔭) : ℤ) := by
        rw [hc'def]
        exact Int.toNat_of_nonneg (Int.emod_nonneg c (by exact_mod_cast (haupos 𝔭).ne'))
      rw [hz]; exact hmod.symm
    have ha'e : bu ^ a = bu ^ (a' : ℤ) := by
      have hmod : bu ^ (a % (orderOf bu : ℤ)) = bu ^ a := zpow_mod_orderOf bu a
      have hz : (a' : ℤ) = a % (orderOf bu : ℤ) := by
        rw [ha'def]
        exact Int.toNat_of_nonneg (Int.emod_nonneg a (by exact_mod_cast hbupos.ne'))
      rw [hz]; exact hmod.symm
    have h3 : (au 𝔭 : ZMod M) ^ c' * (bu : ZMod M) ^ a' = 1 := by
      have h := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) h2'
      rw [hc'e, ha'e] at h
      simpa [Units.val_mul, Units.val_pow_eq_pow_val] using h
    have h4 : ((Ideal.absNorm 𝔭.1.asIdeal : ℕ) : ZMod M) ^ c' * (ℓ : ZMod M) ^ a' = 1 := by
      rw [← hχF 𝔭, ← hbucoe]
      exact h3
    obtain ⟨ha'n, hc'n⟩ := hrel 𝔭.1 𝔭.2 a' c' (by rw [mul_comm]; exact h4)
    have hdivc : (Nat.card (L ≃ₐ[K] L) : ℤ) ∣ c := by
      have h1 : (orderOf (au 𝔭) : ℤ) ∣ c - c' := orderOf_dvd_sub_iff_zpow_eq_zpow.mpr hc'e
      have h2'' : (Nat.card (L ≃ₐ[K] L) : ℤ) ∣ (c' : ℤ) := by exact_mod_cast hc'n
      have h3'' : (Nat.card (L ≃ₐ[K] L) : ℤ) ∣ orderOf (au 𝔭) := by exact_mod_cast hnu 𝔭
      have h5 := dvd_trans h3'' h1
      have h4' : (c - c') + c' = c := by ring
      rw [← h4']
      exact dvd_add h5 h2''
    have hdiva : (Nat.card (L ≃ₐ[K] L) : ℤ) ∣ a := by
      have h1 : (orderOf bu : ℤ) ∣ a - a' := orderOf_dvd_sub_iff_zpow_eq_zpow.mpr ha'e
      have h2'' : (Nat.card (L ≃ₐ[K] L) : ℤ) ∣ (a' : ℤ) := by exact_mod_cast ha'n
      have h3'' : (Nat.card (L ≃ₐ[K] L) : ℤ) ∣ orderOf bu := by exact_mod_cast hnb
      have h5 := dvd_trans h3'' h1
      have h4' : (a - a') + a' = a := by ring
      rw [← h4']
      exact dvd_add h5 h2''
    have h5 : sA ^ (a + t 𝔭 * c) = 1 := by
      refine orderOf_dvd_iff_zpow_eq_one.mp ?_
      rw [hsAord]
      have h6 : (Nat.card (L ≃ₐ[K] L) : ℤ) ∣ a + t 𝔭 * c :=
        dvd_add hdiva (dvd_mul_of_dvd_right hdivc (t 𝔭))
      exact_mod_cast h6
    exact h5
  -- ## Step 6: the composite auxiliary field
  set H : Subgroup ((CyclotomicField M L) ≃ₐ[K] (CyclotomicField M L)) :=
    ⨅ 𝔭, Subgroup.comap Ψ.toMonoidHom (K0 𝔭) with hHdef
  set E : IntermediateField K (CyclotomicField M L) := IntermediateField.fixedField H with hEdef
  have hPsiJ : Ψ (Ψ.symm (sA, bu)) = (sA, bu) := Ψ.apply_symm_apply (sA, bu)
  have hK0sA : ∀ 𝔭 : s, (sA, bu) ∈ K0 𝔭 := by
    intro 𝔭
    refine ⟨1, 0, ?_⟩
    refine Prod.ext ?_ ?_
    · show sA = sA ^ (1 + t 𝔭 * 0)
      rw [mul_zero, add_zero, zpow_one]
    · show bu = bu ^ (1 : ℤ) * au 𝔭 ^ (0 : ℤ)
      rw [zpow_one, zpow_zero, mul_one]
  have hJmem : Ψ.symm (sA, bu) ∈ H := by
    rw [hHdef]
    refine Subgroup.mem_iInf.mpr ?_
    intro 𝔭
    rw [Subgroup.mem_comap]
    change Ψ (Ψ.symm (sA, bu)) ∈ K0 𝔭
    rw [hPsiJ]
    exact hK0sA 𝔭
  have hEA : E ⊓ AuxA K L M = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [IntermediateField.mem_inf] at hx
    obtain ⟨hxE, hxA⟩ := hx
    haveI := AuxA_isGalois (K := K) (L := L) M
    haveI := AuxA_finiteDimensional (K := K) (L := L) M
    rw [IsGalois.mem_bot_iff_fixed]
    intro f
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hsAgen (AuxPhi1 M f))
    have hJk : (Ψ.symm (sA, bu)) ^ k ∈ H := H.zpow_mem hJmem k
    have hfix : ((Ψ.symm (sA, bu)) ^ k) x = x :=
      (IntermediateField.mem_fixedField_iff (H := H) x).mp (hEdef ▸ hxE) _ hJk
    have hPhi1J : AuxPhi1 M (Ψ.symm (sA, bu)) = sA := by
      have := congrArg Prod.fst hPsiJ
      rwa [hPsi_fst] at this
    have hPhi1 : AuxPhi1 M ((Ψ.symm (sA, bu)) ^ k) = AuxPhi1 M f := by
      rw [map_zpow, hPhi1J, hk]
    calc f x = ((AuxPhi1 M f) ⟨x, hxA⟩ : CyclotomicField M L) :=
          (AuxPhi1_apply M f ⟨x, hxA⟩).symm
      _ = ((AuxPhi1 M ((Ψ.symm (sA, bu)) ^ k)) ⟨x, hxA⟩ : CyclotomicField M L) := by rw [hPhi1]
      _ = ((Ψ.symm (sA, bu)) ^ k) x := AuxPhi1_apply M _ ⟨x, hxA⟩
      _ = x := hfix
  -- ## Step 7: `E𝔭 ⊔ ℚ(ζ_M) = Ω`
  have hEB : ∀ 𝔭 : s, IntermediateField.fixedField
      (Subgroup.comap Ψ.toMonoidHom (K0 𝔭)) ⊔ AuxB K L M = ⊤ := by
    intro 𝔭
    have h1 : (IntermediateField.fixedField (Subgroup.comap Ψ.toMonoidHom (K0 𝔭)) ⊔
        AuxB K L M).fixingSubgroup = ⊥ := by
      rw [IntermediateField.fixingSubgroup_sup, IntermediateField.fixingSubgroup_fixedField,
        Subgroup.eq_bot_iff_forall]
      intro h hh
      rw [Subgroup.mem_inf] at hh
      obtain ⟨hhH, hhB⟩ := hh
      have hhζ : h (AuxZeta L M) = AuxZeta L M :=
        (IntermediateField.mem_fixingSubgroup_iff (K := AuxB K L M) h).mp hhB _
          (IntermediateField.subset_adjoin K _ (Set.mem_singleton _))
      have hχ : AuxChi M h = 1 := (AuxChi_eq_one_iff M h).mpr hhζ
      have hmem : Ψ h ∈ K0 𝔭 := by
        have h' := hhH
        rw [Subgroup.mem_comap] at h'
        exact h'
      have h2 : (Ψ h).2 = 1 := by rw [hPsi_snd]; exact hχ
      have h1' : (Ψ h).1 = 1 := hK0key 𝔭 (Ψ h) hmem h2
      have hz : Ψ h = 1 := Prod.ext h1' h2
      exact Ψ.injective (by rw [hz, map_one])
    have h2 : IntermediateField.fixedField (Subgroup.comap Ψ.toMonoidHom (K0 𝔭)) ⊔ AuxB K L M
        = IntermediateField.fixedField ((IntermediateField.fixedField
            (Subgroup.comap Ψ.toMonoidHom (K0 𝔭)) ⊔ AuxB K L M).fixingSubgroup) :=
      (IsGalois.fixedField_fixingSubgroup _).symm
    rw [h2, h1, IntermediateField.fixedField_bot]
  have hFmem : ∀ 𝔭 : s, F 𝔭 ∈ (IntermediateField.fixedField
      (Subgroup.comap Ψ.toMonoidHom (K0 𝔭))).fixingSubgroup := by
    intro 𝔭
    rw [IntermediateField.fixingSubgroup_fixedField]
    rw [Subgroup.mem_comap]
    change Ψ (F 𝔭) ∈ K0 𝔭
    refine ⟨0, 1, ?_⟩
    refine Prod.ext ?_ ?_
    · show AuxPhi1 M (F 𝔭) = sA ^ (0 + t 𝔭 * 1)
      rw [zero_add, mul_one]
      exact ht 𝔭
    · show AuxChi M (F 𝔭) = bu ^ (0 : ℤ) * au 𝔭 ^ (1 : ℤ)
      rw [zpow_zero, one_mul, zpow_one]
  -- ## Step 8: the ℚ-level join and the splitting
  have hjoin : ∀ 𝔭 : s, (IntermediateField.restrictScalars ℚ (IntermediateField.fixedField
        (Subgroup.comap Ψ.toMonoidHom (K0 𝔭)))) ⊔
        (IntermediateField.adjoin ℚ ({AuxZeta L M} : Set (CyclotomicField M L))) = ⊤ := by
    intro 𝔭
    set S' : IntermediateField ℚ (CyclotomicField M L) :=
      (IntermediateField.fixedField (Subgroup.comap Ψ.toMonoidHom (K0 𝔭))).restrictScalars ℚ ⊔
        (IntermediateField.adjoin ℚ ({AuxZeta L M} : Set (CyclotomicField M L))) with hSdef
    have hEBr : (IntermediateField.fixedField (Subgroup.comap Ψ.toMonoidHom (K0 𝔭)) ⊔
        AuxB K L M).restrictScalars ℚ = ⊤ := by rw [hEB 𝔭]; rfl
    have hsup_rat : (IntermediateField.fixedField (Subgroup.comap Ψ.toMonoidHom (K0 𝔭)) ⊔
        AuxB K L M).restrictScalars ℚ
        = (IntermediateField.fixedField (Subgroup.comap Ψ.toMonoidHom (K0 𝔭))).restrictScalars ℚ
          ⊔ (AuxB K L M).restrictScalars ℚ :=
      (IntermediateField.restrictScalars_sup ℚ
        (IntermediateField.fixedField (Subgroup.comap Ψ.toMonoidHom (K0 𝔭))) (AuxB K L M)).symm
    have h6 : (AuxB K L M).restrictScalars ℚ ≤ S' := by
      intro y hy
      rw [IntermediateField.mem_restrictScalars] at hy
      show y ∈ S'
      rw [AuxB] at hy
      refine IntermediateField.adjoin_induction (F := K)
        (s := ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} :
          Set (CyclotomicField M L)))
        (p := fun y _ => y ∈ S')
        (fun z hz => ?_) (fun k => ?_) (fun y z _ _ hy hz => ?_) (fun y _ hy => ?_)
        (fun y z _ _ hy hz => ?_) hy
      · rw [Set.mem_singleton_iff] at hz
        rw [hz, hSdef]
        exact SetLike.le_def.mp le_sup_right
          (IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _))
      · rw [hSdef]
        exact SetLike.le_def.mp le_sup_left ((IntermediateField.mem_restrictScalars ℚ).mpr
          (IntermediateField.algebraMap_mem _ k))
      · rw [hSdef] at hy hz ⊢; exact add_mem hy hz
      · rw [hSdef] at hy ⊢; exact inv_mem hy
      · rw [hSdef] at hy hz ⊢; exact mul_mem hy hz
    rw [eq_top_iff, ← hEBr, hsup_rat, hSdef]
    exact sup_le le_sup_left h6
  have hsplit : ∀ 𝔭 : s, NK.Chebotarev.IsFrobAtPrime (K := K)
      (L := ↥(IntermediateField.fixedField (Subgroup.comap Ψ.toMonoidHom (K0 𝔭)))) 𝔭.1 1 := by
    intro 𝔭
    have hid : ((𝔓 𝔭).under (NumberField.RingOfIntegers ↥(IntermediateField.fixedField
        (Subgroup.comap Ψ.toMonoidHom (K0 𝔭))))).asIdeal.inertiaDeg
        (NumberField.RingOfIntegers K) = 1 :=
      NK.ChebotarevGeneral.inertiaDeg_under_eq_one (K := K) (N := CyclotomicField M L)
        (IntermediateField.fixedField (Subgroup.comap Ψ.toMonoidHom (K0 𝔭)))
        (h𝔓 𝔭) (hFmem 𝔭) (hF 𝔭)
    exact NK.CFTLib.ARL.inertiaDeg_one_isFrobAtPrime_one (K := K)
      (E := ↥(IntermediateField.fixedField (Subgroup.comap Ψ.toMonoidHom (K0 𝔭)))) 𝔭.1
      ((𝔓 𝔭).under (NumberField.RingOfIntegers
        ↥(IntermediateField.fixedField (Subgroup.comap Ψ.toMonoidHom (K0 𝔭)))))
      (Ideal.LiesOver.mk (by
        rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_under]
        exact (h𝔓 𝔭).over)) hid
  -- ## Step 9: assembly
  have hE𝔭le : ∀ 𝔭 : s, IntermediateField.fixedField
      (Subgroup.comap Ψ.toMonoidHom (K0 𝔭)) ≤ E := by
    intro 𝔭
    rw [hEdef, hHdef]
    exact IntermediateField.fixedField_le
      (iInf_le (fun 𝔭 : s => Subgroup.comap Ψ.toMonoidHom (K0 𝔭)) 𝔭)
  refine ⟨M, hMne, hMcop, hMS, hMa, hdisjAB, ?_⟩
  refine ⟨E, disjoint_iff.mpr hEA, ?_⟩
  intro 𝔭 h𝔭
  exact ⟨IntermediateField.fixedField (Subgroup.comap Ψ.toMonoidHom (K0 ⟨𝔭, h𝔭⟩)),
    hE𝔭le ⟨𝔭, h𝔭⟩, hjoin ⟨𝔭, h𝔭⟩, hsplit ⟨𝔭, h𝔭⟩⟩

end NK.CFTLib.ArtinReciprocityIdeal
