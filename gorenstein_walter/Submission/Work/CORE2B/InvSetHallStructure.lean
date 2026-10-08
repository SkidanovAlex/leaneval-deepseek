import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.HallAux
import Submission.Work.CORE2B.L27_pi_subgroup_in_fittingPi
import Submission.Work.CORE2B.L27_fittingPiIn_le_iSup_singleton
import Submission.OddOrder.BG.Ch3_MaximalSubgroups.S10_HallStructure

/-!
# CORE2B — `I_U(s)` is a Hall subgroup of `F(U)`, normal in `U`

Let `U` be a subgroup of a finite group `G` of **odd** order, and let `s ∈ G` be an involution
(`orderOf s = 2`) normalizing `U` such that for every prime `p` the involution `s` either
centralizes or inverts the whole `p`-core `O_p(U)`.

The main result (`Work.CORE2B.InvSetHallStructure`) is that the set

`I_U(s) = invSet U s = {x ∈ U | s x s⁻¹ = x⁻¹}`

is exactly the underlying set of a subgroup of `G`, namely the `π`-part `F_π(U)` of the Fitting
subgroup of `U` for `π = {p prime | s inverts O_p(U)}`, and that this subgroup is Hall in `F(U)`
and normal in `U`.

The supporting lemmas proved here are

* `fittingPiIn_singleton_le_pCoreIn_local`: `F_q(K) ≤ O_q(K)`;
* `isHallIn_fittingPiIn_local`: `F_π(K)` is Hall in `F(K)` (from the odd-order library's
  `oPiCore_isHall_of_isNilpotent` applied inside the nilpotent group `F(K)`);
* `normalTransfer_local`: `F_π(K) ◁ K`.
-/

open scoped MatrixGroups

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.CORE2B

open Subgroup

/-! ## 1. A `{q}`-subgroup of a finite group is a `q`-subgroup -/

theorem isPGroup_of_isPiSubgroup_singleton_local {H : Type} [Group H] [Finite H] {q : ℕ}
    (hq : q.Prime) {N : Subgroup H} (hN : Subgroup.IsPiSubgroup ({q} : Set ℕ) N) :
    IsPGroup q N := by
  haveI : Fact q.Prime := ⟨hq⟩
  exact (OddOrder.Isaacs.Ch03.Subgroup.isPiGroup_singleton_iff_isPGroup).mp hN

/-! ## 2. `F_q(K) ≤ O_q(K)` -/

/-- The `q`-part of the Fitting subgroup of `K`, viewed in the ambient group, lies in the
`q`-core `O_q(K)`: `O_{⟨q⟩}(F(K))` is characteristic in `F(K) ◁ K`, hence a normal
`q`-subgroup of `K`. -/
theorem fittingPiIn_singleton_le_pCoreIn_local {G : Type} [Group G] [Finite G] (K : Subgroup G)
    {q : ℕ} (hq : q.Prime) :
    Work.GW2.fittingPiIn ({q} : Set ℕ) K ≤ Work.GW2.pCoreIn q K := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI hnormF : (Work.GW2.fitting ↥K).Normal := Subgroup.normalCore_normal _
  haveI hcharA : (Work.GW2.piCore ({q} : Set ℕ) ↥(Work.GW2.fitting ↥K)).Characteristic :=
    L27c_piCore_characteristic ({q} : Set ℕ)
  haveI hNnorm : ((Work.GW2.piCore ({q} : Set ℕ) ↥(Work.GW2.fitting ↥K)).map
      (Work.GW2.fitting ↥K).subtype).Normal := ConjAct.normal_of_characteristic_of_normal
  have hpg : IsPGroup q ↥((Work.GW2.piCore ({q} : Set ℕ) ↥(Work.GW2.fitting ↥K)).map
      (Work.GW2.fitting ↥K).subtype) :=
    IsPGroup.map
      (isPGroup_of_isPiSubgroup_singleton_local hq
        (L27c_isPiSubgroup_piCore ({q} : Set ℕ) (G := ↥(Work.GW2.fitting ↥K))))
      (Work.GW2.fitting ↥K).subtype
  have hale : ((Work.GW2.piCore ({q} : Set ℕ) ↥(Work.GW2.fitting ↥K)).map
      (Work.GW2.fitting ↥K).subtype) ≤ Work.GW2.pCore q ↥K :=
    L27c_le_pCore_of_normal_isPGroup hpg
  exact Subgroup.map_mono (f := K.subtype) hale

/-! ## 3. `F_π(K)` is a Hall subgroup of `F(K)` -/

/-- In a finite group `K`, the `π`-part `F_π(K)` of the Fitting subgroup is Hall in `F(K)`.

Inside the *nilpotent* group `F(K)` the library's `oPiCore_isHall_of_isNilpotent` gives that
`O_π(F(K))` is Hall; the statement follows because both the cardinality of `F_π(K)` and the
relative index `[F(K) : F_π(K)]` are those computed inside `F(K)`. -/
theorem isHallIn_fittingPiIn_local {G : Type} [Group G] [Finite G] (K : Subgroup G) (π : Set ℕ) :
    Work.GW2.IsHallIn (Work.GW2.fittingPiIn π K) (Work.GW2.fittingIn K) := by
  haveI : Group.IsNilpotent ↥(Work.GW2.fitting ↥K) := fitting_isNilpotent (G := ↥K)
  have hHallA : OddOrder.Isaacs.Ch03.IsHallSubgroup π
      (Work.GW2.piCore π ↥(Work.GW2.fitting ↥K)) := by
    rw [L27c_piCore_eq_oPiCore]
    exact OddOrder.BG.Ch3.S10.oPiCore_isHall_of_isNilpotent π
  have hcopA : Nat.Coprime (Nat.card ↥(Work.GW2.piCore π ↥(Work.GW2.fitting ↥K)))
      (Work.GW2.piCore π ↥(Work.GW2.fitting ↥K)).index := hHallA.coprime_index
  have hcardA : Nat.card (Work.GW2.fittingPiIn π K)
      = Nat.card ↥(Work.GW2.piCore π ↥(Work.GW2.fitting ↥K)) := by
    rw [Work.GW2.fittingPiIn, Work.GW2.fittingPi,
      Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective (Work.GW2.fitting ↥K).subtype_injective]
  have hcardF : Nat.card (Work.GW2.fittingIn K) = Nat.card ↥(Work.GW2.fitting ↥K) := by
    rw [Work.GW2.fittingIn, Subgroup.card_map_of_injective K.subtype_injective]
  have hIleF : Work.GW2.fittingPiIn π K ≤ Work.GW2.fittingIn K :=
    Subgroup.map_mono (Subgroup.map_subtype_le _)
  have hmul : (Work.GW2.fittingPiIn π K).relIndex (Work.GW2.fittingIn K)
      * Nat.card ↥(Work.GW2.piCore π ↥(Work.GW2.fitting ↥K))
      = Nat.card ↥(Work.GW2.piCore π ↥(Work.GW2.fitting ↥K))
        * (Work.GW2.piCore π ↥(Work.GW2.fitting ↥K)).index := by
    have h := Subgroup.relIndex_mul_card (H := Work.GW2.fittingPiIn π K)
      (K := Work.GW2.fittingIn K)
    rw [inf_eq_left.mpr hIleF, hcardA, hcardF] at h
    exact h.trans (Subgroup.card_mul_index _).symm
  have hidx : (Work.GW2.fittingPiIn π K).relIndex (Work.GW2.fittingIn K)
      = (Work.GW2.piCore π ↥(Work.GW2.fitting ↥K)).index := by
    have h := hmul
    rw [mul_comm (Nat.card ↥(Work.GW2.piCore π ↥(Work.GW2.fitting ↥K)))
      (Work.GW2.piCore π ↥(Work.GW2.fitting ↥K)).index] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos) h
  refine ⟨hIleF, ?_⟩
  rw [hidx, hcardA]
  exact hcopA

/-! ## 4. `F_π(K) ◁ K` -/

/-- `F_π(K) = O_π(F(K))` is normal in `K`. -/
theorem normalTransfer_local {G : Type} [Group G] [Finite G] (K : Subgroup G) (π : Set ℕ) :
    ((Work.GW2.fittingPiIn π K).subgroupOf K).Normal := by
  haveI hnormF : (Work.GW2.fitting ↥K).Normal := Subgroup.normalCore_normal _
  haveI hcharA : (Work.GW2.piCore π ↥(Work.GW2.fitting ↥K)).Characteristic :=
    L27c_piCore_characteristic π
  haveI hNnorm : ((Work.GW2.piCore π ↥(Work.GW2.fitting ↥K)).map
      (Work.GW2.fitting ↥K).subtype).Normal := ConjAct.normal_of_characteristic_of_normal
  exact Subgroup.normal_subgroupOf_of_le_normalizer
    (le_normalizer_map_subtype_local K (Work.GW2.fittingPi π ↥K) ‹_›)

/-! ## 5. The main theorem -/

theorem InvSetHallStructure (hFT : Work.GW2.FeitThompsonProp) {G : Type} [Group G] [Finite G]
    (U : Subgroup G) (s : G) (hoddU : Odd (Nat.card U)) (hs2 : orderOf s = 2)
    (hsN : s ∈ Subgroup.normalizer (U : Set G))
    (hH1 : ∀ p : ℕ, Nat.Prime p →
      (∀ z ∈ Work.GW2.pCoreIn p U, s * z * s⁻¹ = z) ∨
      (∀ z ∈ Work.GW2.pCoreIn p U, s * z * s⁻¹ = z⁻¹)) :
    ∃ I : Subgroup G, (I : Set G) = Work.GW2.invSet U s ∧
      Work.GW2.IsHallIn I (Work.GW2.fittingIn U) ∧ (I.subgroupOf U).Normal := by
  -- `s` is an involution
  have hs : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs2] at h
    simpa [pow_two] using h
  -- `U` is solvable (Feit–Thompson)
  have hsolv : Group.IsSolvable ↥U := hFT ↥U hoddU
  -- `I_U(s)` centralizes `F(U)` and lies in it
  have hcen : ∀ x ∈ Work.GW2.invSet U s, ∀ y ∈ Work.GW2.fittingIn U, x * y = y * x :=
    invSet_le_centralizer_fittingIn U s hoddU hs hsN hH1
  have hIleF : ∀ x ∈ Work.GW2.invSet U s, x ∈ Work.GW2.fittingIn U :=
    invSet_le_fittingIn U s hsolv hcen
  -- the prime set of the primes whose whole `p`-core is inverted
  let P : Set ℕ := {p : ℕ | Nat.Prime p ∧ ∀ z ∈ Work.GW2.pCoreIn p U, s * z * s⁻¹ = z⁻¹}
  -- `invSet U s` is closed under multiplication, inverses and contains `1`
  let I : Subgroup G :=
    { carrier := Work.GW2.invSet U s
      mul_mem' := by
        intro a b ha hb
        refine ⟨U.mul_mem ha.1 hb.1, ?_⟩
        have hcomm : b * a = a * b := hcen b hb a (hIleF a ha)
        have h1 : s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) := by group
        have h2 : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by rw [← hcomm, mul_inv_rev]
        rw [h1, ha.2, hb.2, h2]
      one_mem' := ⟨U.one_mem, by simp⟩
      inv_mem' := by
        intro a ha
        refine ⟨U.inv_mem ha.1, ?_⟩
        have h1 : s * a⁻¹ * s⁻¹ = (s * a * s⁻¹)⁻¹ := by group
        rw [h1, ha.2] }
  have hIcarrier : (I : Set G) = Work.GW2.invSet U s := rfl
  -- (i) `F_P(U) ≤ I_U(s)`: the inverted `p`-cores generate `F_P(U)` and lie in `I_U(s)`
  have hJ_le_I : Work.GW2.fittingPiIn P U ≤ I := by
    refine (L27_fittingPiIn_le_iSup_singleton P U).trans ?_
    refine iSup_le fun q => iSup_le fun hq => ?_
    refine (fittingPiIn_singleton_le_pCoreIn_local U hq.1).trans ?_
    intro z hz
    exact ⟨(in_le_self U q ∅).2.1 hz, hq.2 z hz⟩
  -- (ii) `I_U(s) ≤ F_P(U)`: every inverted element is a `P`-element of `F(U)`
  have hI_le_J : I ≤ Work.GW2.fittingPiIn P U := by
    intro x hx
    have hxF : x ∈ Work.GW2.fittingIn U := hIleF x hx
    -- all powers of `x` are inverted
    have hpow : ∀ k : ℤ, x ^ k ∈ Work.GW2.invSet U s := by
      intro k
      refine ⟨U.zpow_mem hx.1 k, ?_⟩
      have h1 : (MulAut.conj s) (x ^ k) = ((MulAut.conj s) x) ^ k := map_zpow (MulAut.conj s) x k
      have h2 : (MulAut.conj s) x = x⁻¹ := by simpa [MulAut.conj_apply] using hx.2
      have h3 : (MulAut.conj s) (x ^ k) = (x ^ k)⁻¹ := by rw [h1, h2, inv_zpow]
      simpa [MulAut.conj_apply] using h3
    -- `⟨x⟩` is a `P`-subgroup
    have hpi : Subgroup.IsPiSubgroup P (Subgroup.zpowers x) := by
      intro q hqmem
      have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hqmem
      have hdvd : q ∣ orderOf x := by
        rw [← Nat.card_zpowers]
        exact Nat.dvd_of_mem_primeFactors hqmem
      refine ⟨hqprime, ?_⟩
      -- if `s` did not invert `O_q(U)` then, by `hH1`, it would centralize it
      by_contra hnf
      have hcenq : ∀ z ∈ Work.GW2.pCoreIn q U, s * z * s⁻¹ = z :=
        (hH1 q hqprime).resolve_right hnf
      haveI : Fact q.Prime := ⟨hqprime⟩
      -- an element `y` of order `q` inside `⟨x⟩`, hence inverted by `s`
      obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card'
        (G := ↥(Subgroup.zpowers x)) q (by rwa [Nat.card_zpowers])
      have hyzp : ((y : ↥(Subgroup.zpowers x)) : G) ∈ Subgroup.zpowers x := y.2
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyzp
      have hyinv : ((y : ↥(Subgroup.zpowers x)) : G) ∈ Work.GW2.invSet U s := by
        rw [← hk]
        exact hpow k
      have hyord' : orderOf ((y : ↥(Subgroup.zpowers x)) : G) = q :=
        (Subgroup.orderOf_coe y).trans hyord
      -- `y ∈ O_q(U)`
      have hyF : ((y : ↥(Subgroup.zpowers x)) : G) ∈ Work.GW2.fittingIn U :=
        hIleF _ hyinv
      have hypg : IsPGroup q ↥(Subgroup.zpowers ((y : ↥(Subgroup.zpowers x)) : G)) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyord', pow_one])
      have hypi : Subgroup.IsPiSubgroup ({q} : Set ℕ)
          (Subgroup.zpowers ((y : ↥(Subgroup.zpowers x)) : G)) :=
        Subgroup.isPiSubgroup_of_isPGroup_of_mem hypg (Set.mem_singleton q)
      have hypcore : ((y : ↥(Subgroup.zpowers x)) : G) ∈ Work.GW2.pCoreIn q U :=
        ((L27_pi_subgroup_in_fittingPi U
            (Subgroup.zpowers ((y : ↥(Subgroup.zpowers x)) : G)) ({q} : Set ℕ)
            (Subgroup.zpowers_le.mpr hyF) hypi).trans
          (fittingPiIn_singleton_le_pCoreIn_local U hqprime))
          (Subgroup.mem_zpowers _)
      -- `s` fixes `y` but inverts it, forcing `y` to be an involution in the odd-order `U`
      have hfix : s * ((y : ↥(Subgroup.zpowers x)) : G) * s⁻¹ = ((y : ↥(Subgroup.zpowers x)) : G) :=
        hcenq _ hypcore
      have hinv' : s * ((y : ↥(Subgroup.zpowers x)) : G) * s⁻¹
          = ((y : ↥(Subgroup.zpowers x)) : G)⁻¹ := hyinv.2
      have hsq : ((y : ↥(Subgroup.zpowers x)) : G) * ((y : ↥(Subgroup.zpowers x)) : G) = 1 := by
        have heq : ((y : ↥(Subgroup.zpowers x)) : G) = ((y : ↥(Subgroup.zpowers x)) : G)⁻¹ :=
          hfix.symm.trans hinv'
        nth_rewrite 2 [heq]
        exact mul_inv_cancel ((y : ↥(Subgroup.zpowers x)) : G)
      have h2dvd : orderOf ((y : ↥(Subgroup.zpowers x)) : G) ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one, pow_two]
        exact hsq
      have hodd_y : Odd (orderOf ((y : ↥(Subgroup.zpowers x)) : G)) :=
        Odd.of_dvd_nat hoddU (Subgroup.orderOf_dvd_natCard U hyinv.1)
      have hq2 : q = 2 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp (hyord' ▸ h2dvd) with h | h
        · exact absurd h hqprime.ne_one
        · exact h
      rw [hyord', hq2] at hodd_y
      exact hodd_y.not_two_dvd_nat (dvd_refl 2)
    exact (L27_pi_subgroup_in_fittingPi U (Subgroup.zpowers x) P
      (Subgroup.zpowers_le.mpr hxF) hpi) (Subgroup.mem_zpowers x)
  have hIJ : I = Work.GW2.fittingPiIn P U := le_antisymm hI_le_J hJ_le_I
  refine ⟨I, hIcarrier, ?_, ?_⟩
  · rw [hIJ]
    exact isHallIn_fittingPiIn_local U P
  · rw [hIJ]
    exact normalTransfer_local U P

end Work.CORE2B
