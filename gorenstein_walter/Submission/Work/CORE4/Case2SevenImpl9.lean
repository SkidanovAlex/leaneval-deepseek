import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2Seven
import Submission.Work.CORE4.Case2Six9Aux.exists_witness_of_case2pre
import Submission.Work.CORE4.Case2SixEmbed
import Submission.Work.CORE4.Case2SevenCentralizer
import Submission.Work.CORE4.Case2SevenReduction
import Submission.Work.CORE4.Case2SevenRemainingOfCtx
import Submission.Work.CORE4.SevenX.piF_le_pi_K0_of_witness
import Submission.Work.CORE4.SixThree
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2SevenAux
import Submission.Work.CORE4.Case2EightObjExists
import Submission.Work.CORE4.A7V
import Submission.Work.CORE4.SevenRemain.odd_le_U_inf_M
import Submission.Work.CORE4.SevenRemain.fittingIn_M_pi_subset
import Submission.Work.CORE4.SevenNine.O2_HM_eq_O2_H
import Submission.Work.CORE4.SevenNine.pi_comm_SM_B0
import Submission.OddOrder.FeitThompson
import Submission.OddOrder.Isaacs.Ch05_Transfer.Basic

namespace Work.CORE4

open Work.GW2 Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## Design-pass-9 assembly of Bender §4 (7)

The leaf `Work.GW2.Case2SevenImpl` is stated at the `Case2Ctx6` level: for `BenderCtx G`,
`B : BenderSetup G` with `Case2 B`, `C : Case2Ctx6 B` (§4 (1)–(6)) and
`Case2PrePlus B C.D`, produce the six conjuncts of `Case2SevenFacts B C.D`.

Three of the six conjuncts (`O₂(H ⊓ M) = O₂(H)`, `π(F(M)) ⊆ π(F(U))` and `π⁅S ⊓ M, B₀⁆ ⊆ π`) are
proved in the sibling modules of `Submission/Work/CORE4/SevenNine/`; the remaining three
(`π(K₀) = π = π(F(U))`, `π(U ⊓ C_G(K₀F)) = π` and `π(K) ⊆ π`) are proved here. -/

/-! ## §4 (6): the witness, at the `Case2Ctx6` level -/

/-- Bender §4 (6) (p. 225), the witness `∃ g ∉ M, F^g ≤ F(U) ⊓ M`: at the `Case2Ctx6` level it is
a consequence of `Case2Pre` alone (`Submission.Work.CORE4.Case2Six9Aux`). -/
theorem exists_witness_case2ctx6 (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B) :
    ∃ g : G, g ∉ C.D.M ∧ Work.GW2.conjSub g C.D.F ≤ Work.GW2.fittingIn B.U ⊓ C.D.M :=
  Work.CORE4.Case2Six9Aux.exists_witness_of_case2pre I hbc C.D C.pre

/-! ## Conjunct 2: `π(K₀) = π(F(U))` -/

/-- Bender §4 (7), conjunct 2: `π(K₀) = π(F(U))`, from the §4 (6)-witness and Bender's
`X`-argument (`SevenX.piF_le_pi_K0_of_witness` + `conj2_iff_piF_uncond`). -/
theorem primesOf_K0_eq_piFU9 (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h2 : Work.GW2.Case2 B) (C : Work.GW2.Case2Ctx6 B)
    (hplus : Work.GW2.Case2PrePlus B C.D) :
    Work.GW2.primesOf C.D.K0 = B.piFU :=
  (Work.CORE4.conj2_iff_piF_uncond I hbc B C.D C.pre h2).mpr
    (Work.CORE4.SevenX.piF_le_pi_K0_of_witness I G hbc B h2 C hplus
      (exists_witness_case2ctx6 I hbc B C))

/-! ## Conjunct 4: `π(K) ⊆ π(F(U))` -/

/-- Bender §4 (7), conjunct 4: `π(K) ⊆ π`.  `K ≤ U` (§4 (1)) and `K` centralizes `K₀F`:
`K₀ ≤ K` and `K` is cyclic, while `F` commutes with `K` elementwise
(`Work.CORE4.F_commute_K_c4`).  Hence `K ≤ U ⊓ C_G(K₀ ⊔ F)` and conjunct 3
(`Work.CORE4.Case2SevenCentralizer`) identifies `π` of that subgroup with `π(F(U))`. -/
theorem primesOf_K_subset9 (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h2 : Work.GW2.Case2 B) (C : Work.GW2.Case2Ctx6 B)
    (hplus : Work.GW2.Case2PrePlus B C.D) :
    Work.GW2.primesOf C.D.K ⊆ B.piFU := by
  haveI : IsCyclic ↥C.D.K := Work.GW2.Case2Pre.K_cyclic B C.D C.pre
  -- `K` is abelian, hence centralizes `K₀ ≤ K`
  have hKleCK : C.D.K ≤ Subgroup.centralizer ((C.D.K : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr IsCyclic.isMulCommutative
  have hKleCK0 : C.D.K ≤ Subgroup.centralizer ((C.D.K0 : Subgroup G) : Set G) :=
    hKleCK.trans (Subgroup.centralizer_le (inf_le_right : C.D.K0 ≤ C.D.K))
  -- `F` commutes with `K` elementwise
  have hKleCF : C.D.K ≤ Subgroup.centralizer ((C.D.F : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact F_commute_K_c4 I B C.D C.pre f hf k hk
  have hKleC : C.D.K ≤ Subgroup.centralizer (((C.D.K0 ⊔ C.D.F : Subgroup G)) : Set G) :=
    (le_inf hKleCK0 hKleCF).trans (centralizer_inf_le_centralizer_sup C.D.K0 C.D.F)
  have hKle : C.D.K ≤ B.U ⊓ Subgroup.centralizer (((C.D.K0 ⊔ C.D.F : Subgroup G)) : Set G) :=
    le_inf (Work.GW2.Case2Data.K_le_U B C.D) hKleC
  exact (Work.CORE4.SevenX.PiFU.primesOf_mono hKle).trans
    (le_of_eq (Work.CORE4.Case2SevenCentralizer I G hbc B C h2 hplus))

/-! ## Conjunct 5: `π(F(M)) ⊆ π(F(U))`

The route is Bender's own, as reconstructed in `NOTES_LEAD_gw_design12.md`:

* `O₂(C.D.M) = ⊥`: `O₂(M) ≤ O₂(Ĥ)` (`I.thm26` together with Bender 1.1(iv), applied twice), and
  then the coatom/involution-fusion argument of
  `Submission.Work.CORE2B.L27su_eq_bot_of_le_pCoreIn_Hhat`.  That module cannot be imported here
  (it declares the `Work.GW2` vocabulary of the area `CORE2B`, clashing with
  `Submission.Work.CORE4.Defs`), so the argument is reproduced in this file;
* `F(M)` is odd, hence — being `≤ C_M(E(M)) ≤ C_G(t) = H ⊓ M` — lies in `U ⊓ M`;
* the `π`-inclusion is then Bender's 1.1(iv) argument, a copy of
  `SevenRemain.fittingIn_M_pi_subset`'s proof with `Case2Ctx` read as `Case2Pre`. -/

/-- A non-abelian finite simple group has even order. -/
theorem even_card_of_isSimpleGroup_nonabelian_9 (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) : Even (Nat.card G) := by
  by_contra hodd'
  have hodd : Odd (Nat.card G) := Nat.not_even_iff_odd.mp hodd'
  have hsolv : Group.IsSolvable G := OddOrder.feitThompson hodd
  obtain ⟨a, b, hab⟩ := hnonab
  exact hab ((@IsSimpleGroup.comm_iff_isSolvable G _ hsimple).mpr hsolv a b)

/-- Every Sylow `2`-subgroup of a `BenderCtx` group is non-cyclic. -/
theorem not_isCyclic_sylow_9 (hbc : Work.GW2.BenderCtx G) (S : Sylow 2 G) :
    ¬ IsCyclic ↥(S : Subgroup G) := by
  intro hcyc
  have hnonab : ¬ IsMulCommutative G := fun hc => by
    obtain ⟨a, b, hab⟩ := hbc.nonab
    exact hab (@mul_comm' G _ hc a b)
  by_cases hbot : (S : Subgroup G) = ⊥
  · exact (Sylow.ne_bot_of_dvd_card S
      (even_iff_two_dvd.mp (even_card_of_isSimpleGroup_nonabelian_9 hbc.simple hbc.nonab))) hbot
  · exact (OddOrder.Isaacs.Ch05.not_isSimpleGroup_of_isCyclic_sylow_two
      (G := G) (hPcyc := hcyc) hnonab S hbot) hbc.simple

/-- `S ≅ DihedralGroup n` with `n ≥ 2`. -/
theorem S_dihedral_9 (hbc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n) := by
  have hnc : ¬ IsCyclic ↥(B.S : Subgroup G) := not_isCyclic_sylow_9 hbc B.S
  rcases hbc.sylow B.S with h | ⟨n, ⟨e⟩⟩
  · exact absurd h hnc
  · refine ⟨n, ?_, ⟨e⟩⟩
    have hcard : Nat.card ↥(B.S : Subgroup G) = 2 * n := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    by_contra hn2
    have hpos : 0 < Nat.card ↥(B.S : Subgroup G) := Nat.card_pos
    have hn1 : n = 1 := by omega
    exact hnc ((MulEquiv.isCyclic e).mpr (DihedralGroup.isCyclic_iff.mpr hn1))

/-- Bender p. 219: `H = U · S` (`U = O(H)` odd, `S` the dihedral Sylow `2`-subgroup). -/
theorem H_eq_U_sup_S_9 (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) : B.H = B.U ⊔ B.S := by
  obtain ⟨n, hn2, ⟨e⟩⟩ := S_dihedral_9 hbc B
  exact (I.toolkit.split G B.S n hn2 ⟨e⟩ B.t (B.S0_le B.t_mem) B.t_order
    (Work.GW2.BenderSetup.t_central B)).symm

/-- `2^a ∣ 2^b * c` with `c` odd implies `a ≤ b`. -/
theorem pow_two_dvd_pow_two_mul_odd_9 {a b c : ℕ} (hc : Odd c) (h : 2 ^ a ∣ 2 ^ b * c) : a ≤ b := by
  have hcop : Nat.Coprime (2 ^ a) c := (Nat.coprime_two_left.mpr hc).pow_left a
  have h1 : 2 ^ a ∣ 2 ^ b := hcop.dvd_of_dvd_mul_right h
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h1

/-- A group of order `2` is cyclic. -/
theorem isCyclic_of_card_two_9 {H : Type*} [Group H] [Finite H] (h : Nat.card H = 2) :
    IsCyclic H := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 (by rw [h])
  have hle : Nat.card ↥(⊤ : Subgroup H) ≤ Nat.card ↥(Subgroup.zpowers x) := by
    rw [Subgroup.card_top, Nat.card_zpowers, hx, h]
  have hzx : Subgroup.zpowers x = ⊤ := Subgroup.eq_of_le_of_card_ge le_top hle
  refine ⟨x, fun y => ?_⟩
  have hy : y ∈ Subgroup.zpowers x := by rw [hzx]; exact Subgroup.mem_top y
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact ⟨n, hn⟩

/-- A normal `2`-subgroup of `M` lies in the Sylow `S ⊓ M` of `M`. -/
theorem le_sylow_inf_9 (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case2Data B)
    (hodd : ¬ 2 ∣ ((B.S : Subgroup G) ⊓ D.M).relIndex D.M)
    {Q : Subgroup G} (hQp : IsPGroup 2 Q) (hQN : D.M ≤ Subgroup.normalizer (Q : Set G))
    (hQle : Q ≤ D.M) : Q ≤ (B.S : Subgroup G) ⊓ D.M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A : Subgroup G := (B.S : Subgroup G) ⊓ D.M with hA
  have hAle : A ≤ D.M := inf_le_right
  have hAp : IsPGroup 2 ↥A := B.S.isPGroup'.to_le inf_le_left
  have hAleNQ : A ≤ Subgroup.normalizer (Q : Set G) := hAle.trans hQN
  have hQA : IsPGroup 2 ↥(Q ⊔ A) := hQp.to_sup_of_normal_left' hAp hAleNQ
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hQA
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hAp
  -- `|M| = |A| * odd`
  have hAcard : Nat.card ↥(A.subgroupOf D.M) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAle).toEquiv
  have hMcard : A.relIndex D.M * Nat.card ↥A = Nat.card ↥D.M := by
    have h1 := Subgroup.index_mul_card (A.subgroupOf D.M)
    rw [hAcard] at h1
    exact h1
  have hodd' : Odd (A.relIndex D.M) :=
    Nat.not_even_iff_odd.mp (by rw [even_iff_two_dvd]; exact hodd)
  have hdiv : 2 ^ a ∣ Nat.card ↥D.M := by
    rw [← ha]
    exact Subgroup.card_dvd_of_le (sup_le hQle hAle)
  have hle_ab : a ≤ b := by
    refine pow_two_dvd_pow_two_mul_odd_9 hodd' ?_
    rw [← hb, mul_comm, hMcard]
    exact hdiv
  have hle_ba : b ≤ a := by
    have h1 : 2 ^ b ∣ 2 ^ a := by
      rw [← hb, ← ha]
      exact Subgroup.card_dvd_of_le le_sup_right
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h1
  have hab : a = b := le_antisymm hle_ab hle_ba
  have hcard : Nat.card ↥(Q ⊔ A) = Nat.card ↥A := by rw [ha, hb, hab]
  have heq : Q ⊔ A = A :=
    (Subgroup.eq_of_le_of_card_ge le_sup_right (le_of_eq hcard)).symm
  exact le_sup_left.trans (le_of_eq heq)

/-- A nontrivial finite `2`-group contains an element of order `2`. -/
theorem exists_involution_of_isPGroup_two_9 {Q : Subgroup G} (hQp : IsPGroup 2 Q) (hQne : Q ≠ ⊥) :
    ∃ z ∈ Q, orderOf z = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard1 : Nat.card ↥Q ≠ 1 := fun h => hQne (Subgroup.card_eq_one.mp h)
  rcases hQp.card_eq_or_dvd with h | h
  · exact absurd h hcard1
  · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h
    exact ⟨(x : G), x.2, by rw [← Subgroup.orderOf_mk]; exact hx⟩

/-- **Bender 1981, Lemma 2.7 (p. 221), the step `O₂(M) = 1`** for a `Case2Ctx6` group.

`O₂(M) ≤ O₂(Ĥ)` by Theorem 2.6 and Bender 1.1(iv) (applied to `K = F(U)` and then `K = U`); then
the coatom/involution-fusion argument of
`Submission.Work.CORE2B.L27su_eq_bot_of_le_pCoreIn_Hhat` gives `O₂(M) = ⊥`. -/
theorem pCoreIn_two_M_eq_bot_9 (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B)
    (hplus : Work.GW2.Case2PrePlus B C.D) :
    Work.GW2.pCoreIn 2 C.D.M = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup G := hbc.simple
  by_contra hne
  set Q : Subgroup G := Work.GW2.pCoreIn 2 C.D.M with hQ
  have hQp : IsPGroup 2 Q := by rw [hQ]; exact Work.CORE4.A7V_isPGroup_pCoreIn 2 C.D.M
  have hQleM : Q ≤ C.D.M := by rw [hQ]; exact Subgroup.map_subtype_le _
  have hQN : C.D.M ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQ]
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      simpa using Work.CORE4.A7V_conj_mem_pCoreIn 2 C.D.M hm hx
    · intro hx
      have h := Work.CORE4.A7V_conj_mem_pCoreIn 2 C.D.M (C.D.M.inv_mem hm) hx
      have heq : m⁻¹ * (m * x * m⁻¹) * (m⁻¹)⁻¹ = x := by group
      rwa [heq] at h
  -- `Q ≤ S ⊓ M`
  have hQS : Q ≤ (B.S : Subgroup G) ⊓ C.D.M :=
    le_sylow_inf_9 B C.D hplus.1 hQp hQN hQleM
  have hQleH : Q ≤ B.H := (hQS.trans inf_le_left).trans B.S_le_H
  -- `[Q, U ⊓ M] = 1`
  have hQinfUM : Q ⊓ (B.U ⊓ C.D.M) = ⊥ := by
    refine Subgroup.card_eq_one.mp ?_
    have h1 : Nat.card ↥(Q ⊓ (B.U ⊓ C.D.M)) ∣ Nat.card ↥Q :=
      Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(Q ⊓ (B.U ⊓ C.D.M)) ∣ Nat.card ↥(B.U ⊓ C.D.M) :=
      Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨n, hn⟩ := hQp.exists_card_eq
    have h1' : Nat.card ↥(Q ⊓ (B.U ⊓ C.D.M)) ∣ 2 ^ n := by rw [← hn]; exact h1
    have hodd : Odd (Nat.card ↥(B.U ⊓ C.D.M)) :=
      Odd.of_dvd_nat B.U_odd (Subgroup.card_dvd_of_le (inf_le_left : B.U ⊓ C.D.M ≤ B.U))
    exact Nat.eq_one_of_dvd_coprimes
      (((Nat.coprime_two_left.mpr hodd).symm).pow_right n) h2 h1'
  have hUMnormal : ((B.U ⊓ C.D.M).subgroupOf (B.H ⊓ C.D.M)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (le_inf (le_trans inf_le_left B.U_le_H) inf_le_right)).mpr (by
        intro x hx
        obtain ⟨hxH, hxM⟩ := Subgroup.mem_inf.mp hx
        exact Subgroup.inf_normalizer_le_normalizer_inf (H := B.U) (K := C.D.M)
          ⟨(Subgroup.normal_subgroupOf_iff_le_normalizer B.U_le_H).mp B.U_normal hxH,
            Subgroup.le_normalizer hxM⟩)
  have hQleHMinf : Q ≤ B.H ⊓ C.D.M := le_inf hQleH hQleM
  have hQnorm' : (Q.subgroupOf (B.H ⊓ C.D.M)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQleHMinf).mpr (inf_le_right.trans hQN)
  have hQleCUM : Q ≤ Subgroup.centralizer (((B.U ⊓ C.D.M) : Subgroup G) : Set G) :=
    Work.CORE4.A7V_le_centralizer_of_normal_inf_eq_bot hQleHMinf
      (le_inf (le_trans inf_le_left B.U_le_H) inf_le_right) hQnorm' hUMnormal hQinfUM
  -- `Q ≤ C_G(K₀F)`
  have hK0FleUM : C.D.K0 ⊔ C.D.F ≤ B.U ⊓ C.D.M :=
    sup_le (le_inf (le_trans inf_le_left (Subgroup.map_subtype_le (Work.GW2.fitting ↥B.U)))
        (le_trans inf_le_right (Work.GW2.Case2Data.K_le_M B C.D)))
      (Work.GW2.Case2Data.F_le_UinfM B C.D)
  have hQleCK0F : Q ≤ Subgroup.centralizer (((C.D.K0 ⊔ C.D.F) : Subgroup G) : Set G) :=
    hQleCUM.trans (Subgroup.centralizer_le hK0FleUM)
  -- Bender 1.1(iv) with `K = F(U)`, `K₀ = K₀F`
  have hFUodd : Odd (Nat.card ↥(Work.GW2.fittingIn B.U)) :=
    Odd.of_dvd_nat B.U_odd (Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _))
  have hK0FleFU : C.D.K0 ⊔ C.D.F ≤ Work.GW2.fittingIn B.U :=
    sup_le inf_le_left (Work.GW2.Case2Data.F_le_fitting B C.D)
  have hSix : Work.GW2.fittingIn B.U ⊓ C.D.M = C.D.K0 ⊔ C.D.F :=
    Work.CORE4.SixThree I G hbc B C.D C.pre
  have hsc : Work.GW2.fittingIn B.U ⊓
      Subgroup.centralizer (((C.D.K0 ⊔ C.D.F) : Subgroup G) : Set G) ≤ C.D.K0 ⊔ C.D.F :=
    Work.CORE4.SevenX.sevenX_fittingIn_inf_centralizer_sup_le B C.D C.pre hSix
  have hQNF : Q ≤ Subgroup.normalizer (Work.GW2.fittingIn B.U : Set G) :=
    hQleH.trans (Work.CORE4.BenderSetup.H_le_normalizer_fittingIn B)
  have hQleFU : Q ≤ Subgroup.centralizer (Work.GW2.fittingIn B.U : Set G) :=
    Work.CORE4.SevenX.sevenX_le_centralizer_of_isNilpotent I.toolkit.c11iv
      (Work.GW2.fittingIn B.U) (C.D.K0 ⊔ C.D.F) Q
      (Work.CORE4.SevenX.PiFU.isNilpotent_fittingIn B.U) hK0FleFU hsc
      Nat.prime_two hQp (Nat.coprime_two_left.mpr hFUodd) hQNF hQleCK0F
  -- Bender 1.1(iv) with `K = U`, `K₀ = F(U)`
  have hUsolv : Group.IsSolvable ↥B.U := I.toolkit.ft ↥B.U B.U_odd
  have hscU : B.U ⊓ Subgroup.centralizer (Work.GW2.fittingIn B.U : Set G) ≤
      Work.GW2.fittingIn B.U := by
    rw [inf_comm]
    exact Work.CORE4.sevenX_centralizer_fittingIn_inf_le_fittingIn B.U hUsolv
  have hQNU : Q ≤ Subgroup.normalizer (B.U : Set G) :=
    hQleH.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer B.U_le_H).mp B.U_normal)
  have hQleCU : Q ≤ Subgroup.centralizer (B.U : Set G) :=
    I.toolkit.c11iv G 2 Q B.U (Work.GW2.fittingIn B.U) hQp
      (Nat.coprime_two_left.mpr B.U_odd) hQNU (Subgroup.map_subtype_le _)
      (Work.CORE4.fittingIn_subgroupOf_normal B.U) hQleFU hscU
  -- `Q ≤ O₂(Ĥ)`
  have hQleO2Hhat : Q ≤ Work.GW2.pCoreIn 2 B.Hhat := by
    rw [← (I.thm26 G I.toolkit.ft hbc B).2.1]
    exact le_inf (hQS.trans inf_le_left) hQleCU
  -- ## The coatom / involution-fusion argument
  set V : Subgroup G := Work.GW2.pCoreIn 2 B.Hhat with hV
  have hQV : Q ≤ V := by rw [hV]; exact hQleO2Hhat
  have hVne : V ≠ ⊥ := fun h => hne (le_bot_iff.mp (hQV.trans (le_of_eq h)))
  have hVleHhat : V ≤ B.Hhat := by rw [hV]; exact Subgroup.map_subtype_le _
  have hHhat_le_NV : B.Hhat ≤ Subgroup.normalizer (V : Set G) := by
    rw [hV]
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      simpa using Work.CORE4.A7V_conj_mem_pCoreIn 2 B.Hhat hh hx
    · intro hx
      have hx2 := Work.CORE4.A7V_conj_mem_pCoreIn 2 B.Hhat (B.Hhat.inv_mem hh) hx
      have heq : h⁻¹ * (h * x * h⁻¹) * (h⁻¹)⁻¹ = x := by group
      rwa [heq] at hx2
  have hNV : Subgroup.normalizer (V : Set G) = B.Hhat := by
    refine le_antisymm ?_ hHhat_le_NV
    by_contra hcon
    have hlt : B.Hhat < Subgroup.normalizer (V : Set G) :=
      lt_of_le_of_ne hHhat_le_NV (fun hh => hcon (le_of_eq hh.symm))
    have htop : Subgroup.normalizer (V : Set G) = ⊤ := B.Hhat_coatom.2 _ hlt
    have hVnorm : V.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff]
      exact eq_top_iff.mpr (le_of_eq htop.symm)
    rcases hVnorm.eq_bot_or_eq_top with hb | ht
    · exact hVne hb
    · exact B.Hhat_coatom.ne_top (top_le_iff.mp (ht ▸ hVleHhat))
  -- `¬ M ≤ Ĥ`
  have hMnotHhat : ¬ C.D.M ≤ B.Hhat := by
    intro hle
    have heq : C.D.M = B.Hhat := by
      by_contra hne''
      exact B.Hhat_coatom.ne_top (C.D.M_coatom.2 _ (lt_of_le_of_ne hle hne''))
    exact Work.GW2.Case2Pre.not_H_le B C.D C.pre (heq.symm ▸ B.H_le_Hhat)
  -- no normal subgroup of index `2` (so that Bender's fusion lemma applies)
  have hNoIndex2 : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
    intro N hN hidx
    haveI : N.Normal := hN
    rcases Subgroup.Normal.eq_bot_or_eq_top N with hb | ht
    · rw [hb, Subgroup.index_bot] at hidx
      haveI : IsCyclic G := isCyclic_of_card_two_9 hidx
      obtain ⟨a, b, hab⟩ := hbc.nonab
      exact hab (@mul_comm' G _ IsCyclic.isMulCommutative a b)
    · rw [ht, Subgroup.index_top] at hidx
      exact absurd hidx (by norm_num)
  obtain ⟨n, hn2, ⟨eS⟩⟩ := S_dihedral_9 hbc B
  have hfus := I.toolkit.fus G B.S n hn2 ⟨eS⟩ hNoIndex2
  have ht_ne_one : B.t ≠ 1 := by
    intro h
    have h2 := B.t_order
    rw [h] at h2
    simp at h2
  -- `t ∈ V`
  have htV : B.t ∈ V := by
    rw [hV, ← (I.thm26 G I.toolkit.ft hbc B).2.1]
    refine Subgroup.mem_inf.mpr ⟨B.S0_le B.t_mem, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro u hu
    exact (Subgroup.mem_centralizer_iff.mp (B.U_le_H hu) B.t rfl).symm
  rcases (I.thm26 G I.toolkit.ft hbc B).2.2 with ⟨hVS0, -⟩ | ⟨hfour, -, -⟩
  · -- `V ≤ S₀`: `V` is cyclic, so its unique involution is `t`
    obtain ⟨z, hzQ, hz2⟩ := exists_involution_of_isPGroup_two_9 hQp hne
    have hzV : z ∈ V := hQV hzQ
    have huniq : ∀ {a b : G}, a ∈ B.S0 → b ∈ B.S0 → orderOf a = 2 → orderOf b = 2 → a = b := by
      intro a b ha hb ha2 hb2
      haveI : IsCyclic ↥B.S0 := B.S0_cyclic
      exact congrArg Subtype.val (Work.GW2.eq_orderOf_eq_two_of_isCyclic
        (H := ↥B.S0) (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
        (by rw [Subgroup.orderOf_mk]; exact ha2)
        (by rw [Subgroup.orderOf_mk]; exact hb2))
    have hzt : z = B.t := huniq (hVS0 hzV) B.t_mem hz2 B.t_order
    refine hMnotHhat ?_
    intro m hm
    have htQ : B.t ∈ Q := hzt ▸ hzQ
    have hconj : m * B.t * m⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hQN hm) B.t).mp htQ
    have hord : orderOf (m * B.t * m⁻¹) = 2 := by
      have hsemi : SemiconjBy m B.t (m * B.t * m⁻¹) := by
        show m * B.t = (m * B.t * m⁻¹) * m
        group
      exact (SemiconjBy.orderOf_eq m hsemi).symm.trans B.t_order
    have heq : m * B.t * m⁻¹ = B.t := huniq (hVS0 (hQV hconj)) B.t_mem hord B.t_order
    have hcomm : B.t * m = m * B.t := by
      calc B.t * m = m * B.t * m⁻¹ * m := by rw [heq]
        _ = m * B.t := by group
    exact B.H_le_Hhat (by
      show m ∈ Subgroup.centralizer ({B.t} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hcomm)
  · -- `V` is a four-group
    by_cases hQVeq : Q = V
    · exact hMnotHhat ((hQVeq ▸ hQN).trans (le_of_eq hNV))
    · obtain ⟨z, hzQ, hz2⟩ := exists_involution_of_isPGroup_two_9 hQp hne
      have hzV : z ∈ V := hQV hzQ
      have hcardQ : Nat.card ↥Q = 2 := by
        have hVc : Nat.card ↥V = 4 := hfour.1
        have hdvd : Nat.card ↥Q ∣ Nat.card ↥V := Subgroup.card_dvd_of_le hQV
        have hne1 : Nat.card ↥Q ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
        have hne4 : Nat.card ↥Q ≠ 4 := fun h =>
          hQVeq (Subgroup.eq_of_le_of_card_ge hQV (le_of_eq (by rw [hVc, h])))
        have hdvd2 : Nat.card ↥Q ∣ 2 ^ 2 := by simpa [hVc] using hdvd
        obtain ⟨k, hk, hkx⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
        have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
        rcases hk3 with rfl | rfl | rfl
        · rw [pow_zero] at hkx; exact absurd hkx hne1
        · simpa using hkx
        · norm_num at hkx; exact absurd hkx hne4
      have hz1 : z ≠ 1 := by intro h; rw [h] at hz2; simp at hz2
      -- `M ≤ C_G(z)`
      have hMcent : C.D.M ≤ Subgroup.centralizer ({z} : Set G) := by
        haveI : IsCyclic ↥Q := isCyclic_of_card_two_9 hcardQ
        intro m hm
        have hconj : m * z * m⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hQN hm) z).mp hzQ
        have hord : orderOf (m * z * m⁻¹) = 2 := by
          have hsemi : SemiconjBy m z (m * z * m⁻¹) := by
            show m * z = (m * z * m⁻¹) * m
            group
          exact (SemiconjBy.orderOf_eq m hsemi).symm.trans hz2
        have heq : m * z * m⁻¹ = z := by
          have h2 : (⟨m * z * m⁻¹, hconj⟩ : ↥Q) = ⟨z, hzQ⟩ :=
            Work.GW2.eq_orderOf_eq_two_of_isCyclic
              (H := ↥Q) (a := ⟨m * z * m⁻¹, hconj⟩) (b := ⟨z, hzQ⟩)
              (by rw [Subgroup.orderOf_mk]; exact hord)
              (by rw [Subgroup.orderOf_mk]; exact hz2)
          exact congrArg Subtype.val h2
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        calc z * m = (m * z * m⁻¹) * m := by rw [heq]
          _ = m * z := by group
      -- fusion on the four-group `V`
      obtain ⟨g, hgNV, hgtz⟩ := hfus.2 V hfour B.t htV z hzV ht_ne_one hz1
      have hgH : g ∈ B.Hhat := le_of_eq hNV hgNV
      refine hMnotHhat ?_
      intro m hm
      have hcm : m * z * m⁻¹ = z := by
        have h1 : m * z = z * m :=
          (Subgroup.mem_centralizer_iff.mp (hMcent hm) z (Set.mem_singleton z)).symm
        rw [h1, mul_assoc, mul_inv_cancel, mul_one]
      have hfix : m * (g * B.t * g⁻¹) * m⁻¹ = g * B.t * g⁻¹ := by
        rw [hgtz]; exact hcm
      have hconj : (g⁻¹ * m * g) * B.t * (g⁻¹ * m * g)⁻¹ = B.t := by
        calc (g⁻¹ * m * g) * B.t * (g⁻¹ * m * g)⁻¹
            = g⁻¹ * (m * (g * B.t * g⁻¹) * m⁻¹) * g := by group
          _ = g⁻¹ * (g * B.t * g⁻¹) * g := by rw [hfix]
          _ = B.t := by group
      have hmem : g⁻¹ * m * g ∈ B.H := by
        show g⁻¹ * m * g ∈ Subgroup.centralizer ({B.t} : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        calc B.t * (g⁻¹ * m * g)
            = ((g⁻¹ * m * g) * B.t * (g⁻¹ * m * g)⁻¹) * (g⁻¹ * m * g) := by rw [hconj]
          _ = (g⁻¹ * m * g) * B.t := by group
      have : m = g * (g⁻¹ * m * g) * g⁻¹ := by group
      rw [this]
      exact B.Hhat.mul_mem (B.Hhat.mul_mem hgH (B.H_le_Hhat hmem)) (B.Hhat.inv_mem hgH)

/-! ## The remaining pieces of conjunct 5 -/

/-- `F(M)` is odd. -/
theorem odd_card_fittingIn_M_9 (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B)
    (hplus : Work.GW2.Case2PrePlus B C.D) :
    Odd (Nat.card ↥(Work.GW2.fittingIn C.D.M)) := by
  rw [← Nat.not_even_iff_odd]
  intro h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne0 : Work.GW2.pCore 2 ↥(Work.GW2.fittingIn C.D.M) ≠ ⊥ :=
    Work.CORE4.SevenRemain.pCore_ne_bot_of_isNilpotent_of_dvd G 2 _
      (Work.CORE4.SevenX.PiFU.isNilpotent_fittingIn C.D.M) (even_iff_two_dvd.mp h2)
  set N : Subgroup G :=
    (Work.GW2.pCore 2 ↥(Work.GW2.fittingIn C.D.M)).map (Work.GW2.fittingIn C.D.M).subtype
    with hN
  have hNp : IsPGroup 2 N := by rw [hN]; exact Work.CORE4.A7V_isPGroup_pCoreIn 2 _
  have hNle : N ≤ C.D.M := by
    rw [hN]
    exact (Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _)
  have hNn : (N.subgroupOf C.D.M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNle]
    intro x m hx hm
    rw [hN] at hx ⊢
    exact Work.CORE4.conj_mem_pCoreIn_of_normal (Subgroup.map_subtype_le _)
      (Work.CORE4.fittingIn_subgroupOf_normal C.D.M) 2 hm hx
  have hNbot : N = ⊥ := by
    have h1 : N ≤ Work.GW2.pCoreIn 2 C.D.M :=
      Work.CORE4.A7V_le_pCoreIn_of_normal_isPGroup 2 C.D.M hNle hNn
        (hNp.of_equiv (Subgroup.subgroupOfEquivOfLe hNle).symm)
    rw [pCoreIn_two_M_eq_bot_9 I hbc B C hplus] at h1
    exact le_bot_iff.mp h1
  refine hne0 ?_
  have h2' : (Work.GW2.pCore 2 ↥(Work.GW2.fittingIn C.D.M)).map
      (Work.GW2.fittingIn C.D.M).subtype = ⊥ := hNbot
  exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h2'

/-- `F(M) ≤ U ⊓ M`. -/
theorem fittingIn_M_le_UinfM_9 (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B)
    (hplus : Work.GW2.Case2PrePlus B C.D) :
    Work.GW2.fittingIn C.D.M ≤ B.U ⊓ C.D.M := by
  have hFMleH : Work.GW2.fittingIn C.D.M ≤ B.H := by
    have hle := Work.CORE4.SevenRemain.fittingIn_le_centralizer_layerIn C.D.M
    intro x hx
    show x ∈ Subgroup.centralizer ({B.t} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Subgroup.mem_centralizer_iff.mp (hle hx) B.t C.D.t_mem
  have hodd := odd_card_fittingIn_M_9 I hbc B C hplus
  have hsplit := H_eq_U_sup_S_9 I hbc B
  have hUS' : B.U.subgroupOf B.H ⊔ (B.S : Subgroup G).subgroupOf B.H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup B.U_le_H B.S_le_H, ← hsplit, Subgroup.subgroupOf_self]
  have hindex : (B.U.subgroupOf B.H).index = Nat.card ↥(B.S : Subgroup G) :=
    Work.CORE4.relIndex_eq_card_of_sup_eq_inf_eq_bot B.U B.S B.H B.U_le_H B.S_le_H
      hsplit.symm B.U_inf_S B.U_normal
  have hcop : Nat.Coprime (Nat.card ↥(Work.GW2.fittingIn C.D.M))
      ((B.U.subgroupOf B.H)).index := by
    rw [hindex]
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp B.S.isPGroup'
    rw [hn]
    exact ((Nat.coprime_two_left.mpr hodd).symm).pow_right n
  have hleU : Work.GW2.fittingIn C.D.M ≤ B.U :=
    Work.CORE4.SevenRemain.le_of_coprime_card_relIndex B.U (Work.GW2.fittingIn C.D.M) B.H
      B.U_le_H hFMleH B.U_normal hcop
  exact le_inf hleU (Subgroup.map_subtype_le _)

/-- The `π`-inclusion: a copy of `SevenRemain.fittingIn_M_pi_subset`'s proof with the
`Case2Ctx` data replaced by `Case2Ctx6` + `Case2PrePlus`. -/
theorem primesOf_fittingIn_M_subset_9 (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B)
    (hplus : Work.GW2.Case2PrePlus B C.D) :
    Work.GW2.primesOf (Work.GW2.fittingIn C.D.M) ⊆ B.piFU := by
  intro p hp
  show p ∈ Work.GW2.primesOf (Work.GW2.fittingIn B.U)
  rw [Work.GW2.primesOf] at hp ⊢
  obtain ⟨hpprime, hpdvd, -⟩ := Nat.mem_primeFactors.mp hp
  haveI : Fact p.Prime := ⟨hpprime⟩
  refine Nat.mem_primeFactors.mpr ⟨hpprime, ?_, Nat.card_pos.ne'⟩
  by_contra hndvd
  have hFM_le : Work.GW2.fittingIn C.D.M ≤ B.U ⊓ C.D.M :=
    fittingIn_M_le_UinfM_9 I hbc B C hplus
  set Q : Subgroup G := Work.GW2.pCoreIn p (Work.GW2.fittingIn C.D.M) with hQ
  set N : Subgroup G := C.D.K0 ⊔ C.D.F with hN
  have hSix : Work.GW2.fittingIn B.U ⊓ C.D.M = N := by
    rw [hN]; exact Work.CORE4.SixThree I G hbc B C.D C.pre
  have hcopFU : Nat.Coprime p (Nat.card ↥(Work.GW2.fittingIn B.U)) :=
    hpprime.coprime_iff_not_dvd.mpr hndvd
  have hQleFM : Q ≤ Work.GW2.fittingIn C.D.M := by
    rw [hQ]; exact Subgroup.map_subtype_le _
  have hQp : IsPGroup p Q := by rw [hQ]; exact Work.CORE4.A7V_isPGroup_pCoreIn p _
  have hQne : Q ≠ ⊥ := by
    intro hbot
    rw [hQ, Work.GW2.pCoreIn] at hbot
    exact Work.CORE4.SevenRemain.pCore_ne_bot_of_isNilpotent_of_dvd G p _
      (Work.CORE4.SevenX.PiFU.isNilpotent_fittingIn C.D.M) hpdvd
      ((Subgroup.map_eq_bot_iff_of_injective _
        (Subgroup.subtype_injective (Work.GW2.fittingIn C.D.M))).mp hbot)
  have hQleUM : Q ≤ B.U ⊓ C.D.M := hQleFM.trans hFM_le
  have hQleU : Q ≤ B.U := hQleUM.trans inf_le_left
  have hQleM : Q ≤ C.D.M := hQleUM.trans inf_le_right
  have hNleFU : N ≤ Work.GW2.fittingIn B.U := by rw [← hSix]; exact inf_le_left
  have hNleM : N ≤ C.D.M := by rw [← hSix]; exact inf_le_right
  have hQn : (Q.subgroupOf C.D.M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hQleM]
    intro x m hx hm
    rw [hQ] at hx ⊢
    exact Work.CORE4.conj_mem_pCoreIn_of_normal (Subgroup.map_subtype_le _)
      (Work.CORE4.fittingIn_subgroupOf_normal C.D.M) p hm hx
  have hMleNGQ : C.D.M ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQleM).mp hQn
  have hNleNGQ : N ≤ Subgroup.normalizer (Q : Set G) := hNleM.trans hMleNGQ
  have hQFU : Q ≤ Subgroup.normalizer (Work.GW2.fittingIn B.U : Set G) :=
    hQleU.trans (Work.CORE4.le_normalizer_fittingIn B.U)
  have hQM : Q ≤ Subgroup.normalizer (C.D.M : Set G) := hQleM.trans Subgroup.le_normalizer
  have hQleNGN : Q ≤ Subgroup.normalizer (N : Set G) := by
    rw [← hSix]
    refine le_trans (le_inf hQFU hQM) ?_
    exact Subgroup.inf_normalizer_le_normalizer_inf (H := Work.GW2.fittingIn B.U) (K := C.D.M)
  have hQinfN : Q ⊓ N = ⊥ :=
    Work.CORE4.SevenRemain.isPGroup_eq_bot_of_le_coprime hpprime (hQp.to_le inf_le_left)
      (le_trans inf_le_right hNleFU) hcopFU
  have hcomm : ⁅N, Q⁆ = ⊥ := by
    have h1 : ⁅N, Q⁆ ≤ Q := Subgroup.le_normalizer_iff_commutator_le_right.mp hNleNGQ
    have h2 : ⁅N, Q⁆ ≤ N := Subgroup.le_normalizer_iff_commutator_le_left.mp hQleNGN
    exact le_bot_iff.mp ((le_inf h1 h2).trans (le_of_eq hQinfN))
  have hQleCN : Q ≤ Subgroup.centralizer (N : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (Subgroup.commutator_comm N Q ▸ hcomm)
  have hsc : Work.GW2.fittingIn B.U ⊓ Subgroup.centralizer (N : Set G) ≤ N := by
    rw [hN]
    exact Work.CORE4.SevenX.sevenX_fittingIn_inf_centralizer_sup_le B C.D C.pre hSix
  have hQleCFU : Q ≤ Subgroup.centralizer (Work.GW2.fittingIn B.U : Set G) :=
    Work.CORE4.SevenX.sevenX_le_centralizer_of_isNilpotent I.toolkit.c11iv
      (Work.GW2.fittingIn B.U) N Q
      (Work.CORE4.SevenX.PiFU.isNilpotent_fittingIn B.U) hNleFU hsc
      hpprime hQp hcopFU hQFU hQleCN
  have hsolv : Group.IsSolvable ↥B.U := I.toolkit.ft ↥B.U B.U_odd
  have hQleFUk : Q ≤ Work.GW2.fittingIn B.U :=
    (le_inf hQleCFU hQleU).trans
      (Work.CORE4.sevenX_centralizer_fittingIn_inf_le_fittingIn B.U hsolv)
  exact hQne (Work.CORE4.SevenRemain.isPGroup_eq_bot_of_le_coprime hpprime hQp hQleFUk hcopFU)

/-- Bender 1981, §4 (7) (p. 225), design-pass-9 layer: `Case2SevenFacts B C.D` from the §4
(1)–(6) data `C : Case2Ctx6 B` plus `Case2PrePlus B C.D`.

The stale "Gap" note in `Submission/Work/CORE4/Case2Seven.lean` (that `π(F) ⊆ π(K₀)` is not
derivable) is superseded: the missing §4 (6)-witness `∃ g ∉ M, F^g ≤ F(U) ⊓ M` is now PROVED as
`Work.CORE4.Case2Six9Aux.exists_witness_of_case2pre` from `Case2Pre` alone, so `K₀ ≠ ⊥` and
`π(F) ⊆ π(K₀)` are reachable.

IMPORTANT: the old stub `Work.CORE4.Case2Seven` (same statement, `Case2Seven.lean:221`) still
carries a `sorry`; a proof that cites it is tainted. Use only the *other* lemmas of that file
(`K0_sup_F_eq`, `K0_inf_F_eq_bot`, `card_K0_sup_F`, `K0_normal_in_K0supF`, `conj2_iff_piF`,
`primesOf_sup_of_card`), which are sorry-free — check with
`#print axioms Work.CORE4.Case2SevenImpl9`, which must print
`[propext, Classical.choice, Quot.sound]` only. -/
theorem Case2SevenImpl9 (I : Work.GW2.C4Inputs) : Work.GW2.Case2SevenImpl I := by
  intro G _ _ hbc B h2 C hplus
  exact ⟨Work.CORE4.SevenNine.O2_HM_eq_O2_H I hbc B h2 C hplus,
    primesOf_K0_eq_piFU9 I hbc B h2 C hplus,
    Work.CORE4.Case2SevenCentralizer I G hbc B C h2 hplus,
    primesOf_K_subset9 I hbc B h2 C hplus,
    primesOf_fittingIn_M_subset_9 I hbc B C hplus,
    Work.CORE4.SevenNine.pi_comm_SM_B0 I hbc B h2 C hplus⟩

end Work.CORE4
