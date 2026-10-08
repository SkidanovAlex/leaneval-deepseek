import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2RelIndexMH
import Submission.Work.CORE4.CoreQuotientSetup
import Submission.Work.CORE4NK.even_of_commuting_involutions
import Submission.Work.CORE4NK.odd_card_dvd_dihedral
import Submission.Work.CORE4NK.eq_bot_of_inverts_of_centralizes
import Submission.Work.CORE4NK.eq_bot_of_inverts_of_congruent_mod_center

namespace Work.CORE4

open scoped MatrixGroups
open Subgroup

-- (!) The four pure group-theoretic lemmas this file used to carry inline are proved by the
-- delegated modules `Submission.Work.CORE4NK.*` (see the imports above):
-- `Work.CORE4NK.even_of_commuting_involutions`, `Work.CORE4NK.odd_card_dvd_dihedral`,
-- `Work.CORE4NK.eq_bot_of_inverts_of_centralizes`,
-- `Work.CORE4NK.eq_bot_of_inverts_of_congruent_mod_center`.

/-- Transport of `Work.CORE4NK.odd_card_dvd_dihedral` along an isomorphism onto a dihedral
group: an odd-order subgroup of a group isomorphic to `DihedralGroup n` has order dividing `n`. -/
private lemma odd_card_dvd_dihedral_iso {n : ℕ} {A : Type*} [Group A]
    (ψ : A ≃* DihedralGroup n) (X : Subgroup A) (hX : Odd (Nat.card X)) : Nat.card X ∣ n := by
  have h := Work.CORE4NK.odd_card_dvd_dihedral (X.map ψ.toMonoidHom) (by
    rwa [Subgroup.card_map_of_injective ψ.injective])
  rwa [Subgroup.card_map_of_injective ψ.injective] at h

/-! ## The main lemma -/

/-
Formalisation note.  The route above is carried out through the central quotient
`E/Z(E) ≅ PSL(2,q)`, because the hypothesis list `Hyp9` does *not* contain `S ≤ E` (that is a
consequence of §4 (9) proved only at the very end of the chain, by `nine_sylow_arith`).  So:

* `K ≤ E(M)` is proved from `s ∈ E(M) ⊴ M` inverting `K` (as in `Case2EHcard.K_le_layerIn`);
* `K ⊓ Z(E) = 1` because `s` both inverts and centralises `Z(E)`, so the quotient map
  `E → E/Z(E)` is injective on `K` and `|K Z(E)/Z(E)| = |K|`;
* `l2cent` is applied to the image `t̄` of `t` in `E/Z(E)` (an involution since `Z(E)` has odd
  order), giving `n` with `2n = q ∓ 1` and `C_{L₂(q)}(t̄) ≅ D_n`;
* `K Z(E)/Z(E)` is an odd-order subgroup of that dihedral group, so `|K| ∣ n`;
* the images of `s` and `t` are *distinct* commuting involutions of `C_{L₂(q)}(t̄)` — if
  `s̄ = t̄` then `s` centralises `K` (because `t` does and `s t ∈ Z(E)`), while `s` inverts the
  odd-order group `K ≠ 1`, a contradiction; likewise for `s̄ = 1`.  Two distinct commuting
  involutions in `D_n` force `n` to be even.
-/

/-- **LEAF C10.N2 `NineK`**: "Let `k` (even) and `k'` (odd) be `(q ± 1)/2`.  Then
`k = |K| |O₂(H ∩ E)|`" — only `|K| ∣ k` is used.

`NineKProp I` gives, from `Hyp9 G B C`, the divisibility `Nat.card C.D.F ∣ Nat.card C.D.K0`
(= `SixEmbedProp`, proved in `CORE4/Case2SixEmbed`), and `NineShape C.D p e` for `q = p ^ e`:

    ∃ k k' : ℕ, NineKData C.D (p ^ e) k k'

with `NineKData C.D q k k' = Even k ∧ Odd k' ∧ (2k = q ± 1 ∧ 2k' = q ∓ 1) ∧ |K| ∣ k ∧
3 ≤ |K| ∧ Odd |K|`.

Route (design pass 10 §3.3, N2):
* `I.toolkit.l2cent` gives `C_{L₂(q)}(t̄) ≅ D_{2k}` with `2k = q ± 1`; this `k` is even because
  `C(t̄)` contains a Sylow 2-subgroup of the `D_{2k}`, of order ≥ 4;
* `K ≤ E` and `K ∩ Z(E) = 1` (`s` centralises `Z(E)` and inverts `K`), so `K` embeds in the odd
  part of `D_{2k}` and `|K| ∣ k`;
* `K₀ ≠ 1` (`Case2SixEmbed` with `F ≠ ⊥`) and `K₀ ≤ K` give `|K| ≥ 3`; `K ≤ U` is odd;
* `k' := k ∓ 1` is odd.  (Consequently `7 ≤ p ^ e` follows from the proved `nine_seven_le` in
  `Defs10.lean`.) -/
theorem NineK (I : Work.GW2.C4Inputs) : Work.GW2.NineKProp I := by
  classical
  intro G _ _ B C hH hFK p e hp hshape
  haveI : Fact p.Prime := hp
  obtain ⟨hpodd, h5q, ⟨φ⟩, hZodd⟩ := hshape
  have hpre : Work.GW2.Case2Pre B C.D := C.pre
  -- ### Basic facts about `t`, `s` and `K`
  have htE : B.t ∈ Work.GW2.layerIn C.D.M := C.D.t_mem
  have hsE : C.D.s ∈ Work.GW2.layerIn C.D.M := C.D.s_mem.2
  have ht2 : orderOf (⟨B.t, htE⟩ : ↥(Work.GW2.layerIn C.D.M)) = 2 := by
    rw [Subgroup.orderOf_mk, B.t_order]
  have hs2 : orderOf (⟨C.D.s, hsE⟩ : ↥(Work.GW2.layerIn C.D.M)) = 2 := by
    rw [Subgroup.orderOf_mk, C.D.s_order]
  have hK_le_U : C.D.K ≤ B.U := Work.GW2.Case2Data.K_le_U B C.D
  have hKodd : Odd (Nat.card ↥C.D.K) :=
    Odd.of_dvd_nat B.U_odd (Subgroup.card_dvd_of_le hK_le_U)
  have hK_le_H : C.D.K ≤ B.H := le_trans hK_le_U B.U_le_H
  have hK_cent : ∀ k ∈ C.D.K, B.t * k = k * B.t := by
    intro k hk
    exact Subgroup.mem_centralizer_iff.mp (hK_le_H hk) B.t (Set.mem_singleton B.t)
  have hK_inv : ∀ k ∈ C.D.K, C.D.s * k * C.D.s⁻¹ = k⁻¹ := fun k hk => C.D.K_inv B k hk
  -- `K ≠ ⊥`, from `F ≠ ⊥` and `|F| ∣ |K₀|`
  have hF_ne : C.D.F ≠ ⊥ := Work.GW2.Case2Pre.F_ne B C.D hpre
  have hF2 : 2 ≤ Nat.card ↥C.D.F := by
    haveI : Fintype ↥C.D.F := Fintype.ofFinite _
    have hnt : Nontrivial ↥C.D.F := (Subgroup.nontrivial_iff_ne_bot C.D.F).mpr hF_ne
    rw [Nat.card_eq_fintype_card]
    have h1 : 1 < Fintype.card ↥C.D.F := Fintype.one_lt_card_iff.mpr (exists_pair_ne ↥C.D.F)
    omega
  have hK0ge : 2 ≤ Nat.card ↥C.D.K0 :=
    le_trans hF2 (Nat.le_of_dvd Nat.card_pos hFK)
  have hKne : C.D.K ≠ ⊥ := by
    intro hbot
    have hK0bot : C.D.K0 = ⊥ := by
      change Work.GW2.fittingIn B.U ⊓ C.D.K = ⊥
      exact le_bot_iff.mp (le_trans inf_le_right (le_of_eq hbot))
    rw [hK0bot, Subgroup.card_bot] at hK0ge
    omega
  have hK3 : 3 ≤ Nat.card ↥C.D.K := by
    haveI : Fintype ↥C.D.K := Fintype.ofFinite _
    have hnt : Nontrivial ↥C.D.K := (Subgroup.nontrivial_iff_ne_bot C.D.K).mpr hKne
    have h1 : 1 < Nat.card ↥C.D.K := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card_iff.mpr (exists_pair_ne ↥C.D.K)
    rcases hKodd with ⟨j, hj⟩
    omega
  -- ### `K ≤ E` (the layer `E = E(M)`)
  have hEnorm : ((Work.GW2.layerIn C.D.M).subgroupOf C.D.M).Normal := by
    have h1 : (Work.GW2.layerIn C.D.M).subgroupOf C.D.M = Work.GW2.layer ↥C.D.M := by
      rw [Work.GW2.layerIn]
      exact Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _
    rw [h1]
    exact Work.CORE4.layer_normal C.D.M
  have hK_le_E : C.D.K ≤ Work.GW2.layerIn C.D.M := by
    intro k hk
    have hkM : k ∈ C.D.M := Work.GW2.Case2Data.K_le_M B C.D hk
    have hkinv : C.D.s * k * C.D.s⁻¹ = k⁻¹ := hK_inv k hk
    have hconj : k * C.D.s * k⁻¹ ∈ Work.GW2.layerIn C.D.M :=
      (Subgroup.normal_subgroupOf_iff (Work.CORE4.layerIn_le C.D.M)).mp hEnorm C.D.s k hsE hkM
    have hk2 : k ^ 2 ∈ Work.GW2.layerIn C.D.M := by
      have h1 : C.D.s * k⁻¹ * C.D.s⁻¹ = k := by
        have h3 := congrArg (fun z : G => z⁻¹) hkinv
        rw [mul_inv_rev, mul_inv_rev, inv_inv] at h3
        simpa [mul_assoc] using h3
      have heq : (k * C.D.s * k⁻¹) * C.D.s⁻¹ = k * k := by
        calc (k * C.D.s * k⁻¹) * C.D.s⁻¹ = k * (C.D.s * k⁻¹ * C.D.s⁻¹) := by group
          _ = k * k := by rw [h1]
      have heq2 : k ^ 2 = (k * C.D.s * k⁻¹) * C.D.s⁻¹ := by rw [pow_two]; exact heq.symm
      rw [heq2]
      exact Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ hsE)
    have hkodd : Odd (orderOf k) := Odd.of_dvd_nat hKodd (Subgroup.orderOf_dvd_natCard C.D.K hk)
    obtain ⟨j, hj⟩ := hkodd
    have hpow : (k ^ 2) ^ (j + 1) = k := by
      rw [← pow_mul]
      have h2 : 2 * (j + 1) = orderOf k + 1 := by rw [hj]; ring
      rw [h2, pow_succ, pow_orderOf_eq_one, one_mul]
    exact hpow ▸ Subgroup.pow_mem _ hk2 (j + 1)
  -- ### `K` as a subgroup of `E`, and the transport of its structure
  have hK'card : Nat.card ↥(C.D.K.subgroupOf (Work.GW2.layerIn C.D.M)) = Nat.card ↥C.D.K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK_le_E).toEquiv
  have hK'odd : Odd (Nat.card ↥(C.D.K.subgroupOf (Work.GW2.layerIn C.D.M))) := by
    rw [hK'card]; exact hKodd
  have hK'cent : C.D.K.subgroupOf (Work.GW2.layerIn C.D.M) ≤
      Subgroup.centralizer ({⟨B.t, htE⟩} : Set ↥(Work.GW2.layerIn C.D.M)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hxK : ((x : ↥(Work.GW2.layerIn C.D.M)) : G) ∈ C.D.K := Subgroup.mem_subgroupOf.mp hx
    exact (hK_cent _ hxK).symm
  -- `s` and `t` commute (both lie in `S`, and `t` is central in `S`)
  have hst_comm : (⟨C.D.s, hsE⟩ : ↥(Work.GW2.layerIn C.D.M)) * ⟨B.t, htE⟩ =
      ⟨B.t, htE⟩ * ⟨C.D.s, hsE⟩ := by
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (B.S_le_H C.D.s_mem.1) B.t
      (Set.mem_singleton B.t)).symm
  -- the inversion of `K` transported to `↥E`
  have hK'_inv : ∀ y ∈ C.D.K.subgroupOf (Work.GW2.layerIn C.D.M),
      (⟨C.D.s, hsE⟩ : ↥(Work.GW2.layerIn C.D.M)) * y * ⟨C.D.s, hsE⟩⁻¹ = y⁻¹ := by
    intro y hy
    apply Subtype.ext
    exact hK_inv _ (Subgroup.mem_subgroupOf.mp hy)
  -- the centrality of `t` transported to `↥E`
  have hK'_cent : ∀ y ∈ C.D.K.subgroupOf (Work.GW2.layerIn C.D.M),
      (⟨B.t, htE⟩ : ↥(Work.GW2.layerIn C.D.M)) * y = y * ⟨B.t, htE⟩ := by
    intro y hy
    apply Subtype.ext
    exact hK_cent _ (Subgroup.mem_subgroupOf.mp hy)
  -- ### `K ⊓ Z(E) = 1`
  have hK'disj : C.D.K.subgroupOf (Work.GW2.layerIn C.D.M) ⊓
      Subgroup.center ↥(Work.GW2.layerIn C.D.M) = ⊥ := by
    refine Work.CORE4NK.eq_bot_of_inverts_of_centralizes
      (C.D.K.subgroupOf (Work.GW2.layerIn C.D.M) ⊓ Subgroup.center ↥(Work.GW2.layerIn C.D.M))
      (⟨C.D.s, hsE⟩ : ↥(Work.GW2.layerIn C.D.M)) ?_ ?_ ?_
    · exact Odd.of_dvd_nat hK'odd (Subgroup.card_dvd_of_le inf_le_left)
    · intro y hy
      exact hK'_inv y (Subgroup.mem_inf.mp hy).1
    · intro y hy
      exact Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp hy).2
        (⟨C.D.s, hsE⟩ : ↥(Work.GW2.layerIn C.D.M))
  -- ### the central quotient, via `CoreQuotientSetup`
  obtain ⟨ht_not_center, htbar_ord, hKbar_odd, hKbar_cent, -⟩ :=
    Work.CORE4.CoreQuotientSetup hZodd ⊤ (⟨B.t, htE⟩ : ↥(Work.GW2.layerIn C.D.M))
      (Subgroup.mem_top _) ht2 (C.D.K.subgroupOf (Work.GW2.layerIn C.D.M)) hK'odd hK'cent
  -- `K̄` has the same order as `K`
  set f : ↥(C.D.K.subgroupOf (Work.GW2.layerIn C.D.M)) →*
      (↥(Work.GW2.layerIn C.D.M) ⧸ Subgroup.center ↥(Work.GW2.layerIn C.D.M)) :=
    (QuotientGroup.mk' (Subgroup.center ↥(Work.GW2.layerIn C.D.M))).comp
      (C.D.K.subgroupOf (Work.GW2.layerIn C.D.M)).subtype with hf
  have hker : f.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx' : QuotientGroup.mk' (Subgroup.center ↥(Work.GW2.layerIn C.D.M))
        ((x : ↥(C.D.K.subgroupOf (Work.GW2.layerIn C.D.M))) : ↥(Work.GW2.layerIn C.D.M)) = 1 := hx
    have hxZ : ((x : ↥(C.D.K.subgroupOf (Work.GW2.layerIn C.D.M))) : ↥(Work.GW2.layerIn C.D.M)) ∈
        Subgroup.center ↥(Work.GW2.layerIn C.D.M) := (QuotientGroup.eq_one_iff _).mp hx'
    have hmem : ((x : ↥(C.D.K.subgroupOf (Work.GW2.layerIn C.D.M))) : ↥(Work.GW2.layerIn C.D.M)) ∈
        C.D.K.subgroupOf (Work.GW2.layerIn C.D.M) ⊓
          Subgroup.center ↥(Work.GW2.layerIn C.D.M) := ⟨x.2, hxZ⟩
    rw [hK'disj] at hmem
    exact Subtype.ext (Subgroup.mem_bot.mp hmem)
  have hrange : f.range = (C.D.K.subgroupOf (Work.GW2.layerIn C.D.M)).map
      (QuotientGroup.mk' (Subgroup.center ↥(Work.GW2.layerIn C.D.M))) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact Subgroup.mem_map.mpr ⟨(x : ↥(Work.GW2.layerIn C.D.M)), x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hKbarcard : Nat.card ↥((C.D.K.subgroupOf (Work.GW2.layerIn C.D.M)).map
      (QuotientGroup.mk' (Subgroup.center ↥(Work.GW2.layerIn C.D.M)))) = Nat.card ↥C.D.K := by
    have h := Subgroup.card_ker_mul_card_range f
    rw [hker, hrange, Subgroup.card_bot, one_mul] at h
    rw [h, hK'card]
  -- ### `s̄ ≠ 1` and `s̄ ≠ t̄` in `E/Z(E)` (using `K ≠ 1`)
  have hsbar_ne_one : QuotientGroup.mk' (Subgroup.center ↥(Work.GW2.layerIn C.D.M))
      (⟨C.D.s, hsE⟩ : ↥(Work.GW2.layerIn C.D.M)) ≠ 1 := by
    intro h1
    have hmem : (⟨C.D.s, hsE⟩ : ↥(Work.GW2.layerIn C.D.M)) ∈
        Subgroup.center ↥(Work.GW2.layerIn C.D.M) := (QuotientGroup.eq_one_iff _).mp h1
    have hcent' : ∀ y ∈ C.D.K.subgroupOf (Work.GW2.layerIn C.D.M),
        (⟨C.D.s, hsE⟩ : ↥(Work.GW2.layerIn C.D.M)) * y = y * ⟨C.D.s, hsE⟩ :=
      fun y _ => (Subgroup.mem_center_iff.mp hmem y).symm
    have hbot := Work.CORE4NK.eq_bot_of_inverts_of_centralizes _ _ hK'odd hK'_inv hcent'
    have hone : Nat.card ↥C.D.K = 1 := by rw [← hK'card, hbot, Subgroup.card_bot]
    exact hKne (Subgroup.card_eq_one.mp hone)
  have hsbar_ne_tbar : QuotientGroup.mk' (Subgroup.center ↥(Work.GW2.layerIn C.D.M))
      (⟨C.D.s, hsE⟩ : ↥(Work.GW2.layerIn C.D.M)) ≠
      QuotientGroup.mk' (Subgroup.center ↥(Work.GW2.layerIn C.D.M)) ⟨B.t, htE⟩ := by
    intro hcong
    have hbot := Work.CORE4NK.eq_bot_of_inverts_of_congruent_mod_center _ _ _ hK'odd hK'_inv
      hK'_cent hcong
    have hone : Nat.card ↥C.D.K = 1 := by rw [← hK'card, hbot, Subgroup.card_bot]
    exact hKne (Subgroup.card_eq_one.mp hone)
  -- ### `l2cent` at `t̄`
  have hphi_tbar : orderOf (φ (QuotientGroup.mk' (Subgroup.center ↥(Work.GW2.layerIn C.D.M))
      ⟨B.t, htE⟩)) = 2 := by
    rw [MulEquiv.orderOf_eq]; exact htbar_ord
  obtain ⟨n, hn, ⟨ψ⟩⟩ := I.toolkit.l2cent p e hpodd h5q _ hphi_tbar
  -- ### the centralizer of `φ t̄` and the two involutions inside it
  have hquot_comm : QuotientGroup.mk' (Subgroup.center ↥(Work.GW2.layerIn C.D.M))
        (⟨C.D.s, hsE⟩ : ↥(Work.GW2.layerIn C.D.M)) *
        QuotientGroup.mk' (Subgroup.center ↥(Work.GW2.layerIn C.D.M)) ⟨B.t, htE⟩ =
      QuotientGroup.mk' (Subgroup.center ↥(Work.GW2.layerIn C.D.M)) ⟨B.t, htE⟩ *
        QuotientGroup.mk' (Subgroup.center ↥(Work.GW2.layerIn C.D.M))
        (⟨C.D.s, hsE⟩ : ↥(Work.GW2.layerIn C.D.M)) := by
    rw [← map_mul, ← map_mul, hst_comm]
  have hsbar_sq : QuotientGroup.mk' (Subgroup.center ↥(Work.GW2.layerIn C.D.M))
      (⟨C.D.s, hsE⟩ : ↥(Work.GW2.layerIn C.D.M)) *
      QuotientGroup.mk' (Subgroup.center ↥(Work.GW2.layerIn C.D.M))
      (⟨C.D.s, hsE⟩ : ↥(Work.GW2.layerIn C.D.M)) = 1 := by
    rw [← map_mul]
    have h : (⟨C.D.s, hsE⟩ : ↥(Work.GW2.layerIn C.D.M)) * ⟨C.D.s, hsE⟩ = 1 := by
      have h2 : (⟨C.D.s, hsE⟩ : ↥(Work.GW2.layerIn C.D.M)) ^ 2 = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one, hs2]
      rwa [pow_two] at h2
    rw [h, map_one]
  have htbar_sq : QuotientGroup.mk' (Subgroup.center ↥(Work.GW2.layerIn C.D.M)) ⟨B.t, htE⟩ *
      QuotientGroup.mk' (Subgroup.center ↥(Work.GW2.layerIn C.D.M)) ⟨B.t, htE⟩ = 1 := by
    rw [← map_mul]
    have h : (⟨B.t, htE⟩ : ↥(Work.GW2.layerIn C.D.M)) * ⟨B.t, htE⟩ = 1 := by
      have h2 : (⟨B.t, htE⟩ : ↥(Work.GW2.layerIn C.D.M)) ^ 2 = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one, ht2]
      rwa [pow_two] at h2
    rw [h, map_one]
  have hsbar_cent : φ (QuotientGroup.mk' (Subgroup.center ↥(Work.GW2.layerIn C.D.M))
      (⟨C.D.s, hsE⟩ : ↥(Work.GW2.layerIn C.D.M))) ∈
      Subgroup.centralizer
        ({(φ (QuotientGroup.mk' (Subgroup.center ↥(Work.GW2.layerIn C.D.M)) ⟨B.t, htE⟩))} :
          Set (PSL(2, GaloisField p e))) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa only [map_mul] using congrArg φ hquot_comm
  have htbar_cent : φ (QuotientGroup.mk' (Subgroup.center ↥(Work.GW2.layerIn C.D.M)) ⟨B.t, htE⟩) ∈
      Subgroup.centralizer
        ({(φ (QuotientGroup.mk' (Subgroup.center ↥(Work.GW2.layerIn C.D.M)) ⟨B.t, htE⟩))} :
          Set (PSL(2, GaloisField p e))) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  set C0 : Subgroup (PSL(2, GaloisField p e)) :=
    Subgroup.centralizer
      ({(φ (QuotientGroup.mk' (Subgroup.center ↥(Work.GW2.layerIn C.D.M)) ⟨B.t, htE⟩))} :
        Set (PSL(2, GaloisField p e))) with hC0
  set x0 : ↥C0 := ⟨φ (QuotientGroup.mk' (Subgroup.center ↥(Work.GW2.layerIn C.D.M))
      (⟨C.D.s, hsE⟩ : ↥(Work.GW2.layerIn C.D.M))), hsbar_cent⟩ with hx0
  set y0 : ↥C0 := ⟨φ (QuotientGroup.mk' (Subgroup.center ↥(Work.GW2.layerIn C.D.M)) ⟨B.t, htE⟩),
    htbar_cent⟩ with hy0
  have hx0sq : x0 * x0 = 1 := by
    rw [hx0]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_one]
    rw [← map_mul, hsbar_sq, map_one]
  have hy0sq : y0 * y0 = 1 := by
    rw [hy0]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_one]
    rw [← map_mul, htbar_sq, map_one]
  have hx0ne : x0 ≠ 1 := by
    intro h
    rw [hx0] at h
    have h1 : φ (QuotientGroup.mk' (Subgroup.center ↥(Work.GW2.layerIn C.D.M))
        (⟨C.D.s, hsE⟩ : ↥(Work.GW2.layerIn C.D.M))) = 1 := by
      simpa using congrArg Subtype.val h
    exact hsbar_ne_one (φ.injective (by rw [h1, map_one]))
  have hy0ne : y0 ≠ 1 := by
    intro h
    rw [hy0] at h
    have h1 : φ (QuotientGroup.mk' (Subgroup.center ↥(Work.GW2.layerIn C.D.M)) ⟨B.t, htE⟩) = 1 := by
      simpa using congrArg Subtype.val h
    have h2 : QuotientGroup.mk' (Subgroup.center ↥(Work.GW2.layerIn C.D.M)) ⟨B.t, htE⟩ = 1 :=
      φ.injective (by rw [h1, map_one])
    rw [h2] at htbar_ord
    exact absurd htbar_ord (by norm_num)
  have hcomm0 : x0 * y0 = y0 * x0 := by
    rw [hx0, hy0]
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    simpa only [map_mul] using congrArg φ hquot_comm
  have hne0 : x0 ≠ y0 := by
    intro h
    rw [hx0, hy0] at h
    have h1 : φ (QuotientGroup.mk' (Subgroup.center ↥(Work.GW2.layerIn C.D.M))
        (⟨C.D.s, hsE⟩ : ↥(Work.GW2.layerIn C.D.M))) =
        φ (QuotientGroup.mk' (Subgroup.center ↥(Work.GW2.layerIn C.D.M)) ⟨B.t, htE⟩) := by
      simpa using congrArg Subtype.val h
    exact hsbar_ne_tbar (φ.injective h1)
  -- ### `n` is even, from the two involutions `ψ x0 ≠ ψ y0` of `D_n`
  have hnEven : Even n := by
    refine Work.CORE4NK.even_of_commuting_involutions (x := ψ x0) (y := ψ y0) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [← map_mul, hx0sq, map_one]
    · rw [← map_mul, hy0sq, map_one]
    · intro h
      exact hx0ne (ψ.injective (by rw [h, map_one]))
    · intro h
      exact hy0ne (ψ.injective (by rw [h, map_one]))
    · rw [← map_mul, ← map_mul, hcomm0]
    · intro h
      exact hne0 (ψ.injective h)
  -- ### `|K| ∣ n`: the image of `K̄` in `D_n` has order `|K|` and divides `n`
  have hKbarPSL : ((C.D.K.subgroupOf (Work.GW2.layerIn C.D.M)).map
      (QuotientGroup.mk' (Subgroup.center ↥(Work.GW2.layerIn C.D.M)))).map φ.toMonoidHom ≤ C0 := by
    rw [hC0]
    refine (Subgroup.map_mono hKbar_cent).trans ?_
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg φ hy
  have hLcard : Nat.card ↥((((C.D.K.subgroupOf (Work.GW2.layerIn C.D.M)).map
      (QuotientGroup.mk' (Subgroup.center ↥(Work.GW2.layerIn C.D.M)))).map φ.toMonoidHom).subgroupOf
      C0) = Nat.card ↥C.D.K := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKbarPSL).toEquiv,
      Subgroup.card_map_of_injective φ.injective, hKbarcard]
  have hLdvd : Nat.card ↥((((C.D.K.subgroupOf (Work.GW2.layerIn C.D.M)).map
      (QuotientGroup.mk' (Subgroup.center ↥(Work.GW2.layerIn C.D.M)))).map φ.toMonoidHom).subgroupOf
      C0) ∣ n :=
    odd_card_dvd_dihedral_iso ψ _ (by rw [hLcard]; exact hKodd)
  have hKvdn : Nat.card ↥C.D.K ∣ n := by
    rw [← hLcard]; exact hLdvd
  -- ### assembly
  rcases hn with hn | hn
  · refine ⟨n, n + 1, hnEven, hnEven.add_one, Or.inr ⟨hn, by omega⟩, hKvdn, hK3, hKodd⟩
  · refine ⟨n, n - 1, hnEven, ?_, Or.inl ⟨hn, by omega⟩, hKvdn, hK3, hKodd⟩
    obtain ⟨t, ht⟩ := hnEven
    exact ⟨t - 1, by omega⟩

end Work.CORE4
