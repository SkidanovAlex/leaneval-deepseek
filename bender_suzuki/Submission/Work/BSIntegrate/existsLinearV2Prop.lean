import Mathlib
import Submission.Work.BSIntegrate.Defs
import Submission.Work.BSIntegrate.centD_ne_bot_of_rankOneHyp
import Submission.Work.ThmF.ChV12.exists_linear_v2
import Submission.Work.ThmF.ChV12.Ksub_cyclic_normal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.BSIntegrate.existsLinearV2Prop`

Peterfalvi II, Ch. VI §1, p. 258 — field 5 (corrected) of the rank-one structure: in a
`RankOneHyp` situation there is a **linear** character `lam ≠ 1_H` of `H` trivial on `Q` **and on
`K = J(D,t)` (i.e. `QK ⊆ ker lam`).

The proof assembles the `Ch. V §1–2` export of area `ThmF`:

* `Work.ThmF.ChV12.exists_linear_v2` — the character-theoretic core: given `V = C_D(t) ≠ 1`,
  the cyclicity of `K = J(D,t)` and `K = Kset H t`, it produces `lam`;
* `Work.ThmF.ChV12.Ksub_cyclic_normal` — Ch. V §1 Prop. 2: `K = J(D,t)` is cyclic, equals
  `Kset H t` and is normal in `D`;
* `V = C_D(t) ≠ ⊥` — Peterfalvi II, p. 236 (the easy direction of "`G` is a Zassenhaus group iff
  `V = 1`"), in the generality needed here (an arbitrary `RankOneHyp`, so `Q` need not be a
  `2`-group).  This is `Work.PSU3.StageA.centD_ne_bot` with its step 4 refined: writing
  `orderOf q = 2 ^ j * m` with `m` odd, the odd part `q ^ (2 ^ j)` is a non-trivial element of
  `O_{2'}(Q)` centralised by `d`, so it is `1` by `FpfOddPartProp` (Ch. V §2 Lemma 2 c); hence
  `m = 1` and Peterfalvi's involution argument applies verbatim.  It is proved here as the
  private lemma `centD_aux`, so that this module is self-contained; the same statement is also
  available as `Work.ThmG3.centD_ne_bot_of_rankOneHyp` (area `ThmG3`, axiom-clean) and is the
  deliverable of `Submission/Work/BSIntegrate/centD_ne_bot_of_rankOneHyp.lean`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section
open Classical
open LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.BSIntegrate

open Work.ThmG

/-- **Peterfalvi II, p. 236** in the generality of `RankOneHyp`: `V = C_D(t) ≠ 1`.

`Work.PSU3.StageA.centD_ne_bot` is the case where `Q` is a `2`-group; here the odd part of
`orderOf q` is removed by `FpfOddPartProp`. -/
private theorem centD_aux (hFpf : FpfOddPartProp) {G : Type} [Group G] [Fintype G]
    {H Q : Subgroup G} {t : G} (hh : RankOneHyp G H Q t) : centD H t ≠ ⊥ := by
  classical
  have hsplit : IsSplitRankOne H Q t := hh.2.2.1
  have hH : IsStronglyEmbedded H := hsplit.stronglyEmbedded
  have ht2 : orderOf t = 2 := hsplit.invol
  have htH : t ∉ H := hsplit.not_mem
  have htt : t * t = 1 := Work.RankOneUniqueness.mul_self_eq_one hsplit
  have hti : t⁻¹ = t := Work.RankOneUniqueness.inv_eq_self hsplit
  have hZ := hh.2.2.2.1
  rw [Submission.Blueprint.IsZassenhaus] at hZ
  push_neg at hZ
  obtain ⟨a, b, c, hab, hac, hbc, g, hga, hgb, hgc, hg1⟩ := hZ
  have h2t : MulAction.IsMultiplyPretransitive G (G ⧸ H) 2 := hsplit.twoTransitive
  rw [MulAction.is_two_pretransitive_iff] at h2t
  have htpt_ne : t • Work.RankOneUniqueness.pt H ≠ Work.RankOneUniqueness.pt H :=
    Work.RankOneUniqueness.t_smul_pt_ne hsplit
  obtain ⟨x, hxa, hxb⟩ := h2t hab htpt_ne.symm
  set c' : G ⧸ H := x • c with hc'_def
  set d : G := x * g * x⁻¹ with hd_def
  have hd_pt : d • (Work.RankOneUniqueness.pt H) = Work.RankOneUniqueness.pt H := by
    rw [hd_def, ← hxa]
    calc (x * g * x⁻¹) • (x • a) = ((x * g * x⁻¹) * x) • a := (mul_smul (x * g * x⁻¹) x a).symm
      _ = (x * g) • a := by rw [show x * g * x⁻¹ * x = x * g from by group]
      _ = x • (g • a) := mul_smul x g a
      _ = x • a := by rw [hga]
  have hd_tpt : d • (t • Work.RankOneUniqueness.pt H) = t • Work.RankOneUniqueness.pt H := by
    rw [hd_def, ← hxb]
    calc (x * g * x⁻¹) • (x • b) = ((x * g * x⁻¹) * x) • b := (mul_smul (x * g * x⁻¹) x b).symm
      _ = (x * g) • b := by rw [show x * g * x⁻¹ * x = x * g from by group]
      _ = x • (g • b) := mul_smul x g b
      _ = x • b := by rw [hgb]
  have hd_c' : d • c' = c' := by
    rw [hc'_def, hd_def]
    calc (x * g * x⁻¹) • (x • c) = ((x * g * x⁻¹) * x) • c := (mul_smul (x * g * x⁻¹) x c).symm
      _ = (x * g) • c := by rw [show x * g * x⁻¹ * x = x * g from by group]
      _ = x • (g • c) := mul_smul x g c
      _ = x • c := by rw [hgc]
  have hc'_ne_pt : c' ≠ Work.RankOneUniqueness.pt H := by
    intro hcon
    rw [hc'_def] at hcon
    have h1 : x⁻¹ • (x • c) = x⁻¹ • (x • a) := by rw [hcon, hxa]
    rw [inv_smul_smul, inv_smul_smul] at h1
    exact hac h1.symm
  have hc'_ne_tpt : c' ≠ t • Work.RankOneUniqueness.pt H := by
    intro hcon
    rw [hc'_def] at hcon
    have h1 : x⁻¹ • (x • c) = x⁻¹ • (x • b) := by rw [hcon, hxb]
    rw [inv_smul_smul, inv_smul_smul] at h1
    exact hbc h1.symm
  have hd_ne_one : d ≠ 1 := by
    intro h1
    apply hg1
    have h2 : x * g * x⁻¹ = 1 := by rw [← hd_def]; exact h1
    have h3 := congrArg (fun z : G => x⁻¹ * z * x) h2
    simpa [mul_assoc] using h3
  have hd_ptH : d ∈ H := (Work.RankOneUniqueness.smul_pt_iff H d).mp hd_pt
  have hd_memD : d ∈ Submission.Blueprint.twoPoint H t :=
    (Work.ZassenhausTwoGroup.IsTIQ.mem_twoPoint_iff_smul H t d).mpr
      ⟨hd_ptH, by rw [← Work.RankOneUniqueness.smul_pt H t]; exact hd_tpt⟩
  obtain ⟨h, hhH, hh'⟩ := Work.ZassenhausTwoGroup.IsTIQ.h_transitive hsplit
    (t • Work.RankOneUniqueness.pt H) c' htpt_ne hc'_ne_pt
  obtain ⟨q, hqQ, e, heD, hqe⟩ := Work.RankOneUniqueness.fact_exists hsplit hhH
  have he_tpt : e • (t • Work.RankOneUniqueness.pt H) = t • Work.RankOneUniqueness.pt H := by
    have h1 := (Work.ZassenhausTwoGroup.IsTIQ.mem_twoPoint_iff_smul H t e).mp heD
    rw [← Work.RankOneUniqueness.smul_pt H t] at h1
    exact h1.2
  have hq_smul : q • (t • Work.RankOneUniqueness.pt H) = c' := by
    calc q • (t • Work.RankOneUniqueness.pt H)
        = q • (e • (t • Work.RankOneUniqueness.pt H)) := by rw [he_tpt]
      _ = (q * e) • (t • Work.RankOneUniqueness.pt H) :=
          (mul_smul q e (t • Work.RankOneUniqueness.pt H)).symm
      _ = h • (t • Work.RankOneUniqueness.pt H) := by rw [hqe]
      _ = c' := hh'
  have hq_ne_one : q ≠ 1 := by
    intro hq1
    rw [hq1, one_smul] at hq_smul
    exact hc'_ne_tpt hq_smul.symm
  have hd_inv_tpt : d⁻¹ • (t • Work.RankOneUniqueness.pt H) = t • Work.RankOneUniqueness.pt H := by
    have h1 : d⁻¹ ∈ Submission.Blueprint.twoPoint H t :=
      (Submission.Blueprint.twoPoint H t).inv_mem hd_memD
    have h2 := (Work.ZassenhausTwoGroup.IsTIQ.mem_twoPoint_iff_smul H t d⁻¹).mp h1
    rw [← Work.RankOneUniqueness.smul_pt H t] at h2
    exact h2.2
  have hdq_conj : d * q * d⁻¹ = q := by
    have h1 : (d * q * d⁻¹) • (t • Work.RankOneUniqueness.pt H)
        = q • (t • Work.RankOneUniqueness.pt H) := by
      calc (d * q * d⁻¹) • (t • Work.RankOneUniqueness.pt H)
          = d • (q • (d⁻¹ • (t • Work.RankOneUniqueness.pt H))) := by
            rw [mul_smul, mul_smul]
        _ = d • (q • (t • Work.RankOneUniqueness.pt H)) := by rw [hd_inv_tpt]
        _ = d • c' := by rw [hq_smul]
        _ = c' := hd_c'
        _ = q • (t • Work.RankOneUniqueness.pt H) := hq_smul.symm
    have hmem : d * q * d⁻¹ ∈ Q :=
      Work.RankOneUniqueness.conj_mem_of_mem hsplit hd_ptH hqQ
    have hfix : ((d * q * d⁻¹)⁻¹ * q) • (t • Work.RankOneUniqueness.pt H)
        = t • Work.RankOneUniqueness.pt H := by
      rw [mul_smul, ← h1, inv_smul_smul]
    have hone : (d * q * d⁻¹)⁻¹ * q = 1 :=
      Work.ZassenhausTwoGroup.IsTIQ.Q_smul_eq_self hsplit
        (Q.mul_mem (Q.inv_mem hmem) hqQ) hfix htpt_ne
    exact inv_mul_eq_one.mp hone
  -- Step 4 (NEW): `orderOf q = 2^j * m`, `m` odd; the odd part is killed by `FpfOddPartProp`.
  have hconjpow : ∀ n : ℕ, d * q ^ n * d⁻¹ = q ^ n := by
    intro n
    have h := map_pow (MulAut.conj d).toMonoidHom q n
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply] at h
    rw [h, hdq_conj]
  have hq0 : orderOf q ≠ 0 := (orderOf_pos q).ne'
  obtain ⟨j, m, hmodd, hqm⟩ := Nat.exists_eq_two_pow_mul_odd hq0
  have hm1 : m = 1 := by
    by_contra hm1
    have hdvd : 2 ^ j ∣ orderOf q := ⟨m, hqm⟩
    have hord : orderOf (q ^ (2 ^ j)) = m := by
      rw [orderOf_pow_of_dvd (pow_pos (by norm_num) j).ne' hdvd, hqm,
        Nat.mul_div_cancel_left _ (pow_pos (by norm_num) j)]
    have hyodd : q ^ (2 ^ j) ∈ oddPart Q :=
      mem_oddPart_of_odd Q (Q.pow_mem hqQ _) (by rw [hord]; exact hmodd)
    have hy1 := hFpf G H Q t hh d hd_memD hd_ne_one _ hyodd (hconjpow _)
    rw [hy1, orderOf_one] at hord
    exact hm1 hord.symm
  have hj : orderOf q = 2 ^ j := by rw [hqm, hm1, mul_one]
  have hjpos : 1 ≤ j := by
    by_contra h1
    have hj0 : j = 0 := by omega
    rw [hj0] at hj
    exact hq_ne_one (orderOf_eq_one_iff.mp (by simpa using hj))
  set u : G := q ^ (2 ^ (j - 1)) with hu_def
  have hu_mem_Q : u ∈ Q := Subgroup.pow_mem Q hqQ _
  have hu_mem_H : u ∈ H := hsplit.le hu_mem_Q
  have hu_sq : u * u = 1 := by
    have h2j : 2 ^ (j - 1) + 2 ^ (j - 1) = 2 ^ j := by
      have h1 : (2 : ℕ) ^ j = 2 ^ (j - 1) * 2 := by
        rw [← pow_succ, Nat.sub_add_cancel hjpos]
      rw [h1]; ring
    rw [hu_def]
    calc q ^ 2 ^ (j - 1) * q ^ 2 ^ (j - 1) = q ^ (2 ^ (j - 1) + 2 ^ (j - 1)) :=
          (pow_add _ _ _).symm
      _ = q ^ 2 ^ j := by rw [h2j]
      _ = q ^ orderOf q := by rw [← hj]
      _ = 1 := pow_orderOf_eq_one q
  have hu_ne_one : u ≠ 1 := by
    intro hu1
    have hdvd2 : orderOf q ∣ 2 ^ (j - 1) := by
      rw [hu_def] at hu1
      exact orderOf_dvd_iff_pow_eq_one.mpr hu1
    rw [hj] at hdvd2
    have hlt : 2 ^ (j - 1) < 2 ^ j :=
      Nat.pow_lt_pow_right (by norm_num)
        (Nat.sub_lt (by omega) (by norm_num))
    have hle : 2 ^ j ≤ 2 ^ (j - 1) :=
      Nat.le_of_dvd (pow_pos (by norm_num) _) hdvd2
    omega
  have hu_ord : orderOf u = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two]; exact hu_sq
    · exact hu_ne_one
  have hdu : d * u * d⁻¹ = u := hconjpow _
  -- Step 5: counting (verbatim from PSU3).
  have hoddD : Odd (Nat.card (Submission.Blueprint.twoPoint H t)) := hH.2.2 t htH
  have hkey1 : ∀ y : G, t * y * t⁻¹ ∈ H ↔ y ∈ conj t H := by
    intro y
    rw [Work.ThreePoints.mem_conj_iff, hti]
  have hkey2 : ∀ y : G, t * y * t⁻¹ ∈ conj t H ↔ y ∈ H := by
    intro y
    rw [Work.ThreePoints.mem_conj_iff]
    constructor
    · intro hy
      have h2 : t⁻¹ * (t * y * t⁻¹) * t = y := by
        rw [hti]
        calc t * (t * y * t) * t = (t * t) * y * (t * t) := by group
          _ = y := by rw [htt, one_mul, mul_one]
      rwa [h2] at hy
    · intro hy
      rw [show t⁻¹ * (t * y * t⁻¹) * t = y from by
        rw [hti]
        calc t * (t * y * t) * t = (t * t) * y * (t * t) := by group
          _ = y := by rw [htt, one_mul, mul_one]]
      exact hy
  have htN : t ∈ Subgroup.normalizer (Submission.Blueprint.twoPoint H t : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    show y ∈ H ⊓ conj t H ↔ t * y * t⁻¹ ∈ H ⊓ conj t H
    rw [Subgroup.mem_inf, Subgroup.mem_inf, hkey1 y, hkey2 y]
    exact ⟨fun hy => ⟨hy.2, hy.1⟩, fun hy => ⟨hy.2, hy.1⟩⟩
  have hcard1 : (Work.ThmF.Kset H t).ncard * Nat.card ↥(Submission.Blueprint.centD H t)
      = Nat.card ↥(Submission.Blueprint.twoPoint H t) :=
    Work.ThmF.Bender.cardInvertedMulCardCentralizer
      (X := Submission.Blueprint.twoPoint H t) hoddD htN ht2
  have hKcard : (Work.ThmF.Kset H t).ncard = (Submission.Blueprint.involutions (H : Set G)).ncard :=
    Work.ThmF.Bender.cardKsetEqInv hH ht2 htH
  have hinj := Work.ThmF.Bender.Kset_conj_injective hH ht2 htH hu_mem_H hu_ord
  intro hVbot
  have hVone : Nat.card ↥(Submission.Blueprint.centD H t) = 1 := by
    rw [hVbot, Subgroup.card_bot]
  have hDcard : Nat.card ↥(Submission.Blueprint.twoPoint H t)
      = (Submission.Blueprint.involutions (H : Set G)).ncard := by
    rw [hVone, mul_one, hKcard] at hcard1
    exact hcard1.symm
  have hDncard : (Submission.Blueprint.twoPoint H t : Set G).ncard
      = (Work.ThmF.Kset H t).ncard := by
    calc (Submission.Blueprint.twoPoint H t : Set G).ncard
        = Nat.card ↥(Submission.Blueprint.twoPoint H t) := (Nat.card_coe_set_eq _).symm
      _ = (Submission.Blueprint.involutions (H : Set G)).ncard := hDcard
      _ = (Work.ThmF.Kset H t).ncard := hKcard.symm
  have hK_eq : Work.ThmF.Kset H t = (Submission.Blueprint.twoPoint H t : Set G) :=
    Set.eq_of_subset_of_ncard_le (Work.ThmF.Kset_subset H t) (le_of_eq hDncard)
  have hdK : d ∈ Work.ThmF.Kset H t := by
    rw [hK_eq]; exact hd_memD
  have h1K : (1 : G) ∈ Work.ThmF.Kset H t := Work.ThmF.one_mem_Kset H t
  have himg : d * u * d⁻¹ = 1 * u * 1⁻¹ := by
    rw [one_mul, inv_one, mul_one]
    exact hdu
  exact hd_ne_one (hinj hdK h1K himg)

/-- **Field 5, corrected** (`Work.ThmG2.ExistsLinearV2Prop`, Peterfalvi II Ch. VI §1 p. 258). -/
theorem existsLinearV2Prop (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp) (hFpf : Work.ThmG.FpfOddPartProp) : Work.ThmG2.ExistsLinearV2Prop := by
  intro G _ _ H Q t hh
  -- the split rank-one datum underlying `hh`
  have hsplit : IsSplitRankOne H Q t := hh.2.2.1
  -- Ch. V §1 Prop. 2: `K = J(D,t)` is cyclic, is `Kset H t`, and is normal in `D`
  obtain ⟨hKcyc, hKset, -⟩ := Work.ThmF.ChV12.Ksub_cyclic_normal hFT hC4 hh.1 hsplit
  -- Peterfalvi II p. 236: `V = C_D(t) ≠ 1`
  have hV : centD H t ≠ ⊥ := centD_aux hFpf hh
  -- Ch. V §1–2: a linear `lam` trivial on `Q` and on `K`
  exact Work.ThmF.ChV12.exists_linear_v2 hFT H Q t hh.1 hsplit hV hKcyc hKset

end Work.BSIntegrate
