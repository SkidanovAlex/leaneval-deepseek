import Mathlib
import Submission.Work.ThmF.ChV12.L6basic
import Submission.Work.ThmF.ChV12.L5route

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.W_card_dvd` — Peterfalvi II, Ch. V §2, Lemma 6 (divisibility part)

`st` has order `3`, `Q` is a Suzuki 2-group of order `q³` (`q = |Q0sub H|`).  If every
`w ∈ W = C_V(K)` with `w ≠ 1` has `C_Q(w) ⊆ Q0sub H` (the semiregularity
`Work.ThmF.ChV12.W_semireg`), then `|W| ∣ q + 1`.

Route.  WLOG `W ≠ ⊥`.  Then `K = J(D,t)` is a subgroup (`Ksub H t = Kset H t`, Ch. V §1 Prop. 2
in the branch `W ≠ 1`, available from `L5route` without Feit–Thompson) of order `q - 1`, it acts
freely on `Q ∖ Q0sub H` (Ch. V §1 Prop. 1 a: `C_Q(k) = 1` for `k ∈ K^#`), `W` acts freely on
`Q ∖ Q0sub H` (the hypothesis), and the two actions commute because `W = C_V(K)`.  So the product
`K × W` acts freely on `Q ∖ Q0sub H`, whence `(q-1)·|W| ∣ |Q| - q = q³ - q`; as `|W|` is odd
(`W ≤ D` of odd order) and `q` is a power of `2`, Euclid's lemma gives `|W| ∣ q + 1`.

The free action of `K × W` on `Q ∖ Q0sub H` is the group-theoretic core: if `k w x w⁻¹ k⁻¹ = x`
with `k ∈ K`, `w ∈ W`, then squaring gives `w x² w⁻¹ = k⁻¹ x² k`; as `w` centralises
`x² ∈ Q0sub H` (Higman: squares of `Q` are central), `x²` commutes with `k`, so Prop. 1 a
(resp. the semiregularity of `W` when `k = 1`) forces `x² = 1`, i.e. `x ∈ Q0sub H`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.ThmF.ChV12

open LeanEval.GroupTheory.Defs

namespace WCardDvdAux

/-- A free action of a finite group on a finite type has group order dividing the cardinality. -/
theorem card_dvd_card_of_free {Γ X : Type*} [Group Γ] [MulAction Γ X] [Fintype Γ] [Fintype X]
    (hfree : ∀ g : Γ, g ≠ 1 → ∀ x : X, g • x ≠ x) : Nat.card Γ ∣ Nat.card X := by
  classical
  haveI hF : ∀ g : Γ, Fintype ↑(MulAction.fixedBy X g) := fun g => Fintype.ofFinite _
  haveI hQ : Fintype (Quotient (MulAction.orbitRel Γ X)) := Fintype.ofFinite _
  have hburnside := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group Γ X
  have h1card : Fintype.card ↑(MulAction.fixedBy X (1 : Γ)) = Fintype.card X := by simp
  have hsum : (∑ g : Γ, Fintype.card ↑(MulAction.fixedBy X g)) = Fintype.card X := by
    rw [← h1card]
    refine Fintype.sum_eq_single 1 ?_
    intro g hg
    haveI : IsEmpty ↑(MulAction.fixedBy X g) :=
      ⟨fun y => hfree g hg y (MulAction.mem_fixedBy.mp y.2)⟩
    rw [Fintype.card_eq_zero]
  rw [hsum] at hburnside
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact ⟨Fintype.card (Quotient (MulAction.orbitRel Γ X)), by rw [mul_comm]; exact hburnside⟩

/-- Arithmetic: if `q = 2ⁿ ≥ 2` is a power of two and `(q-1)·w ∣ q³ - q` with `w` odd, then
`w ∣ q + 1`.  (`q³ - q = q(q-1)(q+1)`, cancel `q - 1 > 0` and use `gcd (w, q) = 1`.) -/
theorem dvd_add_one_of_mul_dvd_cube_sub (q w : ℕ) (hq : 2 ≤ q) (hpow : ∃ n : ℕ, q = 2 ^ n)
    (hodd : Odd w) (h : (q - 1) * w ∣ q ^ 3 - q) : w ∣ q + 1 := by
  obtain ⟨n, hn⟩ := hpow
  have hfactor : q ^ 3 - q = (q - 1) * (q * (q + 1)) := by
    have h1 : 1 ≤ q := by omega
    have hle : q ≤ q ^ 3 := by
      calc q = q * 1 := (mul_one q).symm
        _ ≤ q * (q * q) := Nat.mul_le_mul_left q (by nlinarith [hq])
        _ = q ^ 3 := by ring
    have hcast : ((q ^ 3 - q : ℕ) : ℤ) = (((q - 1) * (q * (q + 1)) : ℕ) : ℤ) := by
      rw [Nat.cast_sub hle]
      push_cast
      rw [Nat.cast_sub h1]
      ring
    exact_mod_cast hcast
  rw [hfactor] at h
  have hpos : 0 < q - 1 := by omega
  have hw : w ∣ q * (q + 1) := Nat.dvd_of_mul_dvd_mul_left hpos h
  have hcop : Nat.Coprime w q := by
    rw [hn]
    exact (Nat.coprime_two_right.mpr hodd).pow_right n
  exact hcop.dvd_of_dvd_mul_left hw

end WCardDvdAux

theorem W_card_dvd {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}
    (hC4 : Submission.Blueprint.ChIIFourProp) (hHig : Submission.Blueprint.HigmanProp)
    (h : Work.ThmF.Lemma5.Hyp5 H Q t s) (hSuz : Submission.Blueprint.IsSuzukiTwoGroup ↥Q)
    (hcard : Nat.card ↥Q = Nat.card ↥(Work.ThmF.Q0sub H) ^ 3)
    (hsemi : ∀ w ∈ Work.ThmF.W H t, w ≠ 1 → ∀ x ∈ Q, w * x = x * w →
      x ∈ Work.ThmF.Q0sub H) :
    Nat.card ↥(Work.ThmF.W H t) ∣ Nat.card ↥(Work.ThmF.Q0sub H) + 1 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hsplit : Submission.Blueprint.IsSplitRankOne H Q t := h.split
  by_cases hWbot : Work.ThmF.W H t = ⊥
  · rw [hWbot, Subgroup.card_bot]
    exact one_dvd _
  -- ===== main case: `W ≠ ⊥` =====
  -- ## 0. the basic vocabulary
  have hcomm : ∀ a ∈ Submission.Blueprint.involutions (H : Set G),
      ∀ b ∈ Submission.Blueprint.involutions (H : Set G), a * b = b * a :=
    Work.ThmF.L5.involutions_commute h.sit hC4 hsplit
  have hQ0elem := Work.ThmF.ChV12.Q0sub_elementary H hcomm
  have hQ0sq : ∀ x ∈ Work.ThmF.Q0sub H, x * x = 1 := hQ0elem.1
  have hQ0inv : ∀ u ∈ H, ∀ x ∈ Work.ThmF.Q0sub H, u * x * u⁻¹ ∈ Work.ThmF.Q0sub H :=
    hQ0elem.2.2.1
  have hcardQ0 : Nat.card ↥(Work.ThmF.Q0sub H)
      = (Submission.Blueprint.involutions (H : Set G)).ncard + 1 :=
    Work.ThmF.L5.card_Q0sub_eq hcomm
  have hInv2 : 2 ≤ (Submission.Blueprint.involutions (H : Set G)).ncard :=
    Work.ThmF.Bender.cardInvGeTwo hsplit.stronglyEmbedded h.sit.1.1
  have hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t :=
    Work.ThmF.ChV12.Ksub_eq_Kset_of_W_ne_bot hC4 h hWbot
  have hcardKset : (Work.ThmF.Kset H t).ncard
      = (Submission.Blueprint.involutions (H : Set G)).ncard :=
    Work.ThmF.Bender.cardKsetEqInv hsplit.stronglyEmbedded hsplit.invol hsplit.not_mem
  have hcardKsub : Nat.card ↥(Work.ThmF.Ksub H t) = Nat.card ↥(Work.ThmF.Q0sub H) - 1 := by
    have h1 : Nat.card ↥(Work.ThmF.Ksub H t) = (Work.ThmF.Kset H t).ncard := by
      have h1' : Nat.card ↥(Work.ThmF.Ksub H t) = (Work.ThmF.Ksub H t : Set G).ncard := by
        show Nat.card ↥((Work.ThmF.Ksub H t : Set G)) = _
        exact Nat.card_coe_set_eq _
      rw [h1', hKsub]
    rw [h1, hcardKset, hcardQ0]
    omega
  -- ## 1. Higman: squares of `Q` lie in `Q0sub H`, and `Q0sub H = {x | x² = 1}` in `Q`
  have hZ : Subgroup.center ↥Q = (Work.ThmF.Q0sub H).subgroupOf Q :=
    center_eq_subgroupOf hC4 h hHig hSuz
  have hsq0 : ∀ x : ↥Q, ((x ^ 2 : ↥Q) : G) ∈ Work.ThmF.Q0sub H := by
    intro x
    have h1 : x ^ 2 ∈ Subgroup.center ↥Q := (hHig ↥Q hSuz).2.1 x
    rw [hZ] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  have hsqZ : ∀ x : ↥Q, x * x = 1 → (x : G) ∈ Work.ThmF.Q0sub H := by
    intro x hx2
    have hx2' : x ^ 2 = (1 : ↥Q) := by rwa [pow_two]
    have h1 : x ∈ Subgroup.center ↥Q := ((hHig ↥Q hSuz).1 x).mpr hx2'
    rw [hZ] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  have hQ0c : ∀ w ∈ Work.ThmF.W H t, ∀ z ∈ Work.ThmF.Q0sub H, w * z = z * w := by
    intro w hw z hz
    exact (Subgroup.mem_centralizer_iff.mp
      (Work.ThmF.ChV12.W_le_centralizer_Q0sub hC4 h.sit hsplit hw) z hz).symm
  -- ## 2. normalisers of `Q`, and `W` commutes with all of `Ksub = ⟨Kset⟩`
  have hKsubNQ : ∀ k ∈ Work.ThmF.Ksub H t, k ∈ Subgroup.normalizer (Q : Set G) := by
    intro k hk
    exact hsplit.normal (Subgroup.mem_inf.mp (Work.ThmF.Ksub_le_twoPoint (H := H) t hk)).1
  have hW_NQ : ∀ w ∈ Work.ThmF.W H t, w ∈ Subgroup.normalizer (Q : Set G) := by
    intro w hw
    exact hsplit.normal (Subgroup.mem_inf.mp (Work.ThmF.centD_le_twoPoint (H := H) t
      (Work.ThmF.W_le_centD H t hw))).1
  have hWKcomm : ∀ k ∈ Work.ThmF.Ksub H t, ∀ w ∈ Work.ThmF.W H t, w * k = k * w := by
    intro k hk w hw
    have hwc : w ∈ Subgroup.centralizer (Work.ThmF.Kset H t : Set G) := (Subgroup.mem_inf.mp hw).2
    have hle : Work.ThmF.Ksub H t ≤ Subgroup.centralizer ({w} : Set G) := by
      rw [Work.ThmF.Ksub]
      refine (Subgroup.closure_le _).mpr ?_
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hwc x hx)
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hk)).symm
  -- ## 3. the free action of `Ksub × W` on the complement of `Q0sub H` in `Q`
  let act : (↥(Work.ThmF.Ksub H t) × ↥(Work.ThmF.W H t)) →
      {x : ↥Q // (x : G) ∉ Work.ThmF.Q0sub H} →
      {x : ↥Q // (x : G) ∉ Work.ThmF.Q0sub H} :=
    fun p x => ⟨⟨(p.1 : G) * (p.2 : G) * (x.1 : G) * ((p.1 : G) * (p.2 : G))⁻¹, by
        have hmem : (p.1 : G) * (p.2 : G) ∈ Subgroup.normalizer (Q : Set G) :=
          Subgroup.mul_mem _ (hKsubNQ p.1 p.1.2) (hW_NQ p.2 p.2.2)
        exact (Subgroup.mem_normalizer_iff.mp hmem (x.1 : G)).mp x.1.2⟩, by
      intro hcon
      have hdH : (p.1 : G) * (p.2 : G) ∈ H :=
        H.mul_mem (Subgroup.mem_inf.mp (Work.ThmF.Ksub_le_twoPoint (H := H) t p.1.2)).1
          (Subgroup.mem_inf.mp (Work.ThmF.centD_le_twoPoint (H := H) t
            (Work.ThmF.W_le_centD H t p.2.2))).1
      have hinv : ((p.1 : G) * (p.2 : G))⁻¹ ∈ H := H.inv_mem hdH
      have h2 : ((p.1 : G) * (p.2 : G))⁻¹ *
          ((p.1 : G) * (p.2 : G) * (x.1 : G) * ((p.1 : G) * (p.2 : G))⁻¹) *
          ((p.1 : G) * (p.2 : G)) ∈ Work.ThmF.Q0sub H := by
        simpa using hQ0inv (((p.1 : G) * (p.2 : G))⁻¹) hinv
          ((p.1 : G) * (p.2 : G) * (x.1 : G) * ((p.1 : G) * (p.2 : G))⁻¹) hcon
      have heq : ((p.1 : G) * (p.2 : G))⁻¹ *
          ((p.1 : G) * (p.2 : G) * (x.1 : G) * ((p.1 : G) * (p.2 : G))⁻¹) *
          ((p.1 : G) * (p.2 : G)) = (x.1 : G) := by group
      exact x.2 (heq ▸ h2)⟩
  have hact : ∀ (g : ↥(Work.ThmF.Ksub H t) × ↥(Work.ThmF.W H t))
      (y : {x : ↥Q // (x : G) ∉ Work.ThmF.Q0sub H}),
      (((act g y).1 : ↥Q) : G)
        = (g.1 : G) * (g.2 : G) * (y.1 : G) * ((g.1 : G) * (g.2 : G))⁻¹ := fun _ _ => rfl
  letI : MulAction (↥(Work.ThmF.Ksub H t) × ↥(Work.ThmF.W H t))
      {x : ↥Q // (x : G) ∉ Work.ThmF.Q0sub H} :=
    { smul := act
      one_smul := fun x => Subtype.ext (Subtype.ext (by
        change (((act 1 x).1 : ↥Q) : G) = (((x.1 : ↥Q) : G))
        rw [hact]
        simp only [Prod.fst_one, Prod.snd_one, Subgroup.coe_one, one_mul, inv_one]
        group))
      mul_smul := fun p q x => Subtype.ext (Subtype.ext (by
        change (((act (p * q) x).1 : ↥Q) : G) = (((act p (act q x)).1 : ↥Q) : G)
        rw [hact (p * q) x, hact p (act q x), hact q x]
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
        have hc : (p.2 : G) * (q.1 : G) = (q.1 : G) * (p.2 : G) :=
          hWKcomm q.1 q.1.2 p.2 p.2.2
        have hA : ((p.1 : G) * (q.1 : G)) * ((p.2 : G) * (q.2 : G))
            = ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G)) := by
          rw [show ((p.1 : G) * (q.1 : G)) * ((p.2 : G) * (q.2 : G))
              = (p.1 : G) * ((q.1 : G) * (p.2 : G)) * (q.2 : G) from by group, ← hc]
          group
        rw [hA]
        group)) }
  have hfree : ∀ g : ↥(Work.ThmF.Ksub H t) × ↥(Work.ThmF.W H t), g ≠ 1 →
      ∀ x : {x : ↥Q // (x : G) ∉ Work.ThmF.Q0sub H}, g • x ≠ x := by
    intro g hg x hcon
    have hxeq : (g.1 : G) * (g.2 : G) * (x.1 : G) * ((g.1 : G) * (g.2 : G))⁻¹
        = (x.1 : G) := by
      have h1 := congrArg
        (fun y : {x : ↥Q // (x : G) ∉ Work.ThmF.Q0sub H} => ((y.1 : ↥Q) : G)) hcon
      have h2 : (((g • x).1 : ↥Q) : G)
          = (g.1 : G) * (g.2 : G) * (x.1 : G) * ((g.1 : G) * (g.2 : G))⁻¹ :=
        hact g x
      rw [h2] at h1
      exact h1
    by_cases hk : (g.1 : G) = 1
    · -- the `K`-part is trivial: `W` acts freely by the semiregularity hypothesis
      have hxeq' : (g.2 : G) * (x.1 : G) * (g.2 : G)⁻¹ = (x.1 : G) := by
        rw [hk] at hxeq
        simpa using hxeq
      have hg2 : (g.2 : G) ≠ 1 := by
        intro h2
        exact hg (Prod.ext (Subtype.ext hk) (Subtype.ext h2))
      have hcommx : (g.2 : G) * (x.1 : G) = (x.1 : G) * (g.2 : G) := by
        have h2 : (g.2 : G) * (x.1 : G) * (g.2 : G)⁻¹ * (g.2 : G)
            = (x.1 : G) * (g.2 : G) := congrArg (fun y => y * (g.2 : G)) hxeq'
        have h3 : (g.2 : G) * (x.1 : G) * (g.2 : G)⁻¹ * (g.2 : G) = (g.2 : G) * (x.1 : G) := by
          group
        rw [h3] at h2
        exact h2
      exact x.2 (hsemi (g.2 : G) (g.2).2 hg2 (x.1 : G) (x.1).2 hcommx)
    · -- the `K`-part is non-trivial: `x²` commutes with it, contradicting Prop. 1 a
      have hkK : (g.1 : G) ∈ Work.ThmF.Kset H t := by
        rw [← hKsub]; exact g.1.2
      have hstep : (g.2 : G) * (x.1 : G) * (g.2 : G)⁻¹
          = (g.1 : G)⁻¹ * (x.1 : G) * (g.1 : G) := by
        have h2 := congrArg (fun y => (g.1 : G)⁻¹ * y * (g.1 : G)) hxeq
        rw [← h2]; group
      have hsq : (g.2 : G) * ((x.1 : G) * (x.1 : G)) * (g.2 : G)⁻¹
          = (g.1 : G)⁻¹ * ((x.1 : G) * (x.1 : G)) * (g.1 : G) := by
        have h2 := congrArg (fun y : G => y * y) hstep
        rw [show (g.2 : G) * (x.1 : G) * (g.2 : G)⁻¹ * ((g.2 : G) * (x.1 : G) * (g.2 : G)⁻¹)
              = (g.2 : G) * ((x.1 : G) * (x.1 : G)) * (g.2 : G)⁻¹ from by group,
          show ((g.1 : G)⁻¹ * (x.1 : G) * (g.1 : G)) * ((g.1 : G)⁻¹ * (x.1 : G) * (g.1 : G))
              = (g.1 : G)⁻¹ * ((x.1 : G) * (x.1 : G)) * (g.1 : G) from by group] at h2
        exact h2
      have hsq0x : (x.1 : G) * (x.1 : G) ∈ Work.ThmF.Q0sub H := by
        have h3 := hsq0 x.1
        rwa [pow_two, Subgroup.coe_mul] at h3
      have hfix2 : (g.2 : G) * ((x.1 : G) * (x.1 : G)) * (g.2 : G)⁻¹
          = (x.1 : G) * (x.1 : G) := by
        rw [hQ0c (g.2 : G) (g.2).2 ((x.1 : G) * (x.1 : G)) hsq0x]
        group
      rw [hfix2] at hsq
      have hcommk : ((x.1 : G) * (x.1 : G)) * (g.1 : G)
          = (g.1 : G) * ((x.1 : G) * (x.1 : G)) := by
        have h2 : (g.1 : G) * ((x.1 : G) * (x.1 : G))
            = ((x.1 : G) * (x.1 : G)) * (g.1 : G) := by
          have h3 := congrArg (fun y => (g.1 : G) * y) hsq
          rw [show (g.1 : G) * ((g.1 : G)⁻¹ * ((x.1 : G) * (x.1 : G)) * (g.1 : G))
              = ((x.1 : G) * (x.1 : G)) * (g.1 : G) from by group] at h3
          exact h3
        exact h2.symm
      have hone : (x.1 : G) * (x.1 : G) = 1 :=
        Work.ThmF.ChV12.prop1a h.sit hC4 H Q t hsplit (g.1 : G) hkK hk
          ((x.1 : G) * (x.1 : G)) (Q.mul_mem (x.1).2 (x.1).2) hcommk
      exact x.2 (hsqZ x.1 (Subtype.ext hone))
  -- ## 4. cardinality and arithmetic
  have hdvd := WCardDvdAux.card_dvd_card_of_free (Γ := ↥(Work.ThmF.Ksub H t) ×
    ↥(Work.ThmF.W H t)) (X := {x : ↥Q // (x : G) ∉ Work.ThmF.Q0sub H}) hfree
  have hXcard : Nat.card {x : ↥Q // (x : G) ∉ Work.ThmF.Q0sub H}
      = Nat.card ↥Q - Nat.card ↥(Work.ThmF.Q0sub H) := by
    rw [Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl (fun x : ↥Q => (x : G) ∈ Work.ThmF.Q0sub H)]
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    congr 1
    exact Fintype.card_congr (Subgroup.subgroupOfEquivOfLe (Q0sub_le_Q hsplit)).toEquiv
  rw [hXcard, Nat.card_prod, hcardKsub, hcard] at hdvd
  have hQ0pgrp : IsPGroup 2 ↥(Work.ThmF.Q0sub H) := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    simpa [pow_two] using hQ0sq x x.2
  refine WCardDvdAux.dvd_add_one_of_mul_dvd_cube_sub (Nat.card ↥(Work.ThmF.Q0sub H))
    (Nat.card ↥(Work.ThmF.W H t)) ?_ ?_ (Work.ThmF.ChV12.odd_card_W hsplit) hdvd
  · rw [hcardQ0]; omega
  · exact IsPGroup.exists_card_eq hQ0pgrp

end Work.ThmF.ChV12
