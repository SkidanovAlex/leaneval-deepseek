import Mathlib
import Submission.Work.ThmF.ChV12.L6basic
import Submission.Work.ThmF.ChV12.L6faith
import Submission.Work.ThmF.ChV12.W_semireg_defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs

namespace Work.ThmF.ChV12

open Submission.Blueprint Work.ThmF

namespace WLayerSafe

/-- A free action of a finite group on a finite type has group order dividing the cardinality
(copy of `Work.ThmF.ChV12.WCardDvdAux.card_dvd_card_of_free`, kept here so that this module does
not have to import `W_card_dvd`, whose closure contains `L5route` and therefore clashes with
`L6setup`). -/
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


/-! ## §1. Arithmetic: the only odd divisor of both `2 ^ n * (2 ^ n - 1)` and `2 ^ n + 1` is `1`

`q = 2 ^ n`, `d` odd, `d ∣ q (q - 1)` and `d ∣ q + 1` force `d = 1`: coprimality of `d` and
`q` gives `d ∣ q - 1`, hence `d ∣ (q + 1) - (q - 1) = 2`; as `d` is odd, `d = 1`. -/

theorem eq_one_of_dvd_pow_two_sub_and_dvd_add_one {q d : ℕ} (hq : ∃ n : ℕ, q = 2 ^ n)
    (hodd : Odd d) (h1 : d ∣ q ^ 2 - q) (h2 : d ∣ q + 1) : d = 1 := by
  obtain ⟨n, rfl⟩ := hq
  have hcop : Nat.Coprime d (2 ^ n) := (Nat.coprime_two_right.mpr hodd).pow_right n
  have h3 : d ∣ 2 ^ n - 1 := by
    have h4 : d ∣ 2 ^ n * (2 ^ n - 1) := by
      rw [Nat.mul_sub_left_distrib, mul_one, ← pow_two]
      exact h1
    exact hcop.dvd_of_dvd_mul_left h4
  have h5 : d ∣ 2 := by
    have h6 : d ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub h2 h3
    have h7 : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by
      have := Nat.one_le_two_pow (n := n); omega
    rwa [h7] at h6
  rcases (Nat.dvd_prime Nat.prime_two).mp h5 with h | h
  · exact h
  · obtain ⟨k, hk⟩ := hodd
    omega

/-! ## §2. Free action on the complement of a fixed subgroup

Let `A` be an automorphism of a finite group `P`, `Z ≤ M ≤ P` subgroups with `A(M) = M`, with `A`
fixing `Z` pointwise, and suppose that every element of `M` fixed by a non-trivial power of `A`
lies in `Z`.  Then `orderOf A ∣ |M| - |Z|`.

Indeed `⟨A⟩` acts on `M ∖ Z`: a non-trivial `A ^ k` fixing a point of `M` outside `Z` is excluded
by the hypothesis, so the action is free and every orbit has `orderOf A` elements. -/

theorem dvd_card_sub_of_free_on_compl {P : Type} [Group P] [Finite P]
    (A : MulAut P) (Z M : Subgroup P) (hZle : Z ≤ M)
    (hMinv : M.map A.toMonoidHom = M) (hfixZ : ∀ z ∈ Z, A z = z)
    (hfixed : ∀ k : ℕ, 0 < k → A ^ k ≠ 1 → ∀ x ∈ M, (A ^ k) x = x → x ∈ Z) :
    orderOf A ∣ Nat.card ↥M - Nat.card ↥Z := by
  classical
  haveI : Fintype P := Fintype.ofFinite P
  -- The subgroup of automorphisms preserving `M` (as a set).
  let K1 : Subgroup (MulAut P) :=
    { carrier := {g : MulAut P | ∀ x : P, x ∈ M ↔ g x ∈ M}
      one_mem' := by intro x; simp
      mul_mem' := by
        intro g h hg hh x
        rw [MulAut.mul_apply, ← hg (h x), ← hh x]
      inv_mem' := by
        intro g hg x
        have h := hg (g.symm x)
        rw [MulEquiv.apply_symm_apply] at h
        exact h.symm }
  have hAK1 : A ∈ K1 := by
    intro x
    constructor
    · intro hx
      rw [← hMinv]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    · intro hx
      rw [← hMinv] at hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have h1 : y = x := A.injective (by simpa using hyx)
      rwa [h1] at hy
  have hle_K1 : Subgroup.zpowers A ≤ K1 := Subgroup.zpowers_le.mpr hAK1
  -- The subgroup of automorphisms fixing `Z` pointwise.
  let K2 : Subgroup (MulAut P) :=
    { carrier := {g : MulAut P | ∀ z ∈ Z, g z = z}
      one_mem' := by intro z hz; simp
      mul_mem' := by
        intro g h hg hh z hz
        have hz' : h z ∈ Z := by rw [hh z hz]; exact hz
        rw [MulAut.mul_apply, hg (h z) hz', hh z hz]
      inv_mem' := by
        intro g hg z hz
        have h1 := congrArg (fun t => (g.symm : MulAut P) t) (hg z hz)
        rw [MulEquiv.symm_apply_apply] at h1
        exact h1.symm }
  have hAK2 : A ∈ K2 := hfixZ
  have hle_K2 : Subgroup.zpowers A ≤ K2 := Subgroup.zpowers_le.mpr hAK2
  have hMiff : ∀ g ∈ Subgroup.zpowers A, ∀ x : P, x ∈ M ↔ g x ∈ M := by
    intro g hg x
    exact hle_K1 hg x
  have hZfix : ∀ g ∈ Subgroup.zpowers A, ∀ z ∈ Z, g z = z := by
    intro g hg z hz
    exact hle_K2 hg z hz
  -- The complement of `Z` in `M`, on which `⟨A⟩` acts freely.
  let X := {x : ↥M // ((x : ↥M) : P) ∉ Z}
  let act : Subgroup.zpowers A → X → X := fun g x =>
    ⟨⟨(g : MulAut P) ((x.1 : ↥M) : P), (hMiff g g.2 ((x.1 : ↥M) : P)).mp x.1.2⟩, by
      intro hcon
      refine x.2 ?_
      have h1 : ((g : MulAut P))⁻¹ ((g : MulAut P) ((x.1 : ↥M) : P))
          = (g : MulAut P) ((x.1 : ↥M) : P) := by
        have h := hZfix g⁻¹ (Subgroup.inv_mem _ g.2) ((g : MulAut P) ((x.1 : ↥M) : P)) hcon
        simpa using h
      have h2 : ((g : MulAut P))⁻¹ ((g : MulAut P) ((x.1 : ↥M) : P)) = ((x.1 : ↥M) : P) :=
        MulEquiv.symm_apply_apply (g : MulAut P) _
      rw [h2] at h1
      exact h1.symm ▸ hcon⟩
  letI : MulAction (Subgroup.zpowers A) X :=
    { smul := act
      one_smul := fun x => Subtype.ext (Subtype.ext (by
        show (act 1 x).1.1 = x.1.1
        show ((1 : Subgroup.zpowers A) : MulAut P) ((x.1 : ↥M) : P) = ((x.1 : ↥M) : P)
        simp))
      mul_smul := fun p q x => Subtype.ext (Subtype.ext (by
        show (act (p * q) x).1.1 = (act p (act q x)).1.1
        simp only [act, Subgroup.coe_mul, MulAut.mul_apply])) }
  have hfree : ∀ g : Subgroup.zpowers A, g ≠ 1 → ∀ x : X, g • x ≠ x := by
    intro g hg x hcon
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
    have hpos : 0 < orderOf A :=
      Nat.pos_of_dvd_of_pos (orderOf_dvd_natCard A) Nat.card_pos
    have hmne : (orderOf A : ℤ) ≠ 0 := by exact_mod_cast hpos.ne'
    set k : ℕ := (n % (orderOf A : ℤ)).toNat with hk
    have hk_lt : k < orderOf A := by
      have h1 : 0 ≤ n % (orderOf A : ℤ) := Int.emod_nonneg n hmne
      have h2 : n % (orderOf A : ℤ) < (orderOf A : ℤ) :=
        Int.emod_lt_of_pos n (by exact_mod_cast hpos)
      rw [hk]
      exact (Int.toNat_lt h1).mpr h2
    have hk_eq : A ^ k = (g : MulAut P) := by
      rw [← zpow_natCast A k, hk, Int.toNat_of_nonneg (Int.emod_nonneg n hmne),
        zpow_mod_orderOf, hn]
    have hfixpt : (A ^ k) ((x.1 : ↥M) : P) = ((x.1 : ↥M) : P) := by
      have h1 : ((g • x : X) : ↥M) = (x : ↥M) := congrArg Subtype.val hcon
      have h2 : (g : MulAut P) ((x.1 : ↥M) : P) = ((x.1 : ↥M) : P) :=
        congrArg (fun z : ↥M => (z : P)) h1
      rw [hk_eq]
      exact h2
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · apply hg
      apply Subtype.ext
      rw [← hk_eq, hk0, pow_zero]
      exact (Subgroup.coe_one (Subgroup.zpowers A)).symm
    · have hAne : A ^ k ≠ 1 := by
        intro hc
        have hd : orderOf A ∣ k := orderOf_dvd_iff_pow_eq_one.mpr hc
        exact absurd (Nat.le_of_dvd hkpos hd) (not_le.mpr hk_lt)
      exact x.2 (hfixed k hkpos hAne ((x.1 : ↥M) : P) x.1.2 hfixpt)
  haveI : Fintype ↥(Subgroup.zpowers A) := Fintype.ofFinite _
  haveI : Fintype X := Fintype.ofFinite _
  have hdvd := card_dvd_card_of_free (Γ := Subgroup.zpowers A) (X := X) hfree
  rw [Nat.card_zpowers] at hdvd
  have hXcard : Nat.card X = Nat.card ↥M - Nat.card ↥Z := by
    rw [Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl (fun x : ↥M => ((x : ↥M) : P) ∈ Z)]
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    congr 1
    exact Fintype.card_congr (Subgroup.subgroupOfEquivOfLe hZle).toEquiv
  rwa [hXcard] at hdvd

/-! ## §3. The target lemma -/

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}

-- In Peterfalvi II Ch. V §2 Lemma 6: no `w ∈ W = C_V(K)`, `w ≠ 1`, preserves a subgroup
-- `M ≤ ↥Q` of order `|Z(Q)|²` containing `Z(Q)` (a "layer", the preimage of a line of `Q/Z(Q)`).
--
-- Proof route.  Let `A = conjAut w` be the conjugation action of `w` on `↥Q` and `d = orderOf A`.
-- `A` fixes `Z(Q)` pointwise, and `hsemi` applied to the powers `w^i` (`0 < i < d`, so `w^i ≠ 1`,
-- using `W_semireg_defs.conjAut_pow_coe`) gives that every element of `Q` fixed by `A^i` lies in
-- `Q0sub H = Z(Q)`.  Hence on `M ∖ Z(Q)` every `⟨A⟩`-orbit has cardinality exactly `d`, while
-- `Z(Q)` is pointwise fixed, so `d ∣ |M ∖ Z(Q)| = q² - q = q (q-1)` where `q = |Z(Q)| = |Q0sub H|`
-- (`L6basic.center_eq_subgroupOf` plus `Subgroup.subgroupOfEquivOfLe`).  Counting orbits with
-- `Finset.card_eq_sum_card_image` (as in `Work/Higman/Layers/card_dvd_card_sub_one_of_map_xi_eq`)
-- gives the divisibility.  `q = 2^n` because `Q` is a 2-group (`hSuz`), and `d` is odd
-- (`orderOf A ∣ orderOf w ∣ |W|`, and `W ≤ D` has odd order: `L6basic.odd_card_W`), so
-- `d ∣ q - 1` (`Nat.Coprime.dvd_of_dvd_mul_left`).  On the other hand `d ∣ orderOf w ∣ |W| ∣ q + 1`
-- by `hdvd`, so `d ∣ gcd(q-1,q+1) ∣ 2` and, `d` odd, `d = 1`: `conjAut w = 1`, i.e. `w`
-- centralises `Q`, and `w ∈ W ≤ D = twoPoint H t`, so `L6faith.eq_one_of_centralizes_Q` gives
-- `w = 1`, contradicting `hw1`.
--
-- The hypothesis `hcard : |Q| = |Q0sub H|^3` rules out the degenerate case `|Q| = |Z(Q)|^2`, in
-- which `M = ⊤ = Q` would be a layer fixed by `A` (then `M.map A = M`, falsifying the claim).
theorem W_layer_not_preserved {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}
    (hC4 : Submission.Blueprint.ChIIFourProp) (hHig : Submission.Blueprint.HigmanProp)
    (h : Work.ThmF.Lemma5.Hyp5 H Q t s) (hSuz : Submission.Blueprint.IsSuzukiTwoGroup ↥Q)
    (hcard : Nat.card ↥Q = Nat.card ↥(Work.ThmF.Q0sub H) ^ 3)
    (hsemi : ∀ w ∈ Work.ThmF.W H t, w ≠ 1 → ∀ x ∈ Q, w * x = x * w →
      x ∈ Work.ThmF.Q0sub H)
    (hdvd : Nat.card ↥(Work.ThmF.W H t) ∣ Nat.card ↥(Work.ThmF.Q0sub H) + 1)
    {w : G} (hwW : w ∈ Work.ThmF.W H t) (hw1 : w ≠ 1)
    (hwN : w ∈ Subgroup.normalizer (Q : Set G)) :
    ∀ M : Subgroup ↥Q, Subgroup.center ↥Q ≤ M →
      Nat.card ↥M = Nat.card ↥(Subgroup.center ↥Q) ^ 2 →
      M.map (Work.ThmF.ChV12.conjAut w hwN).toMonoidHom ≠ M := by
  classical
  intro M hZle hMcard hMinv
  have hsplit : IsSplitRankOne H Q t := h.split
  have hZeq : Subgroup.center ↥Q = (Work.ThmF.Q0sub H).subgroupOf Q :=
    center_eq_subgroupOf hC4 h hHig hSuz
  have hZcard : Nat.card ↥(Subgroup.center ↥Q) = Nat.card ↥(Work.ThmF.Q0sub H) :=
    card_center_eq hC4 h hHig hSuz
  -- `w` commutes with (the elements of) `Q0sub H = Z(Q)`
  have hwc : ∀ z ∈ Work.ThmF.Q0sub H, w * z = z * w := by
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp
      (W_le_centralizer_Q0sub hC4 h.sit hsplit hwW) z hz).symm
  -- (1) the conjugation action fixes the centre pointwise
  have hfixZ : ∀ z ∈ Subgroup.center ↥Q, (conjAut w hwN) z = z := by
    intro z hz
    have hzg : (z : G) ∈ Work.ThmF.Q0sub H := by
      have h1 : z ∈ (Work.ThmF.Q0sub H).subgroupOf Q := hZeq ▸ hz
      exact Subgroup.mem_subgroupOf.mp h1
    apply Subtype.ext
    rw [conjAut_coe, hwc (z : G) hzg, mul_assoc, mul_inv_cancel, mul_one]
  -- (2) `(conjAut w)^k` fixes `x` iff `w ^ k` commutes with `x`
  have hpow_comm : ∀ k : ℕ, ∀ x : ↥Q,
      ((conjAut w hwN) ^ k) x = x ↔ w ^ k * (x : G) = (x : G) * w ^ k := by
    intro k x
    constructor
    · intro hh
      have h1 : w ^ k * (x : G) * (w ^ k)⁻¹ = (x : G) := by
        have h2 := conjAut_pow_coe w hwN k x
        rw [hh] at h2
        exact h2.symm
      calc w ^ k * (x : G) = (w ^ k * (x : G) * (w ^ k)⁻¹) * (w ^ k) := by group
        _ = (x : G) * w ^ k := by rw [h1]
    · intro hh
      apply Subtype.ext
      rw [conjAut_pow_coe, hh, mul_assoc, mul_inv_cancel, mul_one]
  -- (3) the fixed points of a non-trivial power of the action lie in the centre
  have hfixed : ∀ k : ℕ, 0 < k → (conjAut w hwN) ^ k ≠ 1 →
      ∀ x ∈ M, ((conjAut w hwN) ^ k) x = x → x ∈ Subgroup.center ↥Q := by
    intro k hk0 hAne x hxM hfix
    have hwk_ne : w ^ k ≠ 1 := by
      intro h1
      apply hAne
      apply MulEquiv.ext
      intro y
      show ((conjAut w hwN) ^ k) y = (1 : MulAut ↥Q) y
      rw [MulAut.one_apply]
      apply Subtype.ext
      rw [conjAut_pow_coe, h1, one_mul, inv_one, mul_one]
    have hcomm : w ^ k * (x : G) = (x : G) * w ^ k := (hpow_comm k x).mp hfix
    have hmem : (x : G) ∈ Work.ThmF.Q0sub H :=
      hsemi (w ^ k) (Subgroup.pow_mem _ hwW k) hwk_ne (x : G) x.2 hcomm
    rw [hZeq]
    exact Subgroup.mem_subgroupOf.mpr hmem
  -- (4) divisibility of `|M| - |Z(Q)|`
  have hdvdM : orderOf (conjAut w hwN) ∣
      Nat.card ↥M - Nat.card ↥(Subgroup.center ↥Q) :=
    dvd_card_sub_of_free_on_compl (conjAut w hwN) (Subgroup.center ↥Q) M hZle hMinv hfixZ hfixed
  have hdvd1 : orderOf (conjAut w hwN) ∣
      Nat.card ↥(Work.ThmF.Q0sub H) ^ 2 - Nat.card ↥(Work.ThmF.Q0sub H) := by
    rw [← hZcard, ← hMcard]
    exact hdvdM
  -- (5) the order of the action divides `|W|`
  have hdvdW : orderOf (conjAut w hwN) ∣ Nat.card ↥(Work.ThmF.W H t) := by
    have h1 : orderOf (conjAut w hwN) ∣ orderOf w := by
      rw [orderOf_dvd_iff_pow_eq_one]
      apply MulEquiv.ext
      intro y
      show ((conjAut w hwN) ^ orderOf w) y = (1 : MulAut ↥Q) y
      rw [MulAut.one_apply]
      apply Subtype.ext
      rw [conjAut_pow_coe, pow_orderOf_eq_one, one_mul, inv_one, mul_one]
    have h2 : orderOf w ∣ Nat.card ↥(Work.ThmF.W H t) := by
      have h3 := orderOf_dvd_natCard (⟨w, hwW⟩ : ↥(Work.ThmF.W H t))
      rwa [Subgroup.orderOf_mk] at h3
    exact h1.trans h2
  have hodd : Odd (orderOf (conjAut w hwN)) :=
    (odd_card_W hsplit).of_dvd_nat hdvdW
  -- (6) `|Q0sub H|` is a power of `2`
  have hQ0elem := Q0sub_elementary H (involutions_of_H_commute h.sit hC4 H Q t hsplit)
  have hQ0pgrp : IsPGroup 2 ↥(Work.ThmF.Q0sub H) := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    simpa [pow_two] using hQ0elem.1 (x : G) x.2
  have hpow : ∃ n : ℕ, Nat.card ↥(Work.ThmF.Q0sub H) = 2 ^ n :=
    IsPGroup.exists_card_eq hQ0pgrp
  -- (7) the action is trivial, so `w` centralises `Q`, so `w = 1`
  have hdvd2 : orderOf (conjAut w hwN) ∣ Nat.card ↥(Work.ThmF.Q0sub H) + 1 :=
    hdvdW.trans hdvd
  have hdone : orderOf (conjAut w hwN) = 1 :=
    eq_one_of_dvd_pow_two_sub_and_dvd_add_one hpow hodd hdvd1 hdvd2
  have hA1 : conjAut w hwN = 1 := orderOf_eq_one_iff.mp hdone
  have hcen : ∀ q ∈ Q, w * q = q * w := by
    intro q hq
    have h1 : w * q * w⁻¹ = q := (conjAut_eq_one_iff w hwN).mp hA1 q hq
    calc w * q = (w * q * w⁻¹) * w := by group
      _ = q * w := by rw [h1]
  exact hw1 (eq_one_of_centralizes_Q h.sit hsplit (W_le_twoPoint H t hwW) hcen)

end WLayerSafe

end Work.ThmF.ChV12

/-!
# `Work.ThmF.ChV12.WLayerSafe.W_layer_not_preserved`

Import-safe copy of the fleet-proved lemma `Work.ThmF.ChV12.W_layer_not_preserved`
(`Submission/Work/ThmF/ChV12/W_layer_not_preserved.lean`).  The original module imports
`Submission.Work.ThmF.ChV12.W_card_dvd`, hence (transitively) `Submission.Work.ThmF.ChV12.L5route`;
`L5route` declares a second copy of `Work.ThmF.ChV12.Ksub_eq_Kset_of_W_ne_bot`, so any module that
also imports `L6setup` — as `W_semireg` does, and as the consumer `W_isCyclic` needs — fails to
compile ("environment already contains ...").  The statement and proof below are the same; the one
general input taken from `W_card_dvd` (the Burnside counting lemma) is copied inline as
`WLayerSafe.card_dvd_card_of_free`.
-/
