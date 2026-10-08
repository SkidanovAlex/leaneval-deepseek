import Mathlib
import Submission.Work.ThmF.ChV12.L6basic
import Submission.Work.ThmF.ChV12.L6faith
import Submission.Work.ThmF.ChV12.L6setup
import Submission.Work.ThmF.ChV12.W_semireg_defs
import Submission.Work.PSU3.StageA.suzuki_odd_order_fixed_eq_center
import Submission.Work.ThmF.Bender.cardKsetEqInv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.W_semireg` — Peterfalvi II, Ch. V §2, Lemma 6 (semiregularity of `W`)

Statement: in the situation `(B0)–(B2)` with a split rank-one datum `H = Q ⋊ D`, `t ∉ H` an
involution, `s ∈ Q` with `o(st) = 3`, `Q` a Suzuki `2`-group and `|Q| = |Q₀|³`, the group
`W = C_V(K)` (`K = J(D,t)`) acts **semiregularly** on `Q/Q₀`:

> for `w ∈ W`, `w ≠ 1`, and `x ∈ Q` with `w x = x w` one has `x ∈ Q₀ = Q0sub H`.

Proof, following the route of `Submission/Work/PSU3/StageA/caseC_W_semireg.lean` with the
`PSU3Hyp` hypotheses weakened to `Hyp5`:

* `W ≠ ⊥`, so `K = Ksub H t = Kset H t` is cyclic (`L6setup`) with a generator `k`; write
  `ξ = conjAut k`, `A = conjAut w` for the conjugation actions on `↥Q`.
* `ξ` has order `q - 1` (`q = |Q₀| = |Z(Q)|`, Higman) and every non-trivial power of `ξ` is
  fixed-point-free on `Q ∖ {1}` (Prop. 1 (a)); with `|Q| = q³` this is `FpfXi ξ`.
* `A` has odd order, is non-trivial (else `w ∈ C_D(Q) = 1`), fixes `Z(Q)` pointwise (`W`
  centralises `Q₀ = Z(Q)`) and commutes with `ξ` (as `w` commutes with `k ∈ K#`), so
  `suzuki_odd_order_fixed_eq_center` gives `C_Q(A) ≤ Z(Q) = Q₀`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open LeanEval.GroupTheory.Defs
open scoped commutatorElement

namespace Work.ThmF.ChV12

open Submission.Blueprint Work.ThmF

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}

/-! ## §1. `Ksub H t` in the `Hyp5` setting -/

/-- `Ksub H t ≤ H`. -/
theorem Ksub_le_H_hyp5 (H : Subgroup G) (t : G) : Ksub H t ≤ H :=
  (Subgroup.closure_le H).mpr fun _ hx => (Kset_subset H t hx).1

/-- `Ksub H t ⊆ twoPoint H t` once `Ksub H t = Kset H t`. -/
theorem Ksub_subset_twoPoint (t : G) (hKsub : (Ksub H t : Set G) = Kset H t) :
    Ksub H t ≤ twoPoint H t := by
  intro x hx
  exact Kset_subset H t (hKsub ▸ hx)

/-- `|K| = |Q₀| - 1` (Ch. I §2: `|Kset H t| = |Inv H| = |Q₀| - 1`). -/
theorem card_Ksub_eq (hC4 : ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s)
    (hKsub : (Ksub H t : Set G) = Kset H t) :
    Nat.card ↥(Ksub H t) = Nat.card ↥(Q0sub H) - 1 := by
  have h1 : Nat.card ↥(Ksub H t) = (Kset H t).ncard := by
    have h0 : Nat.card ↥(Ksub H t) = (Ksub H t : Set G).ncard := Nat.card_coe_set_eq _
    rw [h0, hKsub]
  have h2 : (Kset H t).ncard = (involutions (H : Set G)).ncard :=
    Work.ThmF.Bender.cardKsetEqInv h.split.stronglyEmbedded h.split.invol h.split.not_mem
  have h3 := card_Q0sub_eq (H := H) hC4 h
  rw [h1, h2]
  omega

/-- A cyclic `Ksub H t` has a generator `k` with `⟨k⟩ = Ksub H t`. -/
theorem exists_generator_Ksub (hcyc : IsCyclic ↥(Ksub H t)) :
    ∃ k : G, k ∈ Ksub H t ∧ Subgroup.zpowers k = Ksub H t := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(Ksub H t))
  refine ⟨(g : G), g.2, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← hn]
    exact (Ksub H t).zpow_mem g.2 n
  · intro hx
    have h1 : (⟨x, hx⟩ : ↥(Ksub H t)) ∈ Subgroup.zpowers g := hg ⟨x, hx⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h1
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩

/-- `orderOf k = |Ksub H t|` for a generator `k`. -/
theorem orderOf_generator {k : G} (hkK : k ∈ Ksub H t)
    (hkgen : Subgroup.zpowers k = Ksub H t) :
    orderOf k = Nat.card ↥(Ksub H t) := by
  have h1 : orderOf (⟨k, hkK⟩ : ↥(Ksub H t)) = Nat.card ↥(Ksub H t) := by
    refine orderOf_eq_card_of_zpowers_eq_top ?_
    ext y
    constructor
    · intro _; trivial
    · intro _
      have hy : (y : G) ∈ Subgroup.zpowers k := by rw [hkgen]; exact y.2
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext (by simpa using hn)⟩
  rw [← h1]
  exact Subgroup.orderOf_coe (⟨k, hkK⟩ : ↥(Ksub H t))

/-! ## §2. The order of the conjugation action of a generator of `K` -/

/-- `orderOf (conjAut k) = |Q₀| - 1`: the powers of `k` which fix all of `Q` are exactly the
multiples of `|K|`, by the faithfulness of `D` on `Q` (`L6faith`). -/
theorem orderOf_conjAut (hC4 : ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s)
    (hKsub : (Ksub H t : Set G) = Kset H t) {k : G} (hkK : k ∈ Ksub H t)
    (hkgen : Subgroup.zpowers k = Ksub H t)
    (hkN : k ∈ Subgroup.normalizer (Q : Set G)) :
    orderOf (conjAut k hkN) = Nat.card ↥(Q0sub H) - 1 := by
  have hkm : k ^ Nat.card ↥(Ksub H t) = 1 := by
    rw [← orderOf_generator hkK hkgen]
    exact pow_orderOf_eq_one k
  have hdvd1 : orderOf (conjAut k hkN) ∣ Nat.card ↥(Ksub H t) := by
    rw [orderOf_dvd_iff_pow_eq_one]
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    rw [conjAut_pow_coe, hkm]
    simp
  have hdvd2 : Nat.card ↥(Ksub H t) ∣ orderOf (conjAut k hkN) := by
    have hfix : ∀ x ∈ Q,
        k ^ orderOf (conjAut k hkN) * x * (k ^ orderOf (conjAut k hkN))⁻¹ = x := by
      intro x hx
      have h1 : ((conjAut k hkN) ^ orderOf (conjAut k hkN)) ⟨x, hx⟩
          = (1 : MulAut ↥Q) ⟨x, hx⟩ := by rw [pow_orderOf_eq_one]
      have h2 := congrArg (fun z : ↥Q => (z : G)) h1
      rw [conjAut_pow_coe] at h2
      simpa using h2
    have hcent : ∀ x ∈ Q,
        k ^ orderOf (conjAut k hkN) * x = x * k ^ orderOf (conjAut k hkN) := by
      intro x hx
      have h1 := hfix x hx
      have h2 := congrArg (fun z => z * k ^ orderOf (conjAut k hkN)) h1
      simpa [mul_assoc] using h2
    have hknD : k ^ orderOf (conjAut k hkN) ∈ twoPoint H t :=
      Ksub_subset_twoPoint (H := H) t hKsub ((Ksub H t).pow_mem hkK _)
    have hkn1 : k ^ orderOf (conjAut k hkN) = 1 :=
      eq_one_of_centralizes_Q h.sit h.split hknD hcent
    rw [← orderOf_generator hkK hkgen]
    exact orderOf_dvd_iff_pow_eq_one.mpr hkn1
  rw [← card_Ksub_eq (H := H) hC4 h hKsub]
  exact Nat.dvd_antisymm hdvd1 hdvd2

/-- Every non-trivial power of `conjAut k` is fixed-point-free on `Q ∖ {1}` (Prop. 1 (a)). -/
theorem conjAut_pow_fpf (hC4 : ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s)
    (hKsub : (Ksub H t : Set G) = Kset H t) {k : G} (hkK : k ∈ Ksub H t)
    (hkN : k ∈ Subgroup.normalizer (Q : Set G)) :
    ∀ n : ℕ, (conjAut k hkN) ^ n ≠ 1 → ∀ x : ↥Q, ((conjAut k hkN) ^ n) x = x → x = 1 := by
  intro n hn x hx
  have hknK : k ^ n ∈ Ksub H t := (Ksub H t).pow_mem hkK n
  have hknKset : k ^ n ∈ Kset H t := hKsub ▸ hknK
  have hne : k ^ n ≠ 1 := by
    intro h1
    refine hn ?_
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    rw [conjAut_pow_coe, h1]
    simp
  have hcomm : (x : G) * k ^ n = k ^ n * (x : G) := by
    have h2 : k ^ n * (x : G) * (k ^ n)⁻¹ = (x : G) := by
      have hc := congrArg (fun z : ↥Q => (z : G)) hx
      rwa [conjAut_pow_coe] at hc
    have h3 := congrArg (fun z => z * (k ^ n)) h2
    exact (by simpa [mul_assoc] using h3 : k ^ n * (x : G) = (x : G) * k ^ n).symm
  have hq : (x : G) = 1 :=
    prop1a h.sit hC4 H Q t h.split (k ^ n) hknKset hne (x : G) x.2 hcomm
  exact Subtype.ext hq

/-- **`FpfXi` for the conjugation action of a generator of `K`.**  With `q = |Q₀| = |Z(Q)|`,
`|Q| = q³` (`hcard`), `conjAut k` has order `q - 1` and all its non-trivial powers are
fixed-point-free. -/
theorem fpfXi_conjAut (hC4 : ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s)
    (hHig : HigmanProp) (hSuz : IsSuzukiTwoGroup ↥Q)
    (hcard : Nat.card ↥Q = Nat.card ↥(Q0sub H) ^ 3)
    (hKsub : (Ksub H t : Set G) = Kset H t) {k : G} (hkK : k ∈ Ksub H t)
    (hkgen : Subgroup.zpowers k = Ksub H t)
    (hkN : k ∈ Subgroup.normalizer (Q : Set G)) :
    Work.Higman.FpfXi (conjAut k hkN) := by
  have hc : Nat.card ↥(Subgroup.center ↥Q) = Nat.card ↥(Q0sub H) :=
    card_center_eq hC4 h hHig hSuz
  refine ⟨?_, ?_, ?_⟩
  · rw [hc]; exact hcard
  · rw [orderOf_conjAut (H := H) hC4 h hKsub hkK hkgen hkN, hc]
  · exact conjAut_pow_fpf (H := H) hC4 h hKsub hkK hkN

/-! ## §3. Lemma 6: semiregularity of `W` on `Q/Q₀` -/

theorem W_semireg {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}
    (hC4 : Submission.Blueprint.ChIIFourProp) (hHig : Submission.Blueprint.HigmanProp)
    (h : Work.ThmF.Lemma5.Hyp5 H Q t s) (hSuz : Submission.Blueprint.IsSuzukiTwoGroup ↥Q)
    (hcard : Nat.card ↥Q = Nat.card ↥(Work.ThmF.Q0sub H) ^ 3) :
    ∀ w ∈ Work.ThmF.W H t, w ≠ 1 → ∀ x ∈ Q, w * x = x * w → x ∈ Work.ThmF.Q0sub H := by
  intro w hwW hw1 x hxQ hxcomm
  by_cases hW : W H t = ⊥
  · exact absurd (Subgroup.mem_bot.mp (hW ▸ hwW)) hw1
  obtain ⟨hKsub, hcyc⟩ := Ksub_eq_Kset_and_cyclic_of_W_ne_bot h.sit h.split hC4 hW
  obtain ⟨k, hkK, hkgen⟩ := exists_generator_Ksub (H := H) (t := t) hcyc
  have hkN : k ∈ Subgroup.normalizer (Q : Set G) := h.split.normal (Ksub_le_H_hyp5 H t hkK)
  have hfpf : Work.Higman.FpfXi (conjAut k hkN) :=
    fpfXi_conjAut hC4 h hHig hSuz hcard hKsub hkK hkgen hkN
  -- Higman's structure of `Q`
  have hsq : ∀ y : ↥Q, y ^ 2 ∈ Subgroup.center ↥Q := (hHig ↥Q hSuz).2.1
  have hzsq : ∀ z : ↥Q, z ∈ Subgroup.center ↥Q → z ^ 2 = 1 :=
    fun z hz => ((hHig ↥Q hSuz).1 z).mp hz
  have hcommc : ∀ y z : ↥Q, y * z * y⁻¹ * z⁻¹ ∈ Subgroup.center ↥Q := by
    intro y z
    have hc := (hHig ↥Q hSuz).2.2.1
    have h1 : ⁅y, z⁆ ∈ commutator ↥Q :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top z)
    rw [hc] at h1
    simpa [commutatorElement_def] using h1
  obtain ⟨hSuz2⟩ := (Work.Higman.isSuzukiTwoGroup_iff_nonempty_isSuzuki2Grp).mp hSuz
  -- the conjugation action of `w`
  have hwD : w ∈ twoPoint H t :=
    centD_le_twoPoint (H := H) t (W_le_centD H t hwW)
  have hwN : w ∈ Subgroup.normalizer (Q : Set G) := h.split.normal (Subgroup.mem_inf.mp hwD).1
  -- `A = conjAut w` commutes with `ξ = conjAut k`
  have hwK : ∀ c ∈ Kset H t, w * c = c * w :=
    fun c hc => (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hwW).2 c hc).symm
  have hwk : w * k = k * w := hwK k (hKsub ▸ hkK)
  have hAc : conjAut w hwN * conjAut k hkN = conjAut k hkN * conjAut w hwN := by
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    show w * (k * (z : G) * k⁻¹) * w⁻¹ = k * (w * (z : G) * w⁻¹) * k⁻¹
    have h1 : w * (k * (z : G) * k⁻¹) * w⁻¹ = (w * k) * (z : G) * (w * k)⁻¹ := by group
    have h2 : (w * k) * (z : G) * (w * k)⁻¹ = (k * w) * (z : G) * (k * w)⁻¹ := by rw [hwk]
    have h3 : (k * w) * (z : G) * (k * w)⁻¹ = k * (w * (z : G) * w⁻¹) * k⁻¹ := by group
    rw [h1, h2, h3]
  -- `A` fixes `Z(Q) = Q₀` pointwise
  have hAfix : ∀ z ∈ Subgroup.center ↥Q, conjAut w hwN z = z := by
    intro z hz
    have hzQ0 : (z : G) ∈ Q0sub H :=
      Subgroup.mem_subgroupOf.mp (by rw [← center_eq_subgroupOf hC4 h hHig hSuz]; exact hz)
    have hzc := Subgroup.mem_centralizer_iff.mp
      (W_le_centralizer_Q0sub hC4 h.sit h.split hwW) (z : G) hzQ0
    apply Subtype.ext
    rw [conjAut_coe]
    show w * (z : G) * w⁻¹ = (z : G)
    rw [← hzc, mul_assoc, mul_inv_cancel, mul_one]
  -- `A ≠ 1` (faithfulness of `D` on `Q`)
  have hA1 : conjAut w hwN ≠ 1 := by
    intro hA
    have hcent : ∀ q ∈ Q, w * q = q * w := by
      intro q hq
      have h1 := (conjAut_eq_one_iff w hwN).mp hA q hq
      have h2 := congrArg (fun y => y * w) h1
      simpa [mul_assoc] using h2
    exact hw1 (eq_one_of_centralizes_Q h.sit h.split hwD hcent)
  -- `orderOf A` is odd
  have hoddw : Odd (orderOf w) := by
    have h1 : orderOf (⟨w, hwD⟩ : ↥(twoPoint H t)) ∣ Nat.card ↥(twoPoint H t) :=
      orderOf_dvd_natCard _
    have h2 : orderOf (⟨w, hwD⟩ : ↥(twoPoint H t)) = orderOf w :=
      (Subgroup.orderOf_coe _).symm
    rw [← h2]
    exact (split_odd_card_twoPoint h.split).of_dvd_nat h1
  have hoddA : Odd (orderOf (conjAut w hwN)) := by
    have hdvd : orderOf (conjAut w hwN) ∣ orderOf w := by
      rw [orderOf_dvd_iff_pow_eq_one]
      apply MulEquiv.ext
      intro z
      apply Subtype.ext
      rw [conjAut_pow_coe]
      simp
    exact hoddw.of_dvd_nat hdvd
  -- the Suzuki core
  have hcore := Work.PSU3.StageA.suzuki_odd_order_fixed_eq_center hSuz2 hfpf hsq hzsq hcommc
    hoddA hAc hAfix hA1
  have hfix : conjAut w hwN ⟨x, hxQ⟩ = ⟨x, hxQ⟩ := by
    apply Subtype.ext
    rw [conjAut_coe]
    show w * x * w⁻¹ = x
    rw [hxcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hxcenter : (⟨x, hxQ⟩ : ↥Q) ∈ Subgroup.center ↥Q := hcore ⟨x, hxQ⟩ hfix
  have hxcenter' : (⟨x, hxQ⟩ : ↥Q) ∈ (Q0sub H).subgroupOf Q := by
    rwa [← center_eq_subgroupOf hC4 h hHig hSuz]
  simpa using Subgroup.mem_subgroupOf.mp hxcenter'

end Work.ThmF.ChV12
