import Mathlib
import Submission.Work.ZassenhausPSL2.Feit.card_conjClasses_ge
import Submission.Work.ZassenhausPSL2.Basic
import Submission.Work.ZassenhausPSL2.ZData.card_dStab_eq_card_involutions
import Submission.Work.ZassenhausTwoGroup.normalizer_Q_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausPSL2.Feit

section Helpers

variable {G : Type} [Group G]

/-- Elementwise description of `Submission.Blueprint.conj`. -/
lemma mem_conj_gs {H : Subgroup G} {g x : G} :
    x ∈ Submission.Blueprint.conj g H ↔ ∃ h ∈ H, g * h * g⁻¹ = x := by
  rw [Submission.Blueprint.conj, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, hhx⟩
    exact ⟨h, hh, by rw [← hhx]; exact MulAut.conj_apply g h⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, by simpa using MulAut.conj_apply g h⟩

/-- `Q` is non-trivial in a split rank-one datum: `Q = ⊥` would force `D = H`, whose order
would then be both even (strong embedding) and odd (`dStab_odd`). -/
lemma Q_ne_bot_of_split {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) : Q ≠ ⊥ := by
  intro hbot
  have htwo : twoPoint H t = H := by
    have hs : Q ⊔ twoPoint H t = H := h.sup_eq
    rw [hbot, bot_sup_eq] at hs
    exact hs
  have hodd : Odd (Nat.card (twoPoint H t)) :=
    Work.ZassenhausPSL2.dStab_odd H t h.stronglyEmbedded h.not_mem
  rw [htwo] at hodd
  exact (Nat.not_odd_iff_even.mpr h.stronglyEmbedded.2.1) hodd

/-- Conjugation by a fixed group element preserves the number of involutions of a subgroup. -/
lemma ncard_involutions_conj (Q : Subgroup G) (g : G) :
    (involutions (Submission.Blueprint.conj g Q : Set G)).ncard =
      (involutions (Q : Set G)).ncard := by
  have hset : involutions (Submission.Blueprint.conj g Q : Set G) =
      (MulAut.conj g : G → G) '' involutions (Q : Set G) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxQ, hx2⟩ := hx
      have hxQ' : x ∈ Submission.Blueprint.conj g Q := hxQ
      rw [mem_conj_gs] at hxQ'
      obtain ⟨q, hq, hqx⟩ := hxQ'
      refine ⟨q, ⟨hq, ?_⟩, ?_⟩
      · have h1 : orderOf (MulAut.conj g q) = orderOf q :=
          orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective q
        rw [← h1, MulAut.conj_apply g q, hqx]
        exact hx2
      · exact (MulAut.conj_apply g q).trans hqx
    · rintro ⟨q, hq, rfl⟩
      refine ⟨Subgroup.mem_map.mpr ⟨q, hq.1, rfl⟩, ?_⟩
      have h1 : orderOf (MulAut.conj g q) = orderOf q :=
        orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective q
      rw [h1]
      exact hq.2
  rw [hset, Set.ncard_image_of_injective _ (MulAut.conj g).injective]

/-- Every element of a conjugate of a `2`-group `Q` has `2`-power order. -/
lemma Qomega_pow_eq_one {H Q : Subgroup G} (h2 : IsPGroup 2 Q) (ω : G ⧸ H)
    {x : G} (hx : x ∈ Qomega H Q ω) : ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
  rw [Qomega] at hx
  rw [mem_conj_gs] at hx
  obtain ⟨q, hq, hqx⟩ := hx
  obtain ⟨k, hk⟩ := h2 ⟨q, hq⟩
  refine ⟨k, ?_⟩
  have hqk : q ^ (2 ^ k) = 1 := by
    have := congrArg (fun z : ↥Q => (z : G)) hk
    simpa using this
  rw [← hqx,
    show Quotient.out ω * q * (Quotient.out ω)⁻¹ = MulAut.conj (Quotient.out ω) q from
      (MulAut.conj_apply (Quotient.out ω) q).symm,
    ← map_pow, hqk, map_one]

/-- Every element of a conjugate of a `2`-group `Q` has order a power of `2`. -/
lemma Qomega_orderOf {H Q : Subgroup G} (h2 : IsPGroup 2 Q) (ω : G ⧸ H)
    {x : G} (hx : x ∈ Qomega H Q ω) : ∃ n : ℕ, orderOf x = 2 ^ n := by
  obtain ⟨k, hk⟩ := Qomega_pow_eq_one h2 ω hx
  have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨j, hj⟩

end Helpers

theorem qomegaData_nonempty {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (hab : Submission.Blueprint.IsAbelianSubgroup Q) :
    Nonempty (Work.ZassenhausPSL2.Feit.QomegaData H Q t) := by
  classical
  have hQne : Q ≠ ⊥ := Q_ne_bot_of_split h
  have hN : Subgroup.normalizer (Q : Set G) = H :=
    Work.ZassenhausTwoGroup.normalizer_Q_eq h hQne
  have hD : Nat.card ↥(twoPoint H t) = (involutions (Q : Set G)).ncard :=
    Work.ZassenhausPSL2.ZData.card_dStab_eq_card_involutions H Q t h hz hQne h2
  refine ⟨{ normalizer_eq := hN
            card := ?_
            abelian := ?_
            isPGroup := ?_
            twoElt := ?_
            invcard := ?_
            cover := ?_
            inj := ?_ }⟩
  · intro ω
    show Nat.card ↥(Qomega H Q ω) = Nat.card ↥Q
    rw [Qomega]
    exact Subgroup.card_map_of_injective (MulAut.conj (Quotient.out ω)).injective
  · intro ω
    show ∀ x ∈ Qomega H Q ω, ∀ y ∈ Qomega H Q ω, x * y = y * x
    intro x hx y hy
    rw [Qomega] at hx hy
    rw [mem_conj_gs] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    calc (Quotient.out ω * a * (Quotient.out ω)⁻¹) *
            (Quotient.out ω * b * (Quotient.out ω)⁻¹)
        = Quotient.out ω * (a * b) * (Quotient.out ω)⁻¹ := by group
      _ = Quotient.out ω * (b * a) * (Quotient.out ω)⁻¹ := by rw [hab a ha b hb]
      _ = (Quotient.out ω * b * (Quotient.out ω)⁻¹) *
            (Quotient.out ω * a * (Quotient.out ω)⁻¹) := by group
  · intro ω x
    obtain ⟨k, hk⟩ := Qomega_pow_eq_one h2 ω x.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  · intro ω x hx
    exact Qomega_orderOf h2 ω hx
  · intro ω
    have h1 := ncard_involutions_conj Q (Quotient.out ω)
    exact h1.trans hD.symm
  · intro g
    change Submission.Blueprint.conj g Q =
      Submission.Blueprint.conj (Quotient.out ((g : G ⧸ H))) Q
    set a := Quotient.out ((g : G ⧸ H)) with ha
    have hmk : (a : G ⧸ H) = (g : G ⧸ H) := by
      rw [ha]
      exact QuotientGroup.out_eq' _
    have hmem : a⁻¹ * g ∈ H := QuotientGroup.eq.mp hmk
    apply le_antisymm
    · intro x hx
      rw [mem_conj_gs] at hx ⊢
      obtain ⟨q, hq, hqx⟩ := hx
      refine ⟨(a⁻¹ * g) * q * (a⁻¹ * g)⁻¹, ?_, ?_⟩
      · exact (Subgroup.le_normalizer_iff.mp h.normal) (a⁻¹ * g) hmem q hq
      · rw [← hqx]; group
    · intro x hx
      rw [mem_conj_gs] at hx ⊢
      obtain ⟨q, hq, hqx⟩ := hx
      refine ⟨(a⁻¹ * g)⁻¹ * q * (a⁻¹ * g), ?_, ?_⟩
      · simpa using (Subgroup.le_normalizer_iff.mp h.normal) (a⁻¹ * g)⁻¹ (H.inv_mem hmem) q hq
      · rw [← hqx]; group
  · intro ω ω' x hx hx' hx1
    by_contra hne
    rw [Qomega] at hx hx'
    set a := Quotient.out ω with ha
    set b := Quotient.out ω' with hb
    have hab : a⁻¹ * b ∉ H := by
      intro hmem
      apply hne
      have h1 : (a : G ⧸ H) = (b : G ⧸ H) := QuotientGroup.eq.mpr hmem
      have h2 : (a : G ⧸ H) = ω := by rw [ha]; exact QuotientGroup.out_eq' ω
      have h3 : (b : G ⧸ H) = ω' := by rw [hb]; exact QuotientGroup.out_eq' ω'
      exact h2.symm.trans (h1.trans h3)
    have hy : a⁻¹ * x * a ∈ Q := by
      rw [mem_conj_gs] at hx
      obtain ⟨q, hq, hqx⟩ := hx
      rw [← hqx]
      have : a⁻¹ * (a * q * a⁻¹) * a = q := by group
      rw [this]; exact hq
    have hy' : a⁻¹ * x * a ∈ Submission.Blueprint.conj (a⁻¹ * b) Q := by
      rw [mem_conj_gs] at hx'
      rw [mem_conj_gs]
      obtain ⟨q, hq, hqx⟩ := hx'
      refine ⟨q, hq, ?_⟩
      rw [← hqx]; group
    have hbot : a⁻¹ * x * a ∈ (⊥ : Subgroup G) := by
      rw [← Work.ZassenhausTwoGroup.isTI_Q h hz (a⁻¹ * b) hab]
      exact ⟨hy, hy'⟩
    have h1 : a⁻¹ * x * a = 1 := Subgroup.mem_bot.mp hbot
    refine hx1 ?_
    have hx1' : x = a * (a⁻¹ * x * a) * a⁻¹ := by group
    rw [hx1', h1]; group

end Work.ZassenhausPSL2.Feit
