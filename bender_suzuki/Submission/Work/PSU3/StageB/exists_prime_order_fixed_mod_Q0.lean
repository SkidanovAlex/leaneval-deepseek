import Mathlib
import Submission.Work.PSU3.StageB.NotFpfAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB

open LeanEval.GroupTheory.Defs Submission.Blueprint
open Work.ThmF

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-! ## The fixator of a coset modulo `Q₀` is a subgroup -/

/-- **The fixator of a coset modulo `Q₀` is a subgroup.**  For a split rank-one datum
`H = Q ⋊ D` and a coarse frame `fr` (so `Q₀ = Z(Q)`), the set of `d ∈ D = twoPoint H t`
with `d⁻¹ * x * d * x⁻¹ ∈ Q₀` is a subgroup of `G`: it is the stabiliser of the coset
`x Q₀` under the conjugation action of `D` on `Q/Q₀` (`D ≤ H` normalises `Q`, and `Q₀`,
being the set of involutions of `Q`, is characteristic in `Q`). -/
lemma fixatorQ0_subgroup (h : IsSplitRankOne H Q t) (fr : CoarseFrame H Q t n) (x : G) :
    ∃ S : Subgroup G, S ≤ twoPoint H t ∧
      ∀ d : G, d ∈ S ↔ d ∈ twoPoint H t ∧ d⁻¹ * x * d * x⁻¹ ∈ fr.Q0 := by
  -- Conjugation by any `d ∈ D` preserves `Q₀`.
  have hconj : ∀ d ∈ (twoPoint H t : Subgroup G), ∀ q ∈ fr.Q0, d⁻¹ * q * d ∈ fr.Q0 := by
    intro d hd q hq
    have hdH : d ∈ H := (Subgroup.mem_inf.mp hd).1
    have hqQ : q ∈ Q := fr.Q0_le hq
    have hmemQ : d⁻¹ * q * d ∈ Q := by
      simpa using Work.RankOneUniqueness.conj_mem_of_mem h (H.inv_mem hdH) hqQ
    have hq2 : q ^ 2 = 1 := Q0_sq_eq_one fr hq
    have hsq : (d⁻¹ * q * d) ^ 2 = 1 := by
      have h2 : (d⁻¹ * q * d) ^ 2 = d⁻¹ * q ^ 2 * d := by rw [pow_two, pow_two]; group
      rw [h2, hq2]; group
    exact (fr.mem_Q0_iff _ hmemQ).mpr hsq
  refine ⟨{ carrier := {d | d ∈ twoPoint H t ∧ d⁻¹ * x * d * x⁻¹ ∈ fr.Q0},
            mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, ?_, ?_⟩
  · -- multiplicativity: `(ab)⁻¹ x (ab) x⁻¹ = (b⁻¹ q_a b) · q_b`
    intro a b ha hb
    obtain ⟨haD, hafix⟩ := ha
    obtain ⟨hbD, hbfix⟩ := hb
    refine ⟨(twoPoint H t).mul_mem haD hbD, ?_⟩
    set qa := a⁻¹ * x * a * x⁻¹ with hqa
    have hha : a⁻¹ * x * a = qa * x := by rw [hqa]; group
    set qb := b⁻¹ * x * b * x⁻¹ with hqb
    have hhb : b⁻¹ * x * b = qb * x := by rw [hqb]; group
    have key : (a * b)⁻¹ * x * (a * b) * x⁻¹ = (b⁻¹ * qa * b) * qb := by
      rw [mul_inv_rev]
      calc b⁻¹ * a⁻¹ * x * (a * b) * x⁻¹
          = b⁻¹ * (a⁻¹ * x * a) * b * x⁻¹ := by group
        _ = b⁻¹ * (qa * x) * b * x⁻¹ := by rw [hha]
        _ = (b⁻¹ * qa * b) * (b⁻¹ * x * b) * x⁻¹ := by group
        _ = (b⁻¹ * qa * b) * (qb * x) * x⁻¹ := by rw [hhb]
        _ = (b⁻¹ * qa * b) * qb := by group
    rw [key]
    exact fr.Q0.mul_mem (hconj b hbD qa hafix) hbfix
  · -- neutral element
    refine ⟨(twoPoint H t).one_mem, ?_⟩
    have : (1 : G)⁻¹ * x * 1 * x⁻¹ = 1 := by group
    rw [this]; exact fr.Q0.one_mem
  · -- inverses: `a x a⁻¹ x⁻¹ = a q_a a⁻¹`
    intro a ha
    obtain ⟨haD, hafix⟩ := ha
    refine ⟨(twoPoint H t).inv_mem haD, ?_⟩
    set qa := a⁻¹ * x * a * x⁻¹ with hqa
    have hha : a⁻¹ * x * a = qa * x := by rw [hqa]; group
    have hxa : x * a = a * qa * x := by
      calc x * a = a * (a⁻¹ * x * a) := by group
        _ = a * (qa * x) := by rw [hha]
        _ = a * qa * x := by group
    have hxax : x * a * x⁻¹ = a * qa := by rw [hxa]; group
    have hxainv : x * a⁻¹ * x⁻¹ = qa * a⁻¹ := by
      have h1 : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
      rw [h1, hxax, mul_inv_rev, Q0_inv_eq_self fr hafix]
    have key : a * x * a⁻¹ * x⁻¹ = a * qa * a⁻¹ := by
      calc a * x * a⁻¹ * x⁻¹ = a * (x * a⁻¹ * x⁻¹) := by group
        _ = a * (qa * a⁻¹) := by rw [hxainv]
        _ = a * qa * a⁻¹ := by group
    rw [inv_inv, key]
    simpa using hconj a⁻¹ ((twoPoint H t).inv_mem haD) qa hafix
  · exact fun d hd => hd.1
  · intro d
    rfl

/-! ## A nontrivial finite group has a subgroup of prime order -/

/-- Every nontrivial subgroup of a finite group contains a subgroup of prime order. -/
lemma exists_prime_card_subgroup_of_ne_bot (S : Subgroup G) (hS : S ≠ ⊥) :
    ∃ P : Subgroup G, P ≤ S ∧ (Nat.card P).Prime := by
  haveI : Fintype ↥S := Fintype.ofFinite ↥S
  have hcard1 : Nat.card ↥S ≠ 1 := fun h => hS ((Subgroup.card_eq_one).mp h)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcard1
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hpdvd' : p ∣ Fintype.card ↥S := by simpa [Nat.card_eq_fintype_card] using hpdvd
  obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card (G := ↥S) p hpdvd'
  refine ⟨Subgroup.zpowers (e : G), ?_, ?_⟩
  · rw [Subgroup.zpowers_le]; exact e.2
  · rw [Nat.card_zpowers, Subgroup.orderOf_coe, he]; exact hp

/-! ## The main lemma -/

/-- **Existence of a prime-order subgroup of `D` with a fixed coset.**  If `D = twoPoint H t`
does not act fixed-point-freely on `(Q/Q₀)#` (i.e. `¬ DFpfBar H Q t`), then there is a
non-identity `x ∈ Q \ Q₀` whose coset `x Q₀` is fixed by a subgroup `P ≤ D` of prime order.

Indeed, `¬ DFpfBar` provides a non-identity `d ∈ D` fixing the coset of some `x ∈ Q \ Q₀`;
the fixator `S` of that coset is a nontrivial subgroup of `D`, and `S` contains a subgroup
`P` of prime order, which then fixes `x` modulo `Q₀`. -/
theorem exists_prime_order_fixed_mod_Q0 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) {n : ℕ} (fr : Work.PSU3.CoarseFrame H Q t n)
    (hnfpf : ¬ Work.PSU3.DFpfBar H Q t) :
    ∃ P : Subgroup G, P ≤ Submission.Blueprint.twoPoint H t ∧ (Nat.card P).Prime ∧
      ∃ x ∈ Q, x ∉ fr.Q0 ∧ ∀ p ∈ P, p⁻¹ * x * p * x⁻¹ ∈ fr.Q0 := by
  obtain ⟨d, hd, hd1, x, hx, hx0, hfix⟩ := notDFpfBar_witness hS fr hnfpf
  obtain ⟨S, hSle, hSmem⟩ := fixatorQ0_subgroup hS.split fr x
  have hdS : d ∈ S := (hSmem d).mpr ⟨hd, hfix⟩
  have hSne : S ≠ ⊥ := by
    intro hbot
    rw [hbot] at hdS
    exact hd1 (Subgroup.mem_bot.mp hdS)
  obtain ⟨P, hPS, hPprime⟩ := exists_prime_card_subgroup_of_ne_bot S hSne
  refine ⟨P, hPS.trans hSle, hPprime, x, hx, hx0, ?_⟩
  intro p hp
  exact ((hSmem p).mp (hPS hp)).2

end Work.PSU3.StageB
