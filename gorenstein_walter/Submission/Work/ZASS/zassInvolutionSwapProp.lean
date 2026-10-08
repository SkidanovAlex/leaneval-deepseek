/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Z6.2: any two points are interchanged by an involution

`Work.ZASS.zassInvolutionSwapProp` (HB III XI 1.7(b),(c), `Work.GW2.ZassInvolutionSwapProp`):
in a Zassenhaus action with `q` odd, any two distinct points `a ≠ b` are interchanged by an
involution.

The formalised route avoids the parity case distinction of the blueprint.  Let
`S = Stab_G({a,b})` be the setwise stabilizer of the pair and `T = G_{a,b} = G_a ⊓ G_b` the
pointwise stabilizer of the pair.

* `|S| = 2 * |T|` (the orbit of `a` under `S` is `{a,b}` and the stabilizer of `a` inside `S`
  is `T`, so orbit–stabilizer applies); in particular `|S|` is even, so by Cauchy `S` contains
  an involution `t`.
* If `t ∉ T`, then `t` cannot fix `a` (an element of `S` fixing `a` fixes `b` as well), so
  `t` interchanges `a` and `b` and we are done.
* If `t ∈ T`, then `t ≠ 1` fixes `a` and `b`; by `2`-pretransitivity the two distinct points
  `c` and `t • c` (`c` a third point, which exists because `q ≥ 3`) can be mapped to `a` and
  `b` by some `g'`, and then `g' * t * g'⁻¹` is an involution interchanging `a` and `b`.
-/
import Mathlib
import Submission.Work.ZASS.Defs
import Submission.Work.ZASS.Basic
import Submission.Work.Zassenhaus.Basic
import Submission.Work.ZASS.zass_setwiseStabCard
import Submission.Work.ZASS.zass_swapInvolution_of_pairStab

open scoped Pointwise

namespace Work.ZASS

/-! ## The setwise stabilizer of a two-element set -/

/-- The image of the two-element set `{a,b}` under a group element `s`. -/
lemma smul_pair_eq {G X : Type} [Group G] [MulAction G X] (s : G) (a b : X) :
    s • ({a, b} : Set X) = {s • a, s • b} := by
  rw [show ({a, b} : Set X) = insert a {b} from rfl, Set.smul_set_insert,
    Set.smul_set_singleton]

/-- If `s` fixes both `a` and `b`, then it stabilizes the two-element set `{a,b}`. -/
lemma mem_stabilizer_pair_of_smul {G X : Type} [Group G] [MulAction G X] {a b : X} {s : G}
    (h1 : s • a = a) (h2 : s • b = b) : s ∈ MulAction.stabilizer G ({a, b} : Set X) := by
  rw [MulAction.mem_stabilizer_iff, smul_pair_eq s a b, h1, h2]

/-- If `s` either fixes both `a` and `b` or interchanges them, then it stabilizes `{a,b}`. -/
lemma mem_stabilizer_pair_of_cases {G X : Type} [Group G] [MulAction G X] {a b : X} {s : G}
    (h : (s • a = a ∧ s • b = b) ∨ (s • a = b ∧ s • b = a)) :
    s ∈ MulAction.stabilizer G ({a, b} : Set X) := by
  rw [MulAction.mem_stabilizer_iff, smul_pair_eq s a b]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]
    exact (Set.pair_comm a b).symm

/-- An element of the setwise stabilizer of the two-element set `{a,b}` either fixes both
points or interchanges them. -/
lemma smul_pair_cases {G X : Type} [Group G] [MulAction G X] {a b : X} (hab : a ≠ b) {s : G}
    (hs : s ∈ MulAction.stabilizer G ({a, b} : Set X)) :
    (s • a = a ∧ s • b = b) ∨ (s • a = b ∧ s • b = a) := by
  have h : s • ({a, b} : Set X) = {a, b} := hs
  have h' : ({s • a, s • b} : Set X) = {a, b} := by
    rw [← h]
    rw [show ({a, b} : Set X) = insert a {b} from rfl, Set.smul_set_insert,
      Set.smul_set_singleton]
  have h1 : s • a ∈ ({a, b} : Set X) := by rw [← h']; simp
  have h2 : s • b ∈ ({a, b} : Set X) := by rw [← h']; simp
  have hne : s • a ≠ s • b := fun hh => hab (MulAction.injective s hh)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
  rcases h1 with h3 | h3 <;> rcases h2 with h4 | h4
  · exact absurd (h3.trans h4.symm) hne
  · exact Or.inl ⟨h3, h4⟩
  · exact Or.inr ⟨h3, h4⟩
  · exact absurd (h3.trans h4.symm) hne

/-! ## Z6.2 -/

/-- The body of `zassInvolutionSwapProp`, with all hypotheses as explicit binders.  (The
hypothesis `Odd q` of the contract is not needed: the argument below covers both parities of
`(q-1)/2` at once.) -/
theorem zassInvolutionSwap_aux (G X : Type) [Group G] [Finite G] [MulAction G X] [Finite X]
    (q : ℕ) (_hq : Odd q) (h : Work.GW2.ZassHyps2 G X q) (a b : X) (hab : a ≠ b) :
    ∃ s : G, orderOf s = 2 ∧ s • a = b ∧ s • b = a := by
  have hpre : MulAction.IsMultiplyPretransitive G X 2 := h.2.2.1
  -- the pointwise stabilizer of the pair, of order `(q-1)/2`
  let T : Subgroup G := MulAction.stabilizer G a ⊓ MulAction.stabilizer G b
  have hcardT : 2 * Nat.card ↥T = q - 1 := h.2.2.2.2 a b hab
  have hcardTpos : 0 < Nat.card ↥T := Nat.card_pos_iff.mpr ⟨⟨1⟩, inferInstance⟩
  have hq3 : 3 ≤ q := by omega
  -- a third point exists
  have hc3 : ∃ c : X, c ≠ a ∧ c ≠ b := by
    by_contra hcon
    have hsub : (Set.univ : Set X) ⊆ ({a, b} : Set X) := by
      intro x _
      by_cases hx : x = a
      · rw [hx]; simp
      · by_cases hx' : x = b
        · rw [hx']; simp
        · exact absurd ⟨x, hx, hx'⟩ hcon
    have hle := Set.ncard_le_ncard hsub
    rw [Set.ncard_univ, Set.ncard_pair hab, h.2.1] at hle
    omega
  -- Cauchy in the setwise stabilizer of `{a,b}`, whose order is even
  have hcardS : Nat.card (MulAction.stabilizer G ({a, b} : Set X)) = 2 * Nat.card ↥T :=
    zass_setwiseStabCard hab hpre
  have hdvd : 2 ∣ Nat.card ↥(MulAction.stabilizer G ({a, b} : Set X)) := by
    rw [hcardS]
    exact dvd_mul_right 2 _
  obtain ⟨t, htord'⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(MulAction.stabilizer G ({a, b} : Set X))) 2 hdvd
  have htord : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact htord'
  by_cases htT : (t : G) ∈ T
  · -- `t` fixes `a` and `b`: conjugate by an element moving a third point
    have htT' : (t : G) ∈ MulAction.stabilizer G a ⊓ MulAction.stabilizer G b := htT
    have hta : (t : G) • a = a := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp htT').1
    have htb : (t : G) • b = b := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp htT').2
    exact zass_swapInvolution_of_pairStab hab hpre h.2.2.2.1 hc3 hta htb htord
  · -- `t` interchanges `a` and `b`
    rcases smul_pair_cases hab t.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd (Subgroup.mem_inf.mpr ⟨MulAction.mem_stabilizer_iff.mpr h1,
        MulAction.mem_stabilizer_iff.mpr h2⟩) htT
    · exact ⟨(t : G), htord, h1, h2⟩

/-- **Z6.2** (HB III XI 1.7(b),(c)): `Work.GW2.ZassInvolutionSwapProp`, i.e. in a Zassenhaus
action with `q` odd, any two distinct points `a ≠ b` are interchanged by an involution.

Route (elementary, no transfer theory).  By 2-pretransitivity choose `g` with `g • a = b` and
`g • b = a`; every odd power of `g` still swaps them.  Let `s = g^k` where `k` is the odd part
of `orderOf g`, so `orderOf s` is a power of two and `s` still swaps `a` and `b`; then
`s * s ∈ G_{ab}` (it fixes `a` and `b`).
* If `(q-1)/2` is odd (`q ≡ 3 mod 4`), then `orderOf (s*s)` divides both a power of `2` and
  `|G_{ab}| = (q-1)/2`, hence `s * s = 1` and `s` is the required involution.
* If `(q-1)/2` is even (`q ≡ 1 mod 4`), take an involution `t ∈ G_{ab}` (Cauchy; `|G_{ab}|` is
  even and nonzero).  Any nonidentity element of `G_{ab}` fixes exactly `a` and `b`, so `t`
  fixes exactly `a, b`; pick `c ∉ {a,b}` and, by 2-pretransitivity, `g'` with `g' • c = a` and
  `g' • (t • c) = b`.  Then `g' * t * g'⁻¹` is an involution swapping `a` and `b`.

Alternatively: the setwise stabilizer of `{a,b}` has order `2 * |G_{ab}| = q - 1`, which is
even, so it contains an involution by Cauchy; for `q ≡ 3 mod 4` it cannot lie in `G_{ab}` (odd
order) and hence swaps `a` and `b`.

`Odd q` follows from `2 * |G_{ab}| = q - 1`, and `a ≠ b` gives `s ≠ 1`.

The formalisation follows the "alternative" route above in its unified form
(`zassInvolutionSwap_aux`): the involution `t` found in the setwise stabilizer of `{a,b}` either
swaps `a` and `b` already, or lies in `G_{a,b}`, in which case the conjugation argument of
`Work.ZASS.zass_swapInvolution_of_pairStab` applies to it; this covers both parities of
`(q-1)/2` at once, so the hypothesis `Odd q` is not needed. -/
theorem zassInvolutionSwapProp : Work.GW2.ZassInvolutionSwapProp := zassInvolutionSwap_aux

end Work.ZASS
