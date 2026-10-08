/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area ZASS: the normalizer of a two-point stabilizer has index at most two

Let `G` act on `X` under the Zassenhaus hypotheses `ZassHyps2 G X q` with `q ≥ 5`, and let
`a ≠ b` be points of `X`.  Write `H = G_{ab}` for the pointwise stabilizer of `{a,b}` (the
`pairStab` of the Zassenhaus chapter) and `N = N_G(H)` for its normalizer.  Then `[N : H] ≤ 2`.

The proof is the standard one, cf. Huppert–Blackburn III.11:

* `H` has order `(q - 1)/2 ≥ 2`, so it contains a nonidentity element `h₀`;
* the set `S` of points fixed by *all* of `H` is contained in the fixed point set of `h₀`,
  which has at most two elements, while `a, b ∈ S`; hence `S = {a, b}`;
* `N` preserves `S`, because an element of `N` conjugates `H` into itself; so every `n ∈ N`
  permutes `{a, b}`, and (as `n` is injective) it either fixes both points or interchanges them;
* two-transitivity produces `s ∈ G` with `s • a = b`, `s • b = a`; this `s` normalizes `H`
  (it sends `H = G_{ab}` to `G_{s • a, s • b} = G_{ba} = H`), and then `n ∈ H` or `n * s ∈ H`
  according as `n` fixes `{a,b}` pointwise or interchanges it.  Hence `N = H ∪ Hs` and
  `Subgroup.relIndex_dvd_two_iff` gives `[N : H] ∣ 2`, so `[N : H] ≤ 2`.
-/
import Mathlib
import Submission.Work.ZASS.Defs
import Submission.Work.ZASS.Basic

namespace Work.ZASS

theorem index_pairStab_normalizer_le_two {G X : Type} [Group G] [Finite G] [MulAction G X] [Finite X] {q : ℕ} (h : Work.GW2.ZassHyps2 G X q) {a b : X} (hab : a ≠ b) (hq : 5 ≤ q) : ((Work.Zassenhaus.pairStab G a b).subgroupOf (Subgroup.normalizer (Work.Zassenhaus.pairStab G a b : Set G))).index ≤ 2 := by
  let H : Subgroup G := Work.Zassenhaus.pairStab G a b
  let N : Subgroup G := Subgroup.normalizer (Work.Zassenhaus.pairStab G a b : Set G)
  show (H.subgroupOf N).index ≤ 2
  -- ## Membership in `H = G_{ab}`
  have hmemH : ∀ g : G, g ∈ H ↔ g • a = a ∧ g • b = b := by
    intro g
    show g ∈ Work.Zassenhaus.pairStab G a b ↔ g • a = a ∧ g • b = b
    rw [Work.Zassenhaus.pairStab, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
      MulAction.mem_stabilizer_iff]
    constructor <;> intro ⟨h1, h2⟩ <;> exact ⟨h2, h1⟩
  -- ## `H` is nontrivial
  have hHcard : 1 < Nat.card ↥H := by
    show 1 < Nat.card ↥(Work.Zassenhaus.pairStab G a b)
    exact one_lt_card_pairStab h hab hq
  have hHne : H ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot H).mp hHcard
  obtain ⟨h₀, hh₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hHne
  have hh₀G : (h₀ : G) ≠ 1 := fun hc => hh₀ (Subtype.ext hc)
  -- ## The set `S` of points fixed by all of `H`
  set S : Set X := {x : X | ∀ g : G, g ∈ H → g • x = x} with hSdef
  have haS : a ∈ S := by
    rw [hSdef]
    intro g hg
    exact ((hmemH g).mp hg).1
  have hbS : b ∈ S := by
    rw [hSdef]
    intro g hg
    exact ((hmemH g).mp hg).2
  -- `S` lies in the fixed point set of the nonidentity element `h₀`
  have hSsub : S ⊆ {x : X | (h₀ : G) • x = x} := by
    intro x hx
    rw [hSdef] at hx
    exact hx (h₀ : G) h₀.2
  have hScard : S.ncard ≤ 2 :=
    (Set.ncard_le_ncard hSsub (Set.toFinite _)).trans (h.2.2.2.1 (h₀ : G) hh₀G)
  -- hence `S ⊆ {a, b}`
  have hSle : S ⊆ ({a, b} : Set X) := by
    have hfix : (h₀ : G) • a = a ∧ (h₀ : G) • b = b := (hmemH (h₀ : G)).mp h₀.2
    have hsub : ({a, b} : Set X) ⊆ {x : X | (h₀ : G) • x = x} := by
      intro x hx
      rcases hx with rfl | rfl
      · exact hfix.1
      · exact hfix.2
    have hle : ({x : X | (h₀ : G) • x = x}).ncard ≤ ({a, b} : Set X).ncard := by
      rw [Set.ncard_pair hab]
      exact h.2.2.2.1 (h₀ : G) hh₀G
    have heq : ({a, b} : Set X) = {x : X | (h₀ : G) • x = x} :=
      Set.eq_of_subset_of_ncard_le hsub hle
    intro x hx
    rw [heq]
    exact hSsub hx
  -- ## `N` preserves `S`
  have hSinv : ∀ n : G, n ∈ N → ∀ x : X, x ∈ S → n • x ∈ S := by
    intro n hn x hx
    rw [hSdef] at hx ⊢
    intro g hg
    have hconj : n⁻¹ * g * n ∈ H := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (N.inv_mem hn) g).mp hg
      simpa using h1
    calc g • (n • x) = (g * n) • x := (mul_smul g n x).symm
      _ = (n * (n⁻¹ * g * n)) • x := by
            rw [show g * n = n * (n⁻¹ * g * n) from by group]
      _ = n • ((n⁻¹ * g * n) • x) := mul_smul n (n⁻¹ * g * n) x
      _ = n • x := by rw [hx (n⁻¹ * g * n) hconj]
  -- ## Every `n ∈ N` either fixes both `a`, `b` or interchanges them
  have haction : ∀ n : G, n ∈ N → (n • a = a ∧ n • b = b) ∨ (n • a = b ∧ n • b = a) := by
    intro n hn
    have hna : n • a ∈ ({a, b} : Set X) := hSle (hSinv n hn a haS)
    have hnb : n • b ∈ ({a, b} : Set X) := hSle (hSinv n hn b hbS)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hna hnb
    have hinj : ∀ {x y : X}, n • x = n • y → x = y := by
      intro x y hxy
      have h1 := congrArg (fun z : X => n⁻¹ • z) hxy
      simpa using h1
    rcases hna with h | h
    · rcases hnb with h2 | h2
      · exact absurd (hinj (h2.trans h.symm)).symm hab
      · exact Or.inl ⟨h, h2⟩
    · rcases hnb with h2 | h2
      · exact Or.inr ⟨h, h2⟩
      · exact absurd (hinj (h.trans h2.symm)) hab
  -- ## Conjugating `H` by an element interchanging `a` and `b` keeps `H` fixed
  have conj_mem : ∀ t : G, t • a = b → t • b = a → ∀ k : G, k ∈ H → t * k * t⁻¹ ∈ H := by
    intro t hta htb k hk
    have htinv_a : t⁻¹ • a = b := by rw [← htb, inv_smul_smul]
    have htinv_b : t⁻¹ • b = a := by rw [← hta, inv_smul_smul]
    have hka : k • a = a := ((hmemH k).mp hk).1
    have hkb : k • b = b := ((hmemH k).mp hk).2
    rw [hmemH]
    constructor
    · calc (t * k * t⁻¹) • a = t • (k • (t⁻¹ • a)) := by simp only [mul_smul]
        _ = t • (k • b) := by rw [htinv_a]
        _ = t • b := by rw [hkb]
        _ = a := htb
    · calc (t * k * t⁻¹) • b = t • (k • (t⁻¹ • b)) := by simp only [mul_smul]
        _ = t • (k • a) := by rw [htinv_b]
        _ = t • a := by rw [hka]
        _ = b := hta
  -- ## Two-transitivity produces a transposition `s`
  obtain ⟨s, hsa, hsb⟩ : ∃ s : G, s • a = b ∧ s • b = a :=
    (MulAction.is_two_pretransitive_iff.mp h.2.2.1) hab (Ne.symm hab)
  have hs_inv_a : s⁻¹ • a = b := by rw [← hsb, inv_smul_smul]
  have hs_inv_b : s⁻¹ • b = a := by rw [← hsa, inv_smul_smul]
  have hsN : s ∈ N := by
    show s ∈ Subgroup.normalizer (Work.Zassenhaus.pairStab G a b : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · exact conj_mem s hsa hsb k
    · intro hk
      have h1 := conj_mem s⁻¹ hs_inv_a hs_inv_b (s * k * s⁻¹) hk
      have heq : s⁻¹ * (s * k * s⁻¹) * (s⁻¹)⁻¹ = k := by group
      rwa [heq] at h1
  -- ## `N = H ∪ Hs`
  have hdvd : H.relIndex N ∣ 2 :=
    (Subgroup.relIndex_dvd_two_iff (H := H) (K := N)).mpr
      ⟨s, hsN, fun n hn => by
        rcases haction n hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr ((hmemH n).mpr ⟨h1, h2⟩)
        · refine Or.inl ((hmemH (n * s)).mpr ⟨?_, ?_⟩)
          · calc (n * s) • a = n • (s • a) := mul_smul n s a
              _ = n • b := by rw [hsa]
              _ = a := h2
          · calc (n * s) • b = n • (s • b) := mul_smul n s b
              _ = n • a := by rw [hsb]
              _ = b := h1⟩
  exact Nat.le_of_dvd (by norm_num : 0 < 2) hdvd

end Work.ZASS
