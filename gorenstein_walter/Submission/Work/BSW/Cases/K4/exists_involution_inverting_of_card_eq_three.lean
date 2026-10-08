import Mathlib
import Submission.Work.BSW.Defs

namespace Work.BSW.Cases.K4

open Subgroup

/-- In a group whose element `w` has order `3`, every power of `w` is `1`, `w` or `w ^ 2`. -/
lemma mem_zpowers_of_orderOf_three {G : Type} [Group G] {w x : G}
    (hw : orderOf w = 3) (hx : x ∈ Subgroup.zpowers w) :
    x = 1 ∨ x = w ∨ x = w ^ 2 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h3 : w ^ (3 : ℕ) = 1 := by
    have := pow_orderOf_eq_one w
    rw [hw] at this
    simpa using this
  have h1 : w ^ k = w ^ (k % (3 : ℤ)) := zpow_eq_zpow_emod' k h3
  have hk0 : 0 ≤ k % (3 : ℤ) := Int.emod_nonneg k (by norm_num)
  have hk3 : k % (3 : ℤ) < 3 := Int.emod_lt_of_pos k (by norm_num)
  have hcases : k % (3 : ℤ) = 0 ∨ k % (3 : ℤ) = 1 ∨ k % (3 : ℤ) = 2 := by omega
  rcases hcases with hk | hk | hk
  · left; rw [h1, hk]; simp
  · right; left; rw [h1, hk]; simp
  · right; right; rw [h1, hk]; norm_num

/-- The order of an element of a subgroup divides the cardinality of that subgroup. -/
lemma orderOf_dvd_card_of_mem {G : Type} [Group G] {H : Subgroup G} {x : G} (hx : x ∈ H) :
    orderOf x ∣ Nat.card ↥H := by
  have h := orderOf_dvd_natCard (⟨x, hx⟩ : ↥H)
  rw [← Subgroup.orderOf_coe (⟨x, hx⟩ : ↥H)] at h
  simpa using h

/-- If a subgroup `D` of order `3` (a Sylow 3-subgroup of `G`) is not centralized by its own
normalizer, and `G` has no element of order `6`, then some involution outside `D` inverts `D`.

(The hypothesis `∃ g ∈ N_G(D) \ C_G(D)` is what Burnside's normal `p`-complement result supplies in
a simple group; from such a `g` of order `m` one takes `u = g^(m/2)`, which is an involution
because `m` is even, and which inverts `D` because `m/2` is odd — otherwise `g^(m/2)` would be an
involution centralizing `D`, and `d * g^(m/2)` would be an element of order `6`.) -/
theorem exists_involution_inverting_of_card_eq_three {G : Type} [Group G] [Finite G]
    (D : Subgroup G) (hD : Nat.card ↥D = 3) (h6 : ∀ x : G, orderOf x ≠ 6)
    (hex : ∃ g : G, g ∈ Subgroup.normalizer (D : Set G) ∧
      g ∉ Subgroup.centralizer ((D : Subgroup G) : Set G)) :
    ∃ u : G, orderOf u = 2 ∧ u ∉ D ∧ Work.GW2.Inverts u D := by
  classical
  obtain ⟨g, hgN, hgnC⟩ := hex
  have hgN_iff : ∀ x : G, x ∈ D ↔ g * x * g⁻¹ ∈ D := Subgroup.mem_normalizer_iff.mp hgN
  -- a generator of `D`
  have hDne : D ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥D = 1 := by rw [hbot]; exact Subgroup.card_eq_one.mpr rfl
    omega
  obtain ⟨d0, hd0ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDne
  set d : G := (d0 : G) with hd_def
  have hdmem : d ∈ D := by rw [hd_def]; exact d0.2
  have hdne : d ≠ 1 := by
    rw [hd_def]
    exact fun h => hd0ne (Subtype.ext (by simpa using h))
  have hordd : orderOf d = 3 := by
    have h := orderOf_dvd_card_of_mem hdmem
    rw [hD] at h
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hdne
    · exact h3
  have hd3 : d ^ 3 = 1 := by
    have := pow_orderOf_eq_one d
    rw [hordd] at this
    simpa using this
  have hDgen : D = Subgroup.zpowers d := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdmem) ?_).symm
    rw [hD, Nat.card_zpowers, hordd]
  -- conjugation by `g` is inversion on `D`
  have hconjd : g * d * g⁻¹ = d⁻¹ := by
    have hmem' : g * d * g⁻¹ ∈ D := (hgN_iff d).mp hdmem
    have hne' : g * d * g⁻¹ ≠ 1 := by
      intro h
      apply hdne
      have hcalc : g⁻¹ * (g * d * g⁻¹) * g = d := by group
      rw [← hcalc, h]; group
    have hmem'' : g * d * g⁻¹ ∈ Subgroup.zpowers d := by rw [hDgen] at hmem'; exact hmem'
    rcases mem_zpowers_of_orderOf_three hordd hmem'' with h | h | h
    · exact absurd h hne'
    · exfalso
      apply hgnC
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [hDgen] at hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hgy : g * y * g⁻¹ = y := by
        rw [← hk]
        have h1 : g * d ^ k * g⁻¹ = (g * d * g⁻¹) ^ k := by
          rw [← MulAut.conj_apply g (d ^ k), map_zpow, MulAut.conj_apply g d]
        rw [h1, h]
      have hh : g * y = (g * y * g⁻¹) * g := by group
      rw [hgy] at hh
      exact hh.symm
    · have hd2 : d ^ 2 = d⁻¹ := by
        have h4 : d ^ 2 * d = 1 := by rw [← pow_succ]; simpa using hd3
        exact eq_inv_of_mul_eq_one_left h4
      rw [← hd2]; exact h
  have hconj : ∀ x : G, x ∈ D → g * x * g⁻¹ = x⁻¹ := by
    intro x hx
    rw [hDgen] at hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← hk]
    have h1 : g * d ^ k * g⁻¹ = (g * d * g⁻¹) ^ k := by
      rw [← MulAut.conj_apply g (d ^ k), map_zpow, MulAut.conj_apply g d]
    rw [h1, hconjd, inv_zpow]
  -- `g ^ 2` centralizes `D`
  have hmain : ∀ y : G, y ∈ D → g * g * y = y * (g * g) := by
    intro y hy
    have hy1 : g * y * g⁻¹ = y⁻¹ := hconj y hy
    have h1 : g * g * y * (g * g)⁻¹ = y := by
      calc g * g * y * (g * g)⁻¹ = g * (g * y * g⁻¹) * g⁻¹ := by group
        _ = g * y⁻¹ * g⁻¹ := by rw [hy1]
        _ = (g * y * g⁻¹)⁻¹ := by group
        _ = (y⁻¹)⁻¹ := by rw [hy1]
        _ = y := by group
    calc g * g * y = (g * g * y * (g * g)⁻¹) * (g * g) := by group
      _ = y * (g * g) := by rw [h1]
  have hg2C : g ^ 2 ∈ Subgroup.centralizer ((D : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := hmain y hy
    simpa only [pow_two] using this.symm
  -- the order of `g` is even
  have hmeven : Even (orderOf g) := by
    by_contra hne
    rw [Nat.not_even_iff_odd] at hne
    obtain ⟨j, hj⟩ := hne
    have hgm : g ^ (2 * j + 1) = 1 := by
      have := pow_orderOf_eq_one g
      rw [hj] at this
      exact this
    have hg_eq : g = (g ^ 2) ^ (j + 1) := by
      have hpow : (g ^ 2) ^ (j + 1) = g ^ (2 * (j + 1)) := by rw [← pow_mul]
      rw [hpow]
      have h2 : g ^ (2 * (j + 1)) = g := by
        rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, pow_succ, hgm, one_mul]
      exact h2.symm
    have hmem : g ∈ Subgroup.centralizer ((D : Subgroup G) : Set G) := by
      rw [hg_eq]
      exact Subgroup.pow_mem _ hg2C (j + 1)
    exact hgnC hmem
  obtain ⟨c, hc⟩ := hmeven
  -- `u = g ^ c` is an involution
  have hu_ord : orderOf (g ^ c) = 2 := by
    have h2 : (g ^ c) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_two, ← hc, pow_orderOf_eq_one]
    have hdvd : orderOf (g ^ c) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    have hne : g ^ c ≠ 1 := by
      intro hc1
      have hdvd2 : orderOf g ∣ c := orderOf_dvd_iff_pow_eq_one.mpr hc1
      rw [hc] at hdvd2
      have hcpos : 0 < c := by
        rcases Nat.eq_zero_or_pos c with h0 | hpos
        · exfalso
          rw [h0, add_zero] at hc
          exact absurd hc (ne_of_gt (orderOf_pos g))
        · exact hpos
      have hle := Nat.le_of_dvd hcpos hdvd2
      omega
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2'
    · exact absurd (orderOf_eq_one_iff.mp h1) hne
    · exact h2'
  have hu_notmem : g ^ c ∉ D := by
    intro hmem
    have hdvd : orderOf (g ^ c) ∣ Nat.card ↥D := orderOf_dvd_card_of_mem hmem
    rw [hu_ord, hD] at hdvd
    omega
  refine ⟨g ^ c, hu_ord, hu_notmem, ?_⟩
  intro x hx
  by_cases hcodd : Odd c
  · -- `c` odd: `g ^ c` inverts `D`
    obtain ⟨t, ht⟩ := hcodd
    have hwC : (g ^ 2) ^ t ∈ Subgroup.centralizer ((D : Subgroup G) : Set G) :=
      Subgroup.pow_mem _ hg2C t
    have hu_eq : g ^ c = (g ^ 2) ^ t * g := by
      rw [ht, pow_succ, ← pow_mul]
    have hux : g ^ c * x * (g ^ c)⁻¹ =
        (g ^ 2) ^ t * (g * x * g⁻¹) * ((g ^ 2) ^ t)⁻¹ := by
      rw [hu_eq]; group
    rw [hux]
    have hmemconj : g * x * g⁻¹ ∈ D := (hgN_iff x).mp hx
    have hcw : (g ^ 2) ^ t * (g * x * g⁻¹) * ((g ^ 2) ^ t)⁻¹ = g * x * g⁻¹ := by
      have hcomm := Subgroup.mem_centralizer_iff.mp hwC (g * x * g⁻¹) hmemconj
      rw [← hcomm]; group
    rw [hcw, hconj x hx]
  · -- `c` even would produce an element of order `6`
    exfalso
    have hceven : Even c := Nat.not_odd_iff_even.mp hcodd
    obtain ⟨t, ht⟩ := hceven
    have huC : g ^ c ∈ Subgroup.centralizer ((D : Subgroup G) : Set G) := by
      have hgc : g ^ c = (g ^ 2) ^ t := by rw [ht, ← Nat.two_mul, pow_mul]
      rw [hgc]
      exact Subgroup.pow_mem _ hg2C t
    have hcomm : Commute d (g ^ c) := Subgroup.mem_centralizer_iff.mp huC d hdmem
    have hcop : (orderOf d).Coprime (orderOf (g ^ c)) := by rw [hordd, hu_ord]; decide
    have h6eq : orderOf (d * g ^ c) = 6 := by
      rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hordd, hu_ord]
    exact h6 (d * g ^ c) h6eq

end Work.BSW.Cases.K4
