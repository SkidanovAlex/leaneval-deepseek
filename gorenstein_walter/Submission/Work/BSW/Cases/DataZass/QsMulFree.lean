import Mathlib
import Submission.Work.BSW.Cases.DataZass.Setup

open scoped MatrixGroups Pointwise

namespace Work.BSW.Cases.DataZass

open Subgroup Work.GW2

/-- **A `p`-element of `Q` fixes only the base point of `G ⧸ N_G(Q)`.**

Let `N := N_G(Q)` and let `x = aN` be a coset different from the base point `N`, so that
`a ∉ N` (equivalently `a⁻¹ ∉ N`).  If `c ∈ Q` fixes `x`, then `(c·a)⁻¹·a = a⁻¹c⁻¹a ∈ N`, hence
`z := a⁻¹ c a = (a⁻¹ c⁻¹ a)⁻¹ ∈ N_G(Q)` as well.  But `z ∈ a⁻¹ Q a = conjSub a⁻¹ Q` because
`c ∈ Q`, so `z ∈ N_G(Q) ⊓ conjSub a⁻¹ Q`.

Now `z` is a `p`-element of `N_G(Q)`: it is a conjugate of `c ∈ Q`, and `|Q| = q = p^k` is the
full `p`-part of `|N_G(Q)| = p^k·(q-1)/2` (as `q` is odd, `p ∤ (q-1)/2`).  Hence
`mem_of_pElement_of_mem_normalizer` gives `z ∈ Q`, so `z ∈ Q ⊓ conjSub a⁻¹ Q = ⊥` by Bender 3.7
(`IsBSWConf.disjoint`, applied to `a⁻¹ ∉ N_G(Q)`).  Thus `z = 1` and `c = 1`.

This is the geometric content of "a `p`-element normalizing a Sylow `p`-subgroup lies in it": a
nonidentity `p`-element of `Q` fixes no point other than `Q` itself. -/
theorem QsMulFree {G : Type} [Group G] [Finite G] {q p k : ℕ} (hp : p.Prime) (hq : q = p ^ k)
    (h5 : 5 ≤ q) (hodd : Odd q) {Q D : Subgroup G} (h : IsBSWConf (G := G) q Q D) {c : G}
    (hc : c ∈ Q) {x : G ⧸ Subgroup.normalizer (Q : Set G)}
    (hx : x ≠ ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G))) (hfix : c • x = x) : c = 1 := by
  -- `q = p ^ k` is a nontrivial prime power
  have hk : k ≠ 0 := by
    rintro rfl
    simp only [pow_zero] at hq
    omega
  have hQk : Nat.card Q = p ^ k := by rw [h.card_Q, hq]
  -- write `x` as the coset `aN`
  obtain ⟨a, rfl⟩ := Quotient.exists_rep x
  have ha : a ∉ normalizer (Q : Set G) := by
    intro hmem
    refine hx ?_
    rw [QuotientGroup.eq]
    simpa using Subgroup.inv_mem _ hmem
  have ha' : a⁻¹ ∉ normalizer (Q : Set G) :=
    fun hc => ha (by simpa using Subgroup.inv_mem _ hc)
  -- `a⁻¹ c⁻¹ a` normalizes `Q`
  have hmemN : a⁻¹ * c⁻¹ * a ∈ normalizer (Q : Set G) := by
    have h1 : ((c * a : G) : G ⧸ normalizer (Q : Set G))
        = ((a : G) : G ⧸ normalizer (Q : Set G)) := hfix
    have h2 := QuotientGroup.eq.mp h1
    rwa [show (c * a)⁻¹ * a = a⁻¹ * c⁻¹ * a by group] at h2
  -- hence so does `z = a⁻¹ c a`
  have hzN : a⁻¹ * c * a ∈ normalizer (Q : Set G) := by
    have hh := Subgroup.inv_mem _ hmemN
    rwa [show (a⁻¹ * c⁻¹ * a)⁻¹ = a⁻¹ * c * a by group] at hh
  -- and `z ∈ a⁻¹ Q a` because `c ∈ Q`
  have hzC : a⁻¹ * c * a ∈ conjSub a⁻¹ Q := by
    rw [mem_conjSub_iff_H]
    convert hc using 1
    group
  -- the `p`-part data of `N_G(Q) = Q ⊔ D`
  have hDle : D ≤ normalizer (Q : Set G) := by rw [h.normalizer_Q]; exact le_sup_right
  have hH : Nat.card ↥(normalizer (Q : Set G)) = p ^ k * ((q - 1) / 2) := by
    rw [h.normalizer_Q, card_sup_of_inf_bot_of_le_normalizer h.inf_bot hDle, h.card_Q, h.card_D, hq]
  have hm2 : 2 * ((q - 1) / 2) = q - 1 := by
    obtain ⟨t, ht⟩ := hodd
    rw [ht, show (2 * t + 1 - 1) = 2 * t by omega,
      Nat.mul_div_right t (by norm_num : 0 < 2)]
  have hpnd : ¬ p ∣ (q - 1) / 2 := by
    intro hdiv
    have h1 : p ∣ q := by rw [hq]; exact dvd_pow_self p hk
    have h2 : p ∣ q - 1 := by
      have h3 : p ∣ 2 * ((q - 1) / 2) := dvd_mul_of_dvd_right hdiv 2
      rwa [hm2] at h3
    have := Nat.dvd_sub h1 h2
    rw [show q - (q - 1) = 1 by omega] at this
    exact hp.not_dvd_one this
  -- `z`, being a `p`-element of `N_G(Q)`, lies in `Q`
  have hzQ : a⁻¹ * c * a ∈ Q := by
    have horder : ∃ j, orderOf (a⁻¹ * c * a) = p ^ j :=
      exists_orderOf_eq_pow_of_mem hp (by rw [card_conjSub_H, hQk]) hzC
    exact mem_of_pElement_of_mem_normalizer hp hpnd hQk hH hzN horder
  -- Bender 3.7: `Q ⊓ a⁻¹Qa = ⊥`
  have hbot : a⁻¹ * c * a ∈ Q ⊓ conjSub a⁻¹ Q := ⟨hzQ, hzC⟩
  rw [IsBSWConf.disjoint h a⁻¹ ha'] at hbot
  have hz1 : a⁻¹ * c * a = 1 := Subgroup.mem_bot.mp hbot
  have h3 : a * (a⁻¹ * c * a) * a⁻¹ = c := by group
  rw [← h3, hz1]
  group

end Work.BSW.Cases.DataZass
