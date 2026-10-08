import Mathlib
import Submission.Work.FeitSibley.GroupTheory.D_dvd_card_sub_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.Coherence`: `2·|D| + 1 ≤ |A|` for a `D`-invariant odd `A ≤ Q₁`

`D` acts fixed point freely on `Q₁ ⊇ A` and normalises `A`, so `D` acts fixed point freely on
`A`.  Burnside's lemma for this conjugation action gives `|A| - 1 = k·|D|` for the number
`k - 1` of nontrivial orbits; this is `Work.FeitSibley.GroupTheory.D_dvd_card_sub_one`, i.e.
`|D| ∣ |A| - 1`.

Now `|A|` is odd, hence `|A| - 1` is even, while `|D|` is odd; as `k·|D| = |A| - 1` is even and
`|D|` is odd, `k` itself is even.  Finally `A ≠ ⊥` forces `|A| ≥ 2`, so `k·|D| = |A| - 1 ≥ 1`
and hence `k ≥ 1`; an even `k ≥ 1` satisfies `k ≥ 2`, and therefore

`2·|D| ≤ k·|D| = |A| - 1`, i.e. `2·|D| + 1 ≤ |A|`.

(Equivalently: `|A| - 1` is a positive multiple of `|D|` divisible by `2`, and `2` and `|D|`
being coprime, `2·|D| ∣ |A| - 1`.)
-/

namespace Work.FeitSibley.Coherence

theorem two_mul_card_D_add_one_le_card_of_odd {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) (A : Subgroup G) (hA : A ≤ h.Q1)
    (hAn : h.D ≤ Subgroup.normalizer (A : Set G)) (hAne : A ≠ ⊥) (hodd : Odd (Nat.card ↥A)) :
    2 * Nat.card h.D + 1 ≤ Nat.card ↥A := by
  -- `|A| - 1 = k · |D|` for the number `k - 1` of nontrivial orbits of `D` on `A`.
  obtain ⟨k, hk⟩ := Work.FeitSibley.GroupTheory.D_dvd_card_sub_one h A hA hAn
  -- `A ≠ ⊥` gives `|A| ≥ 2`, so `|A| - 1 ≥ 1`.
  have hA2 : 2 ≤ Nat.card ↥A := Work.FeitSibley.FSData.two_le_card_of_ne_bot A hAne
  -- `|A|` odd makes `|A| - 1` even.
  have hEvenA : Even (Nat.card ↥A - 1) := by
    rcases hodd with ⟨m, hm⟩
    exact ⟨m, by omega⟩
  -- `|D|` odd and `k · |D| = |A| - 1` even force `k` even.
  have hkeven : Even k := by
    rcases Nat.even_or_odd k with hk' | hk'
    · exact hk'
    · exfalso
      have hoddprod : Odd (Nat.card h.D * k) := h.D_odd.mul hk'
      rw [← hk] at hoddprod
      exact (Nat.not_even_iff_odd.mpr hoddprod) hEvenA
  -- `k · |D| = |A| - 1 ≥ 1` forces `k ≥ 1`.
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · exfalso
      have : Nat.card h.D * k = 0 := by rw [hk0, mul_zero]
      omega
    · exact hkpos
  -- An even `k ≥ 1` satisfies `k ≥ 2`.
  have hk2 : 2 ≤ k := by
    rcases hkeven with ⟨j, hj⟩
    omega
  -- Hence `2 · |D| ≤ k · |D| = |A| - 1`.
  have hmul : 2 * Nat.card h.D ≤ Nat.card ↥A - 1 := by
    rw [hk]
    calc 2 * Nat.card h.D = Nat.card h.D * 2 := Nat.mul_comm _ _
      _ ≤ Nat.card h.D * k := Nat.mul_le_mul_left _ hk2
  omega

end Work.FeitSibley.Coherence
