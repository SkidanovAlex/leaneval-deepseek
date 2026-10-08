import Mathlib
import Submission.Work.FeitSibley.Coherence.Vocab
import Submission.Work.FeitSibley.Coherence.two_mul_card_D_add_one_le_card_Q1
import Submission.Work.FeitSibley.GroupTheory.D_dvd_card_sub_one
import Submission.Work.FeitSibley.Coherence.Q1_isNilpotent_of_D_ne_bot
import Submission.Work.FeitSibley.GroupTheory.S_Q1
import Submission.Work.FeitSibley.Coherence.card_centerQ1_ge_card_D_add_one
import Submission.Work.FeitSibley.Coherence.card_centerQ1_eq_three_of_card_Q1_eq_three

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.Coherence`: the numerical inequality `2·|D|² ≤ (|Q₁| - 2)·|Z(Q₁)|`

Peterfalvi II, Appendice XII: with `H = Q ⋊ D`, `Q = S × Q₁`, `D` acting fixed point freely on
`Q₁` and `|D|` odd, the pair `(|D|, |Q₁|)` satisfies

`2·|D|² ≤ (|Q₁| - 2)·|Z(Q₁)|`,

the numerical input used in the two-block step of the coherence argument (see
`Coherence/deg_sq_le_of_mem_scriptSR_center.lean`, `Coherence/sum_deg_sq_scriptSR_of_le_S.lean`).

The proof combines the two counting bounds

* `2·|D| + 1 ≤ |Q₁|` (`two_mul_card_D_add_one_le_card_Q1`, valid for every `FSData`: `D` acts
  freely on `Q₁ ∖ {1}`, and the exceptional case `|Q₁| = |D| + 1` — which would make `Q₁` a
  `2`-group — is excluded by `h.Q1_not_two`);
* `|D| + 1 ≤ |Z(Q₁)|` when `|D| ≥ 2` (`card_centerQ1_ge_card_D_add_one`: `Q₁` is nilpotent by
  Thompson (`Q1_isNilpotent_of_D_ne_bot`), so `Z(Q₁) ≠ 1`, and `D ∋ d ↦ d·z·d⁻¹` is free on
  `Z(Q₁)`, so `|D| ∣ |Z(Q₁)| - 1`),

giving `(2|D| - 1)·(|D| + 1) = 2|D|² + |D| - 1 ≥ 2|D|²`.  In the remaining case `D = 1` the
inequality reduces to `2 ≤ (|Q₁| - 2)·|Z(Q₁)|`, which holds because `|Q₁| ≥ 3` and, when
`|Q₁| = 3`, the group `Q₁` is abelian of order `3` so that `|Z(Q₁)| = 3`.
-/

namespace Work.FeitSibley.Coherence

theorem two_mul_card_D_sq_le_card_Q1_sub_two_mul_card_centerQ1 {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) :
    2 * (Nat.card h.D : ℝ) ^ 2 ≤ ((Nat.card h.Q1 : ℝ) - 2) * (Nat.card h.centerQ1 : ℝ) := by
  have hd1 : 1 ≤ Nat.card h.D := Nat.card_pos
  have hq3 : 2 * Nat.card h.D + 1 ≤ Nat.card h.Q1 := two_mul_card_D_add_one_le_card_Q1 h
  have hq : 3 ≤ Nat.card h.Q1 := by omega
  have hqR : (3 : ℝ) ≤ (Nat.card h.Q1 : ℝ) := by exact_mod_cast hq
  have hz1 : 1 ≤ Nat.card h.centerQ1 := Nat.card_pos
  have hz1R : (1 : ℝ) ≤ (Nat.card h.centerQ1 : ℝ) := by exact_mod_cast hz1
  by_cases hd2 : 2 ≤ Nat.card h.D
  · -- `|D| ≥ 2`: `|Q₁| ≥ 2|D| + 1` and `|Z(Q₁)| ≥ |D| + 1`
    have hz : Nat.card h.D + 1 ≤ Nat.card h.centerQ1 := card_centerQ1_ge_card_D_add_one h hd2
    have hqR' : 2 * (Nat.card h.D : ℝ) + 1 ≤ (Nat.card h.Q1 : ℝ) := by exact_mod_cast hq3
    have hzR : (Nat.card h.D : ℝ) + 1 ≤ (Nat.card h.centerQ1 : ℝ) := by exact_mod_cast hz
    have hd2R : (2 : ℝ) ≤ (Nat.card h.D : ℝ) := by exact_mod_cast hd2
    have hqm : 2 * (Nat.card h.D : ℝ) - 1 ≤ (Nat.card h.Q1 : ℝ) - 2 := by linarith
    have hqm0 : (0 : ℝ) ≤ 2 * (Nat.card h.D : ℝ) - 1 := by linarith
    have hz0 : (0 : ℝ) ≤ (Nat.card h.D : ℝ) + 1 := by linarith
    have hb : (0 : ℝ) ≤ (Nat.card h.Q1 : ℝ) - 2 := le_trans hqm0 hqm
    have hmul := mul_le_mul hqm hzR hz0 hb
    have hsq : 2 * (Nat.card h.D : ℝ) ^ 2
        ≤ (2 * (Nat.card h.D : ℝ) - 1) * ((Nat.card h.D : ℝ) + 1) := by nlinarith
    linarith
  · -- `|D| = 1`: `2 ≤ (|Q₁| - 2)·|Z(Q₁)|`
    have hdone : Nat.card h.D = 1 := by omega
    rw [hdone]
    by_cases hz2 : 2 ≤ Nat.card h.centerQ1
    · have hzR : (2 : ℝ) ≤ (Nat.card h.centerQ1 : ℝ) := by exact_mod_cast hz2
      have hqm : (1 : ℝ) ≤ (Nat.card h.Q1 : ℝ) - 2 := by linarith
      have hb : (0 : ℝ) ≤ (Nat.card h.Q1 : ℝ) - 2 := by linarith
      have key : (1 : ℝ) * 2 ≤ ((Nat.card h.Q1 : ℝ) - 2) * (Nat.card h.centerQ1 : ℝ) :=
        mul_le_mul hqm hzR (by norm_num) hb
      norm_num at key ⊢
      linarith
    · -- `Z(Q₁)` is trivial, so `|Q₁| ≠ 3` and hence `|Q₁| ≥ 4`
      have hz1' : Nat.card h.centerQ1 = 1 := by omega
      have hq4 : 4 ≤ Nat.card h.Q1 := by
        by_contra hc
        have hq3' : Nat.card h.Q1 = 3 := by omega
        have := card_centerQ1_eq_three_of_card_Q1_eq_three h hq3'
        omega
      have hqR4 : (4 : ℝ) ≤ (Nat.card h.Q1 : ℝ) := by exact_mod_cast hq4
      have hqm : (2 : ℝ) ≤ (Nat.card h.Q1 : ℝ) - 2 := by linarith
      have hb : (0 : ℝ) ≤ (Nat.card h.Q1 : ℝ) - 2 := by linarith
      have key : (2 : ℝ) * 1 ≤ ((Nat.card h.Q1 : ℝ) - 2) * (Nat.card h.centerQ1 : ℝ) :=
        mul_le_mul hqm hz1R (by norm_num) hb
      norm_num at key ⊢
      linarith

end Work.FeitSibley.Coherence
