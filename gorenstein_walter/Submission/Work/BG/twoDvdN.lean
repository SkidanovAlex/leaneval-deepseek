import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.nCases

namespace Work.BG

/-- Arithmetic core: a power of two written as `2 * n` with `n ≥ 2` forces `2 ∣ n`. -/
private lemma two_dvd_of_two_pow_eq_two_mul {k n : ℕ} (hn : 2 ≤ n) (h : 2 ^ k = 2 * n) :
    2 ∣ n := by
  -- `2 ^ k = 2n ≥ 4 = 2 ^ 2` forces `k ≥ 2`.
  have hk2 : 2 ≤ k := by
    by_contra hlt
    push_neg at hlt
    have hk : k = 0 ∨ k = 1 := by omega
    rcases hk with hk | hk <;> rw [hk] at h <;> norm_num at h <;> omega
  -- Cancelling the factor `2` exhibits `n` as the power of two `2 ^ (k - 1)`.
  have hn' : n = 2 ^ (k - 1) := by
    have h2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
      calc 2 ^ k = 2 ^ ((k - 1) + 1) := by rw [show (k - 1) + 1 = k by omega]
        _ = 2 * 2 ^ (k - 1) := by rw [pow_succ']
    rw [h2] at h
    exact (Nat.mul_left_cancel (by norm_num) h).symm
  -- `k - 1 ≥ 1`, so `2 ^ (k - 1)` is a multiple of `2`.
  rw [hn']
  have hk1 : k - 1 = (k - 2) + 1 := by omega
  rw [hk1, pow_succ']
  exact dvd_mul_right 2 _

theorem twoDvdN {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) : 2 ∣ D.n := by
  -- `|S| = |DihedralGroup n| = 2n`.
  obtain ⟨e⟩ := D.dih
  have hS : Nat.card (D.S : Subgroup G) = 2 * D.n := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  -- `|S|` is a power of `2` because `S` is a Sylow `2`-subgroup.
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp D.S.isPGroup'
  exact two_dvd_of_two_pow_eq_two_mul D.two_le (by rw [← hk, hS])

end Work.BG
