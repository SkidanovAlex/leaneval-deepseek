import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.GLUE.Defs

/-!
# Area BG: the `|S| = 2` versus `|S| ≥ 4` case split (`Work.GW2.C16.NCasesProp`)

`NCasesProp` (design leaf **G2**, Bender–Glauberman 1981, p. 202) records the two facts about
the invariants `n` and `S₀` of a `BGData` that the rest of the development splits on:

* `n = 2 ∨ 4 ≤ n`, i.e. `|S| = 2n` is `4` or at least `8`.  Since `S` is a Sylow 2-subgroup,
  `|S| = 2n` is a power of `2`; together with `2 ≤ n` this leaves exactly `n = 2` and `n ≥ 4`.
* `|S₀| = n`, because `S₀ ≤ S` has index `2` and `|S| = |DihedralGroup n| = 2n`.
-/

namespace Work.BG

/-- Arithmetic core of `nCases`: a power of two `2 ^ k` written as `2 * n` with `n ≥ 2` forces
`n = 2` or `4 ≤ n`.  (Equivalently: `n` itself is `2 ^ (k-1)`, a power of two that is `≥ 2`.) -/
private lemma two_pow_eq_two_mul {k n : ℕ} (hn : 2 ≤ n) (h : 2 ^ k = 2 * n) :
    n = 2 ∨ 4 ≤ n := by
  -- `k ≥ 2`, since `2 ^ k = 2n ≥ 4`
  have hk1 : 1 < k := by
    rcases Nat.lt_or_ge k 2 with hk | hk
    · have : k = 0 ∨ k = 1 := by omega
      rcases this with h0 | h1
      · rw [h0] at h; simp at h; omega
      · rw [h1] at h; simp at h; omega
    · exact hk
  -- hence `n` is the power of two `2 ^ (k-1)`
  have hn' : n = 2 ^ (k - 1) := by
    have h2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
      calc 2 ^ k = 2 ^ ((k - 1) + 1) := by rw [show (k - 1) + 1 = k by omega]
        _ = 2 * 2 ^ (k - 1) := by rw [pow_succ']
    rw [h2] at h
    exact (Nat.mul_left_cancel (by norm_num) h).symm
  rcases Nat.lt_or_ge 2 k with hk | hk
  · right
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = n := hn'.symm
  · left
    have : k = 2 := by omega
    rw [hn', this]; norm_num

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem nCases : Work.GW2.C16.NCasesProp := by
  intro G _ _ D
  have htwo : 2 ≤ D.n := D.two_le
  -- `|S| = |DihedralGroup n| = 2n`
  obtain ⟨e⟩ := D.dih
  have hS : Nat.card (D.S : Subgroup G) = 2 * D.n := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  refine ⟨?_, ?_⟩
  · -- `|S|` is a power of two (Sylow), so `n = 2` or `n ≥ 4`
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp D.S.isPGroup'
    exact two_pow_eq_two_mul htwo (by rw [← hk, hS])
  · -- `S₀ ≤ S` has index two, so `|S₀| = |S| / 2 = n`
    have h := Subgroup.relIndex_mul_card D.S0 (D.S : Subgroup G)
    rw [inf_eq_left.mpr D.S0_le, D.S0_index, hS] at h
    exact Nat.mul_left_cancel (by norm_num) h

end Work.BG
