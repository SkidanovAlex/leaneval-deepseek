import ChallengeDeps
import Submission.Helpers

open vanDerWaerdenConjecture
open Function Polynomial Filter

set_option autoImplicit false

namespace Submission

theorem theorem_1 (n : ℕ) (hn : 3 ≤ n) :
    (fun H ↦ (E n H : ℝ)) =O[atTop] (fun H ↦ (H ^ (n - 1) : ℝ)) := by
  rcases eq_or_lt_of_le hn with h3 | h4
  · subst h3
    exact Vdw.theorem_1_three
  · by_cases h5 : n ≤ 5
    · exact Vdw.theorem_1_of_indexRefined_four_five n (by omega) h5
    · by_cases hp : Nat.Prime n
      · have h7 : 7 ≤ n := by
          have hodd : Odd n := hp.odd_of_ne_two (by omega)
          obtain ⟨t, ht⟩ := hodd
          omega
        exact Vdw.theorem_1_prime n h7 hp
      · have h6' : 6 ≤ n := by omega
        refine Vdw.theorem_1_of_sliceExp n h6' (fun k m => (k : ℝ) + m) ?_
          (Vdw.imprimitiveSliceBoundExp n h6')
        intro k m hk hm hkm
        have hprod : 2 ≤ (k - 1) * (m - 1) := by
          by_cases hk2 : k = 2
          · subst hk2
            have hm3 : 3 ≤ m := by omega
            omega
          · have hk3 : 3 ≤ k := by omega
            by_cases hm2 : m = 2
            · subst hm2
              omega
            · have hm3 : 3 ≤ m := by omega
              calc 2 ≤ 2 * 2 := by norm_num
                _ ≤ (k - 1) * (m - 1) := Nat.mul_le_mul (by omega) (by omega)
        have hcast : ((k - 1) * (m - 1) : ℕ) = ((k : ℝ) - 1) * ((m : ℝ) - 1) := by
          rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_sub (by omega : 1 ≤ m)]
          norm_num
        have hprodR : (2 : ℝ) ≤ ((k : ℝ) - 1) * ((m : ℝ) - 1) := by
          rw [← hcast]
          exact_mod_cast hprod
        have hnR : (n : ℝ) = (k : ℝ) * m := by
          rw [← hkm]
          push_cast
          ring
        rw [hnR]
        nlinarith [hprodR]

end Submission
