import Mathlib.Data.Nat.ModEq
import Mathlib.Order.Interval.Finset.Nat

namespace Commons.NumberTheory.CongruenceWindows

theorem exists_mem_Icc_mod_shift (N q c h : ℕ) (hq : 1 ≤ q) (hqN : q ≤ N) :
    ∃ n ∈ Finset.Icc N (2 * N), (n + h) % q = c % q := by
  have hqpos : 0 < q := hq
  set s : ℕ := (N + h) % q with hs
  set t : ℕ := (c + q - s) % q with ht
  have hs_lt : s < q := by rw [hs]; exact Nat.mod_lt _ hqpos
  have ht_lt : t < q := by rw [ht]; exact Nat.mod_lt _ hqpos
  refine ⟨N + t, ?_, ?_⟩
  · rw [Finset.mem_Icc]
    exact ⟨by omega, by omega⟩
  · have hmod : (s + t) % q = c % q := by
      have hs_le : s ≤ c + q := by omega
      have hsum : s + (c + q - s) = c + q := by omega
      have ht' : t ≡ c + q - s [MOD q] := by
        rw [ht]; exact Nat.mod_modEq _ _
      have h1 : s + t ≡ s + (c + q - s) [MOD q] := Nat.ModEq.add_left s ht'
      rw [hsum] at h1
      exact h1.trans (Nat.add_modEq_right (a := c) (n := q))
    have hstep : ((N + t) + h) % q = (s + t) % q := by
      have hrw : (N + t) + h = (N + h) + t := by omega
      rw [hrw, Nat.add_mod, hs, Nat.mod_eq_of_lt ht_lt]
    rw [hstep, hmod]

end Commons.NumberTheory.CongruenceWindows