import Mathlib.Data.Nat.ModEq
import Submission.Commons.NumberTheory.Chebyshev.theta_le_log3_mul

namespace Commons.NumberTheory.CongruenceWindows

theorem add_mod_eq_zero_iff_neg_residue {m h n : ℕ} (hm : 0 < m) :
    (n + h) % m = 0 ↔ n % m = (m - h % m) % m := by
  -- `h` is congruent to its residue, and `m` to 0, modulo `m`.
  have hh : h ≡ h % m [MOD m] := (Nat.mod_mod h m).symm
  have h0m : 0 ≡ m [MOD m] := by
    rw [Nat.ModEq]
    simp
  -- `(m - h % m) + h % m = m`, hence `(m - h % m) + h % m ≡ 0 [MOD m]`, and
  -- since `h ≡ h % m` also `(m - h % m) + h ≡ 0 [MOD m]`.
  have hB : (m - h % m) + h % m = m :=
    Nat.sub_add_cancel (Nat.le_of_lt (Nat.mod_lt h hm))
  have hsum : (m - h % m) + h % m ≡ 0 [MOD m] := by
    rw [Nat.ModEq, hB]
    simp
  have hcomb : (m - h % m) + h ≡ 0 [MOD m] :=
    (Nat.ModEq.add_left (m - h % m) hh).trans hsum
  -- Residue equalities are exactly the corresponding congruences.
  have hzero_iff : (n + h) % m = 0 ↔ n + h ≡ 0 [MOD m] := by
    simp [Nat.ModEq]
  have hneg_iff : n % m = (m - h % m) % m ↔ n ≡ m - h % m [MOD m] := by
    simp [Nat.ModEq]
  rw [hzero_iff, hneg_iff]
  constructor
  · intro h1
    -- `n + h ≡ 0` and `0 ≡ (m - h % m) + h`: cancel the common `+ h`.
    exact Nat.ModEq.add_right_cancel' h (h1.trans hcomb.symm)
  · intro hn
    -- `n ≡ m - h % m` implies `n + h ≡ (m - h % m) + h ≡ 0`.
    exact (Nat.ModEq.add_right h hn).trans hcomb

end Commons.NumberTheory.CongruenceWindows