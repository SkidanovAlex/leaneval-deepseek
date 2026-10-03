import Mathlib
import Submission.Work.Peluse.Basic

namespace Work.Peluse.TransferUp

/-- If `G` is supported in `[-N,N]` then for every `x` with `|x| > N + |c|·H` the whole shifted
orbit `x + c·n`, `1 ≤ n ≤ H`, lies outside `[-N,N]`, so `G` vanishes on it. -/
theorem support_shift_vanishes {N H : ℕ} (c : ℤ) {G : ℤ → ℂ} (hN : Work.Peluse.SupportIn G N) :
    ∀ x : ℤ, N + c.natAbs * H < x.natAbs → ∀ n ∈ Finset.Icc 1 H, G (x + c * (n : ℤ)) = 0 := by
  intro x hx n hn
  rw [Finset.mem_Icc] at hn
  obtain ⟨hn1, hnH⟩ := hn
  apply hN
  -- `|x| > N + |c|·H` as an integer inequality
  have hx' : (N : ℤ) + |c| * (H : ℤ) < |x| := by
    have h := hx
    rw [← Nat.cast_lt (α := ℤ)] at h
    push_cast at h
    exact h
  -- `|c·n| ≤ |c|·H`
  have hcabs : |c * (n : ℤ)| ≤ |c| * (H : ℤ) := by
    have hnH' : (n : ℤ) ≤ (H : ℤ) := by exact_mod_cast hnH
    have hn0 : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast (Nat.zero_le n)
    rw [abs_mul, abs_of_nonneg hn0]
    exact mul_le_mul_of_nonneg_left hnH' (abs_nonneg c)
  -- reverse triangle inequality
  have hkey : |x| - |c * (n : ℤ)| ≤ |x + c * (n : ℤ)| := by
    have h := abs_add_le (x + c * (n : ℤ)) (-(c * (n : ℤ)))
    rw [abs_neg] at h
    have : (x + c * (n : ℤ)) + (-(c * (n : ℤ))) = x := by ring
    rw [this] at h
    linarith
  have hmain : (N : ℤ) < |x + c * (n : ℤ)| := by linarith
  rw [← Nat.cast_lt (α := ℤ)]
  rw [← Int.abs_eq_natAbs]
  exact hmain

end Work.Peluse.TransferUp
