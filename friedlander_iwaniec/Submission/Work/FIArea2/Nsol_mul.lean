import Mathlib
import Submission.Work.FIArea2.NsolDefs
import Submission.Work.FIArea2.card_solutions_crt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea2

open Finset

/-- **The congruence count `N(a;q)` is multiplicative in the modulus.**  For coprime `m`, `n`, the number of solutions of `aγ₁² ≡ γ₂² (mod mn)` is the product of the numbers of solutions modulo `m` and modulo `n` (Chinese remainder: `ZMod.chineseRemainder`).  This is the "Since `N(a;q)` is multiplicative" step (8.9) of *FI* §8.  Note `Nsol` is a total function of `q` with value `0` at `q = 0`, so the degenerate cases `m = 0` or `n = 0` (which force the other argument to be `1` under `Nat.Coprime`) are included and must be handled. -/
theorem Nsol_mul (a m n : ℕ) (h : Nat.Coprime m n) :
    Nsol (m * n) a = Nsol m a * Nsol n a := by
  rcases eq_or_ne m 0 with hm | hm
  · rw [hm, Nat.coprime_zero_left] at h
    rw [hm, h, Nat.zero_mul]
    simp [Nsol_zero, Nsol_one]
  rcases eq_or_ne n 0 with hn | hn
  · rw [hn, Nat.coprime_zero_right] at h
    rw [hn, h, Nat.mul_zero]
    simp [Nsol_zero, Nsol_one]
  have hmn : m * n ≠ 0 := Nat.mul_ne_zero hm hn
  have : NeZero m := ⟨hm⟩
  have : NeZero n := ⟨hn⟩
  have : NeZero (m * n) := ⟨hmn⟩
  rw [Nsol_eq_filter (m * n) a, Nsol_eq_filter m a, Nsol_eq_filter n a]
  have hR := card_solutions_crt a m n h
  rw [← Nat.cast_mul] at hR
  exact Nat.cast_injective hR

end Work.FIArea2

