import Mathlib.Algebra.Order.Archimedean.Basic

namespace Commons.Order.WithZeroRat

open Multiplicative

theorem archimedean {a ε : WithZero (Multiplicative ℚ)} (ha0 : 0 ≤ a) (ha : a < 1) (hε : 0 < ε) :
    ∃ n : ℕ, a ^ n < ε := by
  cases a with
  | zero =>
    refine ⟨1, ?_⟩
    rw [pow_one]
    simpa using hε
  | coe q =>
    cases ε with
    | zero => exact absurd hε (not_lt_of_ge (zero_le))
    | coe r =>
      have hq : q < 1 := by
        rw [← WithZero.coe_one] at ha
        exact WithZero.coe_lt_coe.mp ha
      obtain ⟨n, hn⟩ := exists_pow_lt hq r
      refine ⟨n, ?_⟩
      rw [← WithZero.coe_pow]
      exact WithZero.coe_lt_coe.mpr hn

end Commons.Order.WithZeroRat