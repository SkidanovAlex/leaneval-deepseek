import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.NormNum.Prime

namespace Commons.NumberTheory.Pow

/-- No rational number has a power `s ≥ 2` equal to `2`. -/
lemma rat_pow_ne_two (r : ℚ) (s : ℕ) (hs : 2 ≤ s) : r ^ s ≠ 2 := by
  intro h
  have hp2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hval : (s : ℤ) * padicValRat 2 r = 1 := by
    have hc := congrArg (padicValRat 2) h
    rw [padicValRat.pow (p := 2) (q := r) (k := s) (hp := hp2)] at hc
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num] at hc
    rw [padicValRat.self (by norm_num : 1 < 2)] at hc
    exact hc
  have hdvd : (s : ℤ) ∣ (1 : ℤ) := ⟨padicValRat 2 r, by rw [hval]⟩
  have hdvd_nat : s ∣ 1 := (Int.ofNat_dvd).mp hdvd
  have hle : s ≤ 1 := Nat.le_of_dvd (by norm_num : 0 < 1) hdvd_nat
  omega

end Commons.NumberTheory.Pow