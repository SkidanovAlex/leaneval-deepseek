import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Pi.Leibniz
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.DirichletCharacter

open Filter Finset

/-- `χ₄` vanishes at even arguments. -/
private lemma chi4_cast_even (m : ℕ) : ZMod.χ₄ (((2 * m : ℕ)) : ZMod 4) = 0 := by
  rw [ZMod.χ₄_nat_eq_if_mod_four]
  have h : (2 * m) % 2 = 0 := by omega
  simp [h]

/-- `χ₄` at odd arguments is the alternating sign `(-1)^m`. -/
private lemma chi4_cast_odd (m : ℕ) : ZMod.χ₄ (((2 * m + 1 : ℕ)) : ZMod 4) = (-1) ^ m := by
  rw [ZMod.χ₄_eq_neg_one_pow (n := 2 * m + 1) (by omega)]
  congr 1
  omega

/-- The partial sums of `χ₄(n)/n` agree with the partial sums of the Leibniz series
indexed by `N / 2`. -/
private lemma chi4_sum_range_eq (N : ℕ) :
    (∑ n ∈ Finset.range N, (((ZMod.χ₄ ((n : ℕ) : ZMod 4) : ℤ)) : ℝ) / (n : ℝ))
      = ∑ i ∈ Finset.range (N / 2), (-1 : ℝ) ^ i / (2 * i + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd N with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hN : N = 2 * m := by omega
      subst hN
      have h1 : (2 * m + 1) / 2 = m := by omega
      have h2 : (2 * m) / 2 = m := by omega
      rw [h1, h2]
      have hz : (((ZMod.χ₄ (((2 * m : ℕ)) : ZMod 4) : ℤ)) : ℝ) / (((2 * m : ℕ)) : ℝ) = 0 := by
        rw [chi4_cast_even]; simp
      rw [hz, add_zero]
    · have hN : N = 2 * m + 1 := by omega
      subst hN
      have h1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
      have h2 : (2 * m + 1) / 2 = m := by omega
      rw [h1, h2, Finset.sum_range_succ]
      congr 1
      have hz : (((ZMod.χ₄ (((2 * m + 1 : ℕ)) : ZMod 4) : ℤ)) : ℝ)
          / (((2 * m + 1 : ℕ)) : ℝ) = (-1 : ℝ) ^ m / (2 * m + 1) := by
        rw [chi4_cast_odd]
        push_cast
        ring
      exact hz

/-- The Leibniz series in terms of the character `χ₄`: `∑_{n < N} χ₄(n)/n → π/4`. -/
theorem chi4_sum_div_tendsto_pi_div_four :
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
        (((ZMod.χ₄ ((n : ℕ) : ZMod 4) : ℤ)) : ℝ) / (n : ℝ))
      Filter.atTop (nhds (Real.pi / 4)) := by
  have hdiv : Tendsto (fun N : ℕ => N / 2) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    exact ⟨2 * b, fun a ha => by omega⟩
  have hmain : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range (N / 2), (-1 : ℝ) ^ i / (2 * i + 1))
      atTop (nhds (Real.pi / 4)) := Real.tendsto_sum_pi_div_four.comp hdiv
  rw [show (fun N : ℕ => ∑ i ∈ Finset.range (N / 2), (-1 : ℝ) ^ i / (2 * i + 1))
      = (fun N : ℕ => ∑ n ∈ Finset.range N,
        (((ZMod.χ₄ ((n : ℕ) : ZMod 4) : ℤ)) : ℝ) / (n : ℝ)) from
      funext fun N => (chi4_sum_range_eq N).symm] at hmain
  exact hmain

end Commons.NumberTheory.DirichletCharacter