import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Data.Rat.Star

namespace Commons.Algebra.Polynomial

/-- A rational polynomial of degree at most `d` which takes nonnegative values at all sufficiently
large natural numbers has nonnegative coefficient of degree `d`. -/
theorem coeff_nonneg_of_eventually_eval_nonneg {f : Polynomial ℚ} {d : ℕ}
    (hd : f.natDegree ≤ d) (hf : ∃ N, ∀ n : ℕ, N ≤ n → 0 ≤ f.eval (n : ℚ)) :
    0 ≤ f.coeff d := by
  by_contra hcon
  have hcon : f.coeff d < 0 := lt_of_not_ge hcon
  obtain ⟨N, hN⟩ := hf
  have hc : f.coeff d ≠ 0 := ne_of_lt hcon
  have hnd : f.natDegree = d := by
    rcases lt_or_ge f.natDegree d with h | h
    · exact absurd (Polynomial.coeff_eq_zero_of_natDegree_lt h) hc
    · exact le_antisymm hd h
  have hfne : f ≠ 0 := by
    intro h
    exact hc (by simp [h])
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    have hC : f = Polynomial.C (f.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hnd
    have := hN N le_rfl
    rw [hC, Polynomial.eval_C] at this
    linarith
  · have hdeg : 0 < f.degree := by
      rw [Polynomial.degree_eq_natDegree hfne, hnd]
      exact WithBot.coe_pos.mpr hdpos
    have hlc : f.leadingCoeff ≤ 0 := by
      rw [← Polynomial.coeff_natDegree, hnd]
      exact le_of_lt hcon
    have hlim := Polynomial.tendsto_atBot_of_leadingCoeff_nonpos f hdeg hlc
    have hev : ∀ᶠ x : ℚ in Filter.atTop, f.eval x < 0 := by
      have h1 : ∀ᶠ x : ℚ in Filter.atTop, f.eval x ≤ (-1 : ℚ) :=
        (Filter.tendsto_atBot.mp hlim) (-1)
      filter_upwards [h1] with x hx
      linarith
    obtain ⟨q, hq⟩ := Filter.eventually_atTop.mp hev
    obtain ⟨k, hk⟩ := exists_nat_ge q
    have hmax : q ≤ ((max k N : ℕ) : ℚ) := by
      have : (k : ℚ) ≤ ((max k N : ℕ) : ℚ) := by exact_mod_cast Nat.le_max_left k N
      linarith
    have hneg := hq ((max k N : ℕ) : ℚ) hmax
    have hpos := hN (max k N) (Nat.le_max_right k N)
    linarith

end Commons.Algebra.Polynomial