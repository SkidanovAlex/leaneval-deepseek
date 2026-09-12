import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Data.Rat.Star

namespace Commons.Algebra.Polynomial

open Filter

theorem natDegree_le_of_eventually_abs_eval_le {P : Polynomial ℚ} {k : ℕ} {C : ℚ} {N : ℕ}
    (h : ∀ n : ℕ, N ≤ n → |P.eval (n : ℚ)| ≤ C * (n : ℚ) ^ k) :
    P.natDegree ≤ k := by
  by_contra hcon
  have hcon : k < P.natDegree := lt_of_not_ge hcon
  have hPne : P ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hcon
    omega
  rcases le_or_gt C 0 with hC | hC
  · have hroot : ∀ n : ℕ, N ≤ n → P.eval (n : ℚ) = 0 := by
      intro n hn
      have h1 := h n hn
      have h2 : C * (n : ℚ) ^ k ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hC (by positivity)
      have h3 : |P.eval (n : ℚ)| ≤ 0 := le_trans h1 h2
      exact abs_eq_zero.mp (le_antisymm h3 (abs_nonneg _))
    refine hPne (Polynomial.eq_zero_of_infinite_isRoot P ?_)
    refine (Set.infinite_range_of_injective (f := fun n : ℕ => ((N + n : ℕ) : ℚ)) ?_).mono ?_
    · intro a b hab
      have h' : (N + a : ℕ) = N + b := Nat.cast_injective hab
      omega
    · rintro x ⟨n, rfl⟩
      simpa using hroot (N + n) (Nat.le_add_right N n)
  · set Q : Polynomial ℚ := Polynomial.X ^ k with hQdef
    have hQne : Q ≠ 0 := by
      rw [hQdef]; exact pow_ne_zero _ Polynomial.X_ne_zero
    have hdeg : Q.degree < P.degree := by
      rw [hQdef, Polynomial.degree_X_pow, Polynomial.degree_eq_natDegree hPne]
      exact WithBot.coe_lt_coe.mpr hcon
    have hev : ∀ᶠ n : ℕ in atTop, C < |P.eval (n : ℚ) / Q.eval (n : ℚ)| :=
      Filter.Eventually.natCast_atTop (R := ℚ) <|
        (Polynomial.abs_div_tendsto_atTop_atTop_of_degree_gt P Q hdeg hQne).eventually
          (eventually_gt_atTop C)
    obtain ⟨M, hM⟩ := eventually_atTop.mp hev
    set n : ℕ := max (max M N) 1 with hn
    have hnM : M ≤ n := by
      rw [hn]; exact le_trans (le_max_left M N) (le_max_left (max M N) 1)
    have hnN : N ≤ n := by
      rw [hn]; exact le_trans (le_max_right M N) (le_max_left (max M N) 1)
    have hn1 : 1 ≤ n := by
      rw [hn]; exact le_max_right (max M N) 1
    have hrw : Q.eval (n : ℚ) = (n : ℚ) ^ k := by
      rw [hQdef, Polynomial.eval_pow, Polynomial.eval_X]
    have hbound := hM n hnM
    rw [hrw] at hbound
    have hpowpos : 0 < (n : ℚ) ^ k := by
      apply pow_pos
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
    have habs : |P.eval (n : ℚ) / (n : ℚ) ^ k| = |P.eval (n : ℚ)| / (n : ℚ) ^ k := by
      rw [abs_div, abs_of_pos hpowpos]
    rw [habs] at hbound
    have hmul : C * (n : ℚ) ^ k < |P.eval (n : ℚ)| := (lt_div_iff₀ hpowpos).mp hbound
    exact absurd hmul (not_lt.mpr (h n hnN))

end Commons.Algebra.Polynomial