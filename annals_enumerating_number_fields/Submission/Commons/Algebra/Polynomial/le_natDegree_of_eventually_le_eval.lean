import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Data.Rat.Star

namespace Commons.Algebra.Polynomial

theorem le_natDegree_of_eventually_le_eval {P : Polynomial ℚ} {k : ℕ} {C : ℚ} {N : ℕ}
    (hC : 0 < C) (h : ∀ n : ℕ, N ≤ n → C * (n : ℚ) ^ k ≤ P.eval (n : ℚ)) :
    k ≤ P.natDegree := by
  by_contra hcon
  rw [not_le] at hcon
  have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le _) hcon
  set Q : Polynomial ℚ := Polynomial.X ^ k with hQ
  have hQeval : ∀ x : ℚ, Q.eval x = x ^ k := by
    intro x; rw [hQ, Polynomial.eval_pow, Polynomial.eval_X]
  have hdeg : P.degree < Q.degree := by
    rw [hQ, Polynomial.degree_X_pow]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (WithBot.coe_lt_coe.mpr hcon)
  have htend : Filter.Tendsto (fun x : ℚ => P.eval x / Q.eval x) Filter.atTop (nhds 0) :=
    Polynomial.div_tendsto_atTop_zero_of_degree_lt P Q hdeg
  have hevQ : ∀ᶠ x : ℚ in Filter.atTop, P.eval x / Q.eval x < C :=
    htend.eventually (eventually_lt_nhds hC)
  have hevN : ∀ᶠ n : ℕ in Filter.atTop, P.eval (n : ℚ) / Q.eval (n : ℚ) < C :=
    Filter.Eventually.natCast_atTop hevQ
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hevN
  set n : ℕ := max M (max N 1) with hn
  have hnM : M ≤ n := le_max_left _ _
  have hnN : N ≤ n := le_trans (le_max_left N 1) (le_max_right M (max N 1))
  have hn1 : 1 ≤ n := le_trans (le_max_right N 1) (le_max_right M (max N 1))
  have hltC : P.eval (n : ℚ) / (n : ℚ) ^ k < C := by
    simpa only [hQeval] using hM n hnM
  have hpos : (0 : ℚ) < (n : ℚ) ^ k :=
    pow_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)) k
  have hle : C ≤ P.eval (n : ℚ) / (n : ℚ) ^ k := by
    rw [le_div_iff₀ hpos]
    exact h n hnN
  linarith

end Commons.Algebra.Polynomial