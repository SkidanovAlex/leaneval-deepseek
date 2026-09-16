import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring.Basic
import Submission.Commons.NumberTheory.SieveWindows.divisorSumProduct_window_eq_k

open scoped BigOperators

namespace Commons.NumberTheory.SieveWindows

private lemma w_indicator_mul_lcm_eq (d e m : ℕ) :
    (if d ∣ m then (1 : ℝ) else 0) * (if e ∣ m then (1 : ℝ) else 0) =
      if Nat.lcm d e ∣ m then (1 : ℝ) else 0 := by
  by_cases hd : d ∣ m
  · by_cases he : e ∣ m
    · have h : Nat.lcm d e ∣ m := (Nat.lcm_dvd_iff).2 ⟨hd, he⟩
      simp [hd, he, h]
    · have hne : ¬ Nat.lcm d e ∣ m := by
        intro hl
        exact he (Nat.dvd_trans (Nat.dvd_lcm_right d e) hl)
      simp [hd, he, hne]
  · have hne : ¬ Nat.lcm d e ∣ m := by
      intro hl
      exact hd (Nat.dvd_trans (Nat.dvd_lcm_left d e) hl)
    simp [hd, hne]

private lemma w_prod_dvd_indicator_eq {k : ℕ} (a m : Fin k → ℕ) :
    (∏ i : Fin k, if a i ∣ m i then (1 : ℝ) else 0) =
      if ∀ i : Fin k, a i ∣ m i then (1 : ℝ) else 0 := by
  rw [Finset.prod_boole]
  simp

private lemma w_prod_sum_mul_sum {k D : ℕ} (A B : Fin k → Fin (D + 1) → ℝ) :
    (∏ i : Fin k, (∑ d : Fin (D + 1), A i d) * (∑ e : Fin (D + 1), B i e)) =
      ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
        ∏ i : Fin k, A i (d i) * B i (e i) := by
  calc
    (∏ i : Fin k, (∑ d : Fin (D + 1), A i d) * (∑ e : Fin (D + 1), B i e))
      = ∏ i : Fin k, (∑ d : Fin (D + 1), A i d * (∑ e : Fin (D + 1), B i e)) := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [Finset.sum_mul]
    _ = ∑ d : (Fin k → Fin (D + 1)), ∏ i : Fin k, A i (d i) * (∑ e : Fin (D + 1), B i e) := by
          exact Fintype.prod_sum (fun (i : Fin k) (d : Fin (D + 1)) => A i d * (∑ e : Fin (D + 1), B i e))
    _ = ∑ d : (Fin k → Fin (D + 1)), (∏ i : Fin k, A i (d i)) * (∏ i : Fin k, ∑ e : Fin (D + 1), B i e) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.prod_mul_distrib]
    _ = (∑ d : (Fin k → Fin (D + 1)), ∏ i : Fin k, A i (d i)) * (∏ i : Fin k, ∑ e : Fin (D + 1), B i e) := by
          rw [← Finset.sum_mul]
    _ = (∑ d : (Fin k → Fin (D + 1)), ∏ i : Fin k, A i (d i)) * (∑ e : (Fin k → Fin (D + 1)), ∏ i : Fin k, B i (e i)) := by
          rw [Fintype.prod_sum (fun (i : Fin k) (e : Fin (D + 1)) => B i e)]
    _ = ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
          (∏ i : Fin k, A i (d i)) * (∏ i : Fin k, B i (e i)) := by
          rw [Finset.sum_mul_sum]
    _ = ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
          ∏ i : Fin k, A i (d i) * B i (e i) := by
          apply Finset.sum_congr rfl
          intro d hd
          apply Finset.sum_congr rfl
          intro e he
          rw [Finset.prod_mul_distrib]

private lemma w_mul_prod_sum_mul_sum {k D : ℕ} (c : ℝ) (A B : Fin k → Fin (D + 1) → ℝ) :
    c * (∏ i : Fin k, (∑ d : Fin (D + 1), A i d) * (∑ e : Fin (D + 1), B i e)) =
      ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
        c * ∏ i : Fin k, A i (d i) * B i (e i) := by
  rw [w_prod_sum_mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]

private lemma w_sum_prod_boole_lcm {k D : ℕ} (s : Finset ℕ) (H : Fin k → ℕ) (g : ℕ → ℝ)
    (d e : Fin k → Fin (D + 1)) :
    (∑ n ∈ s, g n * ∏ i : Fin k,
        (if Nat.lcm (d i : ℕ) (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) =
      ∑ n ∈ s.filter (fun n => ∀ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ) ∣ n + H i), g n := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  rw [w_prod_dvd_indicator_eq]
  by_cases h : ∀ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ) ∣ n + H i <;> simp [h]

private lemma w_sum_divisor_term {k D : ℕ} (s : Finset ℕ) (H : Fin k → ℕ) (g : ℕ → ℝ)
    (α β : Fin k → ℕ → ℝ) (d e : Fin k → Fin (D + 1)) :
    (∑ n ∈ s, g n * ∏ i : Fin k,
        (α i (d i : ℕ) * (if (d i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
        (β i (e i : ℕ) * (if (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0))) =
      (∏ i : Fin k, α i (d i : ℕ) * β i (e i : ℕ)) *
        ∑ n ∈ s.filter (fun n => ∀ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ) ∣ n + H i), g n := by
  calc
    (∑ n ∈ s, g n * ∏ i : Fin k,
        (α i (d i : ℕ) * (if (d i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
        (β i (e i : ℕ) * (if (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0)))
      = ∑ n ∈ s, g n * ((∏ i : Fin k, α i (d i : ℕ) * β i (e i : ℕ)) *
          ∏ i : Fin k,
            (if (d i : ℕ) ∣ n + H i then (1 : ℝ) else 0) *
            (if (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) := by
          apply Finset.sum_congr rfl
          intro n hn
          congr 1
          calc
            (∏ i : Fin k,
              (α i (d i : ℕ) * (if (d i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
              (β i (e i : ℕ) * (if (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0)))
              = ∏ i : Fin k, (α i (d i : ℕ) * β i (e i : ℕ)) *
                  ((if (d i : ℕ) ∣ n + H i then (1 : ℝ) else 0) *
                    (if (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) := by
                  apply Finset.prod_congr rfl
                  intro i hi
                  ring
            _ = (∏ i : Fin k, α i (d i : ℕ) * β i (e i : ℕ)) *
                (∏ i : Fin k,
                  (if (d i : ℕ) ∣ n + H i then (1 : ℝ) else 0) *
                  (if (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) := by
                  rw [Finset.prod_mul_distrib]
    _ = ∑ n ∈ s, (∏ i : Fin k, α i (d i : ℕ) * β i (e i : ℕ)) *
          (g n * ∏ i : Fin k,
            (if (d i : ℕ) ∣ n + H i then (1 : ℝ) else 0) *
            (if (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) := by
          apply Finset.sum_congr rfl
          intro n hn
          ring
    _ = (∏ i : Fin k, α i (d i : ℕ) * β i (e i : ℕ)) *
          (∑ n ∈ s, g n * ∏ i : Fin k,
            (if (d i : ℕ) ∣ n + H i then (1 : ℝ) else 0) *
            (if (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) := by
          rw [Finset.mul_sum]
    _ = (∏ i : Fin k, α i (d i : ℕ) * β i (e i : ℕ)) *
          (∑ n ∈ s, g n * ∏ i : Fin k,
            (if Nat.lcm (d i : ℕ) (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro n hn
          congr 1
          apply Finset.prod_congr rfl
          intro i hi
          exact w_indicator_mul_lcm_eq (d i : ℕ) (e i : ℕ) (n + H i)
    _ = (∏ i : Fin k, α i (d i : ℕ) * β i (e i : ℕ)) *
          ∑ n ∈ s.filter (fun n => ∀ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ) ∣ n + H i), g n := by
          rw [w_sum_prod_boole_lcm]

/-- **Weighted `k`-coordinate divisor-sum expansion.**  Generalisation of
`Commons.NumberTheory.SieveWindows.divisorSumProduct_window_eq_k` (same proof,
with the extra weight `g n` on the inner sum): expanding the product of
one-dimensional divisor sums over a weighted window gives a double sum over
divisor tuples whose coefficient is `∏ᵢ αᵢ(dᵢ)βᵢ(eᵢ)` times the weighted count
of `n ∈ s` with `∀ i, lcm (dᵢ) (eᵢ) ∣ n + Hᵢ`. -/
theorem weighted_divisorSumProduct_window_eq_k {k D : ℕ} {s : Finset ℕ} {H : Fin k → ℕ}
    (g : ℕ → ℝ) (α β : Fin k → ℕ → ℝ) :
    (∑ n ∈ s, g n * ∏ i : Fin k,
        (∑ d : Fin (D + 1), α i (d : ℕ) * (if (d : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
        (∑ e : Fin (D + 1), β i (e : ℕ) * (if (e : ℕ) ∣ n + H i then (1 : ℝ) else 0))) =
    ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
      (∏ i : Fin k, α i (d i : ℕ) * β i (e i : ℕ)) *
        (∑ n ∈ s.filter (fun n => ∀ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ) ∣ n + H i), g n) := by
  classical
  calc
    (∑ n ∈ s, g n * ∏ i : Fin k,
        (∑ d : Fin (D + 1), α i (d : ℕ) * (if (d : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
        (∑ e : Fin (D + 1), β i (e : ℕ) * (if (e : ℕ) ∣ n + H i then (1 : ℝ) else 0)))
      = ∑ n ∈ s, ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
          g n * ∏ i : Fin k,
            (α i (d i : ℕ) * (if (d i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
            (β i (e i : ℕ) * (if (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) := by
          apply Finset.sum_congr rfl
          intro n hn
          exact w_mul_prod_sum_mul_sum (g n)
            (fun i d => α i (d : ℕ) * (if (d : ℕ) ∣ n + H i then (1 : ℝ) else 0))
            (fun i e => β i (e : ℕ) * (if (e : ℕ) ∣ n + H i then (1 : ℝ) else 0))
    _ = ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)), ∑ n ∈ s,
          g n * ∏ i : Fin k,
            (α i (d i : ℕ) * (if (d i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
            (β i (e i : ℕ) * (if (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) := by
          calc
            (∑ n ∈ s, ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
                g n * ∏ i : Fin k,
                  (α i (d i : ℕ) * (if (d i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
                  (β i (e i : ℕ) * (if (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0)))
              = ∑ d : (Fin k → Fin (D + 1)), ∑ n ∈ s, ∑ e : (Fin k → Fin (D + 1)),
                  g n * ∏ i : Fin k,
                    (α i (d i : ℕ) * (if (d i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
                    (β i (e i : ℕ) * (if (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) := by
                  exact Finset.sum_comm (s := s) (t := (Finset.univ : Finset (Fin k → Fin (D + 1))))
                    (f := fun n d => ∑ e : Fin k → Fin (D + 1),
                      g n * ∏ i : Fin k,
                        (α i (d i : ℕ) * (if (d i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
                        (β i (e i : ℕ) * (if (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0)))
              _ = ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)), ∑ n ∈ s,
                  g n * ∏ i : Fin k,
                    (α i (d i : ℕ) * (if (d i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
                    (β i (e i : ℕ) * (if (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) := by
                  apply Finset.sum_congr rfl
                  intro d hd
                  exact Finset.sum_comm (s := s) (t := (Finset.univ : Finset (Fin k → Fin (D + 1))))
                    (f := fun n e => g n * ∏ i : Fin k,
                      (α i (d i : ℕ) * (if (d i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
                      (β i (e i : ℕ) * (if (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0)))
    _ = ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
          (∏ i : Fin k, α i (d i : ℕ) * β i (e i : ℕ)) *
            (∑ n ∈ s.filter (fun n => ∀ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ) ∣ n + H i), g n) := by
          apply Finset.sum_congr rfl
          intro d hd
          apply Finset.sum_congr rfl
          intro e he
          exact w_sum_divisor_term s H g α β d e

end Commons.NumberTheory.SieveWindows