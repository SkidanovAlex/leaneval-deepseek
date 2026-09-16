import Mathlib
open scoped BigOperators

namespace Commons.NumberTheory.SieveWindows

private lemma indicator_mul_lcm_eq (d e m : ℕ) :
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

private lemma prod_dvd_indicator_eq {k : ℕ} (a m : Fin k → ℕ) :
    (∏ i : Fin k, if a i ∣ m i then (1 : ℝ) else 0) =
      if ∀ i : Fin k, a i ∣ m i then (1 : ℝ) else 0 := by
  rw [Finset.prod_boole]
  simp

private lemma sum_prod_boole_lcm {k D : ℕ} (s : Finset ℕ) (H : Fin k → ℕ)
    (d e : Fin k → Fin (D + 1)) :
    (∑ n ∈ s, ∏ i : Fin k,
        (if (d i : ℕ) ∣ n + H i then (1 : ℝ) else 0) *
        (if (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) =
      ((s.filter (fun n => ∀ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ) ∣ n + H i)).card : ℝ) := by
  calc
    (∑ n ∈ s, ∏ i : Fin k,
        (if (d i : ℕ) ∣ n + H i then (1 : ℝ) else 0) *
        (if (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0))
      = ∑ n ∈ s, ∏ i : Fin k, (if Nat.lcm (d i : ℕ) (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro n hn
          apply Finset.prod_congr rfl
          intro i hi
          exact indicator_mul_lcm_eq (d i : ℕ) (e i : ℕ) (n + H i)
    _ = ∑ n ∈ s, (if ∀ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro n hn
          exact prod_dvd_indicator_eq (fun i => Nat.lcm (d i : ℕ) (e i : ℕ)) (fun i => n + H i)
    _ = ((s.filter (fun n => ∀ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ) ∣ n + H i)).card : ℝ) := by
          rw [Finset.sum_boole]

private lemma prod_sum_mul_sum {k D : ℕ} (A B : Fin k → Fin (D + 1) → ℝ) :
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

private lemma sum_divisor_term {k D : ℕ} (s : Finset ℕ) (H : Fin k → ℕ)
    (α β : Fin k → ℕ → ℝ) (d e : Fin k → Fin (D + 1)) :
    (∑ n ∈ s, ∏ i : Fin k,
        (α i (d i : ℕ) * (if (d i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
        (β i (e i : ℕ) * (if (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0))) =
      (∏ i : Fin k, α i (d i : ℕ) * β i (e i : ℕ)) *
        ((s.filter (fun n => ∀ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ) ∣ n + H i)).card : ℝ) := by
  calc
    (∑ n ∈ s, ∏ i : Fin k,
        (α i (d i : ℕ) * (if (d i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
        (β i (e i : ℕ) * (if (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0)))
      = ∑ n ∈ s, (∏ i : Fin k, α i (d i : ℕ) * β i (e i : ℕ)) *
          (∏ i : Fin k,
            (if (d i : ℕ) ∣ n + H i then (1 : ℝ) else 0) *
            (if (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) := by
          apply Finset.sum_congr rfl
          intro n hn
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
    _ = (∏ i : Fin k, α i (d i : ℕ) * β i (e i : ℕ)) *
        (∑ n ∈ s, ∏ i : Fin k,
          (if (d i : ℕ) ∣ n + H i then (1 : ℝ) else 0) *
          (if (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) := by
          rw [← Finset.mul_sum]
    _ = (∏ i : Fin k, α i (d i : ℕ) * β i (e i : ℕ)) *
        ((s.filter (fun n => ∀ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ) ∣ n + H i)).card : ℝ) := by
          rw [sum_prod_boole_lcm s H d e]

theorem divisorSumProduct_window_eq_k {k D : ℕ} {s : Finset ℕ} {H : Fin k → ℕ}
    (α β : Fin k → ℕ → ℝ) :
    (∑ n ∈ s,
        ∏ i : Fin k,
          (∑ d : Fin (D + 1), α i (d : ℕ) * (if (d : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
          (∑ e : Fin (D + 1), β i (e : ℕ) * (if (e : ℕ) ∣ n + H i then (1 : ℝ) else 0))) =
    ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
      (∏ i : Fin k, α i (d i : ℕ) * β i (e i : ℕ)) *
        ((s.filter (fun n => ∀ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ) ∣ n + H i)).card : ℝ) := by
  classical
  calc
    (∑ n ∈ s,
        ∏ i : Fin k,
          (∑ d : Fin (D + 1), α i (d : ℕ) * (if (d : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
          (∑ e : Fin (D + 1), β i (e : ℕ) * (if (e : ℕ) ∣ n + H i then (1 : ℝ) else 0)))
      = ∑ n ∈ s, ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
          ∏ i : Fin k, (α i (d i : ℕ) * (if (d i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
            (β i (e i : ℕ) * (if (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) := by
          apply Finset.sum_congr rfl
          intro n hn
          exact prod_sum_mul_sum (k := k) (D := D)
            (A := fun i d => α i (d : ℕ) * (if (d : ℕ) ∣ n + H i then (1 : ℝ) else 0))
            (B := fun i e => β i (e : ℕ) * (if (e : ℕ) ∣ n + H i then (1 : ℝ) else 0))
    _ = ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)), ∑ n ∈ s,
          ∏ i : Fin k, (α i (d i : ℕ) * (if (d i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
            (β i (e i : ℕ) * (if (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) := by
          calc
            (∑ n ∈ s, ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
                ∏ i : Fin k, (α i (d i : ℕ) * (if (d i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
                  (β i (e i : ℕ) * (if (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0)))
              = ∑ d : (Fin k → Fin (D + 1)), ∑ n ∈ s, ∑ e : (Fin k → Fin (D + 1)),
                  ∏ i : Fin k, (α i (d i : ℕ) * (if (d i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
                    (β i (e i : ℕ) * (if (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) := by
                  exact Finset.sum_comm (s := s) (t := (Finset.univ : Finset (Fin k → Fin (D + 1))))
                    (f := fun n d => ∑ e : Fin k → Fin (D + 1),
                      ∏ i : Fin k, (α i (d i : ℕ) * (if (d i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
                        (β i (e i : ℕ) * (if (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0)))
              _ = ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)), ∑ n ∈ s,
                  ∏ i : Fin k, (α i (d i : ℕ) * (if (d i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
                    (β i (e i : ℕ) * (if (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) := by
                  apply Finset.sum_congr rfl
                  intro d hd
                  exact Finset.sum_comm (s := s) (t := (Finset.univ : Finset (Fin k → Fin (D + 1))))
                    (f := fun n e => ∏ i : Fin k,
                      (α i (d i : ℕ) * (if (d i : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
                        (β i (e i : ℕ) * (if (e i : ℕ) ∣ n + H i then (1 : ℝ) else 0)))
    _ = ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
          (∏ i : Fin k, α i (d i : ℕ) * β i (e i : ℕ)) *
          ((s.filter (fun n => ∀ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ) ∣ n + H i)).card : ℝ) := by
          apply Finset.sum_congr rfl
          intro d hd
          apply Finset.sum_congr rfl
          intro e he
          exact sum_divisor_term (k := k) (D := D) s H α β d e

end Commons.NumberTheory.SieveWindows
