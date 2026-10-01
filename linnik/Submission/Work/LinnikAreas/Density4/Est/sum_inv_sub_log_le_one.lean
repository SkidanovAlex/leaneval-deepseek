import Mathlib

namespace Work.LinnikAreas.Density4.Est

/-- Termwise bound: `1/n - log((n+1)/n) ≤ 1/n - 1/(n+1)` for `n ≥ 1`,
using `log(1+x) ≥ x/(1+x)`. -/
private lemma term_le (n : ℕ) (hn : 1 ≤ n) :
    (1:ℝ)/(n:ℝ) - Real.log (((n:ℝ)+1)/(n:ℝ)) ≤ (1:ℝ)/(n:ℝ) - (1:ℝ)/((n:ℝ)+1) := by
  have hn_pos : (0:ℝ) < (n:ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hx : 0 < ((n:ℝ)+1)/(n:ℝ) := by
    apply div_pos
    · linarith
    · exact hn_pos
  have h := Real.one_sub_inv_le_log_of_pos hx
  have hxinv : (((n:ℝ)+1)/(n:ℝ))⁻¹ = (n:ℝ)/((n:ℝ)+1) := inv_div _ _
  have hone : 1 - (n:ℝ)/((n:ℝ)+1) = (1:ℝ)/((n:ℝ)+1) := by
    have hne : ((n:ℝ)+1) ≠ 0 := by positivity
    field_simp
    ring
  have hlog : (1:ℝ)/((n:ℝ)+1) ≤ Real.log (((n:ℝ)+1)/(n:ℝ)) := by
    rw [← hone, ← hxinv]; exact h
  linarith

/-- The telescoping identity `∑_{n=1}^N (1/n - 1/(n+1)) = 1 - 1/(N+1)`. -/
private lemma sum_telescope (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, ((1:ℝ)/(n:ℝ) - (1:ℝ)/((n:ℝ)+1))) = 1 - 1/((N:ℝ)+1) := by
  have key := Finset.sum_Icc_sub (m := 1) (n := N) hN (fun i : ℕ => -((i:ℝ)⁻¹))
  trans ∑ i ∈ Finset.Icc 1 N, (-((((i+1):ℕ):ℝ)⁻¹) - -((i:ℝ)⁻¹))
  · apply Finset.sum_congr rfl
    intro i _
    simp only [one_div]
    rw [Nat.cast_add, Nat.cast_one]
    ring
  · rw [key]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_one, inv_one]
    rw [one_div]
    ring

theorem sum_inv_sub_log_le_one {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, ((1:ℝ)/(n:ℝ) - Real.log (((n:ℝ)+1)/(n:ℝ)))) ≤ 1 := by
  have hle : (∑ n ∈ Finset.Icc 1 N, ((1:ℝ)/(n:ℝ) - Real.log (((n:ℝ)+1)/(n:ℝ))))
      ≤ ∑ n ∈ Finset.Icc 1 N, ((1:ℝ)/(n:ℝ) - (1:ℝ)/((n:ℝ)+1)) := by
    apply Finset.sum_le_sum
    intro n hn
    exact term_le n (Finset.mem_Icc.mp hn).1
  rw [sum_telescope N hN] at hle
  have hpos : (0:ℝ) ≤ 1/((N:ℝ)+1) := by positivity
  linarith

end Work.LinnikAreas.Density4.Est
