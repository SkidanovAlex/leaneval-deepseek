import Mathlib

/-!
# The chain rule for `Real.negMulLog` over a finite distribution

For nonnegative `x : κ → ℝ` with total `p = ∑ j, x j`,

`∑ j, φ(x j) = φ(p) + p * ∑ j, φ(x j / p)`,  where `φ = Real.negMulLog`.

This is the entropy chain rule `H(X) = H(T) + ∑ p_i H(X | T = i)` in elementary form.
-/

namespace Work.EKLComp

theorem negMulLog_sum_div {κ : Type} [Fintype κ] (x : κ → ℝ) (p : ℝ)
    (hx : ∀ j, 0 ≤ x j) (hsum : ∑ j, x j = p) :
    ∑ j, Real.negMulLog (x j) = Real.negMulLog p + p * ∑ j, Real.negMulLog (x j / p) := by
  have hp0 : 0 ≤ p := by rw [← hsum]; exact Finset.sum_nonneg fun j _ => hx j
  rcases eq_or_lt_of_le hp0 with hp_eq | hp_pos
  · -- degenerate case `p = 0`: then every `x j` vanishes
    subst hp_eq
    have hxj : ∀ j, x j = 0 := fun j => by
      have h := Finset.single_le_sum (f := x) (fun i _ => hx i) (Finset.mem_univ j)
      rw [hsum] at h
      exact le_antisymm h (hx j)
    simp [hxj]
  · have hpne : p ≠ 0 := ne_of_gt hp_pos
    have hcp : ∀ j, x j = p * (x j / p) := fun j => by field_simp
    have hstep : ∀ j, Real.negMulLog (x j)
        = (x j / p) * Real.negMulLog p + p * Real.negMulLog (x j / p) := fun j => by
      conv_lhs => rw [hcp j]
      rw [Real.negMulLog_mul]
    have hsum_div : ∑ j, x j / p = 1 := by
      rw [← Finset.sum_div, hsum]
      exact div_self hpne
    calc ∑ j, Real.negMulLog (x j)
        = ∑ j, ((x j / p) * Real.negMulLog p + p * Real.negMulLog (x j / p)) :=
            Finset.sum_congr rfl fun j _ => hstep j
      _ = (∑ j, x j / p) * Real.negMulLog p + p * ∑ j, Real.negMulLog (x j / p) := by
            rw [Finset.sum_add_distrib]
            congr 1
            · exact (Finset.sum_mul Finset.univ (fun j => x j / p) (Real.negMulLog p)).symm
            · exact (Finset.mul_sum Finset.univ (fun j => Real.negMulLog (x j / p)) p).symm
      _ = Real.negMulLog p + p * ∑ j, Real.negMulLog (x j / p) := by rw [hsum_div, one_mul]

end Work.EKLComp
