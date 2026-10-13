import Mathlib

namespace Work.WilC4aP

open Polynomial Finset

/-- **Cauchy root bound.** A root of a monic polynomial over `ℂ` is bounded by `1 +` the sum of
the absolute values of the (lower) coefficients. -/
theorem poly_root_bound {p : Polynomial ℂ} (hmon : p.Monic) {α : ℂ} (hα : p.eval α = 0) :
    ‖α‖ ≤ max 1 (∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖) := by
  rcases Nat.eq_zero_or_pos p.natDegree with hn | hn
  · -- degree zero: `p = 1` has no roots
    have hp1 : p = 1 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero hn]
      have : p.coeff 0 = 1 := by rw [← hn]; exact hmon.coeff_natDegree
      rw [this, Polynomial.C_1]
    rw [hp1] at hα
    simp at hα
  · set r : ℝ := ‖α‖ with hr
    set S : ℝ := ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖ with hS
    rcases le_or_gt r 1 with hle | hgt
    · exact le_trans hle (le_max_left 1 S)
    · -- `1 < r`: bound the top term against the lower ones
      have hrpos : 0 < r := lt_trans zero_lt_one hgt
      have hroot : α ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree, p.coeff i * α ^ i := by
        apply eq_neg_of_add_eq_zero_left
        have heval : p.eval α = (∑ i ∈ Finset.range p.natDegree, p.coeff i * α ^ i)
            + p.coeff p.natDegree * α ^ p.natDegree := by
          rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ]
        rw [heval, hmon.coeff_natDegree, one_mul] at hα
        rw [add_comm]
        exact hα
      have h1 : r ^ p.natDegree ≤ ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖ * r ^ i := by
        have hab : r ^ p.natDegree = ‖α ^ p.natDegree‖ := by rw [norm_pow, ← hr]
        rw [hab, hroot, norm_neg]
        calc ‖∑ i ∈ Finset.range p.natDegree, p.coeff i * α ^ i‖
            ≤ ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i * α ^ i‖ := norm_sum_le _ _
          _ = ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖ * r ^ i := by
              apply Finset.sum_congr rfl
              intro i _
              rw [norm_mul, norm_pow, ← hr]
      have h2 : ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖ * r ^ i
          ≤ S * r ^ (p.natDegree - 1) := by
        have hstep : ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖ * r ^ i
            ≤ ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖ * r ^ (p.natDegree - 1) := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' : i ≤ p.natDegree - 1 := Nat.le_sub_one_of_lt (Finset.mem_range.mp hi)
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hgt.le hi') (norm_nonneg _)
        calc ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖ * r ^ i
            ≤ ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖ * r ^ (p.natDegree - 1) := hstep
          _ = S * r ^ (p.natDegree - 1) := by
              rw [← Finset.sum_mul, ← hS]
      have h3 : r ^ p.natDegree = r ^ (p.natDegree - 1) * r := by
        conv_lhs => rw [← Nat.sub_add_cancel hn]
        rw [pow_succ]
      have hpos : 0 < r ^ (p.natDegree - 1) := pow_pos hrpos _
      have hb : r ^ p.natDegree ≤ S * r ^ (p.natDegree - 1) := le_trans h1 h2
      have h5 : r ^ (p.natDegree - 1) * r ≤ r ^ (p.natDegree - 1) * S := by
        rw [← h3]
        exact le_trans hb (le_of_eq (mul_comm S _))
      have h4 : r ≤ S := le_of_mul_le_mul_left h5 hpos
      exact le_trans h4 (le_max_right 1 S)

end Work.WilC4aP
