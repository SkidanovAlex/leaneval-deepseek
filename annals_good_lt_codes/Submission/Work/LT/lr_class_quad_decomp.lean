import Mathlib

namespace Work.LT

/-- Expansion of a finite sum of a product of two binomials into the four pairwise terms:
`∑ (f + a)(g + b) = ∑ f·g + b·∑ f + a·∑ g + card·(a·b)`. -/
theorem sum_add_mul_add {ι : Type*} [Fintype ι] (f g : ι → ℝ) (a b : ℝ) :
    ∑ p, (f p + a) * (g p + b)
      = ∑ p, f p * g p + b * (∑ p, f p) + a * (∑ p, g p)
          + (Fintype.card ι : ℝ) * (a * b) := by
  have h : ∀ p, (f p + a) * (g p + b) = f p * g p + b * f p + a * g p + a * b := by
    intro p; ring
  simp only [h]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Quadratic decomposition of a linear, sum-preserving operator `op` fixing the constants:
writing `s = t + q` with the mean-shifted `t = s - q`, one has
`∑ s·op s = q·∑ s + ∑ t·op t`.  The hypotheses are exactly additivity, homogeneity,
`op 1 = 1` and preservation of the total sum, together with the mean constraint
`q·card = ∑ s`. -/
theorem lr_class_quad_decomp {ι : Type*} [Fintype ι]
    (op : (ι → ℝ) → (ι → ℝ))
    (hadd : ∀ x y, op (x + y) = op x + op y)
    (hsmul : ∀ (a : ℝ) x, op (a • x) = a • op x)
    (hone : op (fun _ => (1 : ℝ)) = fun _ => (1 : ℝ))
    (hsum : ∀ x, ∑ p, op x p = ∑ p, x p)
    (s : ι → ℝ) (q : ℝ) (hq : q * (Fintype.card ι : ℝ) = ∑ p, s p) :
    ∑ p, s p * op s p = q * (∑ p, s p) + ∑ p, (s p - q) * op (fun p => s p - q) p := by
  set t : ι → ℝ := fun p => s p - q with ht
  -- `s = t + q` pointwise, hence `op s = op t + q` pointwise (linearity + `op 1 = 1`).
  have hs_apply : ∀ p, s p = t p + q := by intro p; rw [ht]; ring
  have hop : op s = op t + fun _ => q := by
    have hs_eq : s = t + fun _ => q := by funext p; rw [hs_apply p]; simp
    have hq_eq : (fun _ : ι => q) = q • (fun _ : ι => (1 : ℝ)) := by funext p; simp
    rw [hs_eq, hq_eq, hadd, hsmul, hone]
  have hop_apply : ∀ p, op s p = op t p + q := by intro p; rw [hop]; simp
  -- `∑ s = card·q`, hence `∑ t = 0` and, by sum preservation, `∑ op t = 0`.
  have hsum_s : ∑ p, s p = (Fintype.card ι : ℝ) * q := by rw [← hq]; ring
  have h1 : ∑ p, s p = ∑ p, t p + (Fintype.card ι : ℝ) * q := by
    calc ∑ p, s p = ∑ p, (t p + q) := Finset.sum_congr rfl (fun p _ => hs_apply p)
      _ = ∑ p, t p + (Fintype.card ι : ℝ) * q := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsum_t : ∑ p, t p = 0 := by linarith
  have hsum_op_t : ∑ p, op t p = 0 := by rw [hsum t]; exact hsum_t
  -- Both sides equal `∑ t·op t + card·q²`.
  have hL : ∑ p, s p * op s p = ∑ p, t p * op t p + (Fintype.card ι : ℝ) * (q * q) := by
    have hc : ∑ p, s p * op s p = ∑ p, (t p + q) * (op t p + q) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [hs_apply p, hop_apply p]
    rw [hc, sum_add_mul_add, hsum_t, hsum_op_t]
    ring
  have hR : q * (∑ p, s p) + ∑ p, t p * op t p
      = ∑ p, t p * op t p + (Fintype.card ι : ℝ) * (q * q) := by
    rw [hsum_s]; ring
  have hgoal : ∑ p, (s p - q) * op (fun p => s p - q) p = ∑ p, t p * op t p := by
    apply Finset.sum_congr rfl
    intro p _
    rw [ht]
  rw [hgoal, hL, hR]

end Work.LT
