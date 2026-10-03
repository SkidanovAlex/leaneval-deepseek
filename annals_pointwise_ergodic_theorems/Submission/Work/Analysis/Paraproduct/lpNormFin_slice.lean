import Mathlib
import Submission.Work.Analysis.Paraproduct.TensorNorm

open scoped BigOperators

namespace Work.Analysis.Paraproduct

/-- **Slicing identity for the normalised `L^p` norm.**  For a function `f` on a product of two
finite types, the `L^p` norm of the function `x ↦ ‖f (x, ·)‖_{L^p}` of the norms of the `f`-slices
equals `‖f‖_{L^p}`.  This is the Fubini/`ttensor-lin` computation of the paper in the
finite-dimensional (counting-measure) setting: it is the identity underlying the normalisation of
the tensor norms, and reduces to `card (α × α') = card α * card α'` and `(x ^ (1/p)) ^ p = x` for
`x ≥ 0`. -/
theorem lpNormFin_slice {α α' : Type*} [Fintype α] [Fintype α'] {p : ℝ} (hp : 0 < p)
    (f : α × α' → ℂ) :
    lpNormFin α p (fun x => ((lpNormFin α' p (fun y => f (x, y)) : ℝ) : ℂ))
      = lpNormFin (α × α') p f := by
  -- The `p`-th power of the norm of a slice is the corresponding `p`-sum.
  have key : ∀ x : α, ‖((lpNormFin α' p (fun y => f (x, y)) : ℝ) : ℂ)‖ ^ p
      = (Fintype.card α' : ℝ)⁻¹ * ∑ y : α', ‖f (x, y)‖ ^ p := by
    intro x
    have hn : 0 ≤ lpNormFin α' p (fun y => f (x, y)) := lpNormFin_nonneg _ _
    have hbase : 0 ≤ (Fintype.card α' : ℝ)⁻¹ * ∑ y : α', ‖f (x, y)‖ ^ p :=
      mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (Finset.sum_nonneg (fun y _ => Real.rpow_nonneg (norm_nonneg _) _))
    rw [Complex.norm_real, Real.norm_of_nonneg hn]
    show (((Fintype.card α' : ℝ)⁻¹ * ∑ y : α', ‖f (x, y)‖ ^ p) ^ (1 / p)) ^ p
        = (Fintype.card α' : ℝ)⁻¹ * ∑ y : α', ‖f (x, y)‖ ^ p
    rw [← Real.rpow_mul hbase (1 / p) p, one_div_mul_cancel hp.ne', Real.rpow_one]
  -- Summing the slices over the first factor.
  have hsum : (∑ x : α, ‖((lpNormFin α' p (fun y => f (x, y)) : ℝ) : ℂ)‖ ^ p)
      = (Fintype.card α' : ℝ)⁻¹ * ∑ z : α × α', ‖f z‖ ^ p := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => key x)
  show (((Fintype.card α : ℝ)⁻¹
      * ∑ x : α, ‖((lpNormFin α' p (fun y => f (x, y)) : ℝ) : ℂ)‖ ^ p) ^ (1 / p))
      = lpNormFin (α × α') p f
  rw [hsum, lpNormFin]
  have hcard : (Fintype.card (α × α') : ℝ)
      = (Fintype.card α : ℝ) * (Fintype.card α' : ℝ) := by
    rw [Fintype.card_prod, Nat.cast_mul]
  rw [hcard, mul_inv, mul_assoc]

end Work.Analysis.Paraproduct
