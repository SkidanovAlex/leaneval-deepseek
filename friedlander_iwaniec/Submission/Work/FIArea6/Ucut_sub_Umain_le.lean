import Mathlib
import Submission.Work.FIArea6.S16UDefs
import Submission.Work.FIArea6.Ucut_eq_Vd_sum

namespace Work.FIArea6

/-- The triangle-inequality split of the §16 main term: `Ucut = 2Σ_{d≤X}(φ(d)/d)Vd` and `Umain = 2Σ_{d≤X}(φ(d)/d)MainSum` give `‖Ucut‖ ≤ ‖Umain‖ + 2Σ_{d≤X}(φ(d)/d)‖Vd − MainSum‖`. -/
theorem Ucut_sub_Umain_le (Pa : Work.FITop.Params) (X : ℕ) (β : GaussianInt → ℂ) :
    ‖Work.FITop4.Ucut (Work.FITop.radN Pa) X β‖ ≤ ‖Work.FIArea6.Umain Pa X β‖
      + 2 * ∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) *
          ‖Work.FIArea6.Vd Pa d β - Work.FIArea6.MainSum Pa X d β‖ := by
  -- The difference `Ucut - Umain` rewritten by (16.1)/(16.2).
  set S : ℂ := ∑ d ∈ Finset.Icc 1 X,
    ((Nat.totient d : ℝ) / (d : ℝ) : ℂ) *
      (Work.FIArea6.Vd Pa d β - Work.FIArea6.MainSum Pa X d β) with hSdef
  have hkey : Work.FITop4.Ucut (Work.FITop.radN Pa) X β
      = Work.FIArea6.Umain Pa X β + 2 * S := by
    rw [Work.FIArea6.Ucut_eq_Vd_sum Pa X β, Work.FIArea6.Umain, hSdef]
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl; intro d _
    ring
  rw [hkey]
  -- Norm of the per-modulus weight `φ(d)/d`.
  have hcoef : ∀ d : ℕ, ‖((Nat.totient d : ℝ) / (d : ℝ) : ℂ)‖
      = (Nat.totient d : ℝ) / (d : ℝ) := by
    intro d
    rw [← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  -- Triangle inequality on the `d`-sum.
  have hS : ‖S‖ ≤ ∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) *
      ‖Work.FIArea6.Vd Pa d β - Work.FIArea6.MainSum Pa X d β‖ := by
    rw [hSdef]
    calc ‖∑ d ∈ Finset.Icc 1 X,
            ((Nat.totient d : ℝ) / (d : ℝ) : ℂ) *
              (Work.FIArea6.Vd Pa d β - Work.FIArea6.MainSum Pa X d β)‖
        ≤ ∑ d ∈ Finset.Icc 1 X,
            ‖((Nat.totient d : ℝ) / (d : ℝ) : ℂ) *
              (Work.FIArea6.Vd Pa d β - Work.FIArea6.MainSum Pa X d β)‖ :=
          norm_sum_le _ _
      _ = ∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) *
            ‖Work.FIArea6.Vd Pa d β - Work.FIArea6.MainSum Pa X d β‖ := by
          apply Finset.sum_congr rfl; intro d _
          rw [norm_mul, hcoef d]
  calc ‖Work.FIArea6.Umain Pa X β + 2 * S‖
      ≤ ‖Work.FIArea6.Umain Pa X β‖ + ‖(2 : ℂ) * S‖ := norm_add_le _ _
    _ = ‖Work.FIArea6.Umain Pa X β‖ + 2 * ‖S‖ := by
          rw [norm_mul]; norm_num
    _ ≤ ‖Work.FIArea6.Umain Pa X β‖ + 2 * (∑ d ∈ Finset.Icc 1 X,
            ((Nat.totient d : ℝ) / (d : ℝ)) *
              ‖Work.FIArea6.Vd Pa d β - Work.FIArea6.MainSum Pa X d β‖) := by
          linarith [hS]

end Work.FIArea6
