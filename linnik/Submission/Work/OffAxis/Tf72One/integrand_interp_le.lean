import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.G72Base
import Submission.Work.OffAxis.Tf72One.abs_interp_error_le

namespace Work.OffAxis.Tf72One

/-- **Pointwise interpolation in the `t`-variable of the Lemma 7.2 integrand.**

For fixed `s` and `y ∈ [0,2]` the function `t ↦ (e^{sy}-2)·cos(t y)·g72 y` has second
`t`-derivative `-y²·(e^{sy}-2)·cos(t y)·g72 y`, bounded in absolute value by
`y²·|e^{sy}-2|·g72 y`.  The sharp two-point interpolation bound `abs_interp_error_le` therefore
gives the claim. -/
theorem integrand_interp_le (s t a b y : ℝ) (hab : a < b) (hta : a ≤ t) (htb : t ≤ b)
    (hy : y ∈ Set.Icc (0 : ℝ) 2) :
    (Real.exp (s * y) - 2) * Real.cos (t * y) * Work.ZeroFreeTables.g72 y ≤
      (b - t) / (b - a) * ((Real.exp (s * y) - 2) * Real.cos (a * y) * Work.ZeroFreeTables.g72 y)
        + (t - a) / (b - a) * ((Real.exp (s * y) - 2) * Real.cos (b * y) * Work.ZeroFreeTables.g72 y)
        + (b - a) ^ 2 / 8 * (y ^ 2 * |Real.exp (s * y) - 2| * Work.ZeroFreeTables.g72 y) := by
  have hg : 0 ≤ Work.ZeroFreeTables.g72 y := Work.ZeroFreeTables.OffAxis.g72_nonneg hy.1 hy.2
  have hf : ContDiffOn ℝ 2 (fun x : ℝ => Real.cos (x * y)) (Set.Icc a b) := by fun_prop
  have hM : ∀ x ∈ Set.Ioo a b, |iteratedDeriv 2 (fun x : ℝ => Real.cos (x * y)) x| ≤ y ^ 2 := by
    intro x _
    have h1 : iteratedDeriv 2 (fun x : ℝ => Real.cos (x * y)) x = -(y ^ 2) * Real.cos (x * y) := by
      rw [show (fun x : ℝ => Real.cos (x * y)) = (fun x : ℝ => Real.cos (y * x)) by
        funext z; ring_nf]
      rw [iteratedDeriv_comp_const_mul Real.contDiff_cos y]
      have hev : iteratedDeriv 2 Real.cos (y * x) = -Real.cos (y * x) := by
        have h := Real.iteratedDeriv_even_cos 1
        simpa using congrFun h (y * x)
      simp only [hev]
      ring_nf
    rw [h1, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg y)]
    nlinarith [Real.abs_cos_le_one (x * y)]
  have hmain := abs_interp_error_le (fun x : ℝ => Real.cos (x * y)) a b t (y ^ 2)
    hab ⟨hta, htb⟩ hf hM
  have hb1 : (Real.exp (s*y) - 2) * Work.ZeroFreeTables.g72 y * (Real.cos (t*y)
        - ((b - t) / (b - a) * Real.cos (a * y) + (t - a) / (b - a) * Real.cos (b * y)))
      ≤ ((b - a)^2 / 8 * (y^2)) * (|Real.exp (s*y) - 2| * Work.ZeroFreeTables.g72 y) := by
    calc (Real.exp (s*y) - 2) * Work.ZeroFreeTables.g72 y * (Real.cos (t*y)
          - ((b - t) / (b - a) * Real.cos (a * y) + (t - a) / (b - a) * Real.cos (b * y)))
        ≤ |(Real.exp (s*y) - 2) * Work.ZeroFreeTables.g72 y * (Real.cos (t*y)
          - ((b - t) / (b - a) * Real.cos (a * y) + (t - a) / (b - a) * Real.cos (b * y)))| :=
          le_abs_self _
      _ = |(Real.exp (s*y) - 2) * Work.ZeroFreeTables.g72 y| * |Real.cos (t*y)
          - ((b - t) / (b - a) * Real.cos (a * y) + (t - a) / (b - a) * Real.cos (b * y))| :=
          abs_mul _ _
      _ = (|Real.exp (s*y) - 2| * Work.ZeroFreeTables.g72 y) * |Real.cos (t*y)
          - ((b - t) / (b - a) * Real.cos (a * y) + (t - a) / (b - a) * Real.cos (b * y))| := by
          rw [abs_mul, abs_of_nonneg hg]
      _ ≤ (|Real.exp (s*y) - 2| * Work.ZeroFreeTables.g72 y) * ((b - a)^2 / 8 * y^2) :=
          mul_le_mul_of_nonneg_left hmain (mul_nonneg (abs_nonneg _) hg)
      _ = ((b - a)^2 / 8 * (y^2)) * (|Real.exp (s*y) - 2| * Work.ZeroFreeTables.g72 y) := by ring
  have hb2 : (Real.exp (s*y) - 2) * Work.ZeroFreeTables.g72 y
        * ((b - t) / (b - a) * Real.cos (a * y) + (t - a) / (b - a) * Real.cos (b * y))
      = (b - t) / (b - a) * ((Real.exp (s * y) - 2) * Real.cos (a * y) * Work.ZeroFreeTables.g72 y)
        + (t - a) / (b - a) * ((Real.exp (s * y) - 2) * Real.cos (b * y) * Work.ZeroFreeTables.g72 y) :=
      by ring
  have hb3 : ((b - a)^2 / 8 * (y^2)) * (|Real.exp (s*y) - 2| * Work.ZeroFreeTables.g72 y)
      = (b - a) ^ 2 / 8 * (y ^ 2 * |Real.exp (s * y) - 2| * Work.ZeroFreeTables.g72 y) := by ring
  have h1r : (Real.exp (s*y) - 2) * Real.cos (t*y) * Work.ZeroFreeTables.g72 y
      = (Real.exp (s*y) - 2) * Work.ZeroFreeTables.g72 y * Real.cos (t*y) := by ring
  rw [h1r]
  have h2r : (Real.exp (s*y) - 2) * Work.ZeroFreeTables.g72 y * Real.cos (t*y)
      = (Real.exp (s*y) - 2) * Work.ZeroFreeTables.g72 y * (Real.cos (t*y)
          - ((b - t) / (b - a) * Real.cos (a * y) + (t - a) / (b - a) * Real.cos (b * y)))
        + (Real.exp (s*y) - 2) * Work.ZeroFreeTables.g72 y
          * ((b - t) / (b - a) * Real.cos (a * y) + (t - a) / (b - a) * Real.cos (b * y)) := by ring
  rw [h2r]
  linarith [hb1, hb2, hb3]

end Work.OffAxis.Tf72One
