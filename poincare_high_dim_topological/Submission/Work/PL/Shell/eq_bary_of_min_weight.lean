import Mathlib
import Submission.Work.PL.Shell.Basic

namespace Work.PL.Shell

set_option linter.unusedVariables false

/-- If a weight function `w` on a finite vertex set `τ` has all weights at least `w v`
(minimum attained at `v`) and satisfies `|τ| * w v = 1`, then `w` is the uniform weight
`1/|τ|`: the sum `∑ w y • y` is the centroid of `τ`. -/
theorem eq_bary_of_min_weight {N : ℕ} {τ : Finset (PL.E N)} {w : PL.E N → ℝ} {v x : PL.E N}
    (hv : v ∈ τ) (hw0 : ∀ y ∈ τ, 0 ≤ w y) (hmin : ∀ y ∈ τ, w v ≤ w y)
    (hsum : ∑ y ∈ τ, w y = 1) (hx : x = ∑ y ∈ τ, w y • y)
    (ht : (τ.card : ℝ) * w v = 1) : x = Work.PL.Shell.bary τ := by
  -- Every weight equals the minimum weight `w v`, since the excesses are nonnegative and
  -- sum to `1 - |τ| * w v = 0`.
  have hw : ∀ y ∈ τ, w y = w v := by
    intro y hy
    have hd : ∑ z ∈ τ, (w z - w v) = 0 := by
      rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, nsmul_eq_mul, ht, sub_self]
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg
        (f := fun z => w z - w v) (fun z hz => sub_nonneg.mpr (hmin z hz))).mp hd y hy
    linarith
  -- Hence `w v = 1/|τ|`.
  have hwv : w v = (τ.card : ℝ)⁻¹ := eq_inv_of_mul_eq_one_right ht
  calc x = ∑ y ∈ τ, w y • y := hx
    _ = ∑ y ∈ τ, w v • y := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [hw y hy]
    _ = w v • ∑ y ∈ τ, y := (Finset.smul_sum).symm
    _ = (τ.card : ℝ)⁻¹ • ∑ y ∈ τ, y := by rw [hwv]
    _ = Work.PL.Shell.bary τ := rfl

end Work.PL.Shell
