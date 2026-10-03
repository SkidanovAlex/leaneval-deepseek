import Mathlib
import Submission.Work.KMTContract.Defs

namespace Work.KMTPlan.A6

open Work.KMTContract

/-- **The KMT cutoff `η = kmtEta` is Lipschitz** (with a strictly positive constant).

`η` is the smooth bump `kmtBump` (a `ContDiffBump 0` with `rIn = 1/2`, `rOut = 1`) cast to `ℂ`.
The real bump is `C¹` and compactly supported (supported in `[-1,1]`, by
`ContDiffBump.tsupport_eq`), so Mathlib's
`ContDiff.lipschitzWith_of_hasCompactSupport` furnishes a constant `C ≥ 0` with
`dist (kmtBump x) (kmtBump y) ≤ C * dist x y` for all real `x y`.  Rewriting the two real `dist`s as
absolute values and passing the `ℝ`-valued bound to the complex-valued function through the
(linear isometric) cast `ℝ ↪ ℂ` gives the bound with constant `max C 1 > 0`. -/
theorem kmtEta_lipschitz :
    ∃ L : ℝ, 0 < L ∧ ∀ x y : ℝ,
      ‖Work.KMTContract.kmtEta x - Work.KMTContract.kmtEta y‖ ≤ L * |x - y| := by
  -- `kmtBump` is `C¹` with compact support.
  have hcsb : HasCompactSupport (Work.KMTContract.kmtBump : ℝ → ℝ) :=
    ContDiffBump.hasCompactSupport Work.KMTContract.kmtBump
  have hcdb : ContDiff ℝ (1 : WithTop ℕ∞) (Work.KMTContract.kmtBump : ℝ → ℝ) :=
    ContDiffBump.contDiff Work.KMTContract.kmtBump (n := 1)
  -- hence `kmtBump` is Lipschitz with some constant `C`.
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcsb hcdb (by simp)
  refine ⟨max (C : ℝ) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x y => ?_⟩
  -- the mean value theorem form of the Lipschitz bound, written with absolute values
  have hxy : |Work.KMTContract.kmtBump x - Work.KMTContract.kmtBump y| ≤ (C : ℝ) * |x - y| := by
    have h := hC.dist_le_mul x y
    simpa only [Real.dist_eq] using h
  -- `kmtEta` is the cast of `kmtBump` to `ℂ`, and the cast is isometric
  have hnorm : ‖Work.KMTContract.kmtEta x - Work.KMTContract.kmtEta y‖
      = |Work.KMTContract.kmtBump x - Work.KMTContract.kmtBump y| := by
    simp only [Work.KMTContract.kmtEta]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  calc ‖Work.KMTContract.kmtEta x - Work.KMTContract.kmtEta y‖
      = |Work.KMTContract.kmtBump x - Work.KMTContract.kmtBump y| := hnorm
    _ ≤ (C : ℝ) * |x - y| := hxy
    _ ≤ max (C : ℝ) 1 * |x - y| :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)

end Work.KMTPlan.A6
