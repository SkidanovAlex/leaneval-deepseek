/-
# `Work.FTS.PhiStar.Honesty.exists_bound_eFam_mul_cos`

The angular Dirichlet eigenfunctions of `Lzero` are `eFam m θ = cos θ · gC (2m+1) (sin θ)`
(`Gegenbauer/Defs.lean`), where `gC n` is the Gegenbauer polynomial `C_n^{(3/2)}` built by its
classical three-term recurrence.  Hence

  `eFam m θ · cos θ = cos²θ · gC (2m+1) (sin θ)`,

and for `θ ∈ Iθ = [0, π/2]` we have `0 ≤ cos²θ ≤ 1` while `sin θ ∈ [-1,1]`.  Since `gC n` is a
continuous (indeed `C³`, `Gegenbauer.gC_ode.contDiff_gC`) function of one variable, it is bounded
on the compact interval `[-1,1]`; that bound, times `1`, bounds the product.  This is the crude
uniform bound on `Iθ` needed to control the angular modes.

(Contrast `Series.exists_eFam_bounds`, which gives the sharper `|eFam m θ · cos θ| ≤ A sin θ cos²θ`
via the mean value theorem and the vanishing of the odd polynomial at `0`; here compactness of
`[-1,1]` alone suffices.)
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

/-- A continuous function on the compact interval `[-1,1]` is bounded there in absolute value. -/
private lemma exists_abs_le_on_Icc {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (-1 : ℝ) 1)) :
    ∃ C : ℝ, ∀ x ∈ Set.Icc (-1 : ℝ) 1, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := f) hf
  exact ⟨C, fun x hx => by simpa [Real.norm_eq_abs] using hC x hx⟩

/-- The Gegenbauer polynomial `gC (2m+1)` is bounded in absolute value on `[-1,1]`. -/
private lemma exists_abs_gC_le (m : ℕ) : ∃ C : ℝ,
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, |Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) x| ≤ C :=
  exists_abs_le_on_Icc
    (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).continuousOn)

theorem exists_bound_eFam_mul_cos (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ| ≤ C := by
  obtain ⟨M, hM⟩ := exists_abs_gC_le m
  refine ⟨max M 0, le_max_right _ _, fun θ hθ => ?_⟩
  have hsin : Real.sin θ ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have hb : |Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)| ≤ M := hM _ hsin
  have hcos_sq : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (Real.cos θ), Real.cos_le_one θ, Real.neg_one_le_cos θ]
  calc |Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ|
      = Real.cos θ ^ 2 * |Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)| := by
        rw [Work.FTS.PhiStar.Gegenbauer.eFam]
        rw [show Real.cos θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)
              * Real.cos θ
            = Real.cos θ ^ 2 * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)
            from by ring]
        rw [abs_mul, abs_of_nonneg (sq_nonneg (Real.cos θ))]
    _ ≤ 1 * M := mul_le_mul hcos_sq hb (abs_nonneg _) (by norm_num)
    _ ≤ max M 0 := by
        rw [one_mul]
        exact le_max_left _ _

end Work.FTS.PhiStar.Honesty
