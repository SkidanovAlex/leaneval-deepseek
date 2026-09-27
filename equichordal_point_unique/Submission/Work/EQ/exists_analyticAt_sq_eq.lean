import Mathlib
import Submission.Work.EQ.SqrtNearOne

namespace Work.EQ

/-- **Local analytic square root.**  A nonvanishing function `w` analytic at `u₀` admits an
analytic square root: there is `ρ` analytic at `u₀`, nonzero at `u₀`, with `ρ u ^ 2 = w u`
for every `u`.  Concretely one may take `ρ u = sqHalf (w u₀ - 1) * sqHalf (w u / w u₀ - 1)`,
which is analytic at `u₀` because `sqHalf` is analytic near `0` (see `SqrtNearOne`). -/
theorem exists_analyticAt_sq_eq {w : ℂ → ℂ} {u₀ : ℂ} (hw : AnalyticAt ℂ w u₀) (h0 : w u₀ ≠ 0) :
    ∃ ρ : ℂ → ℂ, AnalyticAt ℂ ρ u₀ ∧ ρ u₀ ≠ 0 ∧ ∀ u, ρ u ^ 2 = w u := by
  refine ⟨fun u => sqHalf (w u₀ - 1) * sqHalf (w u / w u₀ - 1), ?_, ?_, ?_⟩
  · -- Analyticity at `u₀`: compose the inner analytic function `u ↦ w u / w u₀ - 1`
    -- (which vanishes at `u₀`) with `sqHalf`, analytic at `0`.
    have hinner : AnalyticAt ℂ (fun u => w u / w u₀ - 1) u₀ :=
      (hw.div_const (c := w u₀)).sub analyticAt_const
    have hsq0 : AnalyticAt ℂ sqHalf (0 : ℂ) := analyticAt_sqHalf (z := 0) (by norm_num)
    have hval : w u₀ / w u₀ - 1 = 0 := by rw [div_self h0, sub_self]
    have hsq : AnalyticAt ℂ sqHalf ((fun u => w u / w u₀ - 1) u₀) := by
      change AnalyticAt ℂ sqHalf (w u₀ / w u₀ - 1)
      rw [hval]; exact hsq0
    have hcomp : AnalyticAt ℂ (fun u => sqHalf (w u / w u₀ - 1)) u₀ :=
      AnalyticAt.comp (f := fun u => w u / w u₀ - 1) (x := u₀) hsq hinner
    exact analyticAt_const.mul hcomp
  · -- Nonvanishing at `u₀`.
    show sqHalf (w u₀ - 1) * sqHalf (w u₀ / w u₀ - 1) ≠ 0
    have h1 : sqHalf (w u₀ - 1) ≠ 0 := by
      intro h
      apply h0
      calc w u₀ = 1 + (w u₀ - 1) := by ring
        _ = sqHalf (w u₀ - 1) ^ 2 := (sqHalf_sq (w u₀ - 1)).symm
        _ = 0 := by rw [h]; ring
    have h2 : sqHalf (w u₀ / w u₀ - 1) = 1 := by
      have hv : w u₀ / w u₀ - 1 = 0 := by rw [div_self h0, sub_self]
      rw [hv, sqHalf_zero]
    rw [h2, mul_one]; exact h1
  · -- The square identity, pointwise.
    intro u
    rw [mul_pow, sqHalf_sq, sqHalf_sq]
    field_simp
    ring

end Work.EQ
