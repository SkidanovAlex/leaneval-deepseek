import Mathlib

namespace Work.EKLNonExc

/-- If `2 lam + lam⁻²` and `lam² + 2 lam⁻¹` are both integers, then `lam` is rational.

Write `A = a`, `B = b`.  From `lam² + 2 lam⁻¹ = B` we get `lam³ - B lam + 2 = 0`,
and from `2 lam + lam⁻² = A` (together with the previous) we get `A lam² - 2B lam + 3 = 0`.
Eliminating `lam²` between these two relations produces the linear relation
`(4B² - 3A - A²B) lam + (2A² - 6B) = 0`.  If the coefficient of `lam` is nonzero, `lam` is the
rational number `(6B - 2A²)/(4B² - 3A - A²B)`.  Otherwise `A² = 3B`, then also `B² = 3A`, and
`A lam² - 2B lam + 3 = 0` becomes `(A lam - B)² = 0`, so `lam = B/A`.  Either way `lam ∈ ℚ`. -/
theorem rat_of_int_traces (lam : ℝ) (hlam : 0 < lam) (a b : ℤ)
    (ha : 2 * lam + (lam ^ 2)⁻¹ = (a : ℝ)) (hb : lam ^ 2 + 2 * lam⁻¹ = (b : ℝ)) :
    ∃ q : ℚ, (q : ℝ) = lam := by
  -- `lam³ - B lam + 2 = 0`, from `lam² + 2 lam⁻¹ = B`.
  have hf : lam ^ 3 - (b:ℝ)*lam + 2 = 0 := by
    have h : lam ^ 2 + 2 * lam⁻¹ = (b:ℝ) := hb
    field_simp at h
    linarith [h]
  -- `A lam² - 2B lam + 3 = 0`, from `2 lam + lam⁻² = A` and the previous relation.
  have hg : (a:ℝ)*lam^2 - 2*(b:ℝ)*lam + 3 = 0 := by
    have hA : (a:ℝ)*lam^2 = 2*lam^3 + 1 := by
      have h : 2 * lam + (lam^2)⁻¹ = (a:ℝ) := ha
      field_simp at h
      linarith [h]
    nlinarith [hA, hf]
  -- The linear relation `C lam + D = 0`.
  have h3 : lam * (4*(b:ℝ)^2 - 3*(a:ℝ) - (a:ℝ)^2*(b:ℝ)) + (2*(a:ℝ)^2 - 6*(b:ℝ)) = 0 := by
    linear_combination ((a:ℝ)^2) * hf - ((a:ℝ)*lam + 2*(b:ℝ)) * hg
  rcases eq_or_ne (4*(b:ℝ)^2 - 3*(a:ℝ) - (a:ℝ)^2*(b:ℝ)) 0 with hC | hC
  · -- Degenerate case: the linear relation is trivial.
    have hA2 : (a:ℝ)^2 - 3*(b:ℝ) = 0 := by nlinarith [h3, hC]
    have hB2 : (b:ℝ)^2 - 3*(a:ℝ) = 0 := by linear_combination hC + (b:ℝ)*hA2
    have hApos : 0 < (a:ℝ) := by rw [← ha]; positivity
    have hsq : ((a:ℝ)*lam - (b:ℝ))^2 = 0 := by
      linear_combination (a:ℝ)*hg + hB2
    have hAxB : (a:ℝ)*lam - (b:ℝ) = 0 := sq_eq_zero_iff.mp hsq
    have hAne : (a:ℝ) ≠ 0 := ne_of_gt hApos
    have hxBA : lam = (b:ℝ)/(a:ℝ) := by rw [eq_div_iff hAne]; linarith [hAxB]
    refine ⟨(b:ℚ)/(a:ℚ), ?_⟩
    push_cast
    exact hxBA.symm
  · -- Nondegenerate case: solve the linear relation for `lam`.
    have hCne : (4*(b:ℝ)^2 - 3*(a:ℝ) - (a:ℝ)^2*(b:ℝ)) ≠ 0 := hC
    refine ⟨((6*b - 2*a^2 : ℤ) : ℚ) / ((4*b^2 - 3*a - a^2*b : ℤ) : ℚ), ?_⟩
    push_cast
    rw [div_eq_iff hCne]
    linarith [h3]

end Work.EKLNonExc
