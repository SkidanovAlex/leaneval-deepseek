import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic

namespace Commons.Analysis.InnerProduct

/-- **Decomposition of a point relative to a line**: for two distinct points
`p₁ ≠ p₂` and any point `w` of a real inner product space, the vector from
the base midpoint `m = (1/2) • (p₁ + p₂)` to `w` decomposes as
`w − m = c • u + n` with `u = p₂ − p₁` and `n ⊥ u`, and `‖n‖` is exactly the
perpendicular distance from `w` to the line through `p₁, p₂` (i.e.
`‖n‖ ≤ ‖w − (m + r • u)‖` for every real `r`).

This supplies the apex data `(c, n, ‖n‖)` used by
`Submission.Commons.Analysis.InnerProduct.A1_of_decomp` in the Figure-2
construction of Lemma G. -/
theorem exists_perp_decomp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p₁ p₂ w : E) (hne : p₂ ≠ p₁) :
    ∃ c : ℝ, ∃ n : E, inner ℝ n (p₂ - p₁) = 0 ∧
      w - (1 / 2 : ℝ) • (p₁ + p₂) = c • (p₂ - p₁) + n ∧
      ∀ r : ℝ, ‖n‖ ≤ ‖w - ((1 / 2 : ℝ) • (p₁ + p₂) + r • (p₂ - p₁))‖ := by
  set m : E := (1 / 2 : ℝ) • (p₁ + p₂) with hm
  set u : E := p₂ - p₁ with hu
  have hu_ne : u ≠ 0 := by
    rw [hu, sub_ne_zero]
    exact hne
  have hnormu_ne : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu_ne
  have hnormu2_ne : ‖u‖ ^ 2 ≠ 0 := pow_ne_zero 2 hnormu_ne
  have huu : inner ℝ u u = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u
  refine ⟨inner ℝ (w - m) u / ‖u‖ ^ 2,
    (w - m) - (inner ℝ (w - m) u / ‖u‖ ^ 2) • u, ?_, ?_, ?_⟩
  · rw [inner_sub_left, real_inner_smul_left, huu, div_mul_cancel₀ _ hnormu2_ne, sub_self]
  · module
  · intro r
    set c : ℝ := inner ℝ (w - m) u / ‖u‖ ^ 2 with hc
    set n : E := (w - m) - c • u with hn
    have hperp : inner ℝ n u = 0 := by
      rw [hn, inner_sub_left, real_inner_smul_left, huu, hc,
        div_mul_cancel₀ _ hnormu2_ne, sub_self]
    have hnu : inner ℝ n ((c - r) • u) = 0 := by
      rw [real_inner_smul_right, hperp, mul_zero]
    have heq : w - (m + r • u) = n + (c - r) • u := by
      rw [hn]
      module
    rw [heq]
    rw [← Real.sqrt_sq (norm_nonneg n), ← Real.sqrt_sq (norm_nonneg (n + (c - r) • u))]
    apply Real.sqrt_le_sqrt
    rw [pow_two, pow_two, norm_add_sq_eq_norm_sq_add_norm_sq_real hnu]
    nlinarith [mul_self_nonneg ‖(c - r) • u‖]

end Commons.Analysis.InnerProduct