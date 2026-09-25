import Mathlib

namespace Work.LT

/-- Per-generator Cauchy–Schwarz along a left-averaging walk: the mixed sum is bounded below by `-|ι|·‖f‖²`. -/
theorem sum_mul_sum_le_left {G : Type*} [Group G] [Fintype G] {ι : Type*} [Fintype ι]
    (α : ι → G) (f : G → ℝ) :
    -((Fintype.card ι : ℝ) * ∑ x, f x ^ 2) ≤ ∑ a, ∑ x, f x * f (α a * x) := by
  -- Reindexing: `x ↦ α a * x` is a bijection of `G`, so the `ℓ²` mass is unchanged.
  have hreindex : ∀ a : ι, (∑ x, f (α a * x) ^ 2) = ∑ x, f x ^ 2 := by
    intro a
    simpa using Equiv.sum_comp (Equiv.mulLeft (α a)) (fun y : G => f y ^ 2)
  -- Pointwise AM–GM: `uv ≥ -(u² + v²)/2`.
  have hterm : ∀ (a : ι) (x : G),
      -((f x ^ 2 + f (α a * x) ^ 2) / 2) ≤ f x * f (α a * x) := by
    intro a x
    nlinarith [sq_nonneg (f x + f (α a * x)), sq_nonneg (f x - f (α a * x))]
  -- Sum the pointwise bound over `x` for a fixed generator `a`.
  have hper : ∀ a : ι, -(∑ x, f x ^ 2) ≤ ∑ x, f x * f (α a * x) := by
    intro a
    have h2 : ∑ x, -((f x ^ 2 + f (α a * x) ^ 2) / 2) = -(∑ x, f x ^ 2) := by
      rw [Finset.sum_neg_distrib, ← Finset.sum_div, Finset.sum_add_distrib, hreindex a]
      ring
    have h1 : ∑ x, -((f x ^ 2 + f (α a * x) ^ 2) / 2) ≤ ∑ x, f x * f (α a * x) :=
      Finset.sum_le_sum (fun x _ => hterm a x)
    linarith
  -- Sum over the generators `a`.
  have hsum : ∑ a, (-(∑ x, f x ^ 2)) ≤ ∑ a, ∑ x, f x * f (α a * x) :=
    Finset.sum_le_sum (fun a _ => hper a)
  have hconst : ∑ _a : ι, (-(∑ x, f x ^ 2)) = -((Fintype.card ι : ℝ) * ∑ x, f x ^ 2) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hconst] at hsum
  exact hsum

end Work.LT
