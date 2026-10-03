import Mathlib
import Submission.Work.Analysis.IWMultiplier.Defs

namespace Work.KMTAreas.A5

/-- Weighted-geometric-mean bookkeeping for the `A5` gain/loss split.

If both `Cg` and `M₁` are bounded by the same quantity `A * ⟨L⟩²` (with `A ≥ 1`, so that this
bound is non-zero), then for `0 < θ < 1` the interpolation
`(Cg * w)^{1-θ} * M₁^θ` is bounded by `A * w^{1-θ} * ⟨L⟩²`.  The point is that the two powers
`(·)^{1-θ}` and `(·)^θ` are monotone and their exponents add up to `1`, so the two copies of the
common bound `A * ⟨L⟩²` recombine into a single copy. -/
theorem gainLoss_combine_sq {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {L : ℕ} {A : NNReal} (hA : 1 ≤ A)
    {Cg M₁ w : NNReal}
    (hCg : Cg ≤ A * Work.Analysis.IWMultiplier.angleBracket L ^ 2)
    (hM₁ : M₁ ≤ A * Work.Analysis.IWMultiplier.angleBracket L ^ 2) :
    ((Cg * w : NNReal) : ENNReal) ^ (1 - θ) * (M₁ : ENNReal) ^ θ
      ≤ (A : ENNReal) * (w : ENNReal) ^ (1 - θ)
          * ((Work.Analysis.IWMultiplier.angleBracket L : NNReal) : ENNReal) ^ 2 := by
  have hθ0le : (0:ℝ) ≤ 1 - θ := by linarith
  have hθle : (0:ℝ) ≤ θ := le_of_lt hθ0
  -- The common bound `K = A * ⟨L⟩²`.
  obtain ⟨K, hK⟩ : ∃ K : ENNReal,
      K = (A : ENNReal) * ((Work.Analysis.IWMultiplier.angleBracket L : NNReal) : ENNReal) ^ 2 :=
    ⟨_, rfl⟩
  have hK0 : K ≠ 0 := by
    rw [hK]
    refine mul_ne_zero ?_ (pow_ne_zero 2 ?_)
    · exact ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hA))
    · exact ENNReal.coe_ne_zero.mpr (ne_of_gt (Work.Analysis.IWMultiplier.angleBracket_pos L))
  have hKtop : K ≠ ⊤ := by
    rw [hK]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have hCgK : (Cg : ENNReal) ≤ K := by
    rw [hK]
    exact_mod_cast hCg
  have hM₁K : (M₁ : ENNReal) ≤ K := by
    rw [hK]
    exact_mod_cast hM₁
  have hu : ((Cg * w : NNReal) : ENNReal) ≤ K * (w : ENNReal) := by
    have h1 := mul_le_mul_left hCgK (w : ENNReal)
    rwa [← ENNReal.coe_mul] at h1
  calc ((Cg * w : NNReal) : ENNReal) ^ (1 - θ) * (M₁ : ENNReal) ^ θ
      ≤ (K * (w : ENNReal)) ^ (1 - θ) * K ^ θ :=
        mul_le_mul' (ENNReal.rpow_le_rpow hu hθ0le) (ENNReal.rpow_le_rpow hM₁K hθle)
    _ = (A : ENNReal) * (w : ENNReal) ^ (1 - θ)
          * ((Work.Analysis.IWMultiplier.angleBracket L : NNReal) : ENNReal) ^ 2 := by
        calc (K * (w : ENNReal)) ^ (1 - θ) * K ^ θ
            = (K ^ (1 - θ) * (w : ENNReal) ^ (1 - θ)) * K ^ θ := by
              rw [ENNReal.mul_rpow_of_nonneg _ _ hθ0le]
          _ = (K ^ (1 - θ) * K ^ θ) * (w : ENNReal) ^ (1 - θ) := by ring
          _ = K ^ ((1 - θ) + θ) * (w : ENNReal) ^ (1 - θ) := by
              rw [← ENNReal.rpow_add (x := K) (1 - θ) θ hK0 hKtop]
          _ = K * (w : ENNReal) ^ (1 - θ) := by
              rw [show (1 - θ) + θ = (1:ℝ) by ring, ENNReal.rpow_one]
          _ = (A : ENNReal) * (w : ENNReal) ^ (1 - θ)
                * ((Work.Analysis.IWMultiplier.angleBracket L : NNReal) : ENNReal) ^ 2 := by
              rw [hK]; ring

end Work.KMTAreas.A5
