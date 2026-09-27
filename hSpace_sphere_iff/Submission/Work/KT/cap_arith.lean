import Mathlib
import Submission.Work.KT.Defs

namespace Work.KT

/-- **Arithmetic core** of the contraction of the cap `{tgtHeight ≥ -1/2}` of `S^{2m}`: if `(r, p)` is a point of the unit circle (`r^2 + p^2 = 1`) with `p ≥ -1/2`, and `α, β ≥ 0` satisfy `α + β = 1`, then the vector `(β r, α + β p)` is nonzero and its normalisation has second coordinate `≥ -1/2`, i.e. `0 ≤ 2 (α + β p) + ‖(β r, α + β p)‖`. -/
lemma cap_arith {α β p r : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1)
    (hrp : r ^ 2 + p ^ 2 = 1) (hp : -(1 / 2) ≤ p) :
    0 < (β * r) ^ 2 + (α + β * p) ^ 2 ∧
      0 ≤ 2 * (α + β * p) + Real.sqrt ((β * r) ^ 2 + (α + β * p) ^ 2) := by
  -- Key identity: the squared norm equals `α² + β² + 2αβp`.
  have hkey : (β * r) ^ 2 + (α + β * p) ^ 2 = α ^ 2 + β ^ 2 + 2 * α * β * p := by
    nlinarith [hrp]
  -- Non-vanishing.
  have hpos : 0 < (β * r) ^ 2 + (α + β * p) ^ 2 := by
    rw [hkey]
    have hab : 0 ≤ α * β := mul_nonneg hα hβ
    have hprod : 0 ≤ 2 * (α * β) * (p + 1/2) := by
      apply mul_nonneg
      · exact mul_nonneg (by norm_num) hab
      · linarith
    nlinarith [hαβ, sq_nonneg (α - β), sq_nonneg α, sq_nonneg β, hprod]
  refine ⟨hpos, ?_⟩
  rcases le_or_gt 0 (α + β * p) with hs | hs
  · -- Second coordinate already nonnegative.
    have h1 : 0 ≤ 2 * (α + β * p) := by linarith
    have h2 : 0 ≤ Real.sqrt ((β * r) ^ 2 + (α + β * p) ^ 2) := Real.sqrt_nonneg _
    linarith
  · -- Second coordinate negative: show `‖·‖² ≥ 4 (α+βp)²`.
    have hp_neg : p < 0 := by
      by_contra h
      rw [not_lt] at h
      nlinarith [hs, hα, hβ, h]
    have hp2 : p ^ 2 ≤ 1/4 := by nlinarith [hp, hp_neg]
    have ht2 : 3 * β ^ 2 / 4 ≤ (β * r) ^ 2 := by
      have hr2 : r ^ 2 = 1 - p ^ 2 := by nlinarith [hrp]
      rw [mul_pow, hr2]
      nlinarith [hp2, sq_nonneg β]
    have hsle : -(α + β * p) ≤ β / 2 := by
      have hple : -p ≤ 1/2 := by linarith [hp]
      have h1 : β * (-p) ≤ β * (1/2) := mul_le_mul_of_nonneg_left hple hβ
      nlinarith [h1, hα]
    have hs2 : (α + β * p) ^ 2 ≤ β ^ 2 / 4 := by
      have hle2 : -(β/2) ≤ -(α + β * p) := by linarith [hs, hβ]
      have h := sq_le_sq' hle2 hsle
      calc (α + β*p)^2 = (-(α+β*p))^2 := by ring
        _ ≤ (β/2)^2 := h
        _ = β^2/4 := by ring
    have hts : 3 * (α + β * p) ^ 2 ≤ (β * r) ^ 2 := by
      have : 3 * (α + β * p) ^ 2 ≤ 3 * (β ^ 2 / 4) := by linarith [hs2]
      linarith [ht2, this]
    have hN : 4 * (α + β * p) ^ 2 ≤ (β * r) ^ 2 + (α + β * p) ^ 2 := by linarith [hts]
    have hsqrt := Real.sqrt_le_sqrt hN
    have hsqrt4 : Real.sqrt (4 * (α + β * p) ^ 2) = -(2 * (α + β * p)) := by
      have hsq : (4 : ℝ) * (α + β * p) ^ 2 = (2 * (α + β * p)) ^ 2 := by ring
      rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonpos (by linarith [hs])]
    linarith [hsqrt, hsqrt4]

end Work.KT
