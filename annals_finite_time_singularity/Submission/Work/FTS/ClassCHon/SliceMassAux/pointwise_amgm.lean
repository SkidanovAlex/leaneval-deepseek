import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.SliceMassAux

/-- Pointwise weighted AM–GM: for `s > 0` and `θ ∈ Iθ`,

  `2 |ab| sin(2θ)^{-η} ≤ a² w(s)² sin(2θ)^{-η} + (s b)² w(s)² sin(2θ)^{-η}`,

i.e. `2 |a| |s b| ≤ a² + (s b)²` (plain AM–GM) multiplied by `w(s)² sin(2θ)^{-η}`,
using the elementary bound `1 ≤ s · w(s)² = (1+s)⁴/s³` valid for `s > 0`. -/
theorem pointwise_amgm {s θ a b : ℝ} (hs : 0 < s) (hθ : θ ∈ Work.Spaces.Iθ) :
    2 * |a * b| * Work.FTS.EllipticEst.sEta θ
      ≤ a ^ 2 * (Work.Spaces.w s) ^ 2 * Work.FTS.EllipticEst.sEta θ
        + (s * b) ^ 2 * (Work.Spaces.w s) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  -- nonnegativity of the angular weight on `Iθ`
  have hη : 0 ≤ Work.FTS.EllipticEst.sEta θ := by
    rw [Work.FTS.EllipticEst.sEta]
    apply Real.rpow_nonneg
    have h2θ : (2 * θ) ∈ Set.Icc 0 Real.pi := by
      constructor
      · have := hθ.1; linarith
      · have := hθ.2; linarith
    exact Real.sin_nonneg_of_mem_Icc h2θ
  -- `1 ≤ s · w(s)² = (1+s)⁴/s³`
  have hsw : 1 ≤ s * (Work.Spaces.w s) ^ 2 := by
    have hw : s * (Work.Spaces.w s) ^ 2 = (1 + s) ^ 4 / s ^ 3 := by
      rw [Work.Spaces.w]
      field_simp
    rw [hw]
    rw [one_le_div (by positivity)]
    nlinarith [sq_nonneg s, sq_nonneg (1 + s), sq_nonneg (s - 1), hs]
  have hW2 : 0 ≤ (Work.Spaces.w s) ^ 2 := sq_nonneg _
  -- plain AM–GM for `|a|` and `|s b|`
  have hamgm : 2 * |a| * |s * b| ≤ a ^ 2 + (s * b) ^ 2 := by
    have h := two_mul_le_add_sq |a| |s * b|
    rw [sq_abs a, sq_abs (s * b)] at h
    exact h
  have habs : |s * b| = s * |b| := by rw [abs_mul, abs_of_pos hs]
  have hx : 0 ≤ 2 * |a| * |b| * Work.FTS.EllipticEst.sEta θ := by positivity
  have hWη : 0 ≤ (Work.Spaces.w s) ^ 2 * Work.FTS.EllipticEst.sEta θ := mul_nonneg hW2 hη
  calc 2 * |a * b| * Work.FTS.EllipticEst.sEta θ
      = 2 * |a| * |b| * Work.FTS.EllipticEst.sEta θ := by rw [abs_mul]; ring
    _ ≤ 2 * |a| * |b| * Work.FTS.EllipticEst.sEta θ * (s * (Work.Spaces.w s) ^ 2) := by
        nlinarith [mul_nonneg hx (by linarith : (0:ℝ) ≤ s * (Work.Spaces.w s) ^ 2 - 1)]
    _ = 2 * |a| * |s * b| * (Work.Spaces.w s) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
        rw [habs]; ring
    _ ≤ (a ^ 2 + (s * b) ^ 2) * (Work.Spaces.w s) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
        nlinarith [hamgm, hWη]
    _ = a ^ 2 * (Work.Spaces.w s) ^ 2 * Work.FTS.EllipticEst.sEta θ
          + (s * b) ^ 2 * (Work.Spaces.w s) ^ 2 * Work.FTS.EllipticEst.sEta θ := by ring

end Work.FTS.ClassCHon.SliceMassAux
