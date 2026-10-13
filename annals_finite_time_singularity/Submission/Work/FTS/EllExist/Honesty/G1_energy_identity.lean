/-
# `Work.FTS.EllExist.Honesty.G1_energy_identity`

The one-dimensional energy identity for the singular (`z → 0`) Green term

  `G1 α m c z = z^{s⁻} · ∫_0^z c t · t^{a-1} dt`,   `s⁻ = -(2m+5)/α = -a`,  `a = G1a α m > 0`

of the explicit radial Green function `radGreen`.

Because `z ↦ z^{-a}` and the primitive `A z = ∫_0^z c t t^{a-1} dt` are both differentiable on
`(0,∞)` (the latter with derivative `c z · z^{a-1}`, `G1A_hasDerivAt`), the product rule gives the
pointwise ODE

  `z * deriv (G1 α m c) z = -a * G1 α m c z + c z`   (`z > 0`),

i.e. `deriv (G1 α m c) z = ((-a * G1 α m c z + c z)) / z`.  Hence
`u z := G1 α m c z ^ 2 / z ^ 3` has derivative

  `u' z = (2 * c z * G1 z - (3 + 2a) * G1 z ^ 2) / z ^ 4`

and the fundamental theorem of calculus on `[x,y] ⊆ (0,1)` yields, after splitting the integral,

  `(3 + 2a) * ∫_x^y G1 z ^ 2 / z ^ 4
     = 2 * ∫_x^y c z * G1 z / z ^ 4 + G1 x ^ 2 / x ^ 3 - G1 y ^ 2 / y ^ 3`.

That is the statement below.  The two derivative inputs are the companion modules
`G1_hasDerivAt` and `hasDerivAt_sq_div_cube`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllExist.Honesty.G1Aux
import Submission.Work.FTS.EllExist.Honesty.G1_continuousOn
import Submission.Work.FTS.EllExist.Honesty.G1_hasDerivAt
import Submission.Work.FTS.EllExist.Honesty.hasDerivAt_sq_div_cube

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty

open MeasureTheory Set

set_option autoImplicit false

theorem G1_energy_identity {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun z => c z ^ 2 / z ^ 4) (Set.Ioo 0 1)) :
    ∀ x y : ℝ, 0 < x → x < y → y < 1 →
      (3 + 2 * Work.FTS.EllExist.Honesty.G1a α m)
          * (∫ z in x..y, Work.FTS.EllExist.Honesty.G1 α m c z ^ 2 / z ^ 4)
        = 2 * (∫ z in x..y, c z * Work.FTS.EllExist.Honesty.G1 α m c z / z ^ 4)
          + Work.FTS.EllExist.Honesty.G1 α m c x ^ 2 / x ^ 3
          - Work.FTS.EllExist.Honesty.G1 α m c y ^ 2 / y ^ 3 := by
  intro x y hx hxy hy1
  -- the pointwise ODE for `G1`
  have hG1d : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (G1 α m c) ((-(G1a α m) * G1 α m c z + c z) / z) z :=
    G1_hasDerivAt hα m hc h0
  -- the derivative of `u z = G1 z ^ 2 / z ^ 3`
  have hF : ∀ z ∈ Set.uIcc x y,
      HasDerivAt (fun w : ℝ => G1 α m c w ^ 2 / w ^ 3)
        ((2 * c z * G1 α m c z - (3 + 2 * G1a α m) * G1 α m c z ^ 2) / z ^ 4) z := by
    intro z hz
    rw [Set.uIcc_of_le hxy.le] at hz
    have hz0 : 0 < z := lt_of_lt_of_le hx hz.1
    exact hasDerivAt_sq_div_cube hz0 (hG1d z hz0)
  -- continuity of the ingredients on the closed interval `[x,y] ⊆ (0,1)`
  have hmem : ∀ z ∈ Set.Icc x y, 0 < z ∧ z < 1 := fun z hz =>
    ⟨lt_of_lt_of_le hx hz.1, lt_of_le_of_lt hz.2 hy1⟩
  have hcc : ContinuousOn c (Set.Icc x y) :=
    hc.mono (fun z hz => (hmem z hz).1)
  have hgc : ContinuousOn (G1 α m c) (Set.Icc x y) :=
    (G1_continuousOn hα m hc h0).mono (fun z hz => ⟨(hmem z hz).1, (hmem z hz).2⟩)
  have hden : ContinuousOn (fun z : ℝ => z ^ 4) (Set.Icc x y) := continuousOn_id.pow 4
  have hne4 : ∀ z ∈ Set.Icc x y, z ^ 4 ≠ 0 := fun z hz =>
    pow_ne_zero 4 (ne_of_gt (hmem z hz).1)
  -- the integrands of the desired identity are interval integrable
  have hintA : IntervalIntegrable (fun z : ℝ => c z * G1 α m c z / z ^ 4) volume x y :=
    ((hcc.mul hgc).div hden hne4).intervalIntegrable_of_Icc hxy.le
  have hintB : IntervalIntegrable (fun z : ℝ => G1 α m c z ^ 2 / z ^ 4) volume x y :=
    ((hgc.pow 2).div hden hne4).intervalIntegrable_of_Icc hxy.le
  have hcontD : ContinuousOn
      (fun z : ℝ => (2 * c z * G1 α m c z - (3 + 2 * G1a α m) * G1 α m c z ^ 2) / z ^ 4)
      (Set.Icc x y) :=
    (((continuousOn_const.mul hcc).mul hgc).sub (continuousOn_const.mul (hgc.pow 2))).div
      hden hne4
  have hintD : IntervalIntegrable
      (fun z : ℝ => (2 * c z * G1 α m c z - (3 + 2 * G1a α m) * G1 α m c z ^ 2) / z ^ 4)
      volume x y := hcontD.intervalIntegrable_of_Icc hxy.le
  -- the fundamental theorem of calculus
  have hftc : (∫ z in x..y,
        (2 * c z * G1 α m c z - (3 + 2 * G1a α m) * G1 α m c z ^ 2) / z ^ 4)
      = G1 α m c y ^ 2 / y ^ 3 - G1 α m c x ^ 2 / x ^ 3 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun w : ℝ => G1 α m c w ^ 2 / w ^ 3) hF hintD
  -- split the integrand
  have hcongr : (∫ z in x..y,
        (2 * c z * G1 α m c z - (3 + 2 * G1a α m) * G1 α m c z ^ 2) / z ^ 4)
      = ∫ z in x..y,
          (2 * (c z * G1 α m c z / z ^ 4) - (3 + 2 * G1a α m) * (G1 α m c z ^ 2 / z ^ 4)) := by
    refine intervalIntegral.integral_congr (fun z hz => ?_)
    rw [Set.uIcc_of_le hxy.le] at hz
    have hz0 : z ≠ 0 := ne_of_gt (hmem z hz).1
    field_simp
  have hsplit : (∫ z in x..y,
          (2 * (c z * G1 α m c z / z ^ 4) - (3 + 2 * G1a α m) * (G1 α m c z ^ 2 / z ^ 4)))
      = 2 * (∫ z in x..y, c z * G1 α m c z / z ^ 4)
        - (3 + 2 * G1a α m) * (∫ z in x..y, G1 α m c z ^ 2 / z ^ 4) := by
    rw [intervalIntegral.integral_sub (hintA.const_mul 2) (hintB.const_mul (3 + 2 * G1a α m)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  linarith [hftc, hcongr, hsplit]

end Work.FTS.EllExist.Honesty
