import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.R1G.AnG

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

/-!
# Hölder continuity in `z` of the analytic perturbation `gA z θ = Zf z · Tf θ`

The goal is `|gA z θ - gA z' θ| ≤ L·|z - z'|^α` for `z, z' ≥ 0`, `θ ∈ Iθ` and `0 < α ≤ 1`.

Since `gA z θ - gA z' θ = (Zf z - Zf z')·Tf θ` and `|Tf θ| ≤ 1`, it suffices to control the radial
factor: `Zf` is smooth on the halfline with

* `|Zf| ≤ 1` on `[0,∞)` (so `|Zf z - Zf z'| ≤ 2`), and
* `|Zf'| ≤ 8` on `[0,∞)` (from the closed form `Zf'(z) = (2z - 6z³)/(1+z²)⁵`),

whence `|Zf z - Zf z'| ≤ 8|z - z'|` by the mean value inequality.  A Lipschitz function with these
two bounds is `α`-Hölder on `[0,∞)` for every `0 < α ≤ 1`: on `|z - z'| ≤ 1` use
`|z - z'| ≤ |z - z'|^α`, on `|z - z'| ≥ 1` use `2 ≤ 2|z - z'|^α ≤ 8|z - z'|^α`.

The constant `L = 8` therefore works for every `α ∈ (0,1]`.
-/

/-- `|Zf'| ≤ 8` on the halfline `z ≥ 0`: from
`Zf'(z) = (2z - 6z³)/(1+z²)⁵`, the numerator is at most `2z + 6z³`, which is `≤ 8` for `z ≤ 1`
(denominator `≥ 1`) and `≤ 8z³ ≤ 8z¹⁰ ≤ 8(1+z²)⁵` for `z ≥ 1`. -/
lemma abs_deriv_Zf_le_eight {z : ℝ} (hz : 0 ≤ z) : |deriv Zf z| ≤ 8 := by
  rw [deriv_Zf]
  have hden : (0 : ℝ) < (1 + z ^ 2) ^ 5 := by positivity
  rw [abs_div, abs_of_pos hden, div_le_iff₀ hden]
  have hb : |2 * z - 6 * z ^ 3| ≤ 2 * z + 6 * z ^ 3 := by
    rw [abs_le]; constructor <;> nlinarith [hz]
  have hmain : 2 * z + 6 * z ^ 3 ≤ 8 * (1 + z ^ 2) ^ 5 := by
    by_cases h : z ≤ 1
    · have h1 : (1 : ℝ) ≤ (1 + z ^ 2) ^ 5 := one_le_pow₀ (by linarith [sq_nonneg z])
      have hz3 : 6 * z ^ 3 ≤ 6 := by
        have := pow_le_one₀ hz h (n := 3); nlinarith
      have hz1 : 2 * z ≤ 2 := by linarith
      nlinarith [h1]
    · push Not at h
      have hz1 : (1 : ℝ) ≤ z := le_of_lt h
      have h2 : 2 * z ≤ 2 * z ^ 3 := by nlinarith [hz1, sq_nonneg z]
      have h3 : z ^ 3 ≤ (1 + z ^ 2) ^ 5 := by
        have h310 : z ^ 3 ≤ z ^ 10 := pow_le_pow_right₀ hz1 (by norm_num)
        have h10 : z ^ 10 = (z ^ 2) ^ 5 := by ring
        have hz2 : z ^ 2 ≤ 1 + z ^ 2 := by linarith [sq_nonneg z]
        have h5 : (z ^ 2) ^ 5 ≤ (1 + z ^ 2) ^ 5 := pow_le_pow_left₀ (sq_nonneg z) hz2 5
        linarith
      have : 2 * z + 6 * z ^ 3 ≤ 8 * z ^ 3 := by linarith
      nlinarith [h3]
  linarith [hb, hmain]

/-- **Lipschitz bound for the radial factor**: on the halfline `z ≥ 0` we have
`|Zf z - Zf z'| ≤ 8|z - z'|` (mean value inequality with `|Zf'| ≤ 8`). -/
lemma abs_Zf_sub_le_eight {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') :
    |Zf z - Zf z'| ≤ 8 * |z - z'| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (𝕜 := ℝ) (G := ℝ) (f := Zf) (s := Set.Ici (0 : ℝ)) (C := 8) (x := z') (y := z)
    (fun x _ => differentiableAt_Zf x)
    (fun x hx => by
      rw [Real.norm_eq_abs]
      exact abs_deriv_Zf_le_eight hx)
    (convex_Ici 0) hz' hz
  rwa [Real.norm_eq_abs, Real.norm_eq_abs] at h

theorem holderZ_gA (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ z z' θ : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ →
      |Work.R1G.gA z θ - Work.R1G.gA z' θ| ≤ L * |z - z'| ^ α := by
  refine ⟨8, by norm_num, ?_⟩
  intro z z' θ hz hz' hθ
  have hT : |Tf θ| ≤ 1 := abs_Tf_le_one θ
  have hLip : |Zf z - Zf z'| ≤ 8 * |z - z'| := abs_Zf_sub_le_eight hz hz'
  have hsup : |Zf z - Zf z'| ≤ 2 := by
    have h1 : |Zf z| ≤ 1 := by rw [abs_of_nonneg (Zf_nonneg hz)]; exact Zf_le_one hz
    have h2 : |Zf z'| ≤ 1 := by rw [abs_of_nonneg (Zf_nonneg hz')]; exact Zf_le_one hz'
    have h3 : |Zf z - Zf z'| ≤ |Zf z| + |Zf z'| := by
      have := abs_add_le (Zf z) (-(Zf z')); simpa [sub_eq_add_neg] using this
    linarith
  have hEq : gA z θ - gA z' θ = (Zf z - Zf z') * Tf θ := by
    simp only [gA]; ring
  have hLHS : |gA z θ - gA z' θ| ≤ |Zf z - Zf z'| := by
    rw [hEq, abs_mul]
    calc |Zf z - Zf z'| * |Tf θ| ≤ |Zf z - Zf z'| * 1 :=
          mul_le_mul_of_nonneg_left hT (abs_nonneg _)
      _ = |Zf z - Zf z'| := by ring
  by_cases hA : |z - z'| ≤ 1
  · rcases eq_or_lt_of_le (abs_nonneg (z - z')) with h0 | h0
    · have hzz : z = z' := by
        have : z - z' = 0 := abs_eq_zero.mp h0.symm
        linarith
      subst hzz
      simp [Real.zero_rpow hα.ne']
    · have hA1 : |z - z'| ^ (1 : ℝ) ≤ |z - z'| ^ α :=
        Real.rpow_le_rpow_of_exponent_ge h0 hA hα1
      rw [Real.rpow_one] at hA1
      calc |gA z θ - gA z' θ| ≤ 8 * |z - z'| := le_trans hLHS hLip
        _ ≤ 8 * |z - z'| ^ α := mul_le_mul_of_nonneg_left hA1 (by norm_num)
  · push Not at hA
    have hA1 : 1 ≤ |z - z'| := by linarith [abs_nonneg (z - z')]
    have hrpow : 1 ≤ |z - z'| ^ α := Real.one_le_rpow hA1 hα.le
    have h4 : |gA z θ - gA z' θ| ≤ 2 := le_trans hLHS hsup
    calc |gA z θ - gA z' θ| ≤ 2 := h4
      _ ≤ 8 * |z - z'| ^ α := by
          have h8 : 8 * 1 ≤ 8 * |z - z'| ^ α :=
            mul_le_mul_of_nonneg_left hrpow (by norm_num)
          linarith

end Work.R1G
