/-
# `Work.FTS.PhiStar.Psi0Est.Gzero_rpow_pi_div_two` — the right-endpoint power bound for `G₀`

`G₀(α,θ) = ∫_θ^{π/2} sin t cos²t Γ̄(α,t) dt` (`Work.FTS.PhiStar.Gzero`), with
`Γ̄ = Γ/c − (5/4) sin 2·` and `Γ = (sin t cos²t)^{α/3}`.

For `|θ − π/2| ≤ 1/2` we prove `|G₀(α,θ)| ≤ 13|θ − π/2|^{3+2α/3}` (the exponent is sharp).

## The route

1. **Pointwise bound on the integrand** (`abs_sin_cos_sq_GamBar_le_rpow`).  For
   `|t − π/2| ≤ 1/2` one has `t ∈ (0,π)`, so `sin t > 0`, the base `sin t cos²t` is
   nonnegative and `|Γ(t)| = Γ(t) = (sin t cos²t)^{α/3} = sin^{α/3}t·|cos t|^{2α/3}`.
   Since `|sin 2t| ≤ 2|cos t|`,
   `|Γ̄| ≤ Γ/c + (5/2)|cos t|`, and therefore
   `|sin t cos²t Γ̄| ≤ cos²t Γ/c + (5/2)cos²t|cos t|
        ≤ |cos t|^{2+2α/3}/c + (5/2)|cos t|³ ≤ (1/c + 5/2)|t − π/2|^{2+2α/3}`,
   using `cos²t·Γ ≤ |cos t|^{2+2α/3}` (`cos_sq_mul_Gam_le_cos_rpow`), `|cos t| ≤ |t − π/2|`
   and `|t − π/2| ≤ 1` to compare the exponents `3` and `2+2α/3`.
2. **Integrating.**  `intervalIntegral.norm_integral_le_of_norm_le_const` bounds the
   (oriented, hence two-sided) interval integral of the integrand by the constant pointwise
   bound times the length `|π/2 − θ|` of the interval; the distance within the interval is
   controlled by `abs_sub_pi_div_two_le_of_mem_uIoc`.  The exponent arithmetic
   `(2+2α/3) + 1 = 3+2α/3` is `Real.rpow_add'`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Psi0Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Psi0Est

open MeasureTheory Set
open scoped Real Topology

set_option autoImplicit false

/-! ## Two elementary ingredients -/

/-- Within the interval between `θ` and `π/2`, the distance to `π/2` is at most the
distance of `θ` to `π/2`: `|x − π/2| ≤ |θ − π/2|` for `x ∈ uIoc θ (π/2)`. -/
lemma abs_sub_pi_div_two_le_of_mem_uIoc {θ x : ℝ} (hx : x ∈ Set.uIoc θ (Real.pi / 2)) :
    |x - Real.pi / 2| ≤ |θ - Real.pi / 2| := by
  rcases le_or_gt θ (Real.pi / 2) with h | h
  · rw [Set.uIoc_of_le h] at hx
    rw [abs_of_nonpos (by linarith [hx.2] : x - Real.pi / 2 ≤ 0),
      abs_of_nonpos (by linarith : θ - Real.pi / 2 ≤ 0)]
    linarith [hx.1]
  · rw [show Set.uIoc θ (Real.pi / 2) = Set.Ioc (Real.pi / 2) θ from by
      simp only [Set.uIoc, min_eq_right h.le, max_eq_left h.le]] at hx
    rw [abs_of_nonneg (by linarith [hx.1] : (0 : ℝ) ≤ x - Real.pi / 2),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ θ - Real.pi / 2)]
    linarith [hx.2]

/-- **The `cos²·Γ` bound**: for `sin t ≥ 0` and `α > 0`,
`cos²t · Γ(t) ≤ |cos t|^{2+2α/3}`.

Indeed `Γ(t) = (sin t cos²t)^{α/3} ≤ (cos²t)^{α/3} = |cos t|^{2α/3}`, and
`cos²t = |cos t|²`; the two powers combine by `Real.rpow_add'`. -/
lemma cos_sq_mul_Gam_le_cos_rpow (α t : ℝ) (hα : 0 < α) (hs : 0 ≤ Real.sin t) :
    Real.cos t ^ 2 * Work.Spaces.Gam α t ≤ |Real.cos t| ^ (2 + 2 * (α / 3)) := by
  have hcosabs : 0 ≤ |Real.cos t| := abs_nonneg _
  have hbase : 0 ≤ Real.sin t * Real.cos t ^ 2 := mul_nonneg hs (sq_nonneg _)
  have hcos2 : |Real.cos t| ^ (2 : ℝ) = Real.cos t ^ 2 := by
    rw [Real.rpow_two, sq_abs]
  have hcle : Real.sin t * Real.cos t ^ 2 ≤ |Real.cos t| ^ (2 : ℝ) := by
    rw [hcos2]
    exact mul_le_of_le_one_left (by positivity) (Real.sin_le_one t)
  have hstep : (Real.sin t * Real.cos t ^ 2) ^ (α / 3)
      ≤ (|Real.cos t| ^ (2 : ℝ)) ^ (α / 3) :=
    Real.rpow_le_rpow hbase hcle (by linarith)
  have hsimp : (|Real.cos t| ^ (2 : ℝ)) ^ (α / 3) = |Real.cos t| ^ (2 * (α / 3)) := by
    rw [← Real.rpow_mul hcosabs]
  have hfinal : |Real.cos t| ^ (2 : ℝ) * |Real.cos t| ^ (2 * (α / 3))
      = |Real.cos t| ^ (2 + 2 * (α / 3)) := by
    rw [← Real.rpow_add' hcosabs (by linarith : 2 + 2 * (α / 3) ≠ 0)]
  have h1 : Real.cos t ^ 2 * (Real.sin t * Real.cos t ^ 2) ^ (α / 3)
      = |Real.cos t| ^ (2 : ℝ) * (Real.sin t * Real.cos t ^ 2) ^ (α / 3) := by
    rw [hcos2]
  rw [Work.Spaces.Gam, h1]
  calc |Real.cos t| ^ (2 : ℝ) * (Real.sin t * Real.cos t ^ 2) ^ (α / 3)
      ≤ |Real.cos t| ^ (2 : ℝ) * (|Real.cos t| ^ (2 : ℝ)) ^ (α / 3) :=
        mul_le_mul_of_nonneg_left hstep (Real.rpow_nonneg hcosabs _)
    _ = |Real.cos t| ^ (2 : ℝ) * |Real.cos t| ^ (2 * (α / 3)) := by rw [hsimp]
    _ = |Real.cos t| ^ (2 + 2 * (α / 3)) := hfinal

/-! ## The pointwise bound on the integrand near `π/2` -/

/-- **The integrand bound near the right endpoint.**  For `0 < α ≤ 1/4` and
`|t − π/2| ≤ 1/2`,
`|sin t · cos²t · Γ̄(t)| ≤ (1/c + 5/2)·|t − π/2|^{2+2α/3}`. -/
private lemma abs_sin_cos_sq_GamBar_le_rpow (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {t : ℝ}
    (ht : |t - Real.pi / 2| ≤ 1 / 2) :
    |Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t|
      ≤ (1 / Work.Spaces.c α + 5 / 2) * |t - Real.pi / 2| ^ (2 + 2 * (α / 3)) := by
  have hcpos : 0 < Work.Spaces.c α := by
    have := (Work.Spaces.c_bounds α hα (by linarith)).1
    linarith
  have htlo : 0 < t := by
    have h := (abs_le.mp ht).1
    linarith [Real.pi_gt_three]
  have hthi : t < Real.pi := by
    have h := (abs_le.mp ht).2
    linarith [Real.pi_gt_three]
  have hsin0 : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi htlo hthi
  have hsinle : Real.sin t ≤ 1 := Real.sin_le_one t
  have hc2 : 0 ≤ Real.cos t ^ 2 := sq_nonneg _
  have hgamnn : 0 ≤ Work.Spaces.Gam α t :=
    Real.rpow_nonneg (mul_nonneg hsin0.le hc2) _
  have hcosabs : 0 ≤ |Real.cos t| := abs_nonneg _
  -- `|Γ̄| ≤ Γ/c + (5/2)|cos t|`
  have hGB : |Work.FTS.VocabO.GamBar α t|
      ≤ Work.Spaces.Gam α t / Work.Spaces.c α + (5 / 2) * |Real.cos t| := by
    rw [Work.FTS.VocabO.GamBar]
    have h1 : |Work.Spaces.Gam α t / Work.Spaces.c α - 5 / 4 * Real.sin (2 * t)|
        ≤ |Work.Spaces.Gam α t / Work.Spaces.c α| + |(5 : ℝ) / 4 * Real.sin (2 * t)| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (Work.Spaces.Gam α t / Work.Spaces.c α)
          (-((5 : ℝ) / 4 * Real.sin (2 * t)))
    have h2 : |Work.Spaces.Gam α t / Work.Spaces.c α| = Work.Spaces.Gam α t / Work.Spaces.c α :=
      abs_of_nonneg (div_nonneg hgamnn hcpos.le)
    have h3 : |(5 : ℝ) / 4 * Real.sin (2 * t)| ≤ (5 / 2) * |Real.cos t| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 4)]
      have h4 : |Real.sin (2 * t)| ≤ 2 * |Real.cos t| := by
        rw [Real.sin_two_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have h5 := Real.abs_sin_le_one t
        nlinarith [abs_nonneg (Real.cos t)]
      linarith
    linarith
  -- `|cos t| ≤ |t − π/2|`
  have hcosle : |Real.cos t| ≤ |t - Real.pi / 2| := by
    rw [show Real.cos t = Real.sin (Real.pi / 2 - t) from (Real.sin_pi_div_two_sub t).symm,
      abs_sub_comm t (Real.pi / 2)]
    exact Real.abs_sin_le_abs
  have ht1 : |t - Real.pi / 2| ≤ 1 := by linarith
  have hp0 : (0 : ℝ) ≤ 2 + 2 * (α / 3) := by linarith
  have hp3 : 2 + 2 * (α / 3) ≤ 3 := by linarith
  -- `cos²t·Γ ≤ |cos t|^p`
  have hgam2 : Real.cos t ^ 2 * Work.Spaces.Gam α t ≤ |Real.cos t| ^ (2 + 2 * (α / 3)) :=
    cos_sq_mul_Gam_le_cos_rpow α t hα hsin0.le
  -- `|cos t|³ ≤ |t − π/2|^p`
  have hcs : |Real.cos t| ^ 3 ≤ |t - Real.pi / 2| ^ (2 + 2 * (α / 3)) := by
    have h3 : |Real.cos t| ^ 3 ≤ |t - Real.pi / 2| ^ 3 :=
      pow_le_pow_left₀ hcosabs hcosle 3
    have h4 : |t - Real.pi / 2| ^ 3 ≤ |t - Real.pi / 2| ^ (2 + 2 * (α / 3)) := by
      rw [show |t - Real.pi / 2| ^ 3 = |t - Real.pi / 2| ^ (3 : ℝ) from
        (Real.rpow_natCast _ 3).symm]
      exact Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg _) ht1 hp0 hp3
    linarith
  have hpc : (1 / Work.Spaces.c α) * |Real.cos t| ^ (2 + 2 * (α / 3))
      ≤ (1 / Work.Spaces.c α) * |t - Real.pi / 2| ^ (2 + 2 * (α / 3)) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hcosabs hcosle hp0) (by positivity)
  -- assembly
  have e1 : |Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t|
      = Real.sin t * Real.cos t ^ 2 * |Work.FTS.VocabO.GamBar α t| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hsin0.le, abs_of_nonneg hc2]
  have step1 : Real.sin t * Real.cos t ^ 2 * |Work.FTS.VocabO.GamBar α t|
      ≤ Real.sin t * Real.cos t ^ 2
        * (Work.Spaces.Gam α t / Work.Spaces.c α + (5 / 2) * |Real.cos t|) :=
    mul_le_mul_of_nonneg_left hGB (mul_nonneg hsin0.le hc2)
  have h5 : Real.cos t ^ 2 * |Real.cos t| = |Real.cos t| ^ 3 := by
    rw [show Real.cos t ^ 2 = |Real.cos t| ^ 2 from (sq_abs (Real.cos t)).symm]
    ring
  have hmul2 : Real.sin t * (Real.cos t ^ 2 * Work.Spaces.Gam α t)
      ≤ Real.cos t ^ 2 * Work.Spaces.Gam α t :=
    mul_le_of_le_one_left (mul_nonneg hc2 hgamnn) hsinle
  have hmul3 : Real.sin t * (Real.cos t ^ 2 * |Real.cos t|)
      ≤ Real.cos t ^ 2 * |Real.cos t| :=
    mul_le_of_le_one_left (mul_nonneg hc2 hcosabs) hsinle
  have step2 : Real.sin t * Real.cos t ^ 2
        * (Work.Spaces.Gam α t / Work.Spaces.c α + (5 / 2) * |Real.cos t|)
      ≤ (1 / Work.Spaces.c α) * |Real.cos t| ^ (2 + 2 * (α / 3))
        + (5 / 2) * |Real.cos t| ^ 3 := by
    have heq : Real.sin t * Real.cos t ^ 2
          * (Work.Spaces.Gam α t / Work.Spaces.c α + (5 / 2) * |Real.cos t|)
        = (1 / Work.Spaces.c α) * (Real.sin t * (Real.cos t ^ 2 * Work.Spaces.Gam α t))
          + (5 / 2) * (Real.sin t * (Real.cos t ^ 2 * |Real.cos t|)) := by ring
    rw [heq]
    have hA : (1 / Work.Spaces.c α) * (Real.sin t * (Real.cos t ^ 2 * Work.Spaces.Gam α t))
        ≤ (1 / Work.Spaces.c α) * |Real.cos t| ^ (2 + 2 * (α / 3)) :=
      mul_le_mul_of_nonneg_left (le_trans hmul2 hgam2) (by positivity)
    have hB : (5 / 2) * (Real.sin t * (Real.cos t ^ 2 * |Real.cos t|))
        ≤ (5 / 2) * |Real.cos t| ^ 3 :=
      mul_le_mul_of_nonneg_left (le_trans hmul3 (le_of_eq h5)) (by norm_num)
    linarith
  have step3 : (1 / Work.Spaces.c α) * |Real.cos t| ^ (2 + 2 * (α / 3))
        + (5 / 2) * |Real.cos t| ^ 3
      ≤ (1 / Work.Spaces.c α) * |t - Real.pi / 2| ^ (2 + 2 * (α / 3))
        + (5 / 2) * |t - Real.pi / 2| ^ (2 + 2 * (α / 3)) := by
    have hB : (5 / 2) * |Real.cos t| ^ 3
        ≤ (5 / 2) * |t - Real.pi / 2| ^ (2 + 2 * (α / 3)) :=
      mul_le_mul_of_nonneg_left hcs (by norm_num)
    linarith
  have step4 : (1 / Work.Spaces.c α) * |t - Real.pi / 2| ^ (2 + 2 * (α / 3))
        + (5 / 2) * |t - Real.pi / 2| ^ (2 + 2 * (α / 3))
      = (1 / Work.Spaces.c α + 5 / 2) * |t - Real.pi / 2| ^ (2 + 2 * (α / 3)) := by ring
  linarith [e1, step1, step2, step3, step4]

/-! ## The target -/

/-- Two-sided power bound for `G₀` near the right endpoint of `Iθ`:
`|G₀(θ)| ≤ C|θ-π/2|^{3+2α/3}` for `|θ-π/2| ≤ 1/2`.

Here `G₀(θ) = ∫_θ^{π/2} sin t cos²t Γ̄(t) dt`, and on the interval between `θ` and `π/2` the
integrand satisfies `|sin t cos²t Γ̄(t)| ≤ cos²t(cos^{2α/3}t/c + (5/2)|cos t|)` (using
`|sin t| ≤ 1` and `|Γ(t)| = |(sin t cos²t)^{α/3}| ≤ cos^{2α/3}t`), which is
`≤ C|π/2-t|^{2+2α/3}` because `|cos t| ≤ |π/2 - t|` there; integrating from `θ` to `π/2`
(or from `π/2` to `θ` when `θ > π/2`) gives `C|θ - π/2|^{3+2α/3}`, the
`(5/2)|cos t|³` term being of higher order (`3 ≥ 2+2α/3`).  This is the quantitative
improvement of the existing `Gzero_abs_le` (`|G₀ θ| ≤ (1/c+5/4)(π/2-θ)cos²θ`, which only
gives `O(|θ-π/2|³)`), and the exponent `3+2α/3` is sharp. -/
theorem Gzero_rpow_pi_div_two (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ, |θ - Real.pi / 2| ≤ 1 / 2 →
      |Work.FTS.PhiStar.Gzero α θ| ≤ C * |θ - Real.pi / 2| ^ (3 + 2 * (α / 3)) := by
  have hKpos : 0 < 1 / Work.Spaces.c α + 5 / 2 := by
    have hcpos : 0 < Work.Spaces.c α := by
      have := (Work.Spaces.c_bounds α hα (by linarith)).1
      linarith
    have : 0 < 1 / Work.Spaces.c α := by positivity
    linarith
  refine ⟨13, by norm_num, fun θ hθ => ?_⟩
  have hp0 : (0 : ℝ) ≤ 2 + 2 * (α / 3) := by linarith
  have hpne : 2 + 2 * (α / 3) + 1 ≠ 0 := by linarith
  -- the pointwise bound on the integrand, pulled back to the interval `uIoc θ (π/2)`
  have hbound : ‖∫ t in θ..(Real.pi / 2),
        Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t‖
      ≤ (1 / Work.Spaces.c α + 5 / 2) * |θ - Real.pi / 2| ^ (2 + 2 * (α / 3))
        * |Real.pi / 2 - θ| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => ?_)
    have hx1 : |x - Real.pi / 2| ≤ 1 / 2 :=
      le_trans (abs_sub_pi_div_two_le_of_mem_uIoc hx) hθ
    calc ‖Real.sin x * Real.cos x ^ 2 * Work.FTS.VocabO.GamBar α x‖
        = |Real.sin x * Real.cos x ^ 2 * Work.FTS.VocabO.GamBar α x| := Real.norm_eq_abs _
      _ ≤ (1 / Work.Spaces.c α + 5 / 2) * |x - Real.pi / 2| ^ (2 + 2 * (α / 3)) :=
          abs_sin_cos_sq_GamBar_le_rpow α hα hα1 hx1
      _ ≤ (1 / Work.Spaces.c α + 5 / 2) * |θ - Real.pi / 2| ^ (2 + 2 * (α / 3)) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (abs_nonneg _) (abs_sub_pi_div_two_le_of_mem_uIoc hx) hp0)
            hKpos.le
  have hfin : (1 / Work.Spaces.c α + 5 / 2) * |θ - Real.pi / 2| ^ (2 + 2 * (α / 3))
        * |Real.pi / 2 - θ|
      = (1 / Work.Spaces.c α + 5 / 2) * |θ - Real.pi / 2| ^ (3 + 2 * (α / 3)) := by
    rw [abs_sub_comm (Real.pi / 2) θ,
      show (3 : ℝ) + 2 * (α / 3) = (2 + 2 * (α / 3)) + 1 by ring,
      Real.rpow_add' (abs_nonneg _) hpne, Real.rpow_one]
    ring
  have h13 : (1 / Work.Spaces.c α + 5 / 2) ≤ 13 := by
    have hcpos : 0 < Work.Spaces.c α := by
      have := (Work.Spaces.c_bounds α hα (by linarith)).1
      linarith
    have h10 : 1 / Work.Spaces.c α ≤ 10 := by
      rw [div_le_iff₀ hcpos]
      have := (Work.Spaces.c_bounds α hα (by linarith)).1
      linarith
    linarith
  calc |Work.FTS.PhiStar.Gzero α θ|
      = ‖∫ t in θ..(Real.pi / 2),
          Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t‖ := by
        rw [Work.FTS.PhiStar.Gzero, Real.norm_eq_abs]
    _ ≤ (1 / Work.Spaces.c α + 5 / 2) * |θ - Real.pi / 2| ^ (2 + 2 * (α / 3))
          * |Real.pi / 2 - θ| := hbound
    _ = (1 / Work.Spaces.c α + 5 / 2) * |θ - Real.pi / 2| ^ (3 + 2 * (α / 3)) := hfin
    _ ≤ 13 * |θ - Real.pi / 2| ^ (3 + 2 * (α / 3)) :=
        mul_le_mul_of_nonneg_right h13 (Real.rpow_nonneg (abs_nonneg _) _)

end Work.FTS.PhiStar.Psi0Est
