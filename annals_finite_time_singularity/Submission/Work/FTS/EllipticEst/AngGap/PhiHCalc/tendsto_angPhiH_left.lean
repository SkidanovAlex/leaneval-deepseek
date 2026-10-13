import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.AngGap.Defs
import Submission.Work.FTS.EllipticEst.AngGap.HardySetup

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngGap.PhiHCalc

/-- **The pointwise size bound behind the right endpoint limit.**

On `(0, π/2)`, where `sin 2θ > 0`, the bound `|angG h θ| ≤ C (sin 2θ)³` gives
`|V θ| = |angG h θ| / sin 2θ ≤ C (sin 2θ)²`, and with `|cot 2θ| ≤ 1/sin 2θ` this yields

  `|angPhiH h θ| = 6 (V θ)² |cot 2θ| ≤ 6 C² (sin 2θ)³`.

No positivity of `C` is needed (it is used only to make the bound decay). -/
theorem abs_angPhiH_le_left (h : ℝ → ℝ) (C : ℝ)
    (hCg : ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
        |angG h θ| ≤ C * (Real.sin (2 * θ)) ^ 3) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |angPhiH h θ| ≤ 6 * C ^ 2 * (Real.sin (2 * θ)) ^ 3 := by
  intro θ hθ
  have hsp : 0 < Real.sin (2 * θ) := sin_two_pos hθ
  have h1 := hCg θ (Set.Ioo_subset_Icc_self hθ)
  -- `|V θ| ≤ C (sin 2θ)²`
  have hV : |angV h θ| ≤ C * (Real.sin (2 * θ)) ^ 2 := by
    rw [angV, abs_div, abs_of_pos hsp, div_le_iff₀ hsp]
    calc |angG h θ| ≤ C * (Real.sin (2 * θ)) ^ 3 := h1
      _ = C * (Real.sin (2 * θ)) ^ 2 * Real.sin (2 * θ) := by ring
  have hcot := abs_cot_two_le hθ
  have h2 : (angV h θ) ^ 2 ≤ (C * (Real.sin (2 * θ)) ^ 2) ^ 2 := by
    simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg (angV h θ)) hV 2
  have h3 : 0 ≤ 6 * (C * (Real.sin (2 * θ)) ^ 2) ^ 2 := by positivity
  have hstep : 6 * (angV h θ) ^ 2 * |Real.cot (2 * θ)|
      ≤ 6 * (C * (Real.sin (2 * θ)) ^ 2) ^ 2 * (1 / Real.sin (2 * θ)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left h2 (by norm_num)) hcot (abs_nonneg _) h3
  have heq : 6 * (C * (Real.sin (2 * θ)) ^ 2) ^ 2 * (1 / Real.sin (2 * θ))
      = 6 * C ^ 2 * (Real.sin (2 * θ)) ^ 3 := by
    have hsne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hsp
    field_simp
  calc |angPhiH h θ| = 6 * (angV h θ) ^ 2 * |Real.cot (2 * θ)| := by
        simp only [angPhiH, abs_mul, abs_sq, abs_of_pos (show (0 : ℝ) < 6 by norm_num)]
    _ ≤ 6 * (C * (Real.sin (2 * θ)) ^ 2) ^ 2 * (1 / Real.sin (2 * θ)) := hstep
    _ = 6 * C ^ 2 * (Real.sin (2 * θ)) ^ 3 := heq

/-- **Right endpoint limit of the antiderivative `angPhiH h = 6 V² cot 2θ`.**

If `|angG h θ| ≤ C (sin 2θ)³` on `[0, π/2]`, then `angPhiH h → 0` as `θ → (π/2)⁻` inside
`(0, π/2)`: the squeeze `|6 V² cot 2θ| ≤ 6 C² (sin 2θ)³` (using `|V| ≤ C sin²2θ` and
`|cot 2θ| ≤ 1/sin 2θ` on the interval) has a continuous left-hand side vanishing at `π/2`.
This is one of the two boundary terms that must vanish in the fundamental identity of
calculus for the weighted Hardy inequality `12 ∫ V² ≤ ∫ h²`. -/
theorem tendsto_angPhiH_left (h : ℝ → ℝ) (C : ℝ) (hC : 0 < C)
    (hCg : ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
        |Work.FTS.EllipticEst.AngGap.angG h θ| ≤ C * (Real.sin (2 * θ)) ^ 3) :
    Filter.Tendsto (Work.FTS.EllipticEst.AngGap.angPhiH h)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  -- `(0, π/2)` is a left-neighbourhood of `π/2`, so the pointwise bound is available
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈
      nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) :=
    Ioo_mem_nhdsLT (by linarith [Real.pi_pos])
  have hev : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      |angPhiH h θ| ≤ 6 * C ^ 2 * (Real.sin (2 * θ)) ^ 3 := by
    filter_upwards [hsub] with θ hθ
    exact abs_angPhiH_le_left h C hCg θ hθ
  -- the majorant is continuous and vanishes at `π/2`
  have hgcont : Continuous (fun θ : ℝ => 6 * C ^ 2 * (Real.sin (2 * θ)) ^ 3) := by fun_prop
  have hh : Filter.Tendsto (fun θ : ℝ => 6 * C ^ 2 * (Real.sin (2 * θ)) ^ 3)
      (nhds (Real.pi / 2)) (nhds 0) := by
    have hthis := hgcont.tendsto (Real.pi / 2)
    have hval : 6 * C ^ 2 * (Real.sin (2 * (Real.pi / 2))) ^ 3 = 0 := by
      rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      ring
    rwa [hval] at hthis
  have hlim : Filter.Tendsto (fun θ : ℝ => 6 * C ^ 2 * (Real.sin (2 * θ)) ^ 3)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
    hh.mono_left (nhdsWithin_le_nhds (s := Set.Iio (Real.pi / 2)))
  -- squeeze, then replace `|angPhiH h|` by `angPhiH h`
  have habs : Filter.Tendsto (fun θ => |angPhiH h θ|)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall (fun θ => abs_nonneg _)) hev hlim
  exact (tendsto_zero_iff_abs_tendsto_zero (angPhiH h)).mpr
    (by simpa [Function.comp_def] using habs)

end Work.FTS.EllipticEst.AngGap.PhiHCalc
