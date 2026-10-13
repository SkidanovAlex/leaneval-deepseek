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

/-- The size bound on `V = angV h` used for the endpoint limits: `|V| ≤ C sin²2θ`
on `(0, π/2)`, obtained by dividing `|G| ≤ C sin³2θ` by the positive `sin 2θ`. -/
theorem abs_angV_le' (h : ℝ → ℝ) (C : ℝ)
    (hCg : ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
        |angG h θ| ≤ C * (Real.sin (2 * θ)) ^ 3) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |angV h θ| ≤ C * (Real.sin (2 * θ)) ^ 2 := by
  intro θ hθ
  have hsp : 0 < Real.sin (2 * θ) := sin_two_pos hθ
  have h1 := hCg θ (Set.Ioo_subset_Icc_self hθ)
  rw [angV, abs_div, abs_of_pos hsp, div_le_iff₀ hsp]
  calc |angG h θ| ≤ C * (Real.sin (2 * θ)) ^ 3 := h1
    _ = C * (Real.sin (2 * θ)) ^ 2 * Real.sin (2 * θ) := by ring

/-- The pointwise squeeze for `angPhiH h`: on `(0, π/2)`,
`|angPhiH h θ| = 6 V² |cot 2θ| ≤ 6 C² sin³2θ`. -/
theorem abs_angPhiH_le (h : ℝ → ℝ) (C : ℝ)
    (hCg : ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
        |angG h θ| ≤ C * (Real.sin (2 * θ)) ^ 3) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |angPhiH h θ| ≤ 6 * C ^ 2 * (Real.sin (2 * θ)) ^ 3 := by
  intro θ hθ
  have hsp : 0 < Real.sin (2 * θ) := sin_two_pos hθ
  have hV := abs_angV_le' h C hCg θ hθ
  have hcot := abs_cot_two_le hθ
  have hVnn : 0 ≤ |angV h θ| := abs_nonneg _
  have h2 : (angV h θ) ^ 2 ≤ (C * (Real.sin (2 * θ)) ^ 2) ^ 2 := by
    simpa [sq_abs] using pow_le_pow_left₀ hVnn hV 2
  have h3 : 0 ≤ 6 * (C * (Real.sin (2 * θ)) ^ 2) ^ 2 := by positivity
  have hstep1 : 6 * (angV h θ) ^ 2 * |Real.cot (2 * θ)|
      ≤ 6 * (C * (Real.sin (2 * θ)) ^ 2) ^ 2 * (1 / Real.sin (2 * θ)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left h2 (by norm_num)) hcot (abs_nonneg _) h3
  have heq : 6 * (C * (Real.sin (2 * θ)) ^ 2) ^ 2 * (1 / Real.sin (2 * θ))
      = 6 * C ^ 2 * (Real.sin (2 * θ)) ^ 3 := by
    have hsne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hsp
    field_simp
  calc |angPhiH h θ| = 6 * (angV h θ) ^ 2 * |Real.cot (2 * θ)| := by
        simp only [angPhiH, abs_mul, abs_sq,
          abs_of_pos (show (0 : ℝ) < 6 by norm_num)]
    _ ≤ 6 * (C * (Real.sin (2 * θ)) ^ 2) ^ 2 * (1 / Real.sin (2 * θ)) := hstep1
    _ = 6 * C ^ 2 * (Real.sin (2 * θ)) ^ 3 := heq

/-- **Left endpoint limit of the antiderivative `angPhiH h = 6 V² cot 2θ`.**

If `|angG h θ| ≤ C (sin 2θ)³` on `[0, π/2]`, then `angPhiH h → 0` as `θ → 0⁺` inside
`(0, π/2)`: the squeeze `|6 V² cot 2θ| ≤ 6 C² (sin 2θ)³` (using `|V| ≤ C sin²2θ` and
`|cot 2θ| ≤ 1/sin 2θ` on the interval) has a continuous right-hand side vanishing at `0`.
This is one of the two boundary terms that must vanish in the fundamental identity of
calculus for the weighted Hardy inequality `12 ∫ V² ≤ ∫ h²`. -/
theorem tendsto_angPhiH_right (h : ℝ → ℝ) (C : ℝ) (hC : 0 < C)
    (hCg : ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
        |Work.FTS.EllipticEst.AngGap.angG h θ| ≤ C * (Real.sin (2 * θ)) ^ 3) :
    Filter.Tendsto (Work.FTS.EllipticEst.AngGap.angPhiH h)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  -- the bound `|angPhiH h θ| ≤ 6 C² sin³2θ` holds eventually at `0⁺`
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    Filter.inter_mem self_mem_nhdsWithin
      (nhdsWithin_le_nhds (Iio_mem_nhds (by linarith [Real.pi_pos])))
  have hev : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      |Work.FTS.EllipticEst.AngGap.angPhiH h θ| ≤ 6 * C ^ 2 * (Real.sin (2 * θ)) ^ 3 := by
    filter_upwards [hsub] with θ hθ
    exact abs_angPhiH_le h C hCg θ hθ
  -- the majorant is continuous and vanishes at `0`
  have hgcont : Continuous (fun θ : ℝ => 6 * C ^ 2 * (Real.sin (2 * θ)) ^ 3) := by fun_prop
  have hh : Filter.Tendsto (fun θ : ℝ => 6 * C ^ 2 * (Real.sin (2 * θ)) ^ 3)
      (nhds (0 : ℝ)) (nhds 0) := by
    simpa using hgcont.tendsto 0
  have hlim : Filter.Tendsto (fun θ : ℝ => 6 * C ^ 2 * (Real.sin (2 * θ)) ^ 3)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    hh.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have habs : Filter.Tendsto (fun θ => |Work.FTS.EllipticEst.AngGap.angPhiH h θ|)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall (fun θ => abs_nonneg _)) hev hlim
  exact (tendsto_zero_iff_abs_tendsto_zero (Work.FTS.EllipticEst.AngGap.angPhiH h)).mpr
    (by simpa [Function.comp_def] using habs)

end Work.FTS.EllipticEst.AngGap.PhiHCalc
