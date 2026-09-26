import Mathlib
import Submission.Work.Drive.sweepFamWideTolDefs
import Submission.Work.Drive.chordSweepDefs

/-!
# The modulus of continuity of the matched phase in the sweep parameter

The matched phase `Work.Drive.wideSig D lam σ` of the wide end of the chord sweep is, for fixed
loop parameter `τ`, the piecewise affine function `wideSfrac` of the knot datum
`(taR D σ, sweepW' D σ, period - sweepW' D σ)`.  Both `taR D` and `sweepW' D` are *continuous*
in the sweep parameter `σ` (they are the clamped continuous lifts of the band arc), and the
piecewise affine function `wideSfrac` is *uniformly* Lipschitz in its first two arguments with
constant `(1, 2)`, uniformly over the chamfer fraction `lam ∈ (0, 1/4]` and the loop fraction
`u ∈ [0,1]`.

Hence `σ ↦ wideSig D lam σ τ` is continuous in `σ`, uniformly in `lam ∈ (0,1/4]` and `τ`: this is
`Work.Drive.wideSig_sigma_modulus`.

## Contents

* `abs_add_mul_le` — the elementary estimate `|(a-a') + c(w-w')| ≤ |a-a'| + 2|w-w'|` for `|c| ≤ 2`;
* `abs_wideSfrac_sub_le` — the uniform two-variable Lipschitz bound for `wideSfrac`;
* `wideSig_sigma_modulus` — the target.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

/-! ## Continuity of the clamped lifts -/

/-- The `a`-lift of the sweep data is continuous in the real parameter. -/
lemma wideSig_taR_continuous {d : BandArcData} (D : SweepData d) : Continuous (taR D) :=
  D.cont_ta.comp
    (Continuous.subtype_mk (continuous_const.min (continuous_const.max continuous_id)) _)

/-- The `b`-lift of the sweep data is continuous in the real parameter. -/
lemma wideSig_tbR_continuous {d : BandArcData} (D : SweepData d) : Continuous (tbR D) :=
  D.cont_tb.comp
    (Continuous.subtype_mk (continuous_const.min (continuous_const.max continuous_id)) _)

/-- The width of the retained arc is continuous in the real parameter. -/
lemma wideSig_sweepW'_continuous {d : BandArcData} (D : SweepData d) :
    Continuous (sweepW' D) :=
  (wideSig_tbR_continuous D).sub (wideSig_taR_continuous D)

/-! ## The elementary estimate for an affine function of `(a, w)` -/

/-- If `|c| ≤ 2` then `(a, w) ↦ a + c * w` is `(1, 2)`-Lipschitz. -/
lemma wideSig_abs_add_mul_le (a a' w w' c : ℝ) (hc : |c| ≤ 2) :
    |(a - a') + c * (w - w')| ≤ |a - a'| + 2 * |w - w'| := by
  calc |(a - a') + c * (w - w')| ≤ |a - a'| + |c * (w - w')| := abs_add_le _ _
    _ = |a - a'| + |c| * |w - w'| := by rw [abs_mul]
    _ ≤ |a - a'| + 2 * |w - w'| := by
        have h := mul_le_mul_of_nonneg_right hc (abs_nonneg (w - w'))
        linarith

/-! ## The uniform Lipschitz bound for the matched fraction -/

/-- **The matched fraction is uniformly Lipschitz in the knot datum.**  For every chamfer fraction
`lam ∈ (0, 1/4]` and every loop fraction `u ∈ [0,1]`,

`|wideSfrac a w (period - w) lam u - wideSfrac a' w' (period - w') lam u|
   ≤ |a - a'| + 2 |w - w'|`  (only `0 ≤ u` is needed, as the branch `u ≤ 1/2` supplies the
other bound).

The four branches of `wideSfrac` are affine in `(a, w)`, the branch selection depends only on
`(lam, u)`, and the four slopes in the `w`-variable lie in `[-2, 2]` for `lam ∈ (0, 1/4]`: on the
arc branch the slope is `lam + (1 - 2 lam) * 2u ∈ [lam, 1-lam]`, on the two chamfers it is
`1 - lam` and `lam`, and on the chord branch it is `1 - B` with
`B = lam + (1 - 2 lam) * (u - 1/2 - lam/2)/(1/2 - lam) ∈ [lam, 1-lam]`. -/
lemma wideSig_abs_wideSfrac_sub_le (lam u a a' w w' : ℝ) (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 4)
    (hu0 : 0 ≤ u) :
    |wideSfrac a w (period - w) lam u - wideSfrac a' w' (period - w') lam u|
      ≤ |a - a'| + 2 * |w - w'| := by
  have hc1 : (0 : ℝ) ≤ 1 - 2 * lam := by linarith
  have hd : (0 : ℝ) < 1 / 2 - lam := by linarith
  by_cases hu : u ≤ 1 / 2
  · have hkey : wideSfrac a w (period - w) lam u - wideSfrac a' w' (period - w') lam u
        = (a - a') + (lam + (1 - 2 * lam) * (2 * u)) * (w - w') := by
      rw [wideSfrac_arc hu, wideSfrac_arc hu]; ring
    rw [hkey]
    refine wideSig_abs_add_mul_le _ _ _ _ _ ?_
    have h2u : (0 : ℝ) ≤ 2 * u := by linarith [hu0]
    have h2u1 : 2 * u ≤ 1 := by linarith
    have hup : lam + (1 - 2 * lam) * (2 * u) ≤ 1 - lam := by
      nlinarith [mul_le_mul_of_nonneg_left h2u1 hc1]
    have hlo : lam ≤ lam + (1 - 2 * lam) * (2 * u) := by
      nlinarith [mul_nonneg hc1 h2u]
    rw [abs_le]; constructor <;> linarith
  · by_cases hu2 : u ≤ 1 / 2 + lam / 2
    · have hkey : wideSfrac a w (period - w) lam u - wideSfrac a' w' (period - w') lam u
          = (a - a') + (1 - lam) * (w - w') := by
        rw [wideSfrac_chamfer₁ hu hu2, wideSfrac_chamfer₁ hu hu2]; ring
      rw [hkey]
      refine wideSig_abs_add_mul_le _ _ _ _ _ ?_
      rw [abs_le]; constructor <;> linarith
    · by_cases hu3 : u ≤ 1 - lam / 2
      · have hkey : wideSfrac a w (period - w) lam u - wideSfrac a' w' (period - w') lam u
            = (a - a')
              + (1 - (lam + (1 - 2 * lam) * ((u - (1 / 2 + lam / 2)) / (1 / 2 - lam))))
                * (w - w') := by
          rw [wideSfrac_chord hu hu2 hu3, wideSfrac_chord hu hu2 hu3]; ring
        rw [hkey]
        refine wideSig_abs_add_mul_le _ _ _ _ _ ?_
        have hs0 : 0 ≤ (u - (1 / 2 + lam / 2)) / (1 / 2 - lam) := div_nonneg (by linarith) hd.le
        have hs1 : (u - (1 / 2 + lam / 2)) / (1 / 2 - lam) ≤ 1 :=
          (div_le_one hd).mpr (by linarith)
        have hX0 : lam ≤ lam + (1 - 2 * lam) * ((u - (1 / 2 + lam / 2)) / (1 / 2 - lam)) := by
          nlinarith [mul_nonneg hc1 hs0]
        have hX1 : lam + (1 - 2 * lam) * ((u - (1 / 2 + lam / 2)) / (1 / 2 - lam)) ≤ 1 - lam := by
          nlinarith [mul_le_mul_of_nonneg_left hs1 hc1]
        rw [abs_le]; constructor <;> linarith
      · have hkey : wideSfrac a w (period - w) lam u - wideSfrac a' w' (period - w') lam u
            = (a - a') + lam * (w - w') := by
          rw [wideSfrac_chamfer₂ hu hu2 hu3, wideSfrac_chamfer₂ hu hu2 hu3]; ring
        rw [hkey]
        refine wideSig_abs_add_mul_le _ _ _ _ _ ?_
        rw [abs_le]; constructor <;> linarith

/-! ## The modulus of continuity of the matched phase -/

theorem wideSig_sigma_modulus {d : LeanEval.KnotTheory.Quadrisecant.BandArcData}
    (D : Work.Drive.SweepData d) (σ₀ : ℝ) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ (lam σ τ : ℝ), 0 < lam → lam ≤ 1 / 4 →
      |σ - σ₀| ≤ δ → ‖Work.Drive.wideSig D lam σ τ - Work.Drive.wideSig D lam σ₀ τ‖ ≤ η := by
  intro η hη
  obtain ⟨d₁, hd₁pos, hd₁⟩ :=
    Metric.continuousAt_iff.mp (wideSig_taR_continuous D).continuousAt (η / 3) (by linarith)
  obtain ⟨d₂, hd₂pos, hd₂⟩ :=
    Metric.continuousAt_iff.mp (wideSig_sweepW'_continuous D).continuousAt (η / 3) (by linarith)
  refine ⟨min (d₁ / 2) (d₂ / 2), by positivity, ?_⟩
  intro lam σ τ hlam0 hlam hσ
  have hσ₁ : |σ - σ₀| < d₁ :=
    lt_of_le_of_lt (le_trans hσ (min_le_left (d₁ / 2) (d₂ / 2))) (half_lt_self hd₁pos)
  have hσ₂ : |σ - σ₀| < d₂ :=
    lt_of_le_of_lt (le_trans hσ (min_le_right (d₁ / 2) (d₂ / 2))) (half_lt_self hd₂pos)
  have hA : |taR D σ - taR D σ₀| < η / 3 := by
    have h := hd₁ (x := σ) (by simpa [Real.dist_eq] using hσ₁)
    simpa [Real.dist_eq] using h
  have hB : |sweepW' D σ - sweepW' D σ₀| < η / 3 := by
    have h := hd₂ (x := σ) (by simpa [Real.dist_eq] using hσ₂)
    simpa [Real.dist_eq] using h
  have hkey : wideSig D lam σ τ - wideSig D lam σ₀ τ
      = wideSfrac (taR D σ) (sweepW' D σ) (period - sweepW' D σ) lam (sweepParam τ)
        - wideSfrac (taR D σ₀) (sweepW' D σ₀) (period - sweepW' D σ₀) lam (sweepParam τ) := by
    simp only [wideSig, wideSigma]
    ring
  have hlip := wideSig_abs_wideSfrac_sub_le lam (sweepParam τ) (taR D σ) (taR D σ₀)
    (sweepW' D σ) (sweepW' D σ₀) hlam0 hlam (sweepParam_mem τ).1
  rw [hkey, Real.norm_eq_abs]
  calc |wideSfrac (taR D σ) (sweepW' D σ) (period - sweepW' D σ) lam (sweepParam τ)
        - wideSfrac (taR D σ₀) (sweepW' D σ₀) (period - sweepW' D σ₀) lam (sweepParam τ)|
      ≤ |taR D σ - taR D σ₀| + 2 * |sweepW' D σ - sweepW' D σ₀| := hlip
    _ ≤ η / 3 + 2 * (η / 3) := by linarith
    _ ≤ η := by linarith

end Work.Drive
