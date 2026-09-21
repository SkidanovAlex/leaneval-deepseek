import Mathlib
import Submission.Work.OddBridge.Defs
import Submission.Work.OddVolterra.KernelExt.Kden_pos_of_curve

/-!
# Positivity of the Abel denominator radicand on the transition-slope curve

The two Abel kernels `K₁ = J₁ / √((t + H(s,σ)) · (L(σ,t) + L(s,t)))` have the square root of
the product

`(t + H(s,σ)) · (L(σ,t) + L(s,t))`,   `H(s,σ) = hquot h s σ = ∫_0^1 h'(s + τ(σ-s)) dτ`,

as denominator, evaluated at the two intersection points `t = y σ` and `t = -(x σ)` of the
line of slope `σ` with the envelope.  Positivity of that product at those points is what makes
`Kden` strictly positive, hence what makes the manifest kernels smooth on a box.

The estimates are the ones of `Work.OddVolterra.KernelExt.Kden_pos_of_curve_support`:

* `y σ, x σ ≥ 1/2 - 1/100 > 0` (`CurveData.close_y`, `CurveData.close_x` and
  `profileX ≥ 1/2` on `[-1,1]`), and `|hquot h s σ| ≤ 1/100`, `|h z| ≤ 1/100`;
* the support hypothesis `support h ⊆ [1 - 2τ, 1 - τ] = [4/5, 9/10]`: whenever `σ + s < 4/5`
  both slopes lie below the support, so `h σ = h s = 0` and the second factor collapses to
  `(σ+s) y σ > 0` (respectively `-(σ+s) x σ < 0`);
* when `σ + s ≥ 4/5`, the crude bound `(σ+s)(1/2 - 1/100) ≥ (4/5)(49/100) > 2/100 ≥ |h σ|+|h s|`
  gives the same conclusion.

This version covers the whole slope window `0 < s, σ ≤ 1` (no positive lower bound on the
slopes), which is the form consumed by the smoothness of the Abel kernels near `s = 0`.
No differentiability of `h` beyond the pointwise bounds in `CurveData` is used.
-/

namespace Work.OddBridge

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

open Work.OddVolterra
open Commons.Geometry.Ulam

noncomputable section

theorem Kden_radicand_pos_of_curve (n : ℕ) {h x y : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hhsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hdata : Work.OddVolterra.CurveData n h x y) :
    (∀ s σ : ℝ, 0 < s → 0 < σ → s ≤ 1 → σ ≤ 1 →
      0 < (y σ + Work.OddVolterra.hquot h s σ) *
        (Work.OddVolterra.line h σ (y σ) + Work.OddVolterra.line h s (y σ))) ∧
    (∀ s σ : ℝ, 0 < s → 0 < σ → s ≤ 1 → σ ≤ 1 →
      0 < (-(x σ) + Work.OddVolterra.hquot h s σ) *
        (Work.OddVolterra.line h σ (-(x σ)) + Work.OddVolterra.line h s (-(x σ)))) := by
  -- `h` vanishes strictly below the transition window: `support h ⊆ [4/5, 9/10]`.
  have hzero : ∀ z : ℝ, z < 4 / 5 → h z = 0 := by
    intro z hz
    by_contra hne
    have hmem : z ∈ Set.Icc (1 - 2 * Work.OddVolterra.tau)
        (1 - Work.OddVolterra.tau) := hhsupp hne
    have h1 : (1 : ℝ) - 2 * Work.OddVolterra.tau ≤ z := hmem.1
    rw [Work.OddVolterra.tau] at h1
    norm_num at h1
    linarith
  have hderiv : ∀ z : ℝ, |deriv h z| ≤ 1 / 100 := fun z => (hdata.close_h z).2.1
  constructor
  · intro s σ hs hσ hs1 hσ1
    have hpX : (1 : ℝ) / 2 ≤ profileX σ :=
      Work.OddVolterra.KernelExt.profileX_ge_half (by rw [abs_of_pos hσ]; linarith)
    have hy : (49 : ℝ) / 100 ≤ y σ := by
      have h := (abs_le.mp (hdata.close_y σ hσ).1).1
      linarith
    have hq : |hquot h s σ| ≤ 1 / 100 :=
      Work.OddVolterra.KernelExt.abs_hquot_le hderiv s σ
    have hqs : -(1 / 100) ≤ hquot h s σ := (abs_le.mp hq).1
    have hσh : -(1 / 100) ≤ h σ := (abs_le.mp (hdata.close_h σ).1).1
    have hsh : -(1 / 100) ≤ h s := (abs_le.mp (hdata.close_h s).1).1
    have hσs : 0 < σ + s := by linarith
    have hA : 0 < y σ + hquot h s σ := by linarith
    have hB : 0 < line h σ (y σ) + line h s (y σ) := by
      rw [line, line]
      by_cases hcase : (4 : ℝ) / 5 ≤ σ + s
      · nlinarith [hcase, hy, hσh, hsh]
      · have hσ0 : h σ = 0 := hzero σ (by linarith)
        have hs0 : h s = 0 := hzero s (by linarith)
        have heq : σ * y σ + h σ + (s * y σ + h s) = (σ + s) * y σ := by
          rw [hσ0, hs0]; ring
        rw [heq]
        exact mul_pos hσs (by linarith)
    exact mul_pos hA hB
  · intro s σ hs hσ hs1 hσ1
    have hpX : (1 : ℝ) / 2 ≤ profileX σ :=
      Work.OddVolterra.KernelExt.profileX_ge_half (by rw [abs_of_pos hσ]; linarith)
    have hx : (49 : ℝ) / 100 ≤ x σ := by
      have h := (abs_le.mp (hdata.close_x σ hσ).1).1
      linarith
    have hq : |hquot h s σ| ≤ 1 / 100 :=
      Work.OddVolterra.KernelExt.abs_hquot_le hderiv s σ
    have hqs : hquot h s σ ≤ 1 / 100 := (abs_le.mp hq).2
    have hσh : h σ ≤ 1 / 100 := (abs_le.mp (hdata.close_h σ).1).2
    have hsh : h s ≤ 1 / 100 := (abs_le.mp (hdata.close_h s).1).2
    have hσs : 0 < σ + s := by linarith
    have hA : -(x σ) + hquot h s σ < 0 := by linarith
    have hB : line h σ (-(x σ)) + line h s (-(x σ)) < 0 := by
      rw [line, line]
      by_cases hcase : (4 : ℝ) / 5 ≤ σ + s
      · nlinarith [hcase, hx, hσh, hsh]
      · have hσ0 : h σ = 0 := hzero σ (by linarith)
        have hs0 : h s = 0 := hzero s (by linarith)
        have heq : σ * (-(x σ)) + h σ + (s * (-(x σ)) + h s) = -((σ + s) * x σ) := by
          rw [hσ0, hs0]; ring
        rw [heq]
        nlinarith [mul_pos hσs (by linarith : (0 : ℝ) < x σ)]
    exact mul_pos_of_neg_of_neg hA hB

end

end Work.OddBridge
