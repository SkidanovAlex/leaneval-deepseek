import Mathlib
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.Assembly
import Submission.Work.OddVolterra.Estimates

/-!
# Positivity of the Abel denominator on the transition-slope curve

`Kden h s σ t = √((t + H(s,σ)) · (L(σ,t) + L(s,t)))`, and the Abel kernels `K₁`, `K₂`
are `J / Kden`.  For the manifest representative `KvecM` to be smooth on a box one needs
`Kden h s σ t > 0` there; since `Kden` is a square root this is exactly positivity of the
product of the two factors.

The two points at which `Kden` is evaluated are `t = y σ` (the upper intersection of the
line of slope `σ` with the curve) and `t = -(x σ)` (the lower one).  In the unperturbed
(ball) case `x = y = profileX` the two factors are `profileX σ + 0 > 0`,
`(σ+s) profileX σ > 0` at the upper point and minus those at the lower point.  The
`CurveData` hypotheses say precisely that the perturbation is small enough for this to
survive: `|h| ≤ 1/100`, `|h'| ≤ 1/100` and `|y σ - profileX σ| ≤ 1/100`,
`|x σ - profileX σ| ≤ 1/100`.  The crude bounds available on the window `[1/2,1]` are

* `profileX σ ≥ 1/2` for `σ ≤ 1`,
* `|hquot h s σ| ≤ 1/100` (an average of `deriv h`),
* `(σ + s) ≥ 1` for `s, σ ≥ 1/2`,

which give `t + H ≥ 1/2 - 1/50 > 0`, `L(σ,t) + L(s,t) ≥ 47/100 > 0` at the upper point
and their negatives at the lower point.  Hence both factors have the same (strict) sign
at either point and the product is positive.
-/

namespace Work.OddVolterra.KernelExt

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

open Work.OddVolterra
open Commons.Geometry.Ulam

noncomputable section

/-- The average `hquot h s σ = ∫_0^1 h'(s + τ(σ-s)) dτ` of `deriv h` is bounded by any
pointwise bound for `deriv h`. -/
lemma abs_hquot_le {h : ℝ → ℝ} {C : ℝ} (hC : ∀ x : ℝ, |deriv h x| ≤ C) (s σ : ℝ) :
    |hquot h s σ| ≤ C := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun τ : ℝ => deriv h (s + τ * (σ - s))) (C := C) (a := (0 : ℝ)) (b := 1)
    (fun x _ => by simpa [Real.norm_eq_abs] using hC (s + x * (σ - s)))
  rw [hquot]
  simpa using h

/-- On the slope window `[-1,1]` the section function of the ball is at least `1/2`. -/
lemma profileX_ge_half {σ : ℝ} (hσ : |σ| ≤ 1) : (1 : ℝ) / 2 ≤ profileX σ := by
  have hpos : 0 < profileX σ := Commons.Geometry.Ulam.profileX_pos' σ
  have h4 : (1 : ℝ) / 4 ≤ profileX σ ^ 2 := by
    rw [Commons.Geometry.Ulam.profileX_sq]
    have hσ2 : σ ^ 2 ≤ 1 := by nlinarith [abs_le.mp hσ]
    have hle : 1 + σ ^ 2 ≤ 4 := by nlinarith [hσ2]
    have h1 : (1 : ℝ) / 4 ≤ 1 / (1 + σ ^ 2) := by
      rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 4) (by positivity : (0:ℝ) < 1 + σ ^ 2)]
      linarith
    linarith [h1]
  nlinarith [h4, hpos]

theorem Kden_pos_of_curve (n : ℕ) {h x y : ℝ → ℝ} {a : ℝ} (ha : 1/2 ≤ a)
    (hdata : Work.OddVolterra.CurveData n h x y) :
    (∀ s σ : ℝ, s ∈ Set.Icc a 1 → σ ∈ Set.Icc a 1 → 0 < Work.OddVolterra.Kden h s σ (y σ)) ∧
    (∀ s σ : ℝ, s ∈ Set.Icc a 1 → σ ∈ Set.Icc a 1 → 0 < Work.OddVolterra.Kden h s σ (-(x σ))) := by
  have hCh : ∀ z : ℝ, |deriv h z| ≤ 1 / 100 := fun z => (hdata.close_h z).2.1
  constructor
  · intro s σ hs hσ
    have hσpos : 0 < σ := by linarith [ha, hσ.1]
    have hspos : 0 < s := by linarith [ha, hs.1]
    have hpX : (1 : ℝ) / 2 ≤ profileX σ := profileX_ge_half (by
      rw [abs_le]; constructor <;> linarith [hσ.1, hσ.2, ha])
    have hy : profileX σ - 1 / 100 ≤ y σ := by
      have h := (abs_le.mp (hdata.close_y σ hσpos).1).1
      linarith
    have hq : |hquot h s σ| ≤ 1 / 100 := abs_hquot_le hCh s σ
    have hqs := (abs_le.mp hq).1
    have hspan : (1 : ℝ) ≤ σ + s := by linarith [hσ.1, hs.1, ha]
    have hhσ := (abs_le.mp (hdata.close_h σ).1).1
    have hhs := (abs_le.mp (hdata.close_h s).1).1
    have hA : 0 < y σ + hquot h s σ := by linarith
    have hB : 0 < line h σ (y σ) + line h s (y σ) := by
      simp only [line]
      nlinarith [hspan, hpX, hy, hhσ, hhs]
    rw [Work.OddVolterra.Kden]
    exact Real.sqrt_pos.mpr (mul_pos hA hB)
  · intro s σ hs hσ
    have hσpos : 0 < σ := by linarith [ha, hσ.1]
    have hspos : 0 < s := by linarith [ha, hs.1]
    have hpX : (1 : ℝ) / 2 ≤ profileX σ := profileX_ge_half (by
      rw [abs_le]; constructor <;> linarith [hσ.1, hσ.2, ha])
    have hx : profileX σ - 1 / 100 ≤ x σ := by
      have h := (abs_le.mp (hdata.close_x σ hσpos).1).1
      linarith
    have hq : |hquot h s σ| ≤ 1 / 100 := abs_hquot_le hCh s σ
    have hqs : hquot h s σ ≤ 1 / 100 := (abs_le.mp hq).2
    have hspan : (1 : ℝ) ≤ σ + s := by linarith [hσ.1, hs.1, ha]
    have hhσ : h σ ≤ 1 / 100 := (abs_le.mp (hdata.close_h σ).1).2
    have hhs : h s ≤ 1 / 100 := (abs_le.mp (hdata.close_h s).1).2
    have hA : -(x σ) + hquot h s σ < 0 := by linarith
    have hB : line h σ (-(x σ)) + line h s (-(x σ)) < 0 := by
      simp only [line]
      nlinarith [hspan, hpX, hx, hhσ, hhs]
    rw [Work.OddVolterra.Kden]
    exact Real.sqrt_pos.mpr (mul_pos_of_neg_of_neg hA hB)

end

end Work.OddVolterra.KernelExt
