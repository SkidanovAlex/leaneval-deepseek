import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Submission.Work.BoseKinLoc.Momentum.cubFT_1d
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Bounds on the one-dimensional factors `hFT`, `mFT` of the cube Fourier symbol

This module proves the four elementary estimates recorded in the header of
`Work.BoseKinLoc.Momentum.cubFT_1d` (Fournais–Solovej, *The energy of dilute Bose gases*,
§"Localization of the kinetic and potential energies"):

    `|hFT t| ≤ 1`,  `|t * hFT t| ≤ 2`,  `|mFT t| ≤ 1/2`,  `|t * mFT t| ≤ 2`,

where `hFT t = ∫_{-1/2}^{1/2} cos (t s) ds` and `mFT t = ∫_{-1/2}^{1/2} s sin (t s) ds`.

Two of the four estimates are proved from the closed forms

    `t * hFT t = 2 * sin (t / 2)`                  (fundamental theorem of calculus),
    `t * mFT t = hFT t - cos (t / 2)`              (integration by parts),

the other two from the crude pointwise bounds `|cos| ≤ 1`, `|s| ≤ 1/2`, `|sin| ≤ 1`.  Both
closed forms are proved here in the `_aux` variants (they are also requested as standalone
lemmas of the library, `hFT_mul_eq` and `mFT_mul_eq`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Momentum

/-- Crude integral bound: a function bounded by `C` on `[-1/2, 1/2]` has integral of absolute
value at most `C` there (the interval has length `1`). -/
lemma abs_setIntegral_Icc_le (f : ℝ → ℝ) (C : ℝ)
    (h : ∀ x ∈ Set.Icc (-(1 / 2)) (1 / 2), |f x| ≤ C) :
    |∫ x in Set.Icc (-(1 / 2)) (1 / 2), f x| ≤ C := by
  have hfin : (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      (Set.Icc (-(1 / 2)) (1 / 2)) < ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  have h' : ∀ x ∈ Set.Icc (-(1 / 2)) (1 / 2), ‖f x‖ ≤ C := by
    intro x hx; rw [Real.norm_eq_abs]; exact h x hx
  have h1 := MeasureTheory.norm_setIntegral_le_of_norm_le_const
    (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) hfin h'
  rw [Real.norm_eq_abs] at h1
  have h2 : (MeasureTheory.volume : MeasureTheory.Measure ℝ).real
      (Set.Icc (-(1 / 2)) (1 / 2)) = 1 := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2 - -(1 / 2))]
    norm_num
  rw [h2, mul_one] at h1
  exact h1

/-- The set integral over `Set.Icc a b` is the interval integral from `a` to `b`. -/
lemma setIntegral_Icc_eq_intervalIntegral (a b : ℝ) (hab : a ≤ b) (g : ℝ → ℝ) :
    ∫ x in Set.Icc a b, g x = ∫ x in a..b, g x := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

/-- **Closed form of `t * hFT t`** (fundamental theorem of calculus): `t hFT t = 2 sin (t/2)`. -/
lemma hFT_mul_eq_aux (t : ℝ) : t * hFT t = 2 * Real.sin (t / 2) := by
  rw [hFT, setIntegral_Icc_eq_intervalIntegral (-(1 / 2)) (1 / 2) (by norm_num)
        (fun x => Real.cos (t * x))]
  rw [← intervalIntegral.integral_const_mul]
  have hder : deriv (fun x : ℝ => Real.sin (t * x)) = fun x => t * Real.cos (t * x) := by
    funext x
    have h1 : HasDerivAt (fun x : ℝ => t * x) t x := by
      simpa using (hasDerivAt_id x).const_mul t
    have h2 : HasDerivAt (fun x : ℝ => Real.sin (t * x)) (Real.cos (t * x) * t) x := h1.sin
    rw [h2.deriv]; ring
  rw [← hder]
  rw [intervalIntegral.integral_deriv_eq_sub (f := fun x : ℝ => Real.sin (t * x))]
  · have h1 : t * (-(1 / 2)) = -(t / 2) := by ring
    have h2 : t * (1 / 2) = t / 2 := by ring
    rw [h1, h2, Real.sin_neg]
    ring
  · intro x _
    exact ((hasDerivAt_id x).const_mul t).sin.differentiableAt
  · rw [hder]
    exact (by fun_prop : Continuous fun x : ℝ => t * Real.cos (t * x)).intervalIntegrable _ _

/-- **Closed form of `t * mFT t`** (integration by parts): `t mFT t = hFT t - cos (t/2)`. -/
lemma mFT_mul_eq_aux (t : ℝ) : t * mFT t = hFT t - Real.cos (t / 2) := by
  have hconv1 := setIntegral_Icc_eq_intervalIntegral (-(1 / 2)) (1 / 2) (by norm_num)
    (fun x => x * Real.sin (t * x))
  have hconv2 := setIntegral_Icc_eq_intervalIntegral (-(1 / 2)) (1 / 2) (by norm_num)
    (fun x => Real.cos (t * x))
  rw [mFT, hFT, hconv1, hconv2, ← intervalIntegral.integral_const_mul]
  have hder_u : ∀ x ∈ Set.uIcc (-(1 / 2)) (1 / 2),
      HasDerivAt (fun x : ℝ => Real.cos (t * x)) (-(t * Real.sin (t * x))) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => t * x) t x := by
      simpa using (hasDerivAt_id x).const_mul t
    have h2 := h1.cos
    convert h2 using 1
    ring
  have hder_v : ∀ x ∈ Set.uIcc (-(1 / 2)) (1 / 2), HasDerivAt (fun x : ℝ => x) (1 : ℝ) x :=
    fun x _ => hasDerivAt_id x
  have hint_u' :
      IntervalIntegrable (fun x : ℝ => -(t * Real.sin (t * x))) volume (-(1 / 2)) (1 / 2) :=
    (by fun_prop : Continuous fun x : ℝ => -(t * Real.sin (t * x))).intervalIntegrable _ _
  have hint_v' : IntervalIntegrable (fun x : ℝ => (1 : ℝ)) volume (-(1 / 2)) (1 / 2) :=
    continuous_const.intervalIntegrable _ _
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hder_u hder_v hint_u' hint_v'
  have hbnd : Real.cos (t * (1 / 2)) * (1 / 2) - Real.cos (t * (-(1 / 2))) * (-(1 / 2))
      = Real.cos (t / 2) := by
    rw [show t * (1 / 2) = t / 2 by ring, show t * (-(1 / 2)) = -(t / 2) by ring, Real.cos_neg]
    ring
  have hInt : ∫ x in (-(1 / 2))..(1 / 2), (-(t * Real.sin (t * x))) * x
      = -(t * ∫ x in (-(1 / 2))..(1 / 2), x * Real.sin (t * x)) := by
    rw [show (fun x : ℝ => (-(t * Real.sin (t * x))) * x)
          = (fun x : ℝ => -(t * (x * Real.sin (t * x)))) from by funext x; ring]
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
  have hmain : ∫ x in (-(1 / 2))..(1 / 2), Real.cos (t * x)
      = Real.cos (t / 2) + t * ∫ x in (-(1 / 2))..(1 / 2), x * Real.sin (t * x) := by
    rw [show (∫ x in (-(1 / 2))..(1 / 2), Real.cos (t * x) * 1)
        = ∫ x in (-(1 / 2))..(1 / 2), Real.cos (t * x) from by simp] at hibp
    rw [hbnd, hInt] at hibp
    linarith
  rw [intervalIntegral.integral_const_mul]
  linarith

/-- `|hFT t| ≤ 1`. -/
lemma hFT_abs_le_one (t : ℝ) : |hFT t| ≤ 1 := by
  rw [hFT]
  exact abs_setIntegral_Icc_le _ 1 fun x _ => by simpa using Real.abs_cos_le_one (t * x)

/-- `|t * hFT t| ≤ 2`. -/
lemma hFT_mul_abs_le (t : ℝ) : |t * hFT t| ≤ 2 := by
  rw [hFT_mul_eq_aux t, abs_mul, show |(2 : ℝ)| = 2 from by norm_num]
  linarith [Real.abs_sin_le_one (t / 2)]

/-- `|mFT t| ≤ 1/2`. -/
lemma mFT_abs_le_half (t : ℝ) : |mFT t| ≤ 1 / 2 := by
  rw [mFT]
  refine abs_setIntegral_Icc_le _ (1 / 2) fun x hx => ?_
  have hx1 : |x| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  calc |x * Real.sin (t * x)| = |x| * |Real.sin (t * x)| := abs_mul _ _
    _ ≤ (1 / 2) * 1 := mul_le_mul hx1 (Real.abs_sin_le_one _) (abs_nonneg _) (by norm_num)
    _ = 1 / 2 := by norm_num

/-- `|t * mFT t| ≤ 2`. -/
lemma mFT_mul_abs_le (t : ℝ) : |t * mFT t| ≤ 2 := by
  rw [mFT_mul_eq_aux t]
  calc |hFT t - Real.cos (t / 2)| ≤ |hFT t| + |Real.cos (t / 2)| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add (hFT_abs_le_one t) (Real.abs_cos_le_one _)
    _ = 2 := by norm_num

theorem hFT_bounds :
    (∀ t : ℝ, |hFT t| ≤ 1) ∧ (∀ t : ℝ, |t * hFT t| ≤ 2) ∧
    (∀ t : ℝ, |mFT t| ≤ 1 / 2) ∧ (∀ t : ℝ, |t * mFT t| ≤ 2) :=
  ⟨hFT_abs_le_one, hFT_mul_abs_le, mFT_abs_le_half, mFT_mul_abs_le⟩

end Work.BoseKinLoc.Momentum
