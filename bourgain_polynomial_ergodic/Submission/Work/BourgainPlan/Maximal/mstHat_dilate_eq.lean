import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_freeze_defs

open MeasureTheory

namespace Work.BourgainPlan.Maximal

/-- **Truncation of an interval integral for a function vanishing off the unit fundamental
interval.**  If `g` vanishes outside `[−1/2, 1/2]` (more precisely: `g x = 0` as soon as
`1/2 < |x|`), then the interval integral of `g` over any interval `(a, b)` containing
`(−1/2, 1/2)` equals its integral over `(−1/2, 1/2)`.

The proof names the two intervals as `Set.Ioc` sets and uses
`MeasureTheory.setIntegral_eq_of_subset_of_ae_sdiff_eq_zero`: on the difference
`Ioc a b \ Ioc (−1/2) (1/2)` the function vanishes except possibly at the single point `−1/2`,
which is null for Lebesgue measure. -/
lemma intervalIntegral_eq_of_vanishes_off_fundamental {g : ℝ → ℂ}
    (hg : ∀ x : ℝ, 1 / 2 < |x| → g x = 0) {a b : ℝ} (ha : a ≤ -(1 / 2))
    (hb : (1 / 2 : ℝ) ≤ b) :
    (∫ x in a..b, g x) = ∫ x in (-(1 / 2))..(1 / 2), g x := by
  rw [intervalIntegral.integral_of_le (by linarith : a ≤ b),
      intervalIntegral.integral_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)]
  refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioc.nullMeasurableSet ?_ ?_
  · intro x hx
    simp only [Set.mem_Ioc] at hx ⊢
    exact ⟨lt_of_le_of_lt ha hx.1, le_trans hx.2 hb⟩
  · filter_upwards [volume.ae_ne (-(1 / 2) : ℝ)] with x hxne hxmem
    simp only [Set.mem_sdiff, Set.mem_Ioc] at hxmem
    obtain ⟨⟨_, _⟩, hns⟩ := hxmem
    rw [not_and_or] at hns
    rcases hns with h | h
    · have hx : x < -(1 / 2) := lt_of_le_of_ne (le_of_not_gt h) hxne
      exact hg x (by rw [lt_abs]; exact Or.inr (by linarith))
    · have hx : (1 / 2 : ℝ) < x := not_le.mp h
      exact hg x (by rw [lt_abs]; exact Or.inl hx)

/-- **The dilation dictionary of the freezing estimate.**  For `Λ` supported in `|w| ≤ 1/2`
(so that it is the fundamental-domain lift of a circle function) and `c ≥ 1`,

`mstHat Λ (t/c) = c ∫_{−1/2}^{1/2} Λ (c u) e^{−2πi t u} du`.

Route: substitute `w = c u` in the defining integral `mstHat Λ (t/c) = ∫_{−1/2}^{1/2} Λ w
e^{−2πi (t/c) w} dw` (`intervalIntegral.integral_comp_mul_left`), getting the integral over
`(−c/2, c/2)`, and truncate back to `(−1/2, 1/2)` with `intervalIntegral_eq_of_support`
(`1 ≤ c` gives `Λ w = 0` for `1/2 < |w| ≤ c/2`). -/
theorem mstHat_dilate_eq (Λ : ℝ → ℂ) (c t : ℝ) (hc : 1 ≤ c)
    (hΛ : ∀ w : ℝ, 1 / 2 < |w| → Λ w = 0) :
    Work.BourgainPlan.Maximal.mstHat Λ (t / c) = c * ∫ u in (-(1 / 2))..(1 / 2), Λ (c * u) *
      Complex.exp ((((-(2 * Real.pi * (t * u))) : ℝ) : ℂ) * Complex.I) := by
  have hc0 : c ≠ 0 := by linarith
  -- the arithmetic identity behind the substitution
  have hπ : ∀ x : ℝ, 2 * Real.pi * (t / c) * (c * x) = 2 * Real.pi * (t * x) := by
    intro x; field_simp
  -- the integrand of the defining integral, as a named function
  set f : ℝ → ℂ :=
    fun w => Λ w * Complex.exp ((((-(2 * Real.pi * (t / c) * w)) : ℝ) : ℂ) * Complex.I) with hf
  have hfzero : ∀ w : ℝ, 1 / 2 < |w| → f w = 0 := by
    intro w hw
    simp only [hf]
    rw [hΛ w hw, zero_mul]
  -- the interval `(−c/2, c/2)` carries the same integral as `(−1/2, 1/2)`
  have htrunc : (∫ w in (-(c / 2))..(c / 2), f w) = ∫ w in (-(1 / 2))..(1 / 2), f w :=
    intervalIntegral_eq_of_vanishes_off_fundamental (g := f) hfzero
      (by linarith : -(c / 2) ≤ -(1 / 2)) (by linarith : (1 / 2 : ℝ) ≤ c / 2)
  have hL : Work.BourgainPlan.Maximal.mstHat Λ (t / c)
      = ∫ w in (-(1 / 2))..(1 / 2), f w := by
    rw [Work.BourgainPlan.Maximal.mstHat_apply]
  rw [hL, ← htrunc]
  -- substitute `w = c u`
  have hsub : (∫ w in (-(c / 2))..(c / 2), f w) = c • ∫ u in (-(1 / 2))..(1 / 2), f (c * u) := by
    have h := intervalIntegral.smul_integral_comp_mul_left (f := f) (a := -(1 / 2)) (b := 1 / 2) c
    rw [show c * (-(1 / 2)) = -(c / 2) by ring, show c * (1 / 2) = c / 2 by ring] at h
    exact h.symm
  rw [hsub]
  -- identify the substituted integrand
  have hcongr : (∫ u in (-(1 / 2))..(1 / 2), f (c * u)) =
      ∫ u in (-(1 / 2))..(1 / 2), Λ (c * u) *
        Complex.exp ((((-(2 * Real.pi * (t * u))) : ℝ) : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only [hf]
    rw [hπ x]
  rw [hcongr, Complex.real_smul]

end Work.BourgainPlan.Maximal
