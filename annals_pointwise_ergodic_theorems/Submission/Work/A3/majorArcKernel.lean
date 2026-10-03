import Mathlib
import Submission.Work.A3.Circle

/-!
# The comparison kernel of the major-arc bound (Area A3)

This module defines the elementary function

  `mArcKernel N d β = (|β| + N^{-d})^{-1/d}`

which is the size of the singular integral `v(β) = ∫₀^N e(-β Q(t)) dt` for a polynomial `Q` of
degree `d`: it equals `N` at `β = 0` and behaves like `|β|^{-1/d}` for `|β| ≥ N^{-d}` (the
additive regularisation `N^{-d}` is needed because Lean's `x ^ y` gives `0` at `x = 0` for
negative `y`, whereas the true decay of `|β|^{-1/d}` is to `+∞`).

* `mArcKernel_le_N` : `mArcKernel N d β ≤ N`;
* `mArcKernel_le`   : `mArcKernel N d β ≤ |β|^{-1/d}` for `β ≠ 0`;
* `mArcKernel_pos`  : `0 < mArcKernel N d β`;
* `mArcKernel_pow`  : `(mArcKernel N d β)^{2s} = (|β| + N^{-d})^{-(2s)/d}`.
-/

set_option autoImplicit false

namespace Work.A3

open Polynomial Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- The comparison kernel `(|β| + N^{-d})^{-1/d}` of the major-arc bound: the size of the
singular integral `∫₀^N e(-β Q(t)) dt` for a polynomial of degree `d`. -/
def mArcKernel (N d : ℕ) (β : ℝ) : ℝ :=
  (|β| + (N : ℝ) ^ (-(d : ℝ))) ^ (-(1 : ℝ) / (d : ℝ))

/-- The kernel is at most `N`. -/
lemma mArcKernel_le_N {N d : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d) (β : ℝ) :
    mArcKernel N d β ≤ (N : ℝ) := by
  rw [mArcKernel]
  have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hx : 0 < (N:ℝ)^(-(d:ℝ)) := Real.rpow_pos_of_pos hN0 _
  have hxy : (N:ℝ)^(-(d:ℝ)) ≤ |β| + (N:ℝ)^(-(d:ℝ)) := le_add_of_nonneg_left (abs_nonneg β)
  have hz : (-(1:ℝ)/(d:ℝ)) ≤ 0 := by
    rw [neg_div]; exact neg_nonpos.mpr (div_nonneg zero_le_one hd0.le)
  refine (Real.rpow_le_rpow_of_nonpos hx hxy hz).trans (le_of_eq ?_)
  rw [← Real.rpow_mul (le_of_lt hN0)]
  have hkey : (-(d:ℝ)) * (-(1:ℝ)/(d:ℝ)) = 1 := by
    rw [neg_div]
    field_simp
  rw [hkey, Real.rpow_one]

/-- For `β ≠ 0` the kernel is at most `|β|^{-1/d}`. -/
lemma mArcKernel_le {N d : ℕ} (hd : 1 ≤ d) {β : ℝ} (hβ : β ≠ 0) :
    mArcKernel N d β ≤ |β| ^ (-(1 : ℝ) / (d : ℝ)) := by
  rw [mArcKernel]
  have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have habs : 0 < |β| := abs_pos.mpr hβ
  have hxy : |β| ≤ |β| + (N:ℝ)^(-(d:ℝ)) := le_add_of_nonneg_right (by positivity)
  have hz : (-(1:ℝ)/(d:ℝ)) ≤ 0 := by
    rw [neg_div]; exact neg_nonpos.mpr (div_nonneg zero_le_one hd0.le)
  exact Real.rpow_le_rpow_of_nonpos habs hxy hz

/-- The kernel is strictly positive. -/
lemma mArcKernel_pos {N d : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d) (β : ℝ) :
    0 < mArcKernel N d β := by
  rw [mArcKernel]
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hc : 0 < (N:ℝ)^(-(d:ℝ)) := Real.rpow_pos_of_pos hN0 _
  have hb : 0 < |β| + (N:ℝ)^(-(d:ℝ)) := by linarith [abs_nonneg β, hc]
  exact Real.rpow_pos_of_pos hb _

/-- Powers of the kernel reduce to a single `rpow` of the base. -/
lemma mArcKernel_pow {N d s : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d) (β : ℝ) :
    (mArcKernel N d β) ^ (2*s) = (|β| + (N:ℝ)^(-(d:ℝ))) ^ (-((2*s:ℝ)/(d:ℝ))) := by
  rw [mArcKernel]
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hc : 0 < (N:ℝ)^(-(d:ℝ)) := Real.rpow_pos_of_pos hN0 _
  have hb : (0:ℝ) ≤ |β| + (N:ℝ)^(-(d:ℝ)) := by linarith [abs_nonneg β, hc]
  rw [← Real.rpow_natCast ((|β| + (N:ℝ)^(-(d:ℝ))) ^ (-(1:ℝ)/(d:ℝ))) (2*s),
      ← Real.rpow_mul hb]
  have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  congr 1
  field_simp
  push_cast
  ring

end

end Work.A3
