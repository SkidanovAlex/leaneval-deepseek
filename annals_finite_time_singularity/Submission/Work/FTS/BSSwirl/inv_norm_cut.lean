/-
# The smooth cutoff used by `Work.FTS.BSSwirl.integral_inv_norm_mul_laplacian`

This module defines the smooth step `fcut : ℝ → ℝ` (equal to `0` on `(-∞,1]`, to `1` on
`[2,∞)`), together with the elementary facts about it that the proof of

  `∫ z, ‖z‖⁻¹ * Δψ z = -4π ψ 0`   (`ψ` smooth, compactly supported)

needs: its values, its smoothness, and the vanishing of its derivatives outside `[1,2]`.
-/
import Mathlib

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Topology
open scoped Topology NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.BSSwirl

noncomputable section

/-- The smooth step: `fcut t = 0` for `t ≤ 1`, `fcut t = 1` for `t ≥ 2`. -/
def fcut (t : ℝ) : ℝ := Real.smoothTransition (t - 1)

lemma fcut_of_le_one {t : ℝ} (ht : t ≤ 1) : fcut t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma fcut_of_two_le {t : ℝ} (ht : 2 ≤ t) : fcut t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

@[simp] lemma fcut_zero : fcut 0 = 0 := fcut_of_le_one (by norm_num)

@[simp] lemma fcut_one : fcut 1 = 0 := fcut_of_le_one le_rfl

@[simp] lemma fcut_three : fcut 3 = 1 := fcut_of_two_le (by norm_num)

/-- `fcut` is smooth (indeed `C^n` for every `n`). -/
lemma contDiff_fcut (n : ℕ) : ContDiff ℝ n fcut := by
  unfold fcut
  exact (Real.smoothTransition.contDiff (n := (n : ℕ∞))).comp
    (contDiff_id.sub contDiff_const)

lemma contDiffAt_fcut (t : ℝ) (n : ℕ) : ContDiffAt ℝ n fcut t :=
  (contDiff_fcut n).contDiffAt

lemma fcut_nonneg (t : ℝ) : 0 ≤ fcut t := Real.smoothTransition.nonneg _

lemma fcut_le_one (t : ℝ) : fcut t ≤ 1 := Real.smoothTransition.le_one _

lemma fcut_monotone : Monotone fcut := fun _ _ h => Real.smoothTransition.monotone (by linarith)

/-- `fcut` is (eventually) the constant `0` to the left of `1`. -/
lemma fcut_eventuallyEq_zero {t : ℝ} (ht : t < 1) : fcut =ᶠ[𝓝 t] 0 := by
  filter_upwards [Iio_mem_nhds ht] with s hs
  exact fcut_of_le_one hs.le

/-- `fcut` is (eventually) the constant `1` to the right of `2`. -/
lemma fcut_eventuallyEq_one {t : ℝ} (ht : 2 < t) : fcut =ᶠ[𝓝 t] 1 := by
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact fcut_of_two_le hs.le

lemma deriv_fcut_eq_zero_of_lt_one {t : ℝ} (ht : t < 1) : deriv fcut t = 0 := by
  have h := (fcut_eventuallyEq_zero ht).deriv_eq
  simpa using h

lemma deriv_fcut_eq_zero_of_gt_two {t : ℝ} (ht : 2 < t) : deriv fcut t = 0 := by
  have h := (fcut_eventuallyEq_one ht).deriv_eq
  simpa using h

/-- The first derivative of `fcut` vanishes to the left of `1`. -/
lemma deriv_deriv_fcut_eq_zero_of_lt_one {t : ℝ} (ht : t < 1) :
    deriv (deriv fcut) t = 0 := by
  have h : deriv fcut =ᶠ[𝓝 t] 0 := by
    filter_upwards [Ioo_mem_nhds (by linarith : 2 * t - 1 < t) ht] with s hs
    exact deriv_fcut_eq_zero_of_lt_one hs.2
  have h2 := h.deriv_eq
  simpa using h2

/-- The first derivative of `fcut` vanishes to the right of `2`. -/
lemma deriv_deriv_fcut_eq_zero_of_gt_two {t : ℝ} (ht : 2 < t) :
    deriv (deriv fcut) t = 0 := by
  have h : deriv fcut =ᶠ[𝓝 t] 0 := by
    filter_upwards [Ioo_mem_nhds (by linarith : (2:ℝ) < t) (by linarith : t < 2 * t - 2)] with s hs
    exact deriv_fcut_eq_zero_of_gt_two hs.1
  rw [h.deriv_eq]
  simp

/-- `deriv fcut` is supported in `[1,2]`, in particular it is compactly supported. -/
lemma hasCompactSupport_deriv_fcut : HasCompactSupport (deriv fcut) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (1:ℝ) 2)
    isCompact_Icc fun t ht => ⟨?_, ?_⟩
  · by_contra h
    exact ht (deriv_fcut_eq_zero_of_lt_one (lt_of_not_ge h))
  · by_contra h
    exact ht (deriv_fcut_eq_zero_of_gt_two (lt_of_not_ge h))

/-- `deriv (deriv fcut)` is supported in `[1,2]`, in particular it is compactly supported. -/
lemma hasCompactSupport_deriv_deriv_fcut : HasCompactSupport (deriv (deriv fcut)) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (1:ℝ) 2)
    isCompact_Icc fun t ht => ⟨?_, ?_⟩
  · by_contra h
    exact ht (deriv_deriv_fcut_eq_zero_of_lt_one (lt_of_not_ge h))
  · by_contra h
    exact ht (deriv_deriv_fcut_eq_zero_of_gt_two (lt_of_not_ge h))

end

end Work.FTS.BSSwirl
