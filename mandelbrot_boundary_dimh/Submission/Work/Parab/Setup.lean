import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.FatouCoord.Setup

/-!
# PARAB0: elementary geometry of the sectors `QLeft`

The interface (`MandelDim.QLeft`) defines Shishikura's sector
`Q₀ = {w | π/3 < |arg (w + ξ)|}` as a set described by the principal `arg`.  For every
geometric argument it is far more convenient to have a description by an elementary
inequality (`2 * (w+ξ).re < ‖w+ξ‖`), which also makes openness and the covering
properties immediate.  This file provides that translation and its first consequences.
-/

open Complex Set Metric Filter
open scoped Topology

namespace Work.Parab

noncomputable section

/-- `|cos|` of the argument of a nonzero complex number. -/
lemma cos_abs_arg {z : ℂ} (hz : z ≠ 0) : Real.cos |z.arg| = z.re / ‖z‖ := by
  rw [Real.cos_abs, Complex.cos_arg hz]

/-- The elementary reformulation of `π/3 < |arg z|` in terms of `cos`. -/
lemma pi_div_three_lt_abs_arg_iff {z : ℂ} :
    Real.pi / 3 < |z.arg| ↔ Real.cos |z.arg| < Real.cos (Real.pi / 3) := by
  constructor
  · intro h
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (Complex.abs_arg_le_pi z) h
  · intro h
    by_contra hc
    push_neg at hc
    exact absurd h (not_lt.mpr
      (Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hc))

/-- Shishikura's sector `QLeft ξ = {π/3 < |arg (w + ξ)|}` is the elementary set
`{w | 2 * (w + ξ).re < ‖w + ξ‖}`. -/
theorem QLeft_iff (ξ : ℝ) (w : ℂ) :
    w ∈ MandelDim.QLeft ξ ↔ 2 * (w + ξ).re < ‖w + ξ‖ := by
  change Real.pi / 3 < |(w + ξ).arg| ↔ 2 * (w + ξ).re < ‖w + ξ‖
  rcases eq_or_ne (w + ξ) 0 with hz | hz
  · rw [hz, Complex.arg_zero, abs_zero]
    simp only [Complex.zero_re, mul_zero, norm_zero]
    constructor <;> intro h <;> linarith [Real.pi_pos]
  · rw [pi_div_three_lt_abs_arg_iff, Real.cos_pi_div_three, cos_abs_arg hz,
      div_lt_iff₀ (norm_pos_iff.mpr hz)]
    constructor <;> intro h <;> linarith

/-- The sector is open. -/
theorem isOpen_QLeft (ξ : ℝ) : IsOpen (MandelDim.QLeft ξ) := by
  have h : MandelDim.QLeft ξ = {w : ℂ | 2 * (w + ξ).re < ‖w + ξ‖} := by
    ext w
    exact QLeft_iff ξ w
  rw [h]
  exact isOpen_lt
    (continuous_const.mul (Complex.continuous_re.comp (continuous_id.add continuous_const)))
    (continuous_norm.comp (continuous_id.add continuous_const))

/-- The left half-plane `{Re w < -ξ}` is contained in the sector. -/
theorem halfplane_subset_QLeft (ξ : ℝ) : {w : ℂ | w.re < -ξ} ⊆ MandelDim.QLeft ξ := by
  intro w hw
  have hw' : w.re < -ξ := hw
  rw [QLeft_iff]
  have hz : (w + ξ).re < 0 := by
    rw [Complex.add_re, Complex.ofReal_re]
    linarith
  have := norm_nonneg (w + ξ)
  linarith

/-- Points of the sector stay in the sector after adding `1`, as long as they are far
enough to the left. -/
theorem QLeft_add_one (ξ : ℝ) {w : ℂ} (hw : w.re < -ξ - 1) (_h : w ∈ MandelDim.QLeft ξ) :
    w + 1 ∈ MandelDim.QLeft ξ := by
  apply halfplane_subset_QLeft ξ
  simp only [mem_setOf_eq, Complex.add_re, Complex.one_re]
  linarith

/-- **Covering.**  The sector `QLeft ξ` together with the half-plane `{Re w > ξ₁}` covers
everything outside a large disc.  (This is the geometric fact behind "the flower is a
neighbourhood of `0`".) -/
theorem QLeft_cover {ξ ξ₁ : ℝ} (hξ : 0 < ξ) :
    ∃ R : ℝ, ∀ w : ℂ, R < ‖w‖ → w ∈ MandelDim.QLeft ξ ∨ ξ₁ < w.re := by
  refine ⟨max 0 (2 * ξ₁ + 3 * ξ) + 1, fun w hw => ?_⟩
  by_cases h : w ∈ MandelDim.QLeft ξ
  · exact Or.inl h
  · right
    rw [QLeft_iff] at h
    push_neg at h
    rw [Complex.add_re, Complex.ofReal_re] at h
    have h2 : ‖w‖ - ξ ≤ ‖w + ξ‖ := by
      have hh := norm_sub_le (w + ξ) (ξ : ℂ)
      rw [add_sub_cancel_right] at hh
      have h3 : ‖((ξ : ℝ) : ℂ)‖ = ξ := by
        simp only [Complex.norm_real]
        exact abs_of_nonneg hξ.le
      linarith [hh, le_of_eq h3]
    have hR : 2 * ξ₁ + 3 * ξ < ‖w‖ := by
      have := le_max_right (0 : ℝ) (2 * ξ₁ + 3 * ξ)
      linarith
    linarith

/-- The sector `QLeft ξ` has no points of modulus `≤ ξ/3`: it is a sector with vertex `-ξ`,
so near the origin its points are far outside.  (This is what lets one take `ξ₀` large enough that
`QLeft ξ₀` is contained in the far part of the sector, where the asymptotics are available.) -/
theorem QLeft_subset_norm {ξ : ℝ} (hξ : 0 < ξ) :
    MandelDim.QLeft ξ ⊆ {w : ℂ | ξ / 3 < ‖w‖} := by
  intro w hw
  rw [QLeft_iff] at hw
  have h1 : ‖w + ξ‖ ≤ ‖w‖ + ξ := by
    have := norm_add_le w (ξ : ℂ)
    simp only [Complex.norm_real, Real.norm_eq_abs] at this
    rw [abs_of_nonneg hξ.le] at this
    exact this
  have h2 : 2 * ξ - 2 * ‖w‖ ≤ 2 * (w + ξ).re := by
    have := Complex.re_le_norm (w + ξ)
    have h3 : -‖w‖ ≤ w.re := by
      have := Complex.abs_re_le_norm w
      have := (abs_le.mp this).1
      linarith
    rw [Complex.add_re, Complex.ofReal_re]
    linarith
  have : ξ / 3 < ‖w‖ := by linarith
  exact this

end
end Work.Parab
