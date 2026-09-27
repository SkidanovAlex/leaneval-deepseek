import Mathlib
import Submission.Work.Mostow.localIsomDefs

/-!
# A Dini-type bound for the hyperbolic quadratic form `gH`

The hyperbolic Riemannian quadratic form at a chart point `p`,

  `gH p w = ‖w‖² − ⟪p,w⟫² / (1 + ‖p‖²)`,

is the restriction of the positive definite form `B_p(x,y) = ⟪x,y⟫ − ⟪p,x⟫⟪p,y⟫/(1+‖p‖²)`
to the diagonal.  `B_p = 1 − p pᵀ/(1+‖p‖²)` is positive definite with operator norm `≤ 1`
w.r.t. the Euclidean inner product, i.e. `0 ≤ B_p(x,x) ≤ ‖x‖²` and `B_p(x,y) ≤ ‖x‖‖y‖`.
Expanding `B_p(h v + R, h v + R)` and applying these two bounds gives

  `gH p (h v + R) ≤ h² gH p v + 4 h ‖v‖ ‖R‖ + ‖R‖²`   for `h ≥ 0`.

This is the elementary estimate used to control the variation of the metric along
segments (Dini-type estimates for the natural map).
-/

namespace Work.Mostow

open Submission.Mostow

/-- The positive definite form associated with the hyperbolic metric at `p`:
`B_p(x,y) = ⟪x,y⟫ − ⟪p,x⟫⟪p,y⟫/(1+‖p‖²)`. -/
private noncomputable def gB {n : ℕ} (p : E n) (x y : E n) : ℝ :=
  inner ℝ x y - inner ℝ p x * inner ℝ p y / (1 + ‖p‖ ^ 2)

/-- `gH p` is the diagonal of `gB p`. -/
private theorem gB_self {n : ℕ} (p x : E n) : gB p x x = gH p x := by
  simp only [gB, gH, real_inner_self_eq_norm_sq]
  ring

/-- Bilinearity: expansion of `gB p` on `h v + R`. -/
private theorem gB_expand {n : ℕ} (p v R : E n) (h : ℝ) :
    gB p (h • v + R) (h • v + R) = h ^ 2 * gB p v v + 2 * h * gB p v R + gB p R R := by
  simp only [gB, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm v R]
  ring

/-- `gB p R R ≤ ‖R‖²`. -/
private theorem gB_RR_le {n : ℕ} (p R : E n) : gB p R R ≤ ‖R‖ ^ 2 := by
  have h : (0:ℝ) ≤ inner ℝ p R * inner ℝ p R / (1 + ‖p‖ ^ 2) :=
    div_nonneg (mul_self_nonneg _) (by positivity)
  simp only [gB, real_inner_self_eq_norm_sq]
  linarith

/-- Cauchy–Schwarz for `gB p`, with the Euclidean bound `gB p v R ≤ ‖v‖‖R‖`. -/
private theorem gB_vR_le {n : ℕ} (p v R : E n) : gB p v R ≤ ‖v‖ * ‖R‖ := by
  have hkey : gB p v R = inner ℝ (v - (inner ℝ p v / (1 + ‖p‖ ^ 2)) • p) R := by
    simp only [gB, inner_sub_left, real_inner_smul_left]
    ring
  rw [hkey]
  -- the corrected vector `v - (⟪p,v⟫/(1+‖p‖²)) p` is no longer than `v`
  have hnorm : ‖v - (inner ℝ p v / (1 + ‖p‖ ^ 2)) • p‖ ≤ ‖v‖ := by
    have hP : (0:ℝ) < 1 + ‖p‖^2 := by positivity
    have hsq : ‖v - (inner ℝ p v / (1 + ‖p‖^2)) • p‖^2 ≤ ‖v‖^2 := by
      have hkey : ‖v - (inner ℝ p v / (1 + ‖p‖^2)) • p‖^2
          = ‖v‖^2 - (inner ℝ p v)^2 * (2 + ‖p‖^2) / (1 + ‖p‖^2)^2 := by
        rw [norm_sub_sq_real, norm_smul, real_inner_smul_right, real_inner_comm v p]
        simp only [Real.norm_eq_abs, sq_abs, mul_pow]
        rw [div_pow]
        field_simp
        ring
      rw [hkey]
      have h1 : (0:ℝ) ≤ (inner ℝ p v)^2 * (2 + ‖p‖^2) / (1 + ‖p‖^2)^2 :=
        div_nonneg (mul_nonneg (sq_nonneg _) (by positivity)) (by positivity)
      linarith
    nlinarith [hsq, norm_nonneg (v - (inner ℝ p v / (1 + ‖p‖^2)) • p), norm_nonneg v]
  calc inner ℝ (v - (inner ℝ p v / (1 + ‖p‖ ^ 2)) • p) R
      ≤ ‖v - (inner ℝ p v / (1 + ‖p‖ ^ 2)) • p‖ * ‖R‖ := real_inner_le_norm _ _
    _ ≤ ‖v‖ * ‖R‖ := by gcongr

theorem diniGHBound {n : ℕ} (p v R : Submission.Mostow.E n) (h : ℝ) (hh : 0 ≤ h) : Submission.Mostow.gH p (h • v + R) ≤ h ^ 2 * Submission.Mostow.gH p v + 4 * h * ‖v‖ * ‖R‖ + ‖R‖ ^ 2 := by
  rw [← gB_self p (h • v + R), gB_expand, gB_self p v]
  have h1 : gB p v R ≤ ‖v‖ * ‖R‖ := gB_vR_le p v R
  have h2 : gB p R R ≤ ‖R‖ ^ 2 := gB_RR_le p R
  have h3 : (0:ℝ) ≤ h * (‖v‖ * ‖R‖) :=
    mul_nonneg hh (mul_nonneg (norm_nonneg v) (norm_nonneg R))
  have h4 : 2 * h * gB p v R ≤ 2 * h * (‖v‖ * ‖R‖) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  have hstep : h ^ 2 * gH p v + 2 * h * gB p v R + gB p R R
      ≤ h ^ 2 * gH p v + 2 * h * (‖v‖ * ‖R‖) + ‖R‖ ^ 2 := by linarith [h4, h2]
  have hfinal : h ^ 2 * gH p v + 2 * h * (‖v‖ * ‖R‖) + ‖R‖ ^ 2
      ≤ h ^ 2 * gH p v + 4 * h * ‖v‖ * ‖R‖ + ‖R‖ ^ 2 := by nlinarith [h3]
  linarith

end Work.Mostow
