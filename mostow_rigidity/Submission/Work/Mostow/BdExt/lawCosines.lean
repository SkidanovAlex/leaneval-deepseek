import Mathlib
import Submission.Work.Mostow.BdExt.Basic

/-!
# The hyperbolic law of cosines in the origin chart

This is the analytic engine behind the boundary extension of a quasi-isometry.

Everything is expressed in the chart `E n` of `Submission.Mostow.Interfaces`; recall
* `tpart u = √(1 + ‖u‖²)` is the time coordinate of the hyperboloid point over `u`,
* `hdist u v = arcosh (tpart u * tpart v - ⟪u, v⟫)` is the hyperbolic distance,
* `lvl u = hdist 0 u` is the hyperbolic distance to the origin,
* `dirv u = ‖u‖⁻¹ • u` is the Euclidean direction of `u` (junk at `0`).

The main content is the classical law of cosines for the triangle `(0, u, v)`:
`cosh (hdist u v) = cosh (lvl u) cosh (lvl v) - sinh (lvl u) sinh (lvl v) ⟪dirv u, dirv v⟫`,
together with the trigonometric identities `tpart u = cosh (lvl u)`, `‖u‖ = sinh (lvl u)`,
`sinh (lvl u) • dirv u = u`, and the two consequences used to control the angle between two
directions at bounded distance.
-/

namespace Work.Mostow.BdExt

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-- The argument of `arcosh` in the definition of `hdist` is always at least `1`
(Cauchy–Schwarz). -/
lemma one_le_tpart_mul_sub_inner (u v : E n) : 1 ≤ tpart u * tpart v - inner ℝ u v := by
  have hu : (0 : ℝ) ≤ 1 + ‖u‖ ^ 2 := by positivity
  have hsq : (1 + ‖u‖ * ‖v‖) ^ 2 ≤ (1 + ‖u‖ ^ 2) * (1 + ‖v‖ ^ 2) := by
    nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
  have hnn : (0 : ℝ) ≤ 1 + ‖u‖ * ‖v‖ := by positivity
  have hstep : 1 + ‖u‖ * ‖v‖ ≤ √((1 + ‖u‖ ^ 2) * (1 + ‖v‖ ^ 2)) := by
    rw [Real.le_sqrt hnn (by positivity)]
    exact hsq
  have hmul : tpart u * tpart v = √((1 + ‖u‖ ^ 2) * (1 + ‖v‖ ^ 2)) := by
    rw [tpart, tpart, Real.sqrt_mul hu]
  have hcs : inner ℝ u v ≤ ‖u‖ * ‖v‖ := real_inner_le_norm u v
  linarith [hstep, hcs, hmul]

/-- The time coordinate of the lift of `u` is `cosh` of the hyperbolic level of `u`. -/
lemma tpart_eq_cosh_lvl (u : E n) : tpart u = Real.cosh (lvl u) := by
  rw [lvl, hdist, Real.cosh_arcosh (one_le_tpart_mul_sub_inner 0 u)]
  simp [tpart]

/-- The hyperbolic level is `arcosh` of the time coordinate. -/
lemma lvl_eq_arcosh (u : E n) : lvl u = Real.arcosh (tpart u) := by
  rw [lvl, hdist]
  congr 1
  simp [tpart]

/-- The Euclidean norm of `u` is `sinh` of the hyperbolic level of `u`. -/
lemma norm_eq_sinh_lvl (u : E n) : ‖u‖ = Real.sinh (lvl u) := by
  have ht : (1 : ℝ) ≤ tpart u := by
    rw [tpart]
    exact Real.one_le_sqrt.mpr (by have := sq_nonneg ‖u‖; linarith)
  have hs : Real.sinh (Real.arcosh (tpart u)) = √(tpart u ^ 2 - 1) := Real.sinh_arcosh ht
  have hsq : tpart u ^ 2 = 1 + ‖u‖ ^ 2 := by
    rw [tpart]
    exact Real.sq_sqrt (by positivity)
  rw [lvl_eq_arcosh, hs, show tpart u ^ 2 - 1 = ‖u‖ ^ 2 by rw [hsq]; ring,
    Real.sqrt_sq (norm_nonneg u)]

/-- The hyperbolic level of a nonzero point is positive. -/
lemma lvl_pos (u : E n) (hu : u ≠ 0) : 0 < lvl u := by
  have h : 0 < Real.sinh (lvl u) := by
    rw [← norm_eq_sinh_lvl u]
    exact norm_pos_iff.mpr hu
  exact Real.sinh_pos_iff.mp h

/-- The Euclidean direction is a unit vector at every nonzero point. -/
lemma norm_dirv (u : E n) (hu : u ≠ 0) : ‖dirv u‖ = 1 := by
  rw [dirv, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg u),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu)]

/-- The scalar product of the directions recovers the scalar product of the points,
after rescaling by the norms. -/
lemma norm_mul_norm_mul_inner_dirv (u v : E n) :
    ‖u‖ * ‖v‖ * inner ℝ (dirv u) (dirv v) = inner ℝ u v := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp [dirv]
  rcases eq_or_ne v 0 with rfl | hv
  · simp [dirv]
  have hu' : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  rw [dirv, dirv, real_inner_smul_left, real_inner_smul_right]
  field_simp

/-- The rescaling `sinh (lvl u) • dirv u` is `u` itself. -/
lemma sinh_lvl_smul_dirv (u : E n) : Real.sinh (lvl u) • dirv u = u := by
  by_cases hu : u = 0
  · subst hu
    simp [dirv]
  · rw [dirv, smul_smul, ← norm_eq_sinh_lvl u, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hu),
      one_smul]

/-- First form of the hyperbolic law of cosines: `cosh` of the distance is the argument of
`arcosh` in the definition of `hdist`. -/
lemma cosh_hdist (u v : E n) :
    Real.cosh (hdist u v) = tpart u * tpart v - inner ℝ u v := by
  rw [hdist, Real.cosh_arcosh (one_le_tpart_mul_sub_inner u v)]

/-- Second form of the hyperbolic law of cosines, i.e. the law of cosines for the triangle
`(0, u, v)` in terms of levels and Euclidean directions. -/
lemma cosh_hdist_lvl (u v : E n) :
    Real.cosh (hdist u v) = Real.cosh (lvl u) * Real.cosh (lvl v) -
      Real.sinh (lvl u) * Real.sinh (lvl v) * inner ℝ (dirv u) (dirv v) := by
  rw [← tpart_eq_cosh_lvl u, ← tpart_eq_cosh_lvl v, ← norm_eq_sinh_lvl u,
    ← norm_eq_sinh_lvl v, hdist, Real.cosh_arcosh (one_le_tpart_mul_sub_inner u v),
    norm_mul_norm_mul_inner_dirv u v]

/-- The cosine of the angle between two directions, from the law of cosines. -/
lemma one_sub_inner_dirv (u v : E n) (hu : u ≠ 0) (hv : v ≠ 0) :
    1 - inner ℝ (dirv u) (dirv v) =
      (Real.cosh (hdist u v) - Real.cosh (lvl u - lvl v)) /
        (Real.sinh (lvl u) * Real.sinh (lvl v)) := by
  have hden : Real.sinh (lvl u) * Real.sinh (lvl v) ≠ 0 :=
    mul_ne_zero (ne_of_gt (Real.sinh_pos_iff.mpr (lvl_pos u hu)))
      (ne_of_gt (Real.sinh_pos_iff.mpr (lvl_pos v hv)))
  have hkey : Real.cosh (hdist u v) - Real.cosh (lvl u - lvl v)
      = Real.sinh (lvl u) * Real.sinh (lvl v) * (1 - inner ℝ (dirv u) (dirv v)) := by
    rw [cosh_hdist_lvl u v, Real.cosh_sub]
    ring
  rw [hkey, mul_div_cancel_left₀ _ hden]

/-- Chord bound: two directions are close on the sphere as soon as the points are close
compared with their levels. -/
lemma norm_sub_dirv_sq_le (u v : E n) (hu : u ≠ 0) (hv : v ≠ 0) :
    ‖dirv u - dirv v‖ ^ 2 ≤ 2 * (Real.cosh (hdist u v) - 1) /
      (Real.sinh (lvl u) * Real.sinh (lvl v)) := by
  have hden : 0 < Real.sinh (lvl u) * Real.sinh (lvl v) :=
    mul_pos (Real.sinh_pos_iff.mpr (lvl_pos u hu)) (Real.sinh_pos_iff.mpr (lvl_pos v hv))
  have hnorm : ‖dirv u - dirv v‖ ^ 2 = 2 * (1 - inner ℝ (dirv u) (dirv v)) := by
    rw [norm_sub_sq_real, norm_dirv u hu, norm_dirv v hv]
    ring
  rw [hnorm, one_sub_inner_dirv u v hu hv, ← mul_div_assoc,
    div_le_div_iff_of_pos_right hden]
  linarith [Real.one_le_cosh (lvl u - lvl v)]

theorem lawCosines (n : ℕ) :
    (∀ u v : Submission.Mostow.E n, Real.cosh (Submission.Mostow.hdist u v) = Submission.Mostow.tpart u * Submission.Mostow.tpart v - inner ℝ u v) ∧
    (∀ u : Submission.Mostow.E n, Submission.Mostow.tpart u = Real.cosh (Work.Mostow.BdExt.lvl u)) ∧
    (∀ (hI : Submission.Mostow.HypIsometryProp n) (u : Submission.Mostow.E n), ‖u‖ = Real.sinh (Work.Mostow.BdExt.lvl u)) ∧
    (∀ (hI : Submission.Mostow.HypIsometryProp n) (u : Submission.Mostow.E n), Real.sinh (Work.Mostow.BdExt.lvl u) • Work.Mostow.BdExt.dirv u = u) ∧
    (∀ (hI : Submission.Mostow.HypIsometryProp n) (u v : Submission.Mostow.E n),
        Real.cosh (Submission.Mostow.hdist u v) = Real.cosh (Work.Mostow.BdExt.lvl u) * Real.cosh (Work.Mostow.BdExt.lvl v) -
          Real.sinh (Work.Mostow.BdExt.lvl u) * Real.sinh (Work.Mostow.BdExt.lvl v) * inner ℝ (Work.Mostow.BdExt.dirv u) (Work.Mostow.BdExt.dirv v)) ∧
    (∀ u : Submission.Mostow.E n, u ≠ 0 → ‖Work.Mostow.BdExt.dirv u‖ = 1) ∧
    (∀ (hI : Submission.Mostow.HypIsometryProp n) (u v : Submission.Mostow.E n), u ≠ 0 → v ≠ 0 →
        1 - inner ℝ (Work.Mostow.BdExt.dirv u) (Work.Mostow.BdExt.dirv v) =
          (Real.cosh (Submission.Mostow.hdist u v) - Real.cosh (Work.Mostow.BdExt.lvl u - Work.Mostow.BdExt.lvl v)) /
            (Real.sinh (Work.Mostow.BdExt.lvl u) * Real.sinh (Work.Mostow.BdExt.lvl v))) ∧
    (∀ (hI : Submission.Mostow.HypIsometryProp n) (u v : Submission.Mostow.E n), u ≠ 0 → v ≠ 0 →
        ‖Work.Mostow.BdExt.dirv u - Work.Mostow.BdExt.dirv v‖ ^ 2 ≤ 2 * (Real.cosh (Submission.Mostow.hdist u v) - 1) /
          (Real.sinh (Work.Mostow.BdExt.lvl u) * Real.sinh (Work.Mostow.BdExt.lvl v))) :=
  ⟨fun u v => cosh_hdist u v,
   fun u => tpart_eq_cosh_lvl u,
   fun _ u => norm_eq_sinh_lvl u,
   fun _ u => sinh_lvl_smul_dirv u,
   fun _ u v => cosh_hdist_lvl u v,
   fun u hu => norm_dirv u hu,
   fun _ u v hu hv => one_sub_inner_dirv u v hu hv,
   fun _ u v hu hv => norm_sub_dirv_sq_le u v hu hv⟩

end

end Work.Mostow.BdExt
