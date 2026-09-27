import Mathlib
import Submission.Work.Mostow.BdExt.Basic
import Submission.Work.Mostow.BdExt.rayDist
import Submission.Work.Mostow.BdExt.lawCosines

/-!
# The one-step Lipschitz bound on the directions of a quasi-isometric ray

Let `Φ` be a `(K, C)`-quasi-isometry of the chart `E n` of `ℍⁿ` and let `ξ ∈ Sph n` be a boundary
point.  Two parameters `s, t` with `|s - t| ≤ 1` give two points `ray ξ s`, `ray ξ t` at hyperbolic
distance `|s - t| ≤ 1`; the quasi-isometry condition then puts their images at distance at most
`K + C`.  The quantitative law of cosines (`norm_sub_dirv_sq_le`) converts this into a bound on the
chord between the two Euclidean directions, in terms of the hyperbolic levels of the images.

This is the elementary "step" estimate used to show that `t ↦ dirv (Φ (ray ξ t))` is a Cauchy
sequence along the ray (summing the steps over a partition of a long interval).
-/

namespace Work.Mostow.BdExt

open Submission.Mostow

noncomputable section

variable {n : ℕ}

/-- The hyperbolic level of the chart origin is zero. -/
lemma lvl_zero_qi : lvl (0 : E n) = 0 := by
  have h := norm_eq_sinh_lvl (0 : E n)
  rw [norm_zero] at h
  exact Real.sinh_eq_zero.mp h.symm

/-- Chord bound for two nonzero points at hyperbolic distance at most `D`: the Euclidean
directions seen from the origin differ by at most the square root of
`2 (cosh D - 1) / (sinh (lvl u) sinh (lvl v))`. -/
lemma norm_sub_dirv_le_sqrt (hI : Submission.Mostow.HypIsometryProp n) {u v : E n}
    (hu : u ≠ 0) (hv : v ≠ 0) (D : ℝ) (hD : 0 ≤ D) (hd : hdist u v ≤ D) :
    ‖dirv u - dirv v‖ ≤
      Real.sqrt (2 * (Real.cosh D - 1) / (Real.sinh (lvl u) * Real.sinh (lvl v))) := by
  have hden : 0 < Real.sinh (lvl u) * Real.sinh (lvl v) :=
    mul_pos (Real.sinh_pos_iff.mpr (lvl_pos u hu)) (Real.sinh_pos_iff.mpr (lvl_pos v hv))
  have hcosh : Real.cosh (hdist u v) ≤ Real.cosh D := by
    rw [Real.cosh_le_cosh, abs_of_nonneg (hI.1 u v), abs_of_nonneg hD]
    exact hd
  have hbound : ‖dirv u - dirv v‖ ^ 2 ≤
      2 * (Real.cosh D - 1) / (Real.sinh (lvl u) * Real.sinh (lvl v)) := by
    calc ‖dirv u - dirv v‖ ^ 2
        ≤ 2 * (Real.cosh (hdist u v) - 1) / (Real.sinh (lvl u) * Real.sinh (lvl v)) :=
          norm_sub_dirv_sq_le u v hu hv
      _ ≤ 2 * (Real.cosh D - 1) / (Real.sinh (lvl u) * Real.sinh (lvl v)) := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hden)
          linarith
  rw [← Real.sqrt_sq (norm_nonneg (dirv u - dirv v))]
  exact Real.sqrt_le_sqrt hbound

theorem qiRayStep (n : ℕ) (hI : Submission.Mostow.HypIsometryProp n) (Φ : Submission.Mostow.E n → Submission.Mostow.E n)
    (K C : ℝ) (hK : 1 ≤ K) (hC : 0 ≤ C)
    (hup : ∀ u v, Submission.Mostow.hdist (Φ u) (Φ v) ≤ K * Submission.Mostow.hdist u v + C)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n)
    (s t : ℝ) (hst : |s - t| ≤ 1)
    (hs0 : 1 ≤ Work.Mostow.BdExt.lvl (Φ (Work.Mostow.BdExt.ray ξ s)))
    (ht0 : 1 ≤ Work.Mostow.BdExt.lvl (Φ (Work.Mostow.BdExt.ray ξ t))) :
    ‖Work.Mostow.BdExt.dirv (Φ (Work.Mostow.BdExt.ray ξ s)) - Work.Mostow.BdExt.dirv (Φ (Work.Mostow.BdExt.ray ξ t))‖ ≤
      Real.sqrt (2 * (Real.cosh (K + C) - 1) /
        (Real.sinh (Work.Mostow.BdExt.lvl (Φ (Work.Mostow.BdExt.ray ξ s))) *
         Real.sinh (Work.Mostow.BdExt.lvl (Φ (Work.Mostow.BdExt.ray ξ t))))) := by
  -- the images of the two ray points are at hyperbolic distance at most `K + C`
  have hd : hdist (Φ (ray ξ s)) (Φ (ray ξ t)) ≤ K + C := by
    have h := hup (ray ξ s) (ray ξ t)
    rw [hdist_ray_ray ξ hξ s t] at h
    have hKs : K * |s - t| ≤ K * 1 := mul_le_mul_of_nonneg_left hst (by linarith)
    linarith
  -- both images are nonzero, because their levels are at least `1`
  have hu0 : Φ (ray ξ s) ≠ 0 := by
    intro h
    rw [h, lvl_zero_qi] at hs0
    linarith
  have hv0 : Φ (ray ξ t) ≠ 0 := by
    intro h
    rw [h, lvl_zero_qi] at ht0
    linarith
  exact norm_sub_dirv_le_sqrt hI hu0 hv0 (K + C) (by linarith) hd

end

end Work.Mostow.BdExt
