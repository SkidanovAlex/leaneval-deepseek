import Mathlib
import Submission.Work.Mostow.BdExt.bdMap
import Submission.Work.Mostow.BdExt.rayDist
import Submission.Work.Mostow.BdExt.lawCosines
import Submission.Work.Mostow.BdExt.bdDirvCmp

/-!
# Comparing the boundary extension at two nearby rays

We prove that the boundary extension `bdMap n Φ` of a `(K, C)`-quasi-isometry `Φ` of `ℍⁿ` is
*uniformly* continuous in the visual metric, with an explicit rate.

Two ingredients enter.

* `bdMap_rate` (from `BdExt/bdMap.lean`): the direction of the image of the geodesic ray to `ξ`
  converges to `bdMap n Φ ξ` at rate `exp (-t/(2K))`, with a constant independent of `ξ`.
* `bdDirvCmp`: two points at hyperbolic distance at most `M` whose levels are at least `L ≥ 1`
  have directions differing by at most `sqrt (2 (cosh M - 1)) / sinh L`.

For boundary points `ξ, ξ'` whose rays are within distance `1` at level `T`, the images of
`ray ξ T`, `ray ξ' T` are at distance at most `K + C` and at level at least
`(T - C)/K - lvl (Φ 0)`; the triangle inequality through the two limits then gives the stated
bound.
-/

namespace Work.Mostow.BdExt

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open Classical

noncomputable section

/-- **Uniform rate of convergence to the boundary map.**  For a `(K, C)`-quasi-isometry `Φ` there is
a constant `C₄` such that for every `ξ ∈ Sph n` the directions of the images of the ray to `ξ`
converge to `bdMap n Φ ξ` at rate `exp (-t/(2K))`, with the *same* constant for all `ξ`.  This is
`bdMap_rate`, whose proof combines the one-step estimate `qiRayStepExp` with the geometric-tail
argument `qiRayLimit`. -/
lemma bdMap_rate_uniform (n : ℕ) (hI : HypIsometryProp n) (Φ : E n → E n) (K C : ℝ)
    (hK : 1 ≤ K) (hC : 0 ≤ C)
    (hup : ∀ u v, hdist (Φ u) (Φ v) ≤ K * hdist u v + C)
    (hlow : ∀ u v, hdist u v ≤ K * hdist (Φ u) (Φ v) + C) :
    ∃ C₄ : ℝ, 0 ≤ C₄ ∧ ∀ (ξ : E n) (hξ : ξ ∈ Sph n) (t : ℝ), 0 ≤ t →
      ‖dirv (Φ (ray ξ t)) - bdMap n Φ ξ‖ ≤ C₄ * Real.exp (-(t / (2 * K))) :=
  bdMap_rate n hI Φ K C hK hC hup hlow

/-- **The boundary extension is uniformly continuous along nearby rays.**  For a `(K, C)`-quasi-
isometry `Φ` of `ℍⁿ` there are constants `T₀, C₆ ≥ 0` such that whenever two boundary points
`ξ, ξ'` have rays at distance at most `1` at level `T ≥ T₀`, the boundary points `bdMap n Φ ξ'`,
`bdMap n Φ ξ` are close, with the explicit rate `C₆ (exp (-T/(2K)) + 1/sinh ((T - C)/K - lvl (Φ 0)))`. -/
theorem bdMapCmp (n : ℕ) (hI : Submission.Mostow.HypIsometryProp n)
    (Φ : Submission.Mostow.E n → Submission.Mostow.E n) (K C : ℝ) (hK : 1 ≤ K) (hC : 0 ≤ C)
    (hup : ∀ u v, Submission.Mostow.hdist (Φ u) (Φ v) ≤ K * Submission.Mostow.hdist u v + C)
    (hlow : ∀ u v, Submission.Mostow.hdist u v ≤ K * Submission.Mostow.hdist (Φ u) (Φ v) + C) :
    ∃ (T₀ C₆ : ℝ), 0 ≤ T₀ ∧ 0 ≤ C₆ ∧
      ∀ (ξ ξ' : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n)
        (hξ' : ξ' ∈ Submission.Mostow.Sph n)
        (T : ℝ), T₀ ≤ T → Submission.Mostow.hdist (Work.Mostow.BdExt.ray ξ' T) (Work.Mostow.BdExt.ray ξ T) ≤ 1 →
        dist (Work.Mostow.BdExt.bdMap n Φ ξ') (Work.Mostow.BdExt.bdMap n Φ ξ) ≤
          C₆ * (Real.exp (-(T / (2 * K))) +
            1 / Real.sinh ((T - C) / K - Work.Mostow.BdExt.lvl (Φ 0))) := by
  obtain ⟨C₄, hC₄nn, hC₄⟩ := bdMap_rate_uniform n hI Φ K C hK hC hup hlow
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hL0nn : 0 ≤ lvl (Φ 0) := hI.1 0 (Φ 0)
  refine ⟨K * (lvl (Φ 0) + 1) + C,
    max (2 * C₄) (Real.sqrt (2 * (Real.cosh (K + C) - 1))), ?_, ?_, ?_⟩
  · have h1 : 0 ≤ K * (lvl (Φ 0) + 1) :=
      mul_nonneg (le_trans zero_le_one hK) (by linarith)
    linarith
  · exact le_trans (by linarith : (0 : ℝ) ≤ 2 * C₄) (le_max_left _ _)
  · intro ξ ξ' hξ hξ' T hT hd
    have hT0nonneg : 0 ≤ K * (lvl (Φ 0) + 1) + C := by
      have h1 : 0 ≤ K * (lvl (Φ 0) + 1) :=
        mul_nonneg (le_trans zero_le_one hK) (by linarith)
      linarith
    have hTnn : 0 ≤ T := le_trans hT0nonneg hT
    -- the level bound
    have hL1 : 1 ≤ (T - C) / K - lvl (Φ 0) := by
      have h2 : lvl (Φ 0) + 1 ≤ (T - C) / K := by
        rw [le_div_iff₀ hK0]
        have h3 : K * (lvl (Φ 0) + 1) ≤ T - C := by linarith
        linarith
      linarith
    have hden : 0 < Real.sinh ((T - C) / K - lvl (Φ 0)) :=
      Real.sinh_pos_iff.mpr (by linarith)
    -- the levels of the images
    have hlevv : (T - C) / K - lvl (Φ 0) ≤ lvl (Φ (ray ξ T)) :=
      lvl_image_ray n hI Φ K C hK hC hlow ξ hξ T hTnn
    have hlevu : (T - C) / K - lvl (Φ 0) ≤ lvl (Φ (ray ξ' T)) :=
      lvl_image_ray n hI Φ K C hK hC hlow ξ' hξ' T hTnn
    -- the images are nonzero
    have hv0 : Φ (ray ξ T) ≠ 0 := by
      intro h0
      have hz : lvl (Φ (ray ξ T)) = 0 := by
        rw [h0]
        exact (hI.2.2.1 0 0).mpr rfl
      linarith
    have hu0 : Φ (ray ξ' T) ≠ 0 := by
      intro h0
      have hz : lvl (Φ (ray ξ' T)) = 0 := by
        rw [h0]
        exact (hI.2.2.1 0 0).mpr rfl
      linarith
    -- the images of the two rays are within `K + C`
    have hdistuv : hdist (Φ (ray ξ' T)) (Φ (ray ξ T)) ≤ K + C := by
      have h := hup (ray ξ' T) (ray ξ T)
      have hKd : K * hdist (ray ξ' T) (ray ξ T) ≤ K * 1 :=
        mul_le_mul_of_nonneg_left hd (le_of_lt hK0)
      linarith
    have hmid := bdDirvCmp n hI (Φ (ray ξ' T)) (Φ (ray ξ T)) hu0 hv0 (K + C)
      ((T - C) / K - lvl (Φ 0)) (by linarith) hdistuv hL1 hlevu hlevv
    -- the two end terms, by the uniform rate
    have hru := hC₄ ξ' hξ' T hTnn
    have hrv := hC₄ ξ hξ T hTnn
    have h1 : ‖bdMap n Φ ξ' - dirv (Φ (ray ξ' T))‖ ≤ C₄ * Real.exp (-(T / (2 * K))) := by
      rw [norm_sub_rev]
      exact hru
    have h3 : dist (bdMap n Φ ξ') (bdMap n Φ ξ) ≤
        ‖bdMap n Φ ξ' - dirv (Φ (ray ξ' T))‖ +
          ‖dirv (Φ (ray ξ' T)) - dirv (Φ (ray ξ T))‖ +
            ‖dirv (Φ (ray ξ T)) - bdMap n Φ ξ‖ := by
      rw [dist_eq_norm]
      have hsplit : bdMap n Φ ξ' - bdMap n Φ ξ =
          (bdMap n Φ ξ' - dirv (Φ (ray ξ' T))) + (dirv (Φ (ray ξ' T)) - dirv (Φ (ray ξ T))) +
            (dirv (Φ (ray ξ T)) - bdMap n Φ ξ) := by abel
      calc ‖bdMap n Φ ξ' - bdMap n Φ ξ‖
          = ‖(bdMap n Φ ξ' - dirv (Φ (ray ξ' T))) + (dirv (Φ (ray ξ' T)) - dirv (Φ (ray ξ T))) +
              (dirv (Φ (ray ξ T)) - bdMap n Φ ξ)‖ := by rw [hsplit]
        _ ≤ ‖(bdMap n Φ ξ' - dirv (Φ (ray ξ' T))) + (dirv (Φ (ray ξ' T)) - dirv (Φ (ray ξ T)))‖ +
              ‖dirv (Φ (ray ξ T)) - bdMap n Φ ξ‖ := norm_add_le _ _
        _ ≤ (‖bdMap n Φ ξ' - dirv (Φ (ray ξ' T))‖ + ‖dirv (Φ (ray ξ' T)) - dirv (Φ (ray ξ T))‖) +
              ‖dirv (Φ (ray ξ T)) - bdMap n Φ ξ‖ := by
              linarith [norm_add_le (bdMap n Φ ξ' - dirv (Φ (ray ξ' T)))
                (dirv (Φ (ray ξ' T)) - dirv (Φ (ray ξ T)))]
        _ = _ := by ring
    -- assembly of the arithmetic
    have hsum : ‖bdMap n Φ ξ' - dirv (Φ (ray ξ' T))‖ +
        ‖dirv (Φ (ray ξ T)) - bdMap n Φ ξ‖ ≤ (2 * C₄) * Real.exp (-(T / (2 * K))) := by
      have h2 : (2 * C₄) * Real.exp (-(T / (2 * K))) =
          2 * (C₄ * Real.exp (-(T / (2 * K)))) := by ring
      rw [h2]
      linarith [h1, hrv]
    have he : 0 ≤ Real.exp (-(T / (2 * K))) := (Real.exp_pos _).le
    have hs : 0 ≤ 1 / Real.sinh ((T - C) / K - lvl (Φ 0)) :=
      div_nonneg zero_le_one (le_of_lt hden)
    have hmax1 : (2 * C₄) ≤ max (2 * C₄) (Real.sqrt (2 * (Real.cosh (K + C) - 1))) :=
      le_max_left _ _
    have hmax2 : Real.sqrt (2 * (Real.cosh (K + C) - 1)) ≤
        max (2 * C₄) (Real.sqrt (2 * (Real.cosh (K + C) - 1))) := le_max_right _ _
    have e1 : (2 * C₄) * Real.exp (-(T / (2 * K))) ≤
        max (2 * C₄) (Real.sqrt (2 * (Real.cosh (K + C) - 1))) * Real.exp (-(T / (2 * K))) :=
      mul_le_mul_of_nonneg_right hmax1 he
    have e2 : Real.sqrt (2 * (Real.cosh (K + C) - 1)) *
          (1 / Real.sinh ((T - C) / K - lvl (Φ 0))) ≤
        max (2 * C₄) (Real.sqrt (2 * (Real.cosh (K + C) - 1))) *
          (1 / Real.sinh ((T - C) / K - lvl (Φ 0))) :=
      mul_le_mul_of_nonneg_right hmax2 hs
    have e3 : Real.sqrt (2 * (Real.cosh (K + C) - 1)) /
          Real.sinh ((T - C) / K - lvl (Φ 0)) =
        Real.sqrt (2 * (Real.cosh (K + C) - 1)) *
          (1 / Real.sinh ((T - C) / K - lvl (Φ 0))) := by
      rw [div_eq_mul_inv, one_div]
    have hdistrib : max (2 * C₄) (Real.sqrt (2 * (Real.cosh (K + C) - 1))) *
        (Real.exp (-(T / (2 * K))) + 1 / Real.sinh ((T - C) / K - lvl (Φ 0))) =
        max (2 * C₄) (Real.sqrt (2 * (Real.cosh (K + C) - 1))) * Real.exp (-(T / (2 * K))) +
        max (2 * C₄) (Real.sqrt (2 * (Real.cosh (K + C) - 1))) *
          (1 / Real.sinh ((T - C) / K - lvl (Φ 0))) := by ring
    have hbig : dist (bdMap n Φ ξ') (bdMap n Φ ξ) ≤
        max (2 * C₄) (Real.sqrt (2 * (Real.cosh (K + C) - 1))) * Real.exp (-(T / (2 * K))) +
        max (2 * C₄) (Real.sqrt (2 * (Real.cosh (K + C) - 1))) *
          (1 / Real.sinh ((T - C) / K - lvl (Φ 0))) := by
      linarith [h3, hsum, hmid, e1, e2, e3]
    exact le_trans hbig (le_of_eq hdistrib.symm)

end

end Work.Mostow.BdExt
