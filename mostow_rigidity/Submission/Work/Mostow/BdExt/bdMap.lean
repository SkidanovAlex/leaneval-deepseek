import Mathlib
import Submission.Mostow.Interfaces
import Submission.Work.Mostow.BdExt.Basic
import Submission.Work.Mostow.BdExt.lawCosines
import Submission.Work.Mostow.BdExt.rayDist
import Submission.Work.Mostow.BdExt.stepSum
import Submission.Work.Mostow.BdExt.closeSeq
import Submission.Work.Mostow.BdExt.qiRayLimit
import Submission.Work.Mostow.BdExt.qiRayRate

/-!
# `bdMap`: the boundary extension of a quasi-isometry

For a quasi-isometry `Φ` of `ℍⁿ` (with constants `K, C`) and `ξ ∈ Sph n`, `bdMap n Φ ξ` is the
limit of the directions `dirv (Φ (ray ξ t))` of the image of the geodesic ray to `ξ`.

This module records the two properties of `bdMap` used by the rest of the development:

* `bdMap_spec`: `bdMap n Φ ξ ∈ Sph n` and `dirv (Φ (ray ξ k)) → bdMap n Φ ξ`;
* `bdMap_rate`: the *uniform* rate `‖dirv (Φ (ray ξ t)) - bdMap n Φ ξ‖ ≤ C₄ e^{-t/(2K)}` with `C₄`
  independent of `ξ`;
* `lvl_image_ray`: the level of the image of a ray grows at least linearly.
-/

namespace Work.Mostow.BdExt

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open Classical

noncomputable section

/-- The boundary extension of `Φ` at `ξ`: the limit of the directions of the quasi-geodesic ray
`Φ ∘ ray ξ`.  Junk (`0`) if the limit does not exist, or off `Sph n`. -/
def bdMap (n : ℕ) (Φ : E n → E n) (ξ : E n) : E n :=
  if h : ∃ η : E n, η ∈ Sph n ∧
      Filter.Tendsto (fun k : ℕ => dirv (Φ (ray ξ k))) Filter.atTop (nhds η)
    then h.choose else 0

/-- For a quasi-isometry with constants `K, C` the boundary map at `ξ ∈ Sph n` is a point of
`Sph n` and realises the visual limit of the image of the ray to `ξ`. -/
lemma bdMap_spec (n : ℕ) (hI : HypIsometryProp n) (Φ : E n → E n) (K C : ℝ)
    (hK : 1 ≤ K) (hC : 0 ≤ C)
    (hup : ∀ u v, hdist (Φ u) (Φ v) ≤ K * hdist u v + C)
    (hlow : ∀ u v, hdist u v ≤ K * hdist (Φ u) (Φ v) + C)
    (ξ : E n) (hξ : ξ ∈ Sph n) :
    bdMap n Φ ξ ∈ Sph n ∧
      Filter.Tendsto (fun k : ℕ => dirv (Φ (ray ξ k))) Filter.atTop (nhds (bdMap n Φ ξ)) := by
  obtain ⟨η, hηS, hηlim, -⟩ := qiRayLimit n hI Φ K C hK hC hup hlow ξ hξ
  have h : ∃ η : E n, η ∈ Sph n ∧
      Filter.Tendsto (fun k : ℕ => dirv (Φ (ray ξ k))) Filter.atTop (nhds η) :=
    ⟨η, hηS, hηlim⟩
  rw [bdMap, dif_pos h]
  exact Classical.choose_spec h

/-- The *uniform* rate of convergence of the boundary map: the constant `C₄` is independent of
`ξ ∈ Sph n`. -/
lemma bdMap_rate (n : ℕ) (hI : HypIsometryProp n) (Φ : E n → E n) (K C : ℝ)
    (hK : 1 ≤ K) (hC : 0 ≤ C)
    (hup : ∀ u v, hdist (Φ u) (Φ v) ≤ K * hdist u v + C)
    (hlow : ∀ u v, hdist u v ≤ K * hdist (Φ u) (Φ v) + C) :
    ∃ C₄ : ℝ, 0 ≤ C₄ ∧ ∀ (ξ : E n) (hξ : ξ ∈ Sph n) (t : ℝ), 0 ≤ t →
      ‖dirv (Φ (ray ξ t)) - bdMap n Φ ξ‖ ≤ C₄ * Real.exp (-(t / (2 * K))) := by
  obtain ⟨C₄, hC₄, hb⟩ := qiRayRate n hI Φ K C hK hC hup hlow
  refine ⟨C₄, hC₄, fun ξ hξ t ht => ?_⟩
  exact hb ξ hξ (bdMap n Φ ξ) (bdMap_spec n hI Φ K C hK hC hup hlow ξ hξ).2 t ht

/-- Lower bound for the hyperbolic level of the image of a ray. -/
lemma lvl_image_ray (n : ℕ) (hI : HypIsometryProp n) (Φ : E n → E n) (K C : ℝ)
    (hK : 1 ≤ K) (hC : 0 ≤ C)
    (hlow : ∀ u v, hdist u v ≤ K * hdist (Φ u) (Φ v) + C)
    (ξ : E n) (hξ : ξ ∈ Sph n) (t : ℝ) (ht : 0 ≤ t) :
    (t - C) / K - lvl (Φ 0) ≤ lvl (Φ (ray ξ t)) := by
  have h0 : ray ξ 0 = (0 : E n) := by simp [ray]
  have ht' : hdist (ray ξ 0) (ray ξ t) = t := by rw [h0]; exact hdist_zero_ray ξ hξ t ht
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have h1 : (hdist (ray ξ 0) (ray ξ t) - C) / K ≤ hdist (Φ (ray ξ 0)) (Φ (ray ξ t)) := by
    rw [div_le_iff₀ hKpos]
    nlinarith [hlow (ray ξ 0) (ray ξ t)]
  have h2 : hdist (Φ (ray ξ 0)) (Φ (ray ξ t)) = hdist (Φ 0) (Φ (ray ξ t)) := by rw [h0]
  have h3 : lvl (Φ (ray ξ t)) ≥ hdist (Φ 0) (Φ (ray ξ t)) - lvl (Φ 0) := by
    have htri := hI.2.2.2.1 (Φ 0) 0 (Φ (ray ξ t))
    have hs := hI.2.1 (Φ 0) 0
    rw [lvl, lvl]
    linarith
  rw [h2] at h1
  have h4 : (hdist (ray ξ 0) (ray ξ t) - C) / K - lvl (Φ 0) ≤ lvl (Φ (ray ξ t)) :=
    calc (hdist (ray ξ 0) (ray ξ t) - C) / K - lvl (Φ 0)
        ≤ hdist (Φ 0) (Φ (ray ξ t)) - lvl (Φ 0) := by linarith [h1]
      _ ≤ lvl (Φ (ray ξ t)) := h3
  rw [ht'] at h4
  exact h4


end

end Work.Mostow.BdExt
