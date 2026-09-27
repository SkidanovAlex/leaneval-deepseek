import Mathlib
import Submission.Work.Mostow.BdExt.Basic
import Submission.Work.Mostow.BusemannRay
import Submission.Work.Mostow.BdExt.rayDist
import Submission.Work.Mostow.BdExt.rayLawCosines

/-!
# The chart of a boundary ray: `rayChart`

For a boundary point `ξ ∈ Sph n` the map `t ↦ ray ξ t = sinh t • ξ` is the geodesic ray issued
from the chart origin `0` towards `ξ`, parametrised by hyperbolic arclength.  This module records
the resulting explicit chart of the ray:

* `tpart (ray ξ t) = cosh t` and `‖ray ξ t‖ = sinh |t|` (the hyperboloid coordinates of the ray),
* `dirv (ray ξ t) = ξ` for `t > 0` (its Euclidean direction from `0`),
* `cosh (hdist (ray ξ s) (ray ξ t)) = cosh (s - t)` and `hdist 0 (ray ξ t) = t` for `t ≥ 0`
  (unit-speed parametrisation), `lvl (ray ξ t) = t`,
* the hyperbolic law of cosines for two rays:
  `cosh (hdist (ray ξ s) (ray η t)) = cosh s * cosh t - sinh s * sinh t * ⟪ξ, η⟫`.
-/

namespace Work.Mostow.BdExt

open Submission.Mostow

noncomputable section

theorem rayChart (n : ℕ) :
    (∀ (ξ : Submission.Mostow.E n) (t : ℝ), ξ ∈ Submission.Mostow.Sph n → Submission.Mostow.tpart (Work.Mostow.BdExt.ray ξ t) = Real.cosh t) ∧
    (∀ (ξ : Submission.Mostow.E n) (t : ℝ), ξ ∈ Submission.Mostow.Sph n → ‖Work.Mostow.BdExt.ray ξ t‖ = Real.sinh |t|) ∧
    (∀ (ξ : Submission.Mostow.E n) (t : ℝ), ξ ∈ Submission.Mostow.Sph n → 0 < t → Work.Mostow.BdExt.dirv (Work.Mostow.BdExt.ray ξ t) = ξ) ∧
    (∀ (ξ : Submission.Mostow.E n) (s t : ℝ), ξ ∈ Submission.Mostow.Sph n →
       Real.cosh (Submission.Mostow.hdist (Work.Mostow.BdExt.ray ξ s) (Work.Mostow.BdExt.ray ξ t)) = Real.cosh (s - t)) ∧
    (∀ (ξ : Submission.Mostow.E n) (t : ℝ), ξ ∈ Submission.Mostow.Sph n → 0 ≤ t → Submission.Mostow.hdist 0 (Work.Mostow.BdExt.ray ξ t) = t) ∧
    (∀ (ξ : Submission.Mostow.E n) (t : ℝ), ξ ∈ Submission.Mostow.Sph n → 0 ≤ t → Work.Mostow.BdExt.lvl (Work.Mostow.BdExt.ray ξ t) = t) ∧
    (∀ (ξ η : Submission.Mostow.E n) (s t : ℝ), ξ ∈ Submission.Mostow.Sph n → η ∈ Submission.Mostow.Sph n →
       Real.cosh (Submission.Mostow.hdist (Work.Mostow.BdExt.ray ξ s) (Work.Mostow.BdExt.ray η t)) =
         Real.cosh s * Real.cosh t - Real.sinh s * Real.sinh t * inner ℝ ξ η) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `tpart (ray ξ t) = cosh t`
    intro ξ t hξ
    have hξn : ‖ξ‖ = 1 := (mem_Sph_iff ξ).mp hξ
    simpa only [ray] using tpart_sinh_smul ξ t hξn
  · -- `‖ray ξ t‖ = sinh |t|`
    intro ξ t hξ
    have hξn : ‖ξ‖ = 1 := (mem_Sph_iff ξ).mp hξ
    rw [ray, norm_smul, hξn, mul_one, Real.norm_eq_abs, Real.abs_sinh]
  · -- `dirv (ray ξ t) = ξ` for `t > 0`
    intro ξ t hξ ht
    have hξn : ‖ξ‖ = 1 := (mem_Sph_iff ξ).mp hξ
    have hsinh : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht
    rw [dirv, ray, norm_smul, hξn, mul_one, Real.norm_eq_abs, abs_of_pos hsinh,
      smul_smul, inv_mul_cancel₀ (ne_of_gt hsinh), one_smul]
  · -- `cosh (hdist (ray ξ s) (ray ξ t)) = cosh (s - t)`
    intro ξ s t hξ
    rw [hdist_ray_ray ξ hξ s t, Real.cosh_abs]
  · -- `hdist 0 (ray ξ t) = t` for `t ≥ 0`
    intro ξ t hξ ht
    exact (rayDist n).2 ξ t hξ ht
  · -- `lvl (ray ξ t) = t` for `t ≥ 0`
    intro ξ t hξ ht
    show Submission.Mostow.hdist 0 (Work.Mostow.BdExt.ray ξ t) = t
    exact (rayDist n).2 ξ t hξ ht
  · -- the hyperbolic law of cosines for two rays
    intro ξ η s t hξ hη
    exact rayLawCosines n ξ η s t hξ hη

end

end Work.Mostow.BdExt
