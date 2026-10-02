import Mathlib
import Submission.Work.LandLeaves.TypeGeometry
import Submission.Work.LandLeaves.dynRay_local_subset
import Submission.Work.LandLeaves.rayAccum_subset_of_limit_alt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

/-- **Surjectivity of a Böttcher coordinate onto the exterior disc.**

`Work.Landing.RaysNearCircle c φ` asks that for every angle `θ` and every level `ρ > 1` the dynamic
ray `R_c(θ)` has a point of Böttcher modulus `≤ ρ`; this is the surjectivity half of Böttcher's
theorem.  The characterisation `Work.ParamRays.IsDynBottcher` already forces it: off the mandelbar
it is unsatisfiable, on the mandelbar the Böttcher coordinate is a homeomorphism onto the exterior
disc (`Work.LandLeaves.isDynBottcherHomeo_of_isDynBottcher`). -/
theorem raysNearCircle_of_isDynBottcher {c : ℂ} {φ : ℂ → ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) : Work.Landing.RaysNearCircle c φ := by
  intro θ ρ hρ
  have hH := Work.LandLeaves.isDynBottcherHomeo_of_isDynBottcher hφ
  set r : ℝ := (1 + ρ) / 2 with hr
  have hr1 : 1 < r := by rw [hr]; linarith
  have hrρ : r ≤ ρ := by rw [hr]; linarith
  have hw : 1 < ‖(r : ℂ) * Work.Landing.rayDirection θ‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith),
      Work.Landing.Rays.norm_rayDirection, mul_one]
    exact hr1
  obtain ⟨z, hz, hzφ⟩ := hH.2.2 _ hw
  refine ⟨z, ⟨hz, r, hr1, hzφ⟩, ?_⟩
  rw [hzφ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith),
    Work.Landing.Rays.norm_rayDirection, mul_one]
  exact hrρ

/-- The accumulation set of the ray at a limit angle contains `y`, provided every ray of the
sequence has accumulation set exactly `{y}` and `y` is a repelling periodic point.

The accumulation set `rayAccum c φ θ` is nonempty (`Work.LandLeaves.rayAccum_nonempty`, using the
surjectivity of the Böttcher coordinate `raysNearCircle_of_isDynBottcher`) and is contained in
`{y}` (`Work.LandLeaves.rayAccum_subset_of_limit_alt`, the "no jump-up" half of the closedness of
the type of a repelling point); hence it is `{y}` and in particular contains `y`. -/
theorem rayAccum_mem_of_limit {c : ℂ} {φ : ℂ → ℂ} {y : ℂ} {k : ℕ} {θ : ℝ} {u : ℕ → ℝ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y)
    (hu : Filter.Tendsto u Filter.atTop (nhds θ))
    (h : ∀ n : ℕ, Work.Landing.rayAccum c φ (u n) = {y}) :
    y ∈ Work.Landing.rayAccum c φ θ := by
  obtain ⟨x, hx⟩ :=
    Work.LandLeaves.rayAccum_nonempty hφ (raysNearCircle_of_isDynBottcher hφ) θ
  have hxy : x = y :=
    Set.mem_singleton_iff.mp (rayAccum_subset_of_limit_alt hφ hrep hu h hx)
  rw [← hxy]
  exact hx

end Work.LandLeaves
