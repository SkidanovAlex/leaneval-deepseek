import Mathlib
import Submission.Work.Landing.Rays

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Landing.Rays


/-- For a Böttcher coordinate `φ` of `T_c`, the points of a dynamic ray whose
Böttcher modulus is bounded by `ρ` lie in a bounded set.

The only analytic input is the asymptotic clause of `IsDynBottcher`: outside a large compact set
`‖φ z - z‖ ≤ ‖z‖ / 2`, so there `‖z‖ / 2 ≤ ‖φ z‖`; together with `‖φ z‖ ≤ ρ` this bounds the
modulus of the ray point by `2 ρ`, while the (bounded) complement of that compact set handles the
remaining points. -/
theorem isBounded_dynRay_sublevel {c : ℂ} {φ : ℂ → ℂ} (h : Work.ParamRays.IsDynBottcher c φ)
    (θ : ℝ) (ρ : ℝ) :
    Bornology.IsBounded {z : ℂ | z ∈ Work.Landing.dynRay c φ θ ∧ ‖φ z‖ ≤ ρ} := by
  rw [Metric.isBounded_iff_subset_closedBall (0 : ℂ)]
  -- the asymptotic clause of the Böttcher coordinate, off a compact set
  have hev : ∀ᶠ z : ℂ in Filter.cocompact ℂ, ‖φ z - z‖ ≤ (1 / 2 : ℝ) * ‖z‖ :=
    h.2.2 (1 / 2) (by norm_num)
  have hev' : {z : ℂ | ‖φ z - z‖ ≤ (1 / 2 : ℝ) * ‖z‖} ∈ Filter.cocompact ℂ := hev
  rw [Filter.mem_cocompact] at hev'
  obtain ⟨K, hKc, hK⟩ := hev'
  -- the exceptional compact set is bounded, so it lies in a ball around the origin
  have hKb : Bornology.IsBounded K := hKc.isBounded
  obtain ⟨R, hR⟩ := hKb.subset_closedBall (0 : ℂ)
  refine ⟨max R (2 * ρ), ?_⟩
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have hzφ : ‖φ z‖ ≤ ρ := hz.2
  by_cases hzR : ‖z‖ ≤ R
  · exact le_trans hzR (le_max_left _ _)
  · -- then `z` is outside the exceptional compact set
    have hzK : z ∉ K := fun hzK => hzR (by
      have := Metric.mem_closedBall.mp (hR hzK)
      rwa [dist_zero_right] at this)
    have hbound : ‖φ z - z‖ ≤ (1 / 2 : ℝ) * ‖z‖ := hK hzK
    have htri : ‖z‖ ≤ ‖φ z - z‖ + ‖φ z‖ := by
      have h1 : (z - φ z) + φ z = z := by ring
      calc ‖z‖ = ‖(z - φ z) + φ z‖ := by rw [h1]
        _ ≤ ‖z - φ z‖ + ‖φ z‖ := norm_add_le _ _
        _ = ‖φ z - z‖ + ‖φ z‖ := by rw [norm_sub_rev]
    have hhalf : ‖z‖ / 2 ≤ ‖φ z‖ := by linarith
    have : ‖z‖ ≤ 2 * ρ := by linarith
    exact le_trans this (le_max_right _ _)

end Work.Landing.Rays
