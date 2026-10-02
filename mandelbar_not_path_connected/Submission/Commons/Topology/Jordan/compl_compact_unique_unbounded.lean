import Mathlib
import Submission.Commons.Topology.Connected.isPreconnected_compl_closedBall

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open Set Metric
open scoped Topology

namespace Commons.Topology.Jordan

noncomputable section

/-- **A compact subset of the plane has at most one unbounded complementary component.**

If `K ⊆ ℂ` is compact and two points `x`, `y` of the complement `Kᶜ` have unbounded
connected components in `Kᶜ`, then these components coincide.

Indeed, `K` is contained in some closed ball `closedBall 0 R`, so the exterior
`{z : ℂ | R < ‖z‖}` is a preconnected subset of `Kᶜ`.  An unbounded component of `Kᶜ`
cannot be contained in `closedBall 0 R`, hence meets the exterior; since the exterior is
preconnected it is contained in every unbounded component.  Two unbounded components thus
share a point and are equal. -/
theorem compl_compact_unique_unbounded {K : Set ℂ} (hK : IsCompact K)
    {x y : ℂ} (hx : x ∈ Kᶜ) (hy : y ∈ Kᶜ)
    (hnx : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ x))
    (hny : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ y)) :
    connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ y := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hK.isBounded
  -- the exterior of the ball is contained in the complement of `K`
  have hEsub : {z : ℂ | R < ‖z‖} ⊆ Kᶜ := by
    intro z hz
    simp only [mem_compl_iff]
    intro hzK
    have h1 : ‖z‖ ≤ R := by
      have := hR hzK
      simpa [Metric.mem_closedBall, dist_zero_right] using this
    have hz' : R < ‖z‖ := hz
    linarith
  have hEpre : IsPreconnected {z : ℂ | R < ‖z‖} := by
    simpa using Commons.Topology.Connected.isPreconnected_compl_closedBall (0 : ℂ) R
  have hEne : ({z : ℂ | R < ‖z‖} : Set ℂ).Nonempty := by
    refine ⟨((R + 1 : ℝ) : ℂ), ?_⟩
    change R < ‖((R + 1 : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_eq_abs]
    linarith [le_abs_self (R + 1)]
  -- every unbounded component meets the exterior
  have hmeet : ∀ z : ℂ, ¬ Bornology.IsBounded (connectedComponentIn Kᶜ z) →
      ({z : ℂ | R < ‖z‖} ∩ connectedComponentIn Kᶜ z).Nonempty := by
    intro z hz
    by_contra hcon
    apply hz
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset ?_
    intro w hw
    by_contra hw'
    have hwE : w ∈ {z : ℂ | R < ‖z‖} := by
      rw [Metric.mem_closedBall, dist_zero_right] at hw'
      exact lt_of_not_ge hw'
    exact hcon ⟨w, hwE, hw⟩
  -- the exterior is contained in every unbounded component
  have hex : ∀ z : ℂ, ¬ Bornology.IsBounded (connectedComponentIn Kᶜ z) →
      {z : ℂ | R < ‖z‖} ⊆ connectedComponentIn Kᶜ z := by
    intro z hz
    obtain ⟨u, huE, huz⟩ := hmeet z hz
    have h1 : {z : ℂ | R < ‖z‖} ⊆ connectedComponentIn Kᶜ u :=
      hEpre.subset_connectedComponentIn huE hEsub
    rwa [← connectedComponentIn_eq huz] at h1
  -- both components contain every point of the exterior, hence coincide
  obtain ⟨e, heE⟩ := hEne
  have h1 : e ∈ connectedComponentIn Kᶜ x := hex x hnx heE
  have h2 : e ∈ connectedComponentIn Kᶜ y := hex y hny heE
  rw [connectedComponentIn_eq h1, connectedComponentIn_eq h2]

end

end Commons.Topology.Jordan
