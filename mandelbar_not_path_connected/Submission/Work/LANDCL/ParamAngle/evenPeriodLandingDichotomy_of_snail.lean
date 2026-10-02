import Mathlib
import Submission.Work.LANDCL.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LANDCL.ParamAngle

/-- **The Snail dichotomy implies the even-period landing dichotomy.**

`Work.LANDCL.SnailDichotomy` is the Snail-lemma statement that a periodic point which is the
landing point of a dynamic ray and is not attracting is repelling or parabolic; here it is
consumed at the value `k = 6` needed for the even-period landing dichotomy of
`Work.Landing.EvenPeriodLandingDichotomy`.

The only analytic input beyond `SnailDichotomy` is the geometric hypothesis
`Work.Landing.AttractingCyclesInner c` (attracting cycles lie in the interior of the filled Julia
set): it excludes `z` from being attracting, because the landing point of a ray lies in the
closure of the escaping set (`Work.Landing.rayAccum_subset_closure_escaping`), whereas an
attracting point has a whole neighbourhood disjoint from the escaping set.

This is the even-period analogue of `Work.Landing.landsAt_repelling_or_parabolic` (the odd-period
form, which uses `deriv_tsq_iterate_odd_real` instead of the Snail input). -/
theorem evenPeriodLandingDichotomy_of_snail {c : ℂ} (h : Work.LANDCL.SnailDichotomy)
    (hgeo : Work.Landing.AttractingCyclesInner c) :
    Work.Landing.EvenPeriodLandingDichotomy c := by
  intro θ z hper _hex hland
  -- The landing point lies in the closure of the escaping set.
  have hclos : z ∈ closure (Work.ParamRays.escapingSet c) := by
    obtain ⟨φ, _hφ, hland'⟩ := hland
    have hz : z ∈ Work.Landing.rayAccum c φ θ := by
      rw [show Work.Landing.rayAccum c φ θ = {z} from hland']
      exact Set.mem_singleton z
    exact Work.Landing.rayAccum_subset_closure_escaping c φ θ hz
  -- Hence it is not an attracting point, by `AttractingCyclesInner`.
  have hnotattr : ¬ Work.Landing.IsAttracting c 6 z := by
    intro hattr
    obtain ⟨ε, hε, hball⟩ := hgeo z ⟨6, hattr⟩
    rw [Metric.mem_closure_iff] at hclos
    obtain ⟨w, hw, hwd⟩ := hclos ε hε
    exact hball w (by simpa only [dist_comm z w, dist_eq_norm] using hwd) hw
  -- The Snail dichotomy at period `6` gives repelling or parabolic.
  rcases h c θ 6 z (by norm_num) hper hland hnotattr with hrep | hpar
  · exact Or.inl ⟨6, hrep.1.2, hrep.2⟩
  · exact Or.inr ⟨6, hpar⟩

end Work.LANDCL.ParamAngle
