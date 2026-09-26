import Mathlib
import Submission.Work.BoxShrink.Bubble.Toolkit.regionEquivalent_of_surgeryStepZero
import Submission.Work.BoxShrink.Bubble.Toolkit.regionEquivalent_trans

namespace Work.BoxShrink.Bubble.Sweep

open LeanEval.KnotTheory.PardonDistortion
open Set

/-- **A loop-level sweep is `RegionEquivalent` at its endpoints.**

Along a `SweepLoops` the loop content of the region is transported between the regions of nearby
parameters: away from the exceptional set this is exactly the `regular` clause, and at an
exceptional parameter a `SurgeryStepZero` is converted into a `RegionEquivalent` by
`regionEquivalent_of_surgeryStepZero` (using that the two regions are non-empty and contained in
`P.carrier`), while the other branch of the `surgery` clause is already a `RegionEquivalent`.

The relation `RegionEquivalent P (S.region 0) ·` is then locally constant: near every parameter `t`
the region is equivalent to `S.region t`, so by transitivity and symmetry the property "is
equivalent to the region at `0`" only depends on a neighbourhood of `t`.  Hence the set `T` of
parameters whose region is equivalent to `S.region 0` is open *and* closed; it contains `0`
(reflexivity) and `ℝ` is preconnected, so `T = ℝ` and in particular `1 ∈ T`. -/
theorem regionEquivalent_endpoints
    {P : Work.CoreTopology.ParamTorus}
    (S : Work.SurgeryInvariance.SweepLoops P)
    (hcarrier : ∀ t : ℝ, S.region t ⊆ P.carrier)
    (hne : ∀ t : ℝ, (S.region t).Nonempty) :
    Work.SurgeryInvariance.RegionEquivalent P (S.region 0) (S.region 1) := by
  -- Near every parameter `t` the region is `RegionEquivalent` to the region of nearby parameters.
  have hlocal : ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ s : ℝ, |s - t| < ε →
        Work.SurgeryInvariance.RegionEquivalent P (S.region t) (S.region s) := by
    intro t
    by_cases ht : t ∈ S.exc
    · obtain ⟨ε, hε, hstep⟩ := S.surgery t ht
      refine ⟨ε, hε, fun s hs => ?_⟩
      rcases hstep s hs with h | h
      · exact Work.BoxShrink.Bubble.Toolkit.regionEquivalent_of_surgeryStepZero h
          (hcarrier t) (hcarrier s) (hne t) (hne s)
      · exact h
    · obtain ⟨ε, hε, -, heq⟩ := S.regular t ht
      exact ⟨ε, hε, heq⟩
  -- The set of parameters whose region is equivalent to `S.region 0`.
  let T : Set ℝ := {t | Work.SurgeryInvariance.RegionEquivalent P (S.region 0) (S.region t)}
  have hTclosed : IsClosed T := by
    rw [← isOpen_compl_iff]
    rw [Metric.isOpen_iff]
    intro t ht
    obtain ⟨ε, hε, hb⟩ := hlocal t
    refine ⟨ε, hε, fun s hs => ?_⟩
    rw [Metric.mem_ball, Real.dist_eq] at hs
    intro hsT
    exact ht (Work.BoxShrink.Bubble.Toolkit.regionEquivalent_trans hsT
      (Work.BoxShrink.Bubble.Toolkit.regionEquivalent_symm (hb s hs)))
  have hTopen : IsOpen T := by
    rw [Metric.isOpen_iff]
    intro t ht
    obtain ⟨ε, hε, hb⟩ := hlocal t
    refine ⟨ε, hε, fun s hs => ?_⟩
    rw [Metric.mem_ball, Real.dist_eq] at hs
    exact Work.BoxShrink.Bubble.Toolkit.regionEquivalent_trans ht (hb s hs)
  have hne0 : T.Nonempty :=
    ⟨0, Work.SurgeryInvariance.RegionEquivalent.refl (P := P) (S.region 0)⟩
  have hall : T = Set.univ := IsClopen.eq_univ ⟨hTclosed, hTopen⟩ hne0
  have h1 : (1 : ℝ) ∈ T := by rw [hall]; exact Set.mem_univ 1
  exact h1

end Work.BoxShrink.Bubble.Sweep
