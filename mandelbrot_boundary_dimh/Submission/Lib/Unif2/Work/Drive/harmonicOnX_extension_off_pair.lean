import Mathlib
import Submission.Lib.Unif2.Work.Potential.removable_singularity_of_bounded_near
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.localRemovability

/-!
# Removing one of two punctures

`Work.Drive.harmonicOnX_extension_off_pair`: if `u` is harmonic on `X \ {q, b}` (`q ≠ b`) and is
bounded in a punctured neighbourhood of `q`, then `u` extends to a function `U` harmonic on
`X \ {b}` and agreeing with `u` off `q`.

The proof is the manifold-level removable singularity, localised at `q`:  the chart at `q` is
shrunk to a Euclidean ball `B` whose `chartAt ℂ q`-image lies in the chart target, inside (the
preimage of) the neighbourhood `V` on which `u` is bounded, and inside the complement of `b`.
On the punctured ball the pullback of `u` is harmonic and bounded, so the planar removable
singularity `Work.Potential.punctured_ball_harmonic_extension` (packaged for manifolds as
`Work.SimplyConnected.ABS.exists_extension_of_punctured_chartBall`) produces a function `h`
harmonic on `B` and equal to the pullback of `u` off the centre.  The extension is then
`U := Function.update u q (h (chartAt ℂ q q))`: harmonic at `q` because near `q` it agrees with
`h ∘ chartAt ℂ q`, and harmonic elsewhere because there it agrees with `u` off a point.
-/

open Filter Set
open scoped Topology Manifold

noncomputable section

namespace Work.Drive

theorem harmonicOnX_extension_off_pair {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {q b : X} (hqb : q ≠ b) {u : X → ℝ} (hu : Submission.HarmonicOnX u (Set.univ \ {q, b}))
    (hbdd : ∃ M : ℝ, ∃ V : Set X, V ∈ nhds q ∧ ∀ x ∈ V, x ≠ q → |u x| ≤ M) :
    ∃ U : X → ℝ, Submission.HarmonicOnX U (Set.univ \ {b}) ∧ ∀ x : X, x ≠ q → U x = u x := by
  classical
  obtain ⟨M, V, hVmem, hVb⟩ := hbdd
  let c : OpenPartialHomeomorph X ℂ := chartAt ℂ q
  have hqsrc : q ∈ c.source := mem_chart_source ℂ q
  have hqtgt : c q ∈ c.target := c.map_source hqsrc
  -- the preimage under `c.symm` of the three relevant neighbourhoods of `q`
  have hVnhds : {z : ℂ | c.symm z ∈ V} ∈ 𝓝 (c q) :=
    (c.continuousAt_symm hqtgt).eventually (by rw [c.left_inv hqsrc]; exact hVmem)
  have hbnhds : {z : ℂ | c.symm z ∈ ({b}ᶜ : Set X)} ∈ 𝓝 (c q) :=
    (c.continuousAt_symm hqtgt).eventually
      (by rw [c.left_inv hqsrc]
          exact (isClosed_singleton.isOpen_compl).mem_nhds (by simpa using hqb))
  have hnhds : {z : ℂ | c.symm z ∈ V} ∩ {z : ℂ | c.symm z ∈ ({b}ᶜ : Set X)} ∩ c.target
      ∈ 𝓝 (c q) :=
    Filter.inter_mem (Filter.inter_mem hVnhds hbnhds) (c.open_target.mem_nhds hqtgt)
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp hnhds
  have hballtarget : Metric.ball (c q) ρ ⊆ c.target := fun z hz => (hρsub hz).2
  have hballV : ∀ z ∈ Metric.ball (c q) ρ, c.symm z ∈ V := fun z hz => (hρsub hz).1.1
  have hballb : ∀ z ∈ Metric.ball (c q) ρ, c.symm z ≠ b := by
    intro z hz h
    have h' := (hρsub hz).1.2
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at h'
    exact h' h
  -- harmonicity and boundedness on the punctured chart ball
  have hharm : Submission.HarmonicOnX u (Submission.chartBall c (c q) ρ \ {q}) := by
    intro x hx
    have hxball : x ∈ Submission.chartBall c (c q) ρ := hx.1
    have hxne : x ∉ ({q} : Set X) := hx.2
    rw [Submission.mem_chartBall] at hxball
    have hxq : x ≠ q := by simpa using hxne
    have hxb : x ≠ b := by
      have h1 := hballb (c x) hxball.2
      rwa [c.left_inv hxball.1] at h1
    exact hu x ⟨mem_univ x, by simp [hxq, hxb]⟩
  have hbd : ∀ x ∈ Submission.chartBall c (c q) ρ, x ≠ q → |u x| ≤ M := by
    intro x hxball hxq
    rw [Submission.mem_chartBall] at hxball
    have hxV : x ∈ V := by
      have h1 := hballV (c x) hxball.2
      rwa [c.left_inv hxball.1] at h1
    exact hVb x hxV hxq
  -- the local extension of the pullback across the puncture
  obtain ⟨h, hharmh, heq⟩ := Work.SimplyConnected.ABS.exists_extension_of_punctured_chartBall
    (ζ := q) (ρ := ρ) (M := M) hρpos hballtarget hharm hbd
  refine ⟨Function.update u q (h (c q)), ?_, ?_⟩
  · intro x hx
    by_cases hxq : x = q
    · -- at the puncture: `U` agrees near `q` with the harmonic function `h ∘ c`
      rw [hxq]
      show InnerProductSpace.HarmonicAt (Function.update u q (h (c q)) ∘ c.symm) (c q)
      have hev : h =ᶠ[𝓝 (c q)] (Function.update u q (h (c q)) ∘ c.symm) := by
        filter_upwards [Metric.ball_mem_nhds (c q) hρpos] with z hz
        by_cases hzq : z = c q
        · rw [hzq]
          show h (c q) = Function.update u q (h (c q)) (c.symm (c q))
          rw [c.left_inv hqsrc]
          rw [Function.update_self]
        · have hzt : z ∈ c.target := hballtarget hz
          have hzs : c.symm z ≠ q := by
            intro hh
            exact hzq (by rw [← c.right_inv hzt, hh])
          have hz' : ‖z - c q‖ < ρ := by
            simpa only [Metric.mem_ball, dist_eq_norm] using hz
          rw [heq z hz' hzq, Function.comp_apply, Function.update_of_ne hzs]
      exact (InnerProductSpace.harmonicAt_congr_nhds hev).mp
        (hharmh (c q) (by rw [sub_self, norm_zero]; exact hρpos))
    · -- away from the puncture: `U` agrees with `u` near `x`
      have hxb : x ≠ b := by simpa using hx.2
      have hev : u =ᶠ[𝓝 x] Function.update u q (h (c q)) := by
        filter_upwards [isOpen_ne.mem_nhds hxq] with y hy
        rw [Function.update_of_ne hy]
      exact Work.Potential.harmonicOnXAt_congr (hu x ⟨mem_univ x, by simp [hxq, hxb]⟩) hev
  · intro x hxq
    rw [Function.update_of_ne hxq]

end Work.Drive
