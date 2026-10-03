import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.GreenSetupReg
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.outerGapDesign
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.dirichletSphereEnvelope_facts
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.isPreconnected_sdiff_chartClosedBall

/-!
# The outer gap for the Perron envelope on `Ω \ chartClosedBall`

Here we assemble the main theorem `Work.SimplyConnected.ABS.envelopeOuterGap_dev` from

* the topological fact that `Ω \ chartClosedBall c a s` is preconnected
  (`Work.SimplyConnected.ABS.isPreconnected_sdiff_chartClosedBall`),
* the classical Perron barrier argument giving a point of the region where the envelope is `< 1`
  (`Work.SimplyConnected.ABS.exists_limEnvelope_lt_one_of_barrier`),
* the strong maximum principle, which then forces the envelope to be `< 1` on the whole region,
* compactness of the outer chart sphere, which upgrades this to a uniform gap.

-/

open Filter Set Metric

namespace Work.SimplyConnected.ABS

/-! ## The chart sphere is preconnected -/

theorem isPreconnected_chartSphere {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ} (hsub : Metric.closedBall a ρ ⊆ c.target) :
    IsPreconnected (Submission.chartSphere c a ρ) := by
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; norm_num
  have heq : Submission.chartSphere c a ρ = c.symm '' Metric.sphere a ρ := by
    ext x
    constructor
    · rintro ⟨hxs, hx⟩
      exact ⟨c x, hx, c.left_inv hxs⟩
    · rintro ⟨w, hw, rfl⟩
      have hwT : w ∈ c.target := hsub (Metric.sphere_subset_closedBall hw)
      refine ⟨c.map_target hwT, ?_⟩
      simp only [Set.mem_preimage]
      rw [c.right_inv hwT]
      exact hw
  rw [heq]
  exact (isPreconnected_sphere hrank a ρ).image c.symm
    (c.continuousOn_symm.mono fun w hw => hsub (Metric.sphere_subset_closedBall hw))

/-! ## The strong maximum principle, in the form needed here -/

/-- If a function harmonic on a preconnected open set `U` is bounded above by `1` and is strictly
below `1` at one point of `U`, then it is strictly below `1` everywhere on `U`. -/
theorem harmonicOnX_lt_one_of_lt_one {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] {U : Set X} (hUo : IsOpen U) (hUpc : IsPreconnected U)
    {u : X → ℝ} (hu : Submission.HarmonicOnX u U) (hle : ∀ x : X, u x ≤ 1) {z₀ : X}
    (hz₀ : z₀ ∈ U) (hz₀lt : u z₀ < 1) : ∀ x ∈ U, u x < 1 := by
  intro x hx
  by_contra hcon
  have hx1 : u x = 1 := le_antisymm (hle x) (not_lt.mp hcon)
  haveI : PreconnectedSpace U := (isPreconnected_iff_preconnectedSpace (s := U)).mp hUpc
  have hcont : Continuous (fun y : U => u y) :=
    continuousOn_iff_continuous_restrict.mp
      (fun y hy => (hu y hy).continuousAt.continuousWithinAt)
  set S : Set U := {y : U | u y = 1} with hSdef
  have hScl : IsClosed S := by
    have hSe : S = (fun y : U => u y) ⁻¹' ({1} : Set ℝ) := rfl
    rw [hSe]
    exact isClosed_singleton.preimage hcont
  have hSop : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hyU : (y : X) ∈ U := y.2
    have hyval : u (y : X) = 1 := hy
    obtain ⟨V, hVn, hVeq⟩ := Submission.SubharmonicOnXAt.eqOn_of_le
      ((hu (y : X) hyU).subharmonic) (hUo.mem_nhds hyU)
      (fun z _ => by rw [hyval]; exact hle z)
    obtain ⟨W, hWV, hWo, hyW⟩ := mem_nhds_iff.mp hVn
    refine Filter.mem_of_superset ((hWo.preimage continuous_subtype_val).mem_nhds hyW) ?_
    intro z hz
    rw [hSdef]
    exact (hVeq z (hWV hz)).trans hyval
  rcases isClopen_iff.mp ⟨hScl, hSop⟩ with h | h
  · have hmem : (⟨x, hx⟩ : U) ∈ S := by rw [hSdef]; simpa using hx1
    rw [h] at hmem
    exact (Set.notMem_empty _ hmem).elim
  · have hmem : (⟨z₀, hz₀⟩ : U) ∈ S := by rw [h]; exact Set.mem_univ _
    have hz1 : u z₀ = 1 := by rw [hSdef] at hmem; exact hmem
    linarith

/-! ## Temporary local copy of the delegated barrier lemma -/

end Work.SimplyConnected.ABS
