import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Calculus.BumpFunction

open scoped Manifold

open scoped ContDiff ENNReal in
theorem contDiff_eq_one_on_isClosed_tsupport_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {A U : Set E} (hA : IsClosed A) (hU : IsOpen U) (hAU : A ⊆ U) : ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧ (∀ x ∈ A, f x = 1) ∧ tsupport f ⊆ U ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ 1) := by
  obtain ⟨V, hVopen, hAV, hVU⟩ := normal_exists_closure_subset hA hU hAU
  have hAV' : A ⊆ interior V := by rwa [hVopen.interior_eq]
  obtain ⟨F, hF1, hF0, hFr⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (𝓘(ℝ, E)) (n := ⊤) hA hAV'
  refine ⟨⇑F, F.contMDiff.contDiff, ?_, ?_, ?_, ?_⟩
  · intro x hx; exact hF1.self_of_nhdsSet x hx
  · intro x hx
    exact hVU (closure_mono (fun y hy => by
      by_contra hyV
      exact hy (hF0 y hyV)) hx)
  · intro x; exact (hFr x).1
  · intro x; exact (hFr x).2

end Commons.Analysis.Calculus.BumpFunction