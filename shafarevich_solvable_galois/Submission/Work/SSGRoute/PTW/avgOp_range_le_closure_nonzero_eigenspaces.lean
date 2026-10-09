import Mathlib
import Submission.Work.SSGRoute.PTW.RegularRep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PTW

open Module

/-- **Spectral theorem, range form.** For a compact self-adjoint operator `A` on a complex
Hilbert space the range of `A` is contained in the closure of the span of the eigenspaces
belonging to nonzero eigenvalues.

Proof: it suffices to show `A z = 0` for `z` orthogonal to all nonzero eigenspaces. For such a
`z`, `A z` is orthogonal to every eigenspace: to `E_0 = ker A` by symmetry, and to `E_μ` for
`μ ≠ 0` because `⟪A z, v⟫ = ⟪z, A v⟫ = μ ⟪z, v⟫ = 0` for `v ∈ E_μ`. Hence `A z` lies in the
orthogonal complement of `⨆ μ, E_μ`, which is `⊥` by
`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`. -/
theorem compact_selfAdjoint_range_le_closure_nonzero_eigenspaces {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {A : E →L[𝕜] E} (hA : IsCompactOperator A) (hs : (A : E →ₗ[𝕜] E).IsSymmetric) :
    A.range ≤ (⨆ (lam : {m : 𝕜 // m ≠ 0}),
      Module.End.eigenspace (A : E →ₗ[𝕜] E) lam.1).topologicalClosure := by
  set W : Submodule 𝕜 E := ⨆ (lam : {m : 𝕜 // m ≠ 0}),
    Module.End.eigenspace (A : E →ₗ[𝕜] E) lam.1 with hW
  -- every vector orthogonal to all nonzero eigenspaces is killed by `A`
  have key : ∀ z ∈ Wᗮ, (A : E →ₗ[𝕜] E) z = 0 := by
    intro z hz
    have hmem : (A : E →ₗ[𝕜] E) z ∈
        (⨆ μ : 𝕜, Module.End.eigenspace (A : E →ₗ[𝕜] E) μ)ᗮ := by
      rw [← Submodule.iInf_orthogonal, Submodule.mem_iInf]
      intro μ
      rw [Submodule.mem_orthogonal]
      intro v hv
      have hvA : (A : E →ₗ[𝕜] E) v = μ • v := (Module.End.mem_eigenspace_iff).mp hv
      rw [← hs v z]
      rcases eq_or_ne μ 0 with rfl | hμ
      · rw [hvA, zero_smul, inner_zero_left]
      · have hvW : v ∈ W := by
          rw [hW]
          exact le_iSup (fun lam : {m : 𝕜 // m ≠ 0} =>
            Module.End.eigenspace (A : E →ₗ[𝕜] E) lam.1) ⟨μ, hμ⟩ hv
        have hvz : inner 𝕜 v z = 0 := (Submodule.mem_orthogonal W z).mp hz v hvW
        rw [hvA, inner_smul_left, hvz, mul_zero]
    rw [ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hA hs] at hmem
    simpa using hmem
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  intro y hy
  obtain ⟨x, rfl⟩ := (LinearMap.mem_range.mp hy)
  rw [Submodule.mem_orthogonal]
  intro z hz
  rw [← inner_conj_symm z ((A : E →ₗ[𝕜] E) x), hs x z, key z hz]
  simp

/-- For a compact self-adjoint operator `A = avgOp ξ`: `A.range ≤ closure (⨆ λ ≠ 0, E_λ)`.
`A.range ≤ (ker A)ᗮ` (symmetry) and `ker A = E_0 ⊥ E_λ` for `λ ≠ 0`; the spectral theorem
`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hc hs`
(`⨆ μ : ℂ, E_μ)ᗮ = ⊥` (note: over *all* `μ`, including `0`) gives
`E_0ᗮ ∩ (⨆ λ ≠ 0, E_λ)ᗮ = ⊥`, whence `E_0ᗮ ≤ closure (⨆ λ ≠ 0, E_λ)`. -/
theorem avgOp_range_le_closure_nonzero_eigenspaces {Q : Type*} [Group Q] [TopologicalSpace Q]
    [IsTopologicalGroup Q] [CompactSpace Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q]
    {μ : MeasureTheory.Measure Q} [MeasureTheory.Measure.IsMulLeftInvariant μ]
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsLocallyFiniteMeasure μ]
    [MeasureTheory.Measure.InnerRegularCompactLTTop μ] (ξ : MeasureTheory.Lp ℂ 2 μ)
    (hc : IsCompactOperator (Work.SSGRoute.PTW.avgOp (μ := μ) ξ))
    (hs : ((Work.SSGRoute.PTW.avgOp (μ := μ) ξ : MeasureTheory.Lp ℂ 2 μ →L[ℂ] MeasureTheory.Lp ℂ 2 μ) :
        MeasureTheory.Lp ℂ 2 μ →ₗ[ℂ] MeasureTheory.Lp ℂ 2 μ).IsSymmetric) :
    (Work.SSGRoute.PTW.avgOp (μ := μ) ξ).range ≤
      (⨆ (lam : {m : ℂ // m ≠ 0}), Module.End.eigenspace
        ((Work.SSGRoute.PTW.avgOp (μ := μ) ξ : MeasureTheory.Lp ℂ 2 μ →L[ℂ] MeasureTheory.Lp ℂ 2 μ) :
          MeasureTheory.Lp ℂ 2 μ →ₗ[ℂ] MeasureTheory.Lp ℂ 2 μ) lam.1).topologicalClosure := by
  exact compact_selfAdjoint_range_le_closure_nonzero_eigenspaces hc hs

end Work.SSGRoute.PTW
