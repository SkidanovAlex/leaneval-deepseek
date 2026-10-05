import Mathlib

namespace Work.RPB.Port.Drive

open scoped Manifold ContDiff Topology
open Manifold Filter

/-- A `C^n` immersion (in the chart-based sense of Mathlib's `IsImmersionAtOfComplement`)
between a `1`-dimensional manifold modelled on `EuclideanSpace ℝ (Fin 1)` and the plane `ℝ × ℝ`
has injective manifold derivative, for `n ≥ 1`. -/
theorem mfderiv_injective_of_immersionAt
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : M → ℝ × ℝ} {x : M} {n : ℕ∞ω}
    (hf : IsImmersionAtOfComplement F (𝓡 1) (𝓘(ℝ, ℝ × ℝ)) n f x) (hn : 1 ≤ n) :
    Function.Injective (mfderiv (𝓡 1) (𝓘(ℝ, ℝ × ℝ)) f x) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact absurd hn (by simp)
  have hx : x ∈ hf.domChart.source := hf.mem_domChart_source
  have hfx : f x ∈ hf.codChart.source := hf.mem_codChart_source
  -- `f` is differentiable at `x`, being an immersion there
  have hdf : MDifferentiableAt (𝓡 1) (𝓘(ℝ, ℝ × ℝ)) f x :=
    hf.contMDiffAt.mdifferentiableAt hn0
  -- the extended codomain chart is differentiable at `f x`
  have hmd_cod : MDifferentiableAt (𝓘(ℝ, ℝ × ℝ)) (𝓘(ℝ, ℝ × ℝ))
      (hf.codChart.extend (𝓘(ℝ, ℝ × ℝ))) (f x) := by
    have h1 : hf.codChart ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℝ × ℝ)) 1 (ℝ × ℝ) :=
      IsManifold.maximalAtlas_subset_of_le hn hf.codChart_mem_maximalAtlas
    have hc : MDifferentiableAt (𝓘(ℝ, ℝ × ℝ)) (𝓘(ℝ, ℝ × ℝ))
        (hf.codChart : ℝ × ℝ → ℝ × ℝ) (f x) :=
      mdifferentiableAt_of_mem_maximalAtlas h1 hfx
    have hJ : MDifferentiableAt (𝓘(ℝ, ℝ × ℝ)) (𝓘(ℝ, ℝ × ℝ))
        (𝓘(ℝ, ℝ × ℝ) : ℝ × ℝ → ℝ × ℝ) (hf.codChart (f x)) :=
      ModelWithCorners.mdifferentiableAt (𝓘(ℝ, ℝ × ℝ))
    have hcomp := hJ.comp (f x) hc
    simpa [OpenPartialHomeomorph.extend_coe] using hcomp
  -- the `writtenInCharts` identity, pushed to a neighbourhood of `x`
  have heq : ((hf.codChart.extend (𝓘(ℝ, ℝ × ℝ))) ∘ f) =ᶠ[𝓝 x]
      ((hf.equiv ∘ (·,0)) ∘ (hf.domChart.extend (𝓡 1))) := by
    have hnhds : (hf.domChart.extend (𝓡 1)).source ∈ 𝓝 x :=
      OpenPartialHomeomorph.extend_source_mem_nhds (f := hf.domChart) (I := 𝓡 1) hx
    filter_upwards [hnhds] with y hy
    have h2 : (hf.domChart.extend (𝓡 1)).symm ((hf.domChart.extend (𝓡 1)) y) = y :=
      (hf.domChart.extend (𝓡 1)).left_inv hy
    simp only [Function.comp_apply]
    conv_lhs => rw [← h2]
    exact hf.writtenInCharts ((hf.domChart.extend (𝓡 1)).map_source hy)
  -- the linear part `h.equiv ∘ (·,0)` of the immersion, in two (definitionally equal) types
  let L : EuclideanSpace ℝ (Fin 1) →L[ℝ] (ℝ × ℝ) :=
    hf.equiv.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ _ F)
  let L' : TangentSpace (𝓡 1) ((hf.domChart.extend (𝓡 1)) x) →L[ℝ]
      TangentSpace (𝓘(ℝ, ℝ × ℝ)) ((hf.equiv ∘ (·,0)) ((hf.domChart.extend (𝓡 1)) x)) := L
  have hLfun : (hf.equiv ∘ (·,0)) = ⇑L := rfl
  have hmd_equiv : MDifferentiableAt (𝓡 1) (𝓘(ℝ, ℝ × ℝ)) (hf.equiv ∘ (·,0))
      ((hf.domChart.extend (𝓡 1)) x) := by
    rw [hLfun]
    exact (ContinuousLinearMap.hasMFDerivAt L).mdifferentiableAt
  have hLmf : mfderiv (𝓡 1) (𝓘(ℝ, ℝ × ℝ)) (hf.equiv ∘ (·,0))
      ((hf.domChart.extend (𝓡 1)) x) = L := by
    rw [hLfun]
    exact (ContinuousLinearMap.hasMFDerivAt L).mfderiv
  have hLmf' : mfderiv (𝓡 1) (𝓘(ℝ, ℝ × ℝ)) (hf.equiv ∘ (·,0))
      ((hf.domChart.extend (𝓡 1)) x) = L' := hLmf
  -- the extended domain chart is differentiable at `x`
  have hmd_e : MDifferentiableAt (𝓡 1) (𝓡 1) (hf.domChart.extend (𝓡 1)) x := by
    have h1 : hf.domChart ∈ IsManifold.maximalAtlas (𝓡 1) 1 M :=
      IsManifold.maximalAtlas_subset_of_le hn hf.domChart_mem_maximalAtlas
    have hc : MDifferentiableAt (𝓡 1) (𝓡 1)
        (hf.domChart : M → EuclideanSpace ℝ (Fin 1)) x :=
      mdifferentiableAt_of_mem_maximalAtlas h1 hx
    have hI : MDifferentiableAt (𝓡 1) (𝓡 1)
        (𝓡 1 : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) (hf.domChart x) :=
      ModelWithCorners.mdifferentiableAt (𝓡 1)
    have hcomp := hI.comp x hc
    simpa [OpenPartialHomeomorph.extend_coe] using hcomp
  have hev : (hf.domChart.extend (𝓡 1)) =ᶠ[𝓝 x]
      (hf.domChart : M → EuclideanSpace ℝ (Fin 1)) := by
    filter_upwards [hf.domChart.open_source.mem_nhds hx] with y hy
    simp
  -- the derivative of the (extended) domain chart at `x` is injective
  have hinj_chart : Function.Injective
      (mfderiv (𝓡 1) (𝓡 1) (hf.domChart : M → EuclideanSpace ℝ (Fin 1)) x) := by
    have h1 : hf.domChart ∈ IsManifold.maximalAtlas (𝓡 1) 1 M :=
      IsManifold.maximalAtlas_subset_of_le hn hf.domChart_mem_maximalAtlas
    have hmd : hf.domChart.MDifferentiable (𝓡 1) (𝓡 1) :=
      ⟨fun y hy => (mdifferentiableAt_of_mem_maximalAtlas h1 hy).mdifferentiableWithinAt,
       fun y hy => (mdifferentiableAt_symm_of_mem_maximalAtlas h1 hy).mdifferentiableWithinAt⟩
    exact hmd.mfderiv_injective hx
  have hinj_e : Function.Injective (mfderiv (𝓡 1) (𝓡 1) (hf.domChart.extend (𝓡 1)) x) := by
    rw [Filter.EventuallyEq.mfderiv_eq hev]
    exact hinj_chart
  -- `L` is injective, being the composite of a linear equivalence with `(·,0)`
  have hL_inj : Function.Injective L := by
    intro v w hvw
    have h2 : ((v, (0 : F)) : EuclideanSpace ℝ (Fin 1) × F) = (w, (0 : F)) :=
      hf.equiv.injective hvw
    simpa using congrArg Prod.fst h2
  have hL'_inj : Function.Injective L' := hL_inj
  -- the whole coordinate expression has injective derivative
  have hinj1 : Function.Injective
      (mfderiv (𝓡 1) (𝓘(ℝ, ℝ × ℝ)) ((hf.codChart.extend (𝓘(ℝ, ℝ × ℝ))) ∘ f) x) := by
    rw [Filter.EventuallyEq.mfderiv_eq heq]
    rw [mfderiv_comp x hmd_equiv hmd_e]
    rw [hLmf']
    intro v w hvw
    have h1 : L' (mfderiv (𝓡 1) (𝓡 1) (hf.domChart.extend (𝓡 1)) x v)
        = L' (mfderiv (𝓡 1) (𝓡 1) (hf.domChart.extend (𝓡 1)) x w) := by
      rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply]
      exact hvw
    exact hinj_e (hL'_inj h1)
  -- conclude by the chain rule for `(h.codChart.extend J) ∘ f`
  have hchain1 : mfderiv (𝓡 1) (𝓘(ℝ, ℝ × ℝ)) ((hf.codChart.extend (𝓘(ℝ, ℝ × ℝ))) ∘ f) x
      = (mfderiv (𝓘(ℝ, ℝ × ℝ)) (𝓘(ℝ, ℝ × ℝ)) (hf.codChart.extend (𝓘(ℝ, ℝ × ℝ))) (f x)) ∘SL
        (mfderiv (𝓡 1) (𝓘(ℝ, ℝ × ℝ)) f x) :=
    mfderiv_comp x hmd_cod hdf
  intro v w hvw
  have h1 : mfderiv (𝓡 1) (𝓘(ℝ, ℝ × ℝ)) ((hf.codChart.extend (𝓘(ℝ, ℝ × ℝ))) ∘ f) x v
      = mfderiv (𝓡 1) (𝓘(ℝ, ℝ × ℝ)) ((hf.codChart.extend (𝓘(ℝ, ℝ × ℝ))) ∘ f) x w := by
    rw [hchain1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hvw]
  exact hinj1 h1

end Work.RPB.Port.Drive
