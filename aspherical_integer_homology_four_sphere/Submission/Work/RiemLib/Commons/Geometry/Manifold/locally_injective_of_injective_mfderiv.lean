import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Local injectivity of a `C^1` map with injective differential

We prove that a `C^1` map `f : E → M` from a finite-dimensional real normed space into a
boundaryless manifold is locally injective at a point `x` provided its manifold derivative
`mfderiv f x` is injective.

The proof reduces to the model space: writing `F = extChartAt I (f x) ∘ f` (a map `E → E`),
the chain rule expresses `fderiv ℝ F x` as an invertible linear coordinate change applied to
`mfderiv f x`, so it is injective. For the model-space statement we use the inverse function
theorem in the form that a `C^1` map with invertible strict derivative is a local homeomorphism
(`HasStrictFDerivAt.toOpenPartialHomeomorph`); since `E` is finite-dimensional the injective
(self-)derivative is automatically invertible.
-/

open scoped Manifold ContDiff Topology
open Set Filter

namespace Commons.Geometry.Manifold

/-- Model-space version: a `C^1` self-map of a finite-dimensional real normed space whose
derivative at `x` is injective is injective near `x`. -/
private lemma locally_injective_of_contDiffAt_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → E} {x : E} (hf : ContDiffAt ℝ 1 f x)
    (hinj : Function.Injective (fderiv ℝ f x)) :
    ∃ ε > 0, ∀ y z : E, ‖y - x‖ < ε → ‖z - x‖ < ε → f y = f z → y = z := by
  have instCE : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hstrict : HasStrictFDerivAt f (fderiv ℝ f x) x := hf.hasStrictFDerivAt (by norm_num)
  have hker : (fderiv ℝ f x : E →L[ℝ] E).ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]; exact hinj
  have hsurj : Function.Surjective (fderiv ℝ f x : E →L[ℝ] E) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℝ) (V := E) (V₂ := E) rfl
      (f := (fderiv ℝ f x : E →ₗ[ℝ] E))).mp hinj
  have hrange : (fderiv ℝ f x : E →L[ℝ] E).range = ⊤ := by
    rw [LinearMap.range_eq_top]; exact hsurj
  let f' : E ≃L[ℝ] E := ContinuousLinearEquiv.ofBijective (fderiv ℝ f x) hker hrange
  have hcoe : (f' : E →L[ℝ] E) = fderiv ℝ f x := ContinuousLinearEquiv.coe_ofBijective _ _ _
  have hstrict' : HasStrictFDerivAt f (f' : E →L[ℝ] E) x := by rw [hcoe]; exact hstrict
  let φ : OpenPartialHomeomorph E E := hstrict'.toOpenPartialHomeomorph f
  have hxc : x ∈ φ.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source hstrict'
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp (φ.open_source.mem_nhds hxc)
  refine ⟨ε, hεpos, fun y z hy hz hyz => ?_⟩
  have hφ : φ y = φ z := by
    have hcoe2 : (φ : E → E) = f := HasStrictFDerivAt.toOpenPartialHomeomorph_coe hstrict'
    rw [hcoe2]; exact hyz
  refine φ.injOn (hε ?_) (hε ?_) hφ <;>
    (rw [Metric.mem_ball, dist_eq_norm]; assumption)

theorem locally_injective_of_injective_mfderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {f : E → M} {x : E} (hf : ContMDiffAt (modelWithCornersSelf ℝ E) I 1 f x)
    (hinj : Function.Injective (mfderiv (modelWithCornersSelf ℝ E) I f x)) :
    ∃ ε > 0, ∀ y z : E, ‖y - x‖ < ε → ‖z - x‖ < ε → f y = f z → y = z := by
  set e : M → E := ⇑(extChartAt I (f x)) with he
  -- The coordinate representative `e ∘ f : E → E` is `C^1` at `x`.
  have hFdiff : ContDiffAt ℝ 1 (e ∘ f) x := by
    have h1 : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 1 (e ∘ f) x := by
      have := (contMDiffAt_iff_target.mp hf).2
      simpa [he] using this
    exact h1.contDiffAt
  -- Its derivative at `x` is injective, because it is an invertible coordinate change applied
  -- to the (injective) manifold derivative of `f`.
  have hinjF : Function.Injective (fderiv ℝ (e ∘ f) x) := by
    have hmdg : MDiffAt e (f x) := by
      have := mdifferentiableAt_extChartAt (I := I) (x := f x) (y := f x)
        (mem_chart_source H (f x))
      simpa [he] using this
    have hmdf : MDiffAt f x := hf.mdifferentiableAt one_ne_zero
    have hchain : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (e ∘ f) x
        = mfderiv I 𝓘(ℝ, E) e (f x) ∘SL mfderiv 𝓘(ℝ, E) I f x :=
      mfderiv_comp x hmdg hmdf
    have hfde : fderiv ℝ (e ∘ f) x
        = mfderiv I 𝓘(ℝ, E) e (f x) ∘SL mfderiv 𝓘(ℝ, E) I f x := by
      rw [mfderiv_eq_fderiv] at hchain; exact hchain
    rw [hfde]
    have hA : (mfderiv I 𝓘(ℝ, E) e (f x)).IsInvertible :=
      isInvertible_mfderiv_extChartAt (I := I) (x := f x) (mem_extChartAt_source (f x))
    exact hA.injective.comp hinj
  obtain ⟨ε, hεpos, hε⟩ := locally_injective_of_contDiffAt_one hFdiff hinjF
  refine ⟨ε, hεpos, fun y z hy hz hyz => hε y z hy hz ?_⟩
  simp only [Function.comp_apply]; rw [hyz]

end Commons.Geometry.Manifold