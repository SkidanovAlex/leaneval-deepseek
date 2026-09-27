import Mathlib
import Submission.Work.Drive.TripleMeetDefs
import Submission.Work.Drive.tripleDiffLM

/-!
# The three-chain transversality conditions for an arbitrary target

`Work.Drive.TripleTransverse` and `Work.Drive.TripleCommonDir` (`TripleMeetDefs.lean`) are stated for
derivatives with values in `EuclideanSpace ℝ (Fin 4)` — the tangent space of the capping space.  But
the *chart* computation of `Work.Drive.fderiv_chartAt_halfLineProjective` produces derivatives with
values in `EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3)` (the product model), which are then
transported to `ℝ⁴` by the linear isomorphism `Work.Drive.psiEquiv`.  This file provides the
`E`-valued versions of the two conditions, the two bridges back to the `ℝ⁴` form, the invariance under
post-composition with a linear isomorphism (so that `psiEquiv` may be dropped), and — for
`finrank E = 4` — the kernel form of transversality.

Thus a computation of the chart derivative in the product coordinates may be turned into a statement
about `TripleTransverse` by: `TripleTransverse (Ψ ∘ f k) ↔ TripleTransverseE (f k)`.
-/

namespace Work.Drive

open scoped Manifold ContDiff

noncomputable section

/-- **Transversality of three derivatives**, for derivatives with values in an arbitrary normed space
`E`: the difference map `(v₀,v₁,v₂) ↦ (f₀v₀ − f₁v₁, f₀v₀ − f₂v₂)` is onto `E × E`. -/
def TripleTransverseE {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f₀ f₁ f₂ : EuclideanSpace ℝ (Fin 3) →L[ℝ] E) : Prop :=
  ∀ w₁ w₂ : E, ∃ v : Fin 3 → EuclideanSpace ℝ (Fin 3),
    f₀ (v 0) - f₁ (v 1) = w₁ ∧ f₀ (v 0) - f₂ (v 2) = w₂

/-- **A common tangent direction** of three derivatives, with values in an arbitrary normed space. -/
def TripleCommonDirE {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f₀ f₁ f₂ : EuclideanSpace ℝ (Fin 3) →L[ℝ] E)
    (v : Fin 3 → EuclideanSpace ℝ (Fin 3)) : Prop :=
  f₀ (v 0) = f₁ (v 1) ∧ f₀ (v 0) = f₂ (v 2)

/-- The `E`-valued transversality condition at `E = ℝ⁴` is `Work.Drive.TripleTransverse`. -/
theorem tripleTransverseE_iff (f₀ f₁ f₂ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4)) :
    TripleTransverseE f₀ f₁ f₂ ↔ TripleTransverse f₀ f₁ f₂ := Iff.rfl

/-- The `E`-valued common-direction condition at `E = ℝ⁴` is `Work.Drive.TripleCommonDir`. -/
theorem tripleCommonDirE_iff
    (f₀ f₁ f₂ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (v : Fin 3 → EuclideanSpace ℝ (Fin 3)) :
    TripleCommonDirE f₀ f₁ f₂ v ↔ TripleCommonDir f₀ f₁ f₂ v := Iff.rfl

/-- **The difference map of three `E`-valued derivatives**, as one linear map. -/
def tripleDiffLME {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f₀ f₁ f₂ : EuclideanSpace ℝ (Fin 3) →L[ℝ] E) :
    (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) →L[ℝ]
      (E × E) :=
  ((f₀.comp cubeProj0) - (f₁.comp cubeProj1)).prod
    ((f₀.comp cubeProj0) - (f₂.comp cubeProj2))

@[simp] lemma tripleDiffLME_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f₀ f₁ f₂ : EuclideanSpace ℝ (Fin 3) →L[ℝ] E)
    (v : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    tripleDiffLME f₀ f₁ f₂ v = (f₀ v.1 - f₁ v.2.1, f₀ v.1 - f₂ v.2.2) := rfl

/-- `TripleTransverseE` is the surjectivity of the `E`-valued difference map. -/
theorem tripleTransverseE_iff_range_eq_top {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f₀ f₁ f₂ : EuclideanSpace ℝ (Fin 3) →L[ℝ] E) :
    TripleTransverseE f₀ f₁ f₂ ↔ (tripleDiffLME f₀ f₁ f₂).range = ⊤ := by
  constructor
  · intro h
    refine LinearMap.range_eq_top.mpr ?_
    rintro ⟨w₁, w₂⟩
    obtain ⟨v, h1, h2⟩ := h w₁ w₂
    exact ⟨(v 0, v 1, v 2), by simp [h1, h2]⟩
  · intro h w₁ w₂
    have hmem : (w₁, w₂) ∈ (tripleDiffLME f₀ f₁ f₂).range := by
      rw [h]; exact Submodule.mem_top
    obtain ⟨v, hv⟩ := hmem
    have hv1 : f₀ v.1 - f₁ v.2.1 = w₁ := by
      have := congrArg Prod.fst hv; simpa using this
    have hv2 : f₀ v.1 - f₂ v.2.2 = w₂ := by
      have := congrArg Prod.snd hv; simpa using this
    refine ⟨![v.1, v.2.1, v.2.2], ?_, ?_⟩
    · simpa using hv1
    · simpa using hv2

/-- `TripleCommonDirE` is the vanishing of the `E`-valued difference map. -/
theorem tripleCommonDirE_iff_tripleDiffLME_eq_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f₀ f₁ f₂ : EuclideanSpace ℝ (Fin 3) →L[ℝ] E)
    (v : Fin 3 → EuclideanSpace ℝ (Fin 3)) :
    TripleCommonDirE f₀ f₁ f₂ v ↔ tripleDiffLME f₀ f₁ f₂ (v 0, v 1, v 2) = 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [tripleDiffLME_apply]
    exact Prod.ext (sub_eq_zero.mpr h1) (sub_eq_zero.mpr h2)
  · intro h
    have h1 : f₀ (v 0) - f₁ (v 1) = 0 := by
      have := congrArg Prod.fst h; simpa using this
    have h2 : f₀ (v 0) - f₂ (v 2) = 0 := by
      have := congrArg Prod.snd h; simpa using this
    exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩

/-- **The kernel form**, for an `E` of dimension `4`: the difference map is onto exactly when its
kernel is a line. -/
theorem tripleTransverseE_iff_finrank_ker_eq_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hE : Module.finrank ℝ E = 4)
    (f₀ f₁ f₂ : EuclideanSpace ℝ (Fin 3) →L[ℝ] E) :
    TripleTransverseE f₀ f₁ f₂ ↔
      Module.finrank ℝ (LinearMap.ker (tripleDiffLME f₀ f₁ f₂).toLinearMap) = 1 := by
  rw [tripleTransverseE_iff_range_eq_top]
  have hrank := LinearMap.finrank_range_add_finrank_ker (tripleDiffLME f₀ f₁ f₂).toLinearMap
  have hdom : Module.finrank ℝ
      (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) = 9 := by
    simp [Module.finrank_prod]
  have hcod : Module.finrank ℝ (E × E) = 8 := by
    simp [Module.finrank_prod, hE]
  have hrange : Module.finrank ℝ (LinearMap.range (tripleDiffLME f₀ f₁ f₂).toLinearMap)
      = Module.finrank ℝ ((tripleDiffLME f₀ f₁ f₂).range) := rfl
  rw [hrange, hdom] at hrank
  constructor
  · intro h
    have hh : Module.finrank ℝ ((tripleDiffLME f₀ f₁ f₂).range) = 8 := by
      rw [h]; simp [hcod]
    omega
  · intro h
    have hh : Module.finrank ℝ ((tripleDiffLME f₀ f₁ f₂).range) = 8 := by omega
    have : (tripleDiffLME f₀ f₁ f₂).range = ⊤ := by
      rw [Submodule.eq_top_iff_finrank_eq]; rw [hh, hcod]
    exact this

/-- **The two conditions are invariant under a linear isomorphism of the target**: post-composing all
three derivatives with a linear equivalence does not change transversality. -/
theorem tripleTransverseE_comp_of_equiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ψ : E ≃L[ℝ] EuclideanSpace ℝ (Fin 4))
    (f₀ f₁ f₂ : EuclideanSpace ℝ (Fin 3) →L[ℝ] E) :
    TripleTransverse ((Ψ : E →L[ℝ] EuclideanSpace ℝ (Fin 4)).comp f₀)
        ((Ψ : _ →L[ℝ] _).comp f₁) ((Ψ : _ →L[ℝ] _).comp f₂)
      ↔ TripleTransverseE f₀ f₁ f₂ := by
  constructor
  · intro h w₁ w₂
    obtain ⟨v, h1, h2⟩ := h (Ψ w₁) (Ψ w₂)
    have h1' := h1
    have h2' := h2
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at h1'
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at h2'
    refine ⟨v, ?_, ?_⟩
    · refine Ψ.injective ?_
      exact (map_sub (Ψ : E →L[ℝ] EuclideanSpace ℝ (Fin 4))
        (f₀ (v 0)) (f₁ (v 1))).trans h1'
    · refine Ψ.injective ?_
      exact (map_sub (Ψ : E →L[ℝ] EuclideanSpace ℝ (Fin 4))
        (f₀ (v 0)) (f₂ (v 2))).trans h2'
  · intro h w₁ w₂
    obtain ⟨v, h1, h2⟩ := h (Ψ.symm w₁) (Ψ.symm w₂)
    refine ⟨v, ?_, ?_⟩
    · simp only [ContinuousLinearMap.comp_apply]
      rw [← map_sub, h1]
      exact Ψ.apply_symm_apply w₁
    · simp only [ContinuousLinearMap.comp_apply]
      rw [← map_sub, h2]
      exact Ψ.apply_symm_apply w₂

/-- The common-direction condition is invariant under a linear isomorphism of the target. -/
theorem tripleCommonDirE_comp_of_equiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ψ : E ≃L[ℝ] EuclideanSpace ℝ (Fin 4))
    (f₀ f₁ f₂ : EuclideanSpace ℝ (Fin 3) →L[ℝ] E)
    (v : Fin 3 → EuclideanSpace ℝ (Fin 3)) :
    TripleCommonDir ((Ψ : E →L[ℝ] EuclideanSpace ℝ (Fin 4)).comp f₀)
      ((Ψ : _ →L[ℝ] _).comp f₁) ((Ψ : _ →L[ℝ] _).comp f₂) v ↔ TripleCommonDirE f₀ f₁ f₂ v := by
  constructor
  · rintro ⟨h1, h2⟩
    have h1' := h1
    have h2' := h2
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at h1'
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at h2'
    exact ⟨Ψ.injective h1', Ψ.injective h2'⟩
  · rintro ⟨h1, h2⟩
    constructor
    · simp only [ContinuousLinearMap.comp_apply]
      rw [h1]
    · simp only [ContinuousLinearMap.comp_apply]
      rw [h2]

end

end Work.Drive
