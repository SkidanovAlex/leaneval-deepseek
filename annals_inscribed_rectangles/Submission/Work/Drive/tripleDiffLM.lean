import Mathlib
import Submission.Work.Drive.TripleMeetDefs

/-!
# The difference map of three derivatives as one linear map

`Work.Drive.TripleTransverse f₀ f₁ f₂` (`Submission/Work/Drive/TripleMeetDefs.lean`) says, for three
derivatives `f₀ f₁ f₂ : ℝ³ →L ℝ⁴`, that for all `w₁ w₂` there is a triple `(v₀,v₁,v₂)` with
`f₀v₀ - f₁v₁ = w₁` and `f₀v₀ - f₂v₂ = w₂` — i.e. that the *difference map*

> `Φ (v₀,v₁,v₂) = (f₀v₀ - f₁v₁, f₀v₀ - f₂v₂)`

is surjective.  This file makes that map a single linear map and proves the resulting criteria:

* `TripleTransverse f₀ f₁ f₂ ↔ Φ.range = ⊤`;
* `TripleTransverse f₀ f₁ f₂ ↔ finrank (ker Φ) = 1` — by rank-nullity, the source being
  `9`-dimensional and the target `8`-dimensional;
* the kernel of `Φ` *is* the set of common tangent directions:
  `TripleCommonDir f₀ f₁ f₂ v ↔ Φ (v 0, v 1, v 2) = 0`.

The last two are the form in which the geometric genericity of the concrete chains is checked: **the
three derivative images meet in a unique line**, and the kernel direction is the tangent direction of
the triple intersection `1`-manifold that the face condition of the parity engine uses.
-/

namespace Work.Drive

open scoped Manifold ContDiff

/-- The first coordinate of a triple of parameter vectors. -/
def cubeProj0 :
    (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) :=
  ContinuousLinearMap.fst ℝ _ _

/-- The second coordinate of a triple of parameter vectors. -/
def cubeProj1 :
    (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) :=
  (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)

/-- The third coordinate of a triple of parameter vectors. -/
def cubeProj2 :
    (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) :=
  (ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)

@[simp] lemma cubeProj0_apply
    (v : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    cubeProj0 v = v.1 := rfl

@[simp] lemma cubeProj1_apply
    (v : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    cubeProj1 v = v.2.1 := rfl

@[simp] lemma cubeProj2_apply
    (v : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    cubeProj2 v = v.2.2 := rfl

/-- **The difference map of three derivatives**: `(v₀,v₁,v₂) ↦ (f₀v₀ - f₁v₁, f₀v₀ - f₂v₂)`, as a
linear map from the triples of parameter vectors to the pairs of target vectors. -/
def tripleDiffLM (f₀ f₁ f₂ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4)) :
    (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) →L[ℝ]
      (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) :=
  ((f₀.comp cubeProj0) - (f₁.comp cubeProj1)).prod
    ((f₀.comp cubeProj0) - (f₂.comp cubeProj2))

@[simp] lemma tripleDiffLM_apply
    (f₀ f₁ f₂ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (v : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    tripleDiffLM f₀ f₁ f₂ v = (f₀ v.1 - f₁ v.2.1, f₀ v.1 - f₂ v.2.2) := rfl

/-- **`TripleTransverse` is the surjectivity of the difference map.** -/
theorem tripleTransverse_iff_range_eq_top
    (f₀ f₁ f₂ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4)) :
    TripleTransverse f₀ f₁ f₂ ↔ (tripleDiffLM f₀ f₁ f₂).range = ⊤ := by
  constructor
  · intro h
    refine LinearMap.range_eq_top.mpr ?_
    rintro ⟨w₁, w₂⟩
    obtain ⟨v, h1, h2⟩ := h w₁ w₂
    exact ⟨(v 0, v 1, v 2), by simp [h1, h2]⟩
  · intro h w₁ w₂
    have hmem : (w₁, w₂) ∈ (tripleDiffLM f₀ f₁ f₂).range := by
      rw [h]; exact Submodule.mem_top
    obtain ⟨v, hv⟩ := hmem
    have hv1 : f₀ v.1 - f₁ v.2.1 = w₁ := by
      have := congrArg Prod.fst hv; simpa using this
    have hv2 : f₀ v.1 - f₂ v.2.2 = w₂ := by
      have := congrArg Prod.snd hv; simpa using this
    refine ⟨![v.1, v.2.1, v.2.2], ?_, ?_⟩
    · simpa using hv1
    · simpa using hv2

/-- **The kernel of the difference map is the set of common tangent directions.** -/
theorem tripleCommonDir_iff_tripleDiffLM_eq_zero
    (f₀ f₁ f₂ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (v : Fin 3 → EuclideanSpace ℝ (Fin 3)) :
    TripleCommonDir f₀ f₁ f₂ v ↔
      tripleDiffLM f₀ f₁ f₂ (v 0, v 1, v 2) = 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [tripleDiffLM_apply]
    exact Prod.ext (sub_eq_zero.mpr h1) (sub_eq_zero.mpr h2)
  · intro h
    have h1 : f₀ (v 0) - f₁ (v 1) = 0 := by
      have := congrArg Prod.fst h; simpa using this
    have h2 : f₀ (v 0) - f₂ (v 2) = 0 := by
      have := congrArg Prod.snd h; simpa using this
    exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩

/-- **The kernel form**: with a `9`-dimensional source and an `8`-dimensional target, the difference
map is surjective exactly when its kernel is a line.  This is the form in which the geometric
genericity of the concrete chains is checked: *the three derivative images meet in a line*. -/
theorem tripleTransverse_iff_finrank_ker_eq_one
    (f₀ f₁ f₂ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4)) :
    TripleTransverse f₀ f₁ f₂ ↔
      Module.finrank ℝ (LinearMap.ker (tripleDiffLM f₀ f₁ f₂).toLinearMap) = 1 := by
  rw [tripleTransverse_iff_range_eq_top]
  have hrank := LinearMap.finrank_range_add_finrank_ker (tripleDiffLM f₀ f₁ f₂).toLinearMap
  have hdom : Module.finrank ℝ
      (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) = 9 := by
    simp [Module.finrank_prod]
  have hcod : Module.finrank ℝ (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) = 8 := by
    simp [Module.finrank_prod]
  have hrange : Module.finrank ℝ (LinearMap.range (tripleDiffLM f₀ f₁ f₂).toLinearMap)
      = Module.finrank ℝ ((tripleDiffLM f₀ f₁ f₂).range) := rfl
  rw [hrange, hdom] at hrank
  constructor
  · intro h
    have hh : Module.finrank ℝ ((tripleDiffLM f₀ f₁ f₂).range) = 8 := by
      rw [h]; simp [hcod]
    omega
  · intro h
    have hh : Module.finrank ℝ ((tripleDiffLM f₀ f₁ f₂).range) = 8 := by omega
    have : (tripleDiffLM f₀ f₁ f₂).range = ⊤ := by
      rw [Submodule.eq_top_iff_finrank_eq]; rw [hh, hcod]
    exact this

end Work.Drive
