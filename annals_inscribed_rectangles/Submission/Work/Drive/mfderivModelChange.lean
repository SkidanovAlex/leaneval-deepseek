import Mathlib
import Submission.Work.Drive.TripleGeneral
import Submission.Work.Drive.chartedSpaceChangeModel
import Submission.Work.Drive.fderiv_chartAt_chartedSpaceChangeModel

/-!
# The manifold derivative under a linear model change, and its use for `TripleTransverse`

*(Committed from the scratch file `_cm1.lean` at the workspace root of session
`orderSplit_model` (2026-09-25 10:45), which was written for the `mfderiv` block bridge of the
encoded chains and then left outside the library.  This module makes the lemmas importable.)*

Let `M` carry two `ChartedSpace` structures over `E` and `E'` whose preferred charts at every point are
related by a linear equivalence `e : E ≃L[ℝ] E'`:

> `chartAt E' y = e ∘ chartAt E y`     (for every `y : M`).

Then, for any map `G : ℝ^k → M` that is manifold-differentiable in the first structure, the manifold
derivative in the second structure is the composition with `e`:

* `Work.Drive.extChartAt_eq_of_chartAt_eq` — the extended charts agree up to `e`;
* `Work.Drive.hasMFDerivAt_of_chartAt_eq` — `HasMFDerivAt` transports along `e`;
* **`Work.Drive.mfderiv_of_chartAt_eq`** — `mfderiv (𝓡 k) (𝓡 E') G x = e ∘ mfderiv (𝓡 k) (𝓡 E) G x`;
* **`Work.Drive.tripleTransverseE_comp_continuousLinearEquiv`** — `TripleTransverseE` is invariant
  under post-composition with a linear equivalence (so the `TripleTransverse` of the transported
  derivatives is equivalent to the `TripleTransverseE` of the product-structure derivatives, which is
  what `Work.Drive.tripleTransverseE_encoded` computes).

The chart form for the *Fréchet* derivative of the pushed-forward chart is the committed
`Submission/Work/Drive/fderiv_chartAt_chartedSpaceChangeModel.lean`
(`chartAt_chartedSpaceChangeModel_apply`, `fderiv_chartAt_chartedSpaceChangeModel`); the bridge for
the `trans` field of `Meet3Hyp` for the encoded chains is assembled from the two files.
-/

namespace Work.Drive

open Manifold Function Set
open scoped Manifold ContDiff

noncomputable section

section ChangeModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {X : Type*} [TopologicalSpace X] [ChartedSpace E X] [ChartedSpace E' X]

/-- **The extended charts of two charted-space structures related by a chart formula.** -/
theorem extChartAt_eq_of_chartAt_eq (e : E ≃L[ℝ] E')
    (hchart : ∀ y : X, (⇑(chartAt E' y) : X → E') = ⇑e ∘ ⇑(chartAt E y)) (p : X) :
    (⇑(extChartAt (modelWithCornersSelf ℝ E') p) : X → E')
      = ⇑e ∘ (⇑(extChartAt (modelWithCornersSelf ℝ E) p) : X → E) := by
  rw [extChartAt_coe, extChartAt_coe, modelWithCornersSelf_coe, modelWithCornersSelf_coe,
    Function.id_comp, Function.id_comp]
  exact hchart p

/-- **The derivative in a charted-space structure changed by a linear equivalence.** -/
theorem hasMFDerivAt_of_chartAt_eq {k : ℕ} (e : E ≃L[ℝ] E')
    (hchart : ∀ y : X, (⇑(chartAt E' y) : X → E') = ⇑e ∘ ⇑(chartAt E y))
    {G : EuclideanSpace ℝ (Fin k) → X} {x : EuclideanSpace ℝ (Fin k)}
    {f' : EuclideanSpace ℝ (Fin k) →L[ℝ] E}
    (h : HasMFDerivAt (𝓡 k) (modelWithCornersSelf ℝ E) G x f') :
    HasMFDerivAt (𝓡 k) (modelWithCornersSelf ℝ E') G x ((e : E →L[ℝ] E').comp f') := by
  refine ⟨h.1, ?_⟩
  have hfun : (writtenInExtChartAt (𝓡 k) (modelWithCornersSelf ℝ E') x G : EuclideanSpace ℝ (Fin k) → E')
      = ⇑e ∘ (writtenInExtChartAt (𝓡 k) (modelWithCornersSelf ℝ E) x G :
          EuclideanSpace ℝ (Fin k) → E) := by
    funext z
    simp only [writtenInExtChartAt, Function.comp_apply]
    rw [extChartAt_eq_of_chartAt_eq e hchart (G x)]
    rfl
  rw [hfun]
  exact HasFDerivWithinAt.comp (x := (extChartAt (𝓡 k) x) x) (t := Set.univ)
    ((ContinuousLinearEquiv.hasFDerivAt e).hasFDerivWithinAt) h.2 (Set.mapsTo_univ _ _)

/-- **The manifold derivative in a charted-space structure changed by a linear equivalence.** -/
theorem mfderiv_of_chartAt_eq {k : ℕ} (e : E ≃L[ℝ] E')
    (hchart : ∀ y : X, (⇑(chartAt E' y) : X → E') = ⇑e ∘ ⇑(chartAt E y))
    {G : EuclideanSpace ℝ (Fin k) → X} {x : EuclideanSpace ℝ (Fin k)}
    (h : MDifferentiableAt (𝓡 k) (modelWithCornersSelf ℝ E) G x) :
    mfderiv (𝓡 k) (modelWithCornersSelf ℝ E') G x
      = (e : E →L[ℝ] E').comp (mfderiv (𝓡 k) (modelWithCornersSelf ℝ E) G x) :=
  (hasMFDerivAt_of_chartAt_eq e hchart h.hasMFDerivAt).mfderiv

end ChangeModel

/-- **`TripleTransverseE` is invariant under post-composition with a linear equivalence.** -/
theorem tripleTransverseE_comp_continuousLinearEquiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (Ψ : E ≃L[ℝ] E') (f₀ f₁ f₂ : EuclideanSpace ℝ (Fin 3) →L[ℝ] E) :
    TripleTransverseE ((Ψ : E →L[ℝ] E').comp f₀) ((Ψ : E →L[ℝ] E').comp f₁)
        ((Ψ : E →L[ℝ] E').comp f₂)
      ↔ TripleTransverseE f₀ f₁ f₂ := by
  constructor
  · intro h w₁ w₂
    obtain ⟨v, h1, h2⟩ := h (Ψ w₁) (Ψ w₂)
    refine ⟨v, ?_, ?_⟩
    · have h1' : Ψ (f₀ (v 0)) - Ψ (f₁ (v 1)) = Ψ w₁ := h1
      rw [← map_sub] at h1'
      exact Ψ.injective h1'
    · have h2' : Ψ (f₀ (v 0)) - Ψ (f₂ (v 2)) = Ψ w₂ := h2
      rw [← map_sub] at h2'
      exact Ψ.injective h2'
  · intro h w₁ w₂
    obtain ⟨v, h1, h2⟩ := h (Ψ.symm w₁) (Ψ.symm w₂)
    refine ⟨v, ?_, ?_⟩
    · simp only [ContinuousLinearMap.comp_apply]
      rw [← map_sub, h1]
      simpa using Ψ.apply_symm_apply w₁
    · simp only [ContinuousLinearMap.comp_apply]
      rw [← map_sub, h2]
      simpa using Ψ.apply_symm_apply w₂

end

end Work.Drive
