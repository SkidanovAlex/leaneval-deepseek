import Mathlib
import Submission.Work.Brown.Basic

namespace Work.Brown.Compactify

open Metric

/-!
# The one-point compactification of a locally compact space, and the sphere

If the one-point compactification `OnePoint X` of a locally compact space `X` is homeomorphic to
the unit sphere `𝕊ⁿ ⊂ ℝⁿ⁺¹`, then `X` itself is homeomorphic to `ℝⁿ`.

The two geometric ingredients are

* stereographic projection: removing a point `p` from the unit sphere in `E` leaves a space
  homeomorphic to the hyperplane `(ℝ ∙ p)ᗮ` orthogonal to that point;
* any hyperplane `(ℝ ∙ v)ᗮ` of `ℝⁿ⁺¹` (with `v ≠ 0`) is homeomorphic to `ℝⁿ`, since the two
  finite-dimensional real vector spaces have the same dimension.

The reduction is then: a homeomorphism `OnePoint X ≃ₜ 𝕊ⁿ` restricts to a homeomorphism between
`X` (via the open embedding `X → OnePoint X`) and the sphere punctured at the image of `∞`.
-/

/-- Removing a point from a sphere of radius one yields a space homeomorphic to the orthogonal
complement of the line through that point, via stereographic projection centred at the point. -/
noncomputable def sphereComplSingletonHomeomorph {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (p : ↥(Metric.sphere (0 : E) 1)) :
    ↥({p}ᶜ : Set ↥(Metric.sphere (0 : E) 1)) ≃ₜ ↥(ℝ ∙ (p : E))ᗮ := by
  have hv : ‖(p : E)‖ = 1 := norm_eq_of_mem_sphere p
  have hf : Topology.IsEmbedding (stereographic hv).symm :=
    (isOpenEmbedding_stereographic_symm hv).toIsEmbedding
  have hrange : Set.range (stereographic hv).symm = ({p}ᶜ : Set ↥(Metric.sphere (0 : E) 1)) := by
    rw [range_stereographic_symm (hv := hv) (hv' := by simp [hv])]
  exact (Homeomorph.setCongr hrange).symm.trans hf.toHomeomorph.symm

/-- The hyperplane of `ℝⁿ⁺¹` orthogonal to a nonzero vector is homeomorphic to `ℝⁿ`. -/
theorem nonempty_homeomorph_orthogonal_span_singleton {n : ℕ} (v : PL.E (n + 1)) (hv : v ≠ 0) :
    Nonempty (↥(ℝ ∙ v)ᗮ ≃ₜ PL.E n) := by
  have hdim : Module.finrank ℝ ↥(ℝ ∙ v)ᗮ = Module.finrank ℝ (PL.E n) := by
    have h1 : Module.finrank ℝ ↥(ℝ ∙ v) = 1 := finrank_span_singleton hv
    have h2 : Module.finrank ℝ ↥(ℝ ∙ v) + Module.finrank ℝ ↥(ℝ ∙ v)ᗮ =
        Module.finrank ℝ (PL.E (n + 1)) :=
      Submodule.finrank_add_finrank_orthogonal _
    rw [finrank_euclideanSpace, Fintype.card_fin, h1] at h2
    rw [finrank_euclideanSpace, Fintype.card_fin]
    omega
  obtain ⟨e⟩ := FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq hdim
  exact ⟨e.toHomeomorph⟩

/-- The sphere `𝕊ⁿ ⊂ ℝⁿ⁺¹` with one point removed is homeomorphic to `ℝⁿ`. -/
theorem nonempty_homeomorph_sphere_compl_singleton {n : ℕ}
    (p : ↥(Metric.sphere (0 : PL.E (n + 1)) 1)) :
    Nonempty (↥({p}ᶜ : Set ↥(Metric.sphere (0 : PL.E (n + 1)) 1)) ≃ₜ PL.E n) := by
  have hp : (p : PL.E (n + 1)) ≠ 0 := by
    intro hc
    have h := norm_eq_of_mem_sphere p
    rw [hc] at h
    simp at h
  obtain ⟨e1⟩ : Nonempty
      (↥({p}ᶜ : Set ↥(Metric.sphere (0 : PL.E (n + 1)) 1)) ≃ₜ ↥(ℝ ∙ (p : PL.E (n + 1)))ᗮ) :=
    ⟨sphereComplSingletonHomeomorph p⟩
  obtain ⟨e2⟩ := nonempty_homeomorph_orthogonal_span_singleton (n := n) (p : PL.E (n + 1)) hp
  exact ⟨e1.trans e2⟩

theorem nonempty_homeomorph_of_onePoint_homeomorph {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] {n : ℕ} (h : Nonempty (OnePoint X ≃ₜ ↥(Metric.sphere (0 : PL.E (n + 1)) 1))) : Nonempty (X ≃ₜ PL.E n) := by
  obtain ⟨e⟩ := h
  -- `X` is the complement of `∞` inside `OnePoint X`, via the open embedding `X → OnePoint X`.
  have hr : Set.range (OnePoint.some : X → OnePoint X) = ({OnePoint.infty}ᶜ : Set (OnePoint X)) := by
    ext x
    exact OnePoint.ne_infty_iff_exists.symm
  -- A homeomorphism sends the complement of `∞` to the complement of its image `e ∞`.
  have himg : e '' ({OnePoint.infty}ᶜ : Set (OnePoint X)) = {e OnePoint.infty}ᶜ := by
    rw [Set.image_compl_eq e.bijective, Set.image_singleton]
  have h1 : X ≃ₜ Set.range (OnePoint.some : X → OnePoint X) :=
    OnePoint.isOpenEmbedding_coe.toIsEmbedding.toHomeomorph
  have hX : X ≃ₜ ↥({e OnePoint.infty}ᶜ : Set ↥(Metric.sphere (0 : PL.E (n + 1)) 1)) :=
    ((h1.trans (Homeomorph.setCongr hr)).trans (e.image _)).trans (Homeomorph.setCongr himg)
  obtain ⟨hp⟩ := nonempty_homeomorph_sphere_compl_singleton (e OnePoint.infty)
  exact ⟨hX.trans hp⟩

end Work.Brown.Compactify
