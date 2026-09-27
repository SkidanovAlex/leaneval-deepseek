import Mathlib
import Submission.Work.Whitney.reduce_double_points_abstract

namespace Work.Whitney

open scoped Manifold ContDiff

/-!
# Oriented atlases restrict to open submanifolds

An oriented atlas `A` of smooth charts on `M` restricts to an oriented atlas of smooth charts on
any open subset `U ⊆ M`, namely `A' = {c.subtypeRestr hU | c ∈ A}` (Mathlib's
`OpenPartialHomeomorph.subtypeRestr`).  The point is that the transition of two restrictions agrees
on its source with the ambient transition (`OpenPartialHomeomorph.subtypeRestr_symm_trans_subtypeRestr`),
so the positive determinant of the ambient transition transfers -- and being an agreement on an
*open* set, it also transfers the derivative: the transition of the restrictions has the same
`fderiv` as the ambient transition at the relevant point.  The smoothness clauses transfer because
the charts of the restriction are `<ambient chart> ∘ Subtype.val`, `Subtype.val` being smooth
(`contMDiff_subtype_val`), and because a map into the open submanifold is smooth iff its composite
with the inclusion is (`ChartedSpace.ContMDiffAt.subtypeVal_comp_iff`).

The empty case is vacuous: no chart is needed to cover the empty open set.

This is the missing piece for discharging the hypothesis `hconn` of
`Work.Embedding.exists_embedding_of_components` (the reduction of the compact case to the connected
one); see also `Work.Whitney.exists_embedding_of_compact_connected_orientable`.
-/

section deriv

variable {n : ℕ} {M : Type*} [TopologicalSpace M]

/-- Restricting a chart to an open subset does not change the derivative of a transition map: the
transition of the restrictions agrees on its (open) source with the ambient transition, hence has
the same Fréchet derivative at every point of that source. -/
lemma subtypeRestr_symm_trans_fderiv
    (d₁ d₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    {U : TopologicalSpace.Opens M} (hU : Nonempty U) (x : U)
    (hx₁ : (x : M) ∈ d₁.source) (hx₂ : (x : M) ∈ d₂.source) :
    fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) =>
        (d₂.subtypeRestr hU) ((d₁.subtypeRestr hU).symm u)) ((d₁.subtypeRestr hU) x) =
      fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => d₂ (d₁.symm u)) (d₁ (x : M)) := by
  have hx₁' : x ∈ (d₁.subtypeRestr hU).source := by
    simpa [OpenPartialHomeomorph.subtypeRestr_source] using hx₁
  have hx₂' : x ∈ (d₂.subtypeRestr hU).source := by
    simpa [OpenPartialHomeomorph.subtypeRestr_source] using hx₂
  have hEqSrc := OpenPartialHomeomorph.subtypeRestr_symm_trans_subtypeRestr
    (s := U) hU d₁ d₂
  have hmem₁ : (d₁.subtypeRestr hU) x ∈
      ((d₁.subtypeRestr hU).symm ≫ₕ (d₂.subtypeRestr hU)).source := by
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨(d₁.subtypeRestr hU).map_source hx₁',
      by rw [(d₁.subtypeRestr hU).left_inv hx₁']; exact hx₂'⟩
  have hpt : (d₁.subtypeRestr hU) x = d₁ (x : M) := rfl
  rw [hpt]
  refine Filter.EventuallyEq.fderiv_eq ?_
  have hmem : d₁ (x : M) ∈ ((d₁.symm ≫ₕ d₂).restr
      (d₁.target ∩ d₁.symm ⁻¹' (U : Set M))).source := by
    rw [← hEqSrc.1]
    exact hmem₁
  refine Filter.eventually_of_mem
    (((d₁.symm ≫ₕ d₂).restr
      (d₁.target ∩ d₁.symm ⁻¹' (U : Set M))).open_source.mem_nhds hmem) (fun u hu => ?_)
  have hu₁ : u ∈ ((d₁.subtypeRestr hU).symm ≫ₕ (d₂.subtypeRestr hU)).source := by
    rw [hEqSrc.1]; exact hu
  have h := hEqSrc.2 hu₁
  simpa using h

end deriv

section oriented

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- **An oriented atlas restricts to an open subset.** -/
lemma subtypeRestr_isOrientedAtlas
    {A : Set (OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))}
    (hA : IsOrientedAtlas A) (U : TopologicalSpace.Opens M) (hU : Nonempty U) :
    IsOrientedAtlas {c : OpenPartialHomeomorph U (EuclideanSpace ℝ (Fin n)) |
      ∃ d ∈ A, c = d.subtypeRestr hU} := by
  constructor
  · intro x
    obtain ⟨d, hdA, hxd⟩ := hA.1 (x : M)
    exact ⟨d.subtypeRestr hU, ⟨d, hdA, rfl⟩,
      by simpa [OpenPartialHomeomorph.subtypeRestr_source] using hxd⟩
  · rintro c₁ ⟨d₁, hd₁, rfl⟩ c₂ ⟨d₂, hd₂, rfl⟩ x hx₁ hx₂
    have hx₁' : (x : M) ∈ d₁.source := by
      simpa [OpenPartialHomeomorph.subtypeRestr_source] using hx₁
    have hx₂' : (x : M) ∈ d₂.source := by
      simpa [OpenPartialHomeomorph.subtypeRestr_source] using hx₂
    rw [subtypeRestr_symm_trans_fderiv d₁ d₂ hU x hx₁' hx₂']
    exact hA.2 d₁ hd₁ d₂ hd₂ (x : M) hx₁' hx₂'

end oriented

section smooth

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- **An oriented atlas of smooth charts restricts to an open subset**, the charts of the
restriction being the restrictions of the charts of the atlas. -/
lemma subtypeRestr_isSmoothOrientedAtlas
    {A : Set (OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))}
    (hA : IsSmoothOrientedAtlas A) (U : TopologicalSpace.Opens M) (hU : Nonempty U) :
    IsSmoothOrientedAtlas {c : OpenPartialHomeomorph U (EuclideanSpace ℝ (Fin n)) |
      ∃ d ∈ A, c = d.subtypeRestr hU} := by
  refine ⟨subtypeRestr_isOrientedAtlas hA.1 U hU, ?_⟩
  rintro c ⟨d, hdA, rfl⟩
  refine ⟨?_, ?_⟩
  · intro x hx
    have hx' : (x : M) ∈ d.source := by
      simpa [OpenPartialHomeomorph.subtypeRestr_source] using hx
    have h1 : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (∞ : ℕ∞ω)
        (d ∘ Subtype.val) x :=
      ((hA.2 d hdA).1 (x : M) hx').comp x (contMDiff_subtype_val (U := U) x)
    exact h1
  · intro u hu
    have hu' : u ∈ d.target := OpenPartialHomeomorph.subtypeRestr_target_subset d hU hu
    rw [← ContMDiffAt.subtypeVal_comp_iff U ((d.subtypeRestr hU).symm) u]
    refine ((hA.2 d hdA).2 u hu').congr_of_eventuallyEq ?_
    exact Filter.eventually_of_mem ((d.subtypeRestr hU).open_target.mem_nhds hu)
      (fun y hy => OpenPartialHomeomorph.subtypeRestr_symm_apply d hU hy)

end smooth

-- An oriented atlas of smooth charts restricts to an open submanifold.  This is the missing piece
-- for discharging the hypothesis `hconn` of `Work.Embedding.exists_embedding_of_components`
-- (the reduction of the compact case to the connected one): for a compact connected open `U : Opens M`
-- one needs an oriented smooth atlas *on `U`* in order to apply
-- `Work.Whitney.exists_embedding_of_compact_connected_orientable` there.
--
-- Suggested construction: `A' = {c.subtypeRestr U | c ∈ A}` (Mathlib's
-- `OpenPartialHomeomorph.subtypeRestr`; see `TopologicalSpace.Opens.instChartedSpace` in
-- `Mathlib/Geometry/Manifold/HasGroupoid.lean` for the open-submanifold structure on `U`).
-- Useful Mathlib facts: `subtypeRestr_source`, `subtypeRestr_symm_trans_subtypeRestr` (the
-- transition of restrictions agrees with the ambient transition, so the positive determinant
-- transfers), and smoothness of the open inclusion `U ↪ M` (`contMDiff_subtype_val`).
-- The empty `U` case is vacuous.
--
-- The conclusion is a bare existential on purpose: the consumer only needs *some* oriented smooth
-- atlas on `U`.
--
-- Engineering: `lean_check`/`lean_tactic` are broken here; use scratch files at the workspace root
-- and `lake env lean F.lean` (batch checks into ONE file).  `ContDiff ℝ ⊤` is *analyticity*;
-- `C^∞` is `((⊤ : ℕ∞) : WithTop ℕ∞)`.  Do not edit files that are not yours.
theorem exists_isSmoothOrientedAtlas_restrict {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (A : Set (OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))))
    (hA : Work.Whitney.IsSmoothOrientedAtlas A)
    (U : TopologicalSpace.Opens M) :
    ∃ A' : Set (OpenPartialHomeomorph U (EuclideanSpace ℝ (Fin n))),
      Work.Whitney.IsSmoothOrientedAtlas A' := by
  by_cases hU : Nonempty U
  · exact ⟨_, subtypeRestr_isSmoothOrientedAtlas hA U hU⟩
  · refine ⟨∅, ?_, ?_⟩
    · exact ⟨fun x => absurd ⟨x⟩ hU, fun c hc => absurd hc (Set.notMem_empty c)⟩
    · intro c hc
      exact absurd hc (Set.notMem_empty c)

end Work.Whitney
