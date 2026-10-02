import Mathlib
import Submission.Work.Glue.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Glue

open scoped Manifold ContDiff Topology in
open Submission.Glue in
theorem mem_groupoid_of_contMDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I n X]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I n Y]
    {φ : OpenPartialHomeomorph X Y}
    (hφ : ContMDiffOn I I n ⇑φ φ.source) (hφ' : ContMDiffOn I I n ⇑φ.symm φ.target) :
    ∀ (e : OpenPartialHomeomorph X H), e ∈ atlas H X →
      ∀ (e' : OpenPartialHomeomorph Y H), e' ∈ atlas H Y →
        e.symm ≫ₕ φ ≫ₕ e' ∈ contDiffGroupoid n I := by
  intro e he e' he'
  -- `φ` is a local structomorphism for the `C^n` groupoid, by the hypothesis.
  have hLift : ChartedSpace.LiftPropOn (contDiffGroupoid n I).IsLocalStructomorphWithinAt
      (⇑φ : X → Y) φ.source :=
    (isLocalStructomorphOn_contDiffGroupoid_iff (I := I) (n := n) φ).mpr ⟨hφ, hφ'⟩
  -- atlas members are elements of the maximal atlas.
  have heM : e ∈ (contDiffGroupoid n I).maximalAtlas X :=
    StructureGroupoid.subset_maximalAtlas (contDiffGroupoid n I) he
  have he'M : e' ∈ (contDiffGroupoid n I).maximalAtlas Y :=
    StructureGroupoid.subset_maximalAtlas (contDiffGroupoid n I) he'
  -- membership in the groupoid is local.
  refine StructureGroupoid.locality (contDiffGroupoid n I) (fun z hz => ?_)
  -- unpacking the source of the triple composition
  have hz' : z ∈ e.target ∩ ⇑e.symm ⁻¹' (φ.source ∩ ⇑φ ⁻¹' e'.source) := by
    simpa only [mfld_simps] using hz
  -- independence of the chart: at `z`, the conjugation of `φ` by the charts is locally
  -- equal to an element of the groupoid.
  have hP := StructureGroupoid.LocalInvariantProp.liftPropOn_indep_chart
    (StructureGroupoid.isLocalStructomorphWithinAt_localInvariantProp (contDiffGroupoid n I))
    heM he'M hLift hz'
  have hfun : (⇑e' ∘ ⇑φ ∘ ⇑e.symm : H → H) = ⇑(e.symm ≫ₕ φ ≫ₕ e') := by
    ext x
    simp only [Function.comp_apply, OpenPartialHomeomorph.coe_trans]
  rw [hfun] at hP
  have hS : (e.symm ≫ₕ φ ≫ₕ e').source ⊆ ⇑e.symm ⁻¹' φ.source := by
    intro x hx
    have hx' : x ∈ e.target ∧ ⇑e.symm x ∈ φ.source ∧ ⇑φ (⇑e.symm x) ∈ e'.source := by
      simpa only [mfld_simps] using hx
    exact hx'.2.1
  -- reformulation of local structomorphism for an open partial homeomorphism
  obtain ⟨g, hgG, hgsrc, hgeq, hgz⟩ :=
    ((e.symm ≫ₕ φ ≫ₕ e').isLocalStructomorphWithinAt_iff' hS (Or.inl hz)).mp hP hz'.2.1
  refine ⟨g.source, g.open_source, hgz, ?_⟩
  have hsrc : ((e.symm ≫ₕ φ ≫ₕ e').restr g.source).source = g.source := by
    rw [OpenPartialHomeomorph.restr_source, g.open_source.interior_eq]
    exact Set.inter_eq_right.mpr hgsrc
  exact StructureGroupoid.mem_of_eqOnSource (contDiffGroupoid n I) hgG ⟨hsrc, fun x hx => by
    rw [OpenPartialHomeomorph.restr_apply]
    exact hgeq (hsrc ▸ hx)⟩

end Work.Glue
