/-
# The gluing `τ_v` of the hyperbolic piece to the filling boundary, with its coordinate formula

`Work.RTInstance.GlueHomeo` is the homeomorphism
`Tset ≃ₜ ∂(⊔_v [-1,1]² × T_v)` of the assembled space `M̂`.  This file builds it *explicitly* from
the ceiling data of the five cusps, in the cusp coordinates of the chart
(`Work.RTOwed.mbarPtC v x = mbarPt v (x + h)`), so that its coordinate form is available:

  the ceiling point over the cusp coordinate `x` is glued to the filling boundary point with
  perimeter parameter `bndOfU (outerU v x)` and torus coordinates `outerY v x`,

which is the field `Work.Cusp.CuspGlueData.glue_eq` (the content of the gluing `τ_v`).

The chain of homeomorphisms is

* `sigHomeo : (Σ v, range (mbarPtC v)) ≃ₜ Tset` — `⟨v, y⟩ ↦ y`, the cusped boundary is the disjoint
  union of the five ceiling tori;
* `sigmaCongrRightHomeomorph (PhiC v).symm : (Σ v, range (mbarPtC v)) ≃ₜ Σ v, ℝ³/Λ_v`;
* `sigmaCongrRightHomeomorph (Ψ v) : Σ v, ℝ³/Λ_v ≃ₜ Σ v, ∂[-1,1]² × (ℝ/ℤ)²`, the explicit
  boundary homeomorphism of `Work.RTOwed.cuspTorus_homeo_boundary_explicit`;
* `(subtypeSigmaHomeomorph _).symm : Σ v, ∂[-1,1]² × (ℝ/ℤ)² ≃ₜ {q ∈ ⊔_v [-1,1]² × T_v : q ∈
  FillingBdry}`.
-/
import Mathlib
import Submission.Work.RTOwed.cuspChartGlue
import Submission.Work.RTInstance.Instance

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function

namespace Work.RTOwed

open Work.RTInstance

/-! ## The range of the ceiling map in cusp coordinates -/

/-- The ranges of `mbarPtC v` and of `mbarPt v` agree: they are the range of the same map up to the
coordinate translation `x ↦ x + h`. -/
theorem range_mbarPtC (v : Work.Space.Cusp) : Set.range (mbarPtC v) = Set.range (mbarPt v) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x + cuspH, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x - cuspH, by show mbarPt v (x - cuspH + cuspH) = mbarPt v x; rw [sub_add_cancel]⟩

/-- **The truncation set is the union of the five ceiling tori**, in the cusp coordinates of the
chart. -/
theorem tset_eq_mbarPtC :
    Work.FoldInst.Tset = ⋃ v : Work.Space.Cusp, Set.range (mbarPtC v) := by
  rw [ceilingData.tset_eq]
  refine le_antisymm ?_ ?_ <;> intro y hy
  · obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hy
    exact Set.mem_iUnion.mpr ⟨v, (range_mbarPtC v) ▸ hv⟩
  · obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hy
    exact Set.mem_iUnion.mpr ⟨v, (range_mbarPtC v).symm ▸ hv⟩

/-- The five ceiling tori of the cusp coordinates are pairwise disjoint. -/
theorem disjoint_mbarPtC (v v' : Work.Space.Cusp) (h : v ≠ v') :
    Disjoint (Set.range (mbarPtC v)) (Set.range (mbarPtC v')) := by
  rw [range_mbarPtC, range_mbarPtC]
  exact ceilingData.disjoint v v' h

/-! ## The cusped boundary as the disjoint union of the ceiling tori -/

/-- The cusp torus is compact (it is a quotient of the trivially compact `(ℝ/ℤ)³`). -/
instance compactSpace_cuspTorus (v : Work.Space.Cusp) : CompactSpace (Work.Cusp.CuspTorus v) := by
  obtain ⟨h⟩ := cuspTorus_homeo_circle_torus v
  exact h.symm.compactSpace

/-- Each ceiling torus is compact. -/
instance compactSpace_range_mbarPtC (v : Work.Space.Cusp) :
    CompactSpace (Set.range (mbarPtC v)) :=
  (PhiC v).compactSpace

/-- The underlying point of the disjoint union of the five ceiling tori lies in `Tset`. -/
theorem mem_tset_sigma (z : Σ v : Work.Space.Cusp, Set.range (mbarPtC v)) :
    z.2.1 ∈ Work.FoldInst.Tset := by
  rw [tset_eq_mbarPtC]
  exact Set.mem_iUnion.mpr ⟨z.1, z.2.2⟩

/-- The map `⟨v, y⟩ ↦ y` from the disjoint union of the five ceiling tori to `Tset`. -/
noncomputable def sigToTset (z : Σ v : Work.Space.Cusp, Set.range (mbarPtC v)) :
    Work.FoldInst.Tset :=
  ⟨z.2.1, mem_tset_sigma z⟩

theorem sigToTset_apply (z : Σ v : Work.Space.Cusp, Set.range (mbarPtC v)) :
    (sigToTset z : Work.FoldInst.Mbar) = z.2.1 := rfl

theorem continuous_sigToTset : Continuous sigToTset := by
  rw [continuous_sigma_iff]
  intro v
  exact Continuous.subtype_mk continuous_subtype_val fun a => mem_tset_sigma ⟨v, a⟩

theorem sigToTset_injective : Function.Injective sigToTset := by
  rintro ⟨v, y, hy⟩ ⟨v', y', hy'⟩ h
  have hyy : (y : Work.FoldInst.Mbar) = y' := by
    have h2 : ((sigToTset ⟨v, ⟨y, hy⟩⟩ : Work.FoldInst.Tset) : Work.FoldInst.Mbar) =
        ((sigToTset ⟨v', ⟨y', hy'⟩⟩ : Work.FoldInst.Tset) : Work.FoldInst.Mbar) :=
      congrArg Subtype.val h
    rw [show (sigToTset ⟨v, ⟨y, hy⟩⟩ : Work.FoldInst.Mbar) = (y : Work.FoldInst.Mbar) from rfl,
      show (sigToTset ⟨v', ⟨y', hy'⟩⟩ : Work.FoldInst.Mbar) = (y' : Work.FoldInst.Mbar) from rfl] at h2
    exact h2
  have hvv : v = v' := by
    by_contra hne
    exact (Set.disjoint_left.mp (disjoint_mbarPtC v v' hne)) hy (hyy ▸ hy')
  subst hvv
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext hyy))

theorem sigToTset_surjective : Function.Surjective sigToTset := by
  intro y
  have hy : (y : Work.FoldInst.Mbar) ∈ ⋃ v : Work.Space.Cusp, Set.range (mbarPtC v) := by
    rw [← tset_eq_mbarPtC]
    exact y.2
  obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hy
  exact ⟨⟨v, ⟨y.1, hv⟩⟩, Subtype.ext rfl⟩

/-- **The cusped boundary is the disjoint union of the five ceiling tori.** -/
noncomputable def sigHomeo :
    (Σ v : Work.Space.Cusp, Set.range (mbarPtC v)) ≃ₜ Work.FoldInst.Tset :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective sigToTset ⟨sigToTset_injective, sigToTset_surjective⟩)
    continuous_sigToTset

/-- The coordinate formula of `sigHomeo`. -/
theorem sigHomeo_apply (v : Work.Space.Cusp) (x : CuspE3) :
    sigHomeo ⟨v, ⟨mbarPtC v x, Set.mem_range_self x⟩⟩ =
      ⟨mbarPtC v x, mem_tset_sigma ⟨v, ⟨mbarPtC v x, Set.mem_range_self x⟩⟩⟩ :=
  Subtype.ext rfl

/-- The coordinate formula of `sigHomeo.symm`. -/
theorem sigHomeo_symm_apply (v : Work.Space.Cusp) (x : CuspE3)
    (h : mbarPtC v x ∈ Work.FoldInst.Tset) :
    sigHomeo.symm ⟨mbarPtC v x, h⟩ = ⟨v, ⟨mbarPtC v x, Set.mem_range_self x⟩⟩ := by
  have h1 : sigHomeo ⟨v, ⟨mbarPtC v x, Set.mem_range_self x⟩⟩ =
      (⟨mbarPtC v x, h⟩ : Work.FoldInst.Tset) := Subtype.ext rfl
  conv_lhs => rw [← h1]
  exact Homeomorph.symm_apply_apply sigHomeo _

/-! ## The gluing, from the boundary homeomorphism of the cusp torus -/

/-- The last step of the gluing: a subtype of a `Σ`-type defined componentwise is the `Σ` of the
subtypes, with the `FillingBdry` form of the predicate. -/
noncomputable def sigmaBdryHomeo :
    (Σ _ : Work.Space.Cusp, {p : Work.RTInstance.SquarePt × Work.RTInstance.Torus //
        Work.Space.sqNorm p.1 = 1}) ≃ₜ
      {q : Σ _ : Work.Space.Cusp, Work.RTInstance.SquarePt × Work.RTInstance.Torus //
        q ∈ Work.Space.FillingBdry (fun _ : Work.Space.Cusp => Work.RTInstance.Torus)} :=
  (Work.Space.Split.subtypeSigmaHomeomorph
    (fun _ (p : Work.RTInstance.SquarePt × Work.RTInstance.Torus) =>
      Work.Space.sqNorm p.1 = 1)).symm

/-- The coordinate formula of `sigmaBdryHomeo`. -/
theorem sigmaBdryHomeo_apply
    (w : Σ _ : Work.Space.Cusp, {p : Work.RTInstance.SquarePt × Work.RTInstance.Torus //
        Work.Space.sqNorm p.1 = 1}) :
    sigmaBdryHomeo w = ⟨⟨w.1, w.2.1⟩, w.2.2⟩ := by
  show (Work.Space.Split.subtypeSigmaHomeomorph
    (fun _ (p : Work.RTInstance.SquarePt × Work.RTInstance.Torus) =>
      Work.Space.sqNorm p.1 = 1)).symm w = _
  rw [Work.RTOwed.subtypeSigmaHomeomorph_symm_apply]
  try exact Subtype.ext rfl

/-- **The gluing `τ_v` in cusp coordinates**: the homeomorphism `Tset ≃ₜ ∂(⊔_v [-1,1]² × T_v)`
which sends the ceiling point over the cusp coordinate `x` to the boundary point with perimeter
parameter `bndOfU (outerU v x)` and torus coordinates `outerY v x`.

The parameter `Ψ v : ℝ³/Λ_v ≃ₜ ∂[-1,1]² × (ℝ/ℤ)²` is the explicit boundary homeomorphism of
`Work.RTOwed.cuspTorus_homeo_boundary_explicit`. -/
noncomputable def glueHomeoOf
    (Ψ : ∀ v : Work.Space.Cusp, Work.Cusp.CuspTorus v ≃ₜ
      {p : Work.RTInstance.SquarePt × Work.RTInstance.Torus // Work.Space.sqNorm p.1 = 1}) :
    Work.FoldInst.Tset ≃ₜ
      {q : Σ _ : Work.Space.Cusp, Work.RTInstance.SquarePt × Work.RTInstance.Torus //
        q ∈ Work.Space.FillingBdry (fun _ : Work.Space.Cusp => Work.RTInstance.Torus)} :=
  (sigHomeo.symm.trans
    ((Work.Space.Split.sigmaCongrRightHomeomorph (fun v => (PhiC v).symm)).trans
      (Work.Space.Split.sigmaCongrRightHomeomorph Ψ))).trans sigmaBdryHomeo

/-- **The coordinate formula of the gluing**: the ceiling point over the cusp coordinate `x` is sent
to the boundary point with perimeter parameter `bndOfU (outerU v x)` and torus coordinates
`outerY v x`. -/
theorem glueHomeoOf_apply
    (Ψ : ∀ v : Work.Space.Cusp, Work.Cusp.CuspTorus v ≃ₜ
      {p : Work.RTInstance.SquarePt × Work.RTInstance.Torus // Work.Space.sqNorm p.1 = 1})
    (v : Work.Space.Cusp) (x : CuspE3) (h : mbarPtC v x ∈ Work.FoldInst.Tset) :
    glueHomeoOf Ψ ⟨mbarPtC v x, h⟩
      = ⟨⟨v, (Ψ v (Quotient.mk'' x)).1⟩, (Ψ v (Quotient.mk'' x)).2⟩ := by
  have h1 : sigHomeo.symm ⟨mbarPtC v x, h⟩ = ⟨v, ⟨mbarPtC v x, Set.mem_range_self x⟩⟩ :=
    sigHomeo_symm_apply v x h
  have h2 : (Work.Space.Split.sigmaCongrRightHomeomorph (fun v => (PhiC v).symm))
      ⟨v, ⟨mbarPtC v x, Set.mem_range_self x⟩⟩ = ⟨v, Quotient.mk'' x⟩ := by
    rw [Work.RTOwed.sigmaCongrRightHomeomorph_apply]
    congr 1
    exact Eq.trans (congrArg (fun t => (PhiC v).symm t)
      (Subtype.ext rfl : (⟨mbarPtC v x, Set.mem_range_self x⟩ : Set.range (mbarPtC v)) =
        PhiC v (Quotient.mk'' x))) (Homeomorph.symm_apply_apply (PhiC v) _)
  have h3 : (Work.Space.Split.sigmaCongrRightHomeomorph Ψ) ⟨v, Quotient.mk'' x⟩
      = ⟨v, Ψ v (Quotient.mk'' x)⟩ := by
    rw [Work.RTOwed.sigmaCongrRightHomeomorph_apply]
  rw [glueHomeoOf]
  simp only [Homeomorph.trans_apply]
  rw [h1, h2, h3, sigmaBdryHomeo_apply]

end Work.RTOwed
