/-
# The ceiling map in the cusp coordinates of the chart, and the `τ_v` parameterisation

`Work.RTOwed.mbarPtC v x = Work.RTOwed.mbarPt v (x + h)` is the ceiling map of the `v`-th cusp
written in the *cusp* coordinates of the chart (`h = (1/2,1/2,1/2)` is the shift between the cube
coordinates of the development and the cusp coordinates of the chapter `Work.Cusp`); it is the
`mbarPt` field of `Work.Cusp.CuspGlueData`, and `Work.RTOwed.mbarPtC_eq` identifies it with the
chart at the ceiling.

This file

* proves the two `Tset`-related fields of `CuspGlueData` for the concrete chart
  (`mbarPt_mem_field`, `ceiling_mem`) and the periodicity/continuity/injectivity of `mbarPtC`
  modulo the cusp lattice `Λ_v`;
* builds, for any continuous lattice-periodic map with fibres the `Λ_v`-cosets, the `τ_v`
  homeomorphism `Work.RTOwed.tauHomeoOf`, and instantiates it at `mbarPtC`
  (`Work.RTOwed.PhiC`, with the coordinate formula `PhiC_apply`).

`tauHomeoOf` is the general form of `Work.RTOwed.tauHomeo` (which is the case of
`Work.RTOwed.mbarPt`), stated as a *definition* rather than an existence statement so that the
coordinate formula of the homeomorphism is available.
-/
import Mathlib
import Submission.Work.RTOwed.cuspChartBeta
import Submission.Work.RTOwed.cuspTorus_homeo_circle_torus
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.bndOfU_mem
import Submission.Work.Cusp.nrm_bndOfU
import Submission.Work.Space.Split.retrAB_homotopyEquiv

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function
open scoped BigOperators

namespace Work.RTOwed

/-! ## The `Σ`/subtype homeomorphisms of `Work.Space.Split` -/

/-- The coordinate formula of `Work.Space.Split.sigmaCongrRightHomeomorph`. -/
theorem sigmaCongrRightHomeomorph_apply {ι : Type*} {X Y : ι → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (F : ∀ i, X i ≃ₜ Y i) (z : Σ i, X i) :
    Work.Space.Split.sigmaCongrRightHomeomorph F z = ⟨z.1, F z.1 z.2⟩ := rfl

/-- The coordinate formula of the symmetric form of `Work.Space.Split.subtypeSigmaHomeomorph`. -/
theorem subtypeSigmaHomeomorph_symm_apply {ι : Type*} {β : ι → Type*}
    [∀ i, TopologicalSpace (β i)] (P : (i : ι) → β i → Prop)
    (w : Σ i, {b : β i // P i b}) :
    (Work.Space.Split.subtypeSigmaHomeomorph P).symm w = ⟨⟨w.1, w.2.1⟩, w.2.2⟩ := rfl

/-! ## The ceiling map in cusp coordinates -/

/-- The ceiling map of `CuspGlueData`: the ceiling map of the development at the cube coordinate
`x + h`. -/
theorem mbarPtC_periodic (v : Fin 5) {x x' : CuspE3} (h : x - x' ∈ Work.Cusp.lattice v) :
    mbarPtC v x = mbarPtC v x' := by
  have hmem : latVec v (x - x') := latVec_of_mem cuspCertificates v h
  have h1 : mbarPtC v x = mbarPt v ((x' + cuspH) + (x - x')) := by
    show mbarPt v (x + cuspH) = mbarPt v ((x' + cuspH) + (x - x'))
    congr 1
    abel
  rw [h1, cuspCert.mbarPt_latVec v (x' + cuspH) (x - x') hmem]
  rfl

/-- **The ceiling map in cusp coordinates is continuous.** -/
theorem mbarPtC_continuous (v : Fin 5) : Continuous (mbarPtC v) := by
  show Continuous fun x : CuspE3 => mbarPt v (x + cuspH)
  exact (cuspCert.mbarPt_continuous v).comp (continuous_id.add continuous_const)

/-- **The fibres of the ceiling map in cusp coordinates are the cosets of `Λ_v`.** -/
theorem mbarPtC_inj (v : Fin 5) {x x' : CuspE3} (h : mbarPtC v x = mbarPtC v x') :
    x - x' ∈ Work.Cusp.lattice v := by
  have h' : x + cuspH - (x' + cuspH) = x - x' := by abel
  have hl : latVec v (x - x') := by
    have h2 := cuspCert.mbarPt_inj v (x + cuspH) (x' + cuspH) h
    rwa [h'] at h2
  exact mem_of_latVec cuspCertificates v hl

/-! ## The `Tset` fields of the chart -/

/-- **The ceiling map lands in the truncation set** (`CuspGlueData.mbarPt_mem`). -/
theorem mbarPtC_mem_field (v : Fin 5) (x : CuspE3) : mbarPtC v x ∈ Work.FoldInst.Tset :=
  mbarPtC_mem v x

/-- Every point of `E4` is its own horizontal part at its own height. -/
theorem mkE4_xOf4 (q : CuspE4) : mkE4 (xOf4 q) (q 3) = q := by
  apply PiLp.ext; intro i
  fin_cases i <;> rfl

/-- **The points of the ceiling lie on the truncation torus** (`CuspGlueData.ceiling_mem`): a point
of a collar box whose height is exactly the ceiling is a point of `Tset`. -/
theorem ceiling_mem (v : Fin 5) (c : Work.Cusp.E3) (δ : ℝ) {q : Work.Cusp.E4}
    (hq : q ∈ Work.Cusp.cuspChartBox v c δ)
    (hqs : q 3 = Work.Cusp.beta (Work.Cusp.xOf q)) :
    mbarLow v q ∈ Work.FoldInst.Tset := by
  have hb : Work.Cusp.beta (xOf4 q) = q 3 := by
    rw [hqs]
    exact congrArg _ (xOf4_eq_xOf q)
  have h : q = mkE4 (xOf4 q) (Work.Cusp.beta (xOf4 q)) := by
    rw [hb]
    exact (mkE4_xOf4 q).symm
  rw [h]
  exact mbarLow_ceiling_mem v (xOf4 q)

/-- The ceiling map in cusp coordinates is the chart at the ceiling (the field `mbarPt_eq`, in the
form used by `CuspGlueData`). -/
theorem mbarPtC_eq_field (v : Fin 5) (x : CuspE3) :
    mbarPtC v x = mbarLow v (Work.Cusp.ceilingPt x) := by
  have h : Work.Cusp.ceilingPt x = mkE4 x (Work.Cusp.beta x) := rfl
  rw [h, mbarPtC]
  exact mbarPtC_eq v x

/-! ## The `τ_v` homeomorphism from a lattice-periodic ceiling map -/

/-- **A continuous lattice-periodic map with fibres the `Λ_v`-cosets descends to a homeomorphism**
`ℝ³/Λ_v ≃ₜ range f`, carried by the class of `x` to `f x`.

This is the general form of `Work.RTOwed.tauHomeo` (`cuspCeilingData_exists.lean`), stated as a
definition so that its coordinate formula `tauHomeoOf_apply` is available. -/
noncomputable def tauHomeoOf (v : Fin 5) (f : CuspE3 → Work.FoldInst.Mbar)
    (hper : ∀ x l : CuspE3, l ∈ Work.Cusp.lattice v → f (x + l) = f x)
    (hcont : Continuous f)
    (hinj : ∀ x x' : CuspE3, f x = f x' → x - x' ∈ Work.Cusp.lattice v) :
    Work.Cusp.CuspTorus v ≃ₜ Set.range f := by
  classical
  have hperF : ∀ x y : CuspE3, QuotientAddGroup.leftRel (Work.Cusp.lattice v) x y → f x = f y := by
    intro x y hxy
    have hb : -x + y ∈ Work.Cusp.lattice v := QuotientAddGroup.leftRel_apply.mp hxy
    have h1 := hper x (-x + y) hb
    rw [show x + (-x + y) = y by abel] at h1
    exact h1.symm
  let F : CuspE3 → Set.range f := fun x => ⟨f x, Set.mem_range_self x⟩
  let g : Work.Cusp.CuspTorus v → Set.range f :=
    Quotient.lift F fun x y h => Subtype.ext (hperF x y h)
  have hgm : ∀ x : CuspE3, g (Quotient.mk'' x) = F x := fun x => rfl
  have hgc : Continuous g :=
    (hcont.subtype_mk (fun x => Set.mem_range_self x)).quotient_lift
      (fun x y h => Subtype.ext (hperF x y h))
  have hinjg : Function.Injective g := by
    intro t t' htt
    revert htt
    refine Quotient.inductionOn₂ t t' ?_
    intro x y h
    have hxy : f x = f y := congrArg Subtype.val h
    exact QuotientAddGroup.eq_iff_sub_mem.mpr (hinj x y hxy)
  have hsurjg : Function.Surjective g := by
    intro w
    obtain ⟨x, hx⟩ := w.2
    exact ⟨Quotient.mk'' x, Subtype.ext (by rw [hgm]; exact hx)⟩
  haveI : CompactSpace (Work.Cusp.CuspTorus v) := by
    obtain ⟨h⟩ := cuspTorus_homeo_circle_torus v
    exact h.symm.compactSpace
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g ⟨hinjg, hsurjg⟩) hgc

/-- **The coordinate formula of `tauHomeoOf`**: the class of `x` goes to `f x`. -/
theorem tauHomeoOf_apply (v : Fin 5) (f : CuspE3 → Work.FoldInst.Mbar)
    (hper : ∀ x l : CuspE3, l ∈ Work.Cusp.lattice v → f (x + l) = f x)
    (hcont : Continuous f)
    (hinj : ∀ x x' : CuspE3, f x = f x' → x - x' ∈ Work.Cusp.lattice v) (x : CuspE3) :
    tauHomeoOf v f hper hcont hinj (Quotient.mk'' x) = ⟨f x, Set.mem_range_self x⟩ := rfl

/-- **The `τ_v` homeomorphism in the cusp coordinates of the chart**: the cusp torus `ℝ³/Λ_v` is
the range of `mbarPtC v`, carried by the class of `x` to the ceiling point over `x`. -/
noncomputable def PhiC (v : Fin 5) : Work.Cusp.CuspTorus v ≃ₜ Set.range (mbarPtC v) :=
  tauHomeoOf v (mbarPtC v)
    (fun x l hl => mbarPtC_periodic v (show (x + l) - x ∈ Work.Cusp.lattice v from by
      simpa using hl))
    (mbarPtC_continuous v)
    (fun x x' h => mbarPtC_inj v h)

/-- The coordinate formula of `PhiC`. -/
theorem PhiC_apply (v : Fin 5) (x : CuspE3) :
    PhiC v (Quotient.mk'' x) = ⟨mbarPtC v x, Set.mem_range_self x⟩ := rfl

end Work.RTOwed
