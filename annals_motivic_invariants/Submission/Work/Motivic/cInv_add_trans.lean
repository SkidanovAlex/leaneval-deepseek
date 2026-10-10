import Mathlib
import Submission.Work.Motivic.Defs
import Submission.Work.Motivic.cInv_add_defs
import Submission.Work.Motivic.cInv_add_pt
import Submission.Work.Motivic.mem_trans_source
import Submission.Work.Motivic.trans_toRationalMap

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The behaviour of `IsIsoAt` under composition

This file contains the "F1/F2/F3" facts of the Lin–Shinder additivity argument: for a point `x` at
which `φ` is an isomorphism, `φ.trans ψ` is an isomorphism at `x` exactly when `ψ` is an
isomorphism at `phiPt φ x` (`isIsoAt_trans_iff`), and if `φ` is *not* an isomorphism at `x` while
`φ.trans ψ` is, then `ψ.symm` is not an isomorphism at the image of `x`
(`not_isIsoAt_symm`).
-/

namespace Work.Motivic

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants Order

/-- `f.trans f.symm` is the identity. -/
lemma self_trans_symm {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X.BirationalMap Y) : f.trans f.symm = BirationalMap.refl X := by
  ext
  rw [BirationalMap.trans_hom, BirationalMap.symm_hom, BirationalMap.refl_hom]
  exact BirationalMap.hom_comp_inv_id f

/-- `φ.symm.trans (φ.trans ψ) = ψ`. -/
lemma symm_trans_trans {X Y Z : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    [IrreducibleSpace Z] (φ : X.BirationalMap Y) (ψ : Y.BirationalMap Z) :
    φ.symm.trans (φ.trans ψ) = ψ := by
  rw [← BirationalMap.trans_assoc, BirationalMap.symm_trans_self_id, BirationalMap.refl_trans]

/-- `(φ.trans ψ).trans ψ.symm = φ`. -/
lemma trans_trans_symm {X Y Z : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    [IrreducibleSpace Z] (φ : X.BirationalMap Y) (ψ : Y.BirationalMap Z) :
    (φ.trans ψ).trans ψ.symm = φ := by
  rw [BirationalMap.trans_assoc, self_trans_symm, BirationalMap.trans_refl]

/-- The rational map of a composite of partial isomorphisms, computed from the birational maps
they represent. -/
lemma toRationalMap_trans_of_toBirationalMap {X Y Z : Scheme.{0}} [IrreducibleSpace X]
    [IrreducibleSpace Y] [IrreducibleSpace Z] {i : X.PartialIso Y} {j : Y.PartialIso Z}
    {φ : X.BirationalMap Y} {ψ : Y.BirationalMap Z}
    (hi : i.toBirationalMap = φ) (hj : j.toBirationalMap = ψ) :
    (i.trans j).toRationalMap = (φ.trans ψ).hom := by
  have hbij : (i.trans j).toBirationalMap = i.toBirationalMap.trans j.toBirationalMap := by
    apply BirationalMap.ext
    show (i.trans j).toRationalMap = i.toRationalMap.comp j.toRationalMap
    exact trans_toRationalMap i j
  rw [← PartialIso.toBirationalMap_hom (i.trans j), hbij, hi, hj]

/-- The evaluation of the underlying partial map of `i` at a point of its source agrees with
`phiPt`. -/
lemma toPartialMap_hom_eq_phiPt {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (φ : X.BirationalMap Y) (x : X) (h : IsIsoAt φ x) :
    h.choose.toPartialMap.hom ⟨x, h.choose_spec.1⟩ = phiPt φ ⟨x, h⟩ := by
  change h.choose.target.ι (h.choose.iso.hom ⟨x, h.choose_spec.1⟩) = phiPt φ ⟨x, h⟩
  rw [phiPt_apply]

/-- If `φ` is an isomorphism at `x`, then `φ.trans ψ` is an isomorphism at `x` if and only if `ψ`
is an isomorphism at `phiPt φ x`. -/
theorem isIsoAt_trans_iff {𝕜 : Type} [Field 𝕜] {X Y Z : Scheme.{0}} [Variety 𝕜 X]
    [Variety 𝕜 Y] [Variety 𝕜 Z] (φ : X.BirationalMap Y) (ψ : Y.BirationalMap Z) (x : X)
    (h : IsIsoAt φ x) : IsIsoAt (φ.trans ψ) x ↔ IsIsoAt ψ (phiPt φ ⟨x, h⟩) := by
  constructor
  · intro hk
    have hmem : phiPt φ ⟨x, h⟩ ∈ h.choose.target := by
      rw [phiPt_apply]
      exact (h.choose.iso.hom ⟨x, h.choose_spec.1⟩).2
    refine ⟨h.choose.symm.trans hk.choose, ?_, ?_⟩
    · rw [mem_trans_source h.choose.symm hk.choose hmem]
      rw [CAdd.symm_toPartialMap_hom_target h.choose h.choose_spec.1 hmem
        (phiPt_apply (φ := φ) ⟨x, h⟩)]
      exact hk.choose_spec.1
    · have h1 : (h.choose.symm).toBirationalMap = φ.symm := BirationalMap.ext _ _ (by
        rw [PartialIso.toBirationalMap_hom, BirationalMap.symm_hom]
        exact CAdd.symm_toRationalMap h.choose h.choose_spec.2)
      have h2 : hk.choose.toBirationalMap = φ.trans ψ := BirationalMap.ext _ _
        ((PartialIso.toBirationalMap_hom hk.choose).trans hk.choose_spec.2)
      rw [toRationalMap_trans_of_toBirationalMap h1 h2, symm_trans_trans]
  · intro hy
    refine ⟨h.choose.trans hy.choose, ?_, ?_⟩
    · rw [mem_trans_source h.choose hy.choose h.choose_spec.1]
      rw [toPartialMap_hom_eq_phiPt]
      exact hy.choose_spec.1
    · have h1 : h.choose.toBirationalMap = φ := BirationalMap.ext _ _
        ((PartialIso.toBirationalMap_hom h.choose).trans h.choose_spec.2)
      have h2 : hy.choose.toBirationalMap = ψ := BirationalMap.ext _ _
        ((PartialIso.toBirationalMap_hom hy.choose).trans hy.choose_spec.2)
      exact toRationalMap_trans_of_toBirationalMap h1 h2

/-- If `φ` is not an isomorphism at `x` but `φ.trans ψ` is, then `ψ.symm` is not an isomorphism at
the image of `x` under `φ.trans ψ`. -/
theorem not_isIsoAt_symm {𝕜 : Type} [Field 𝕜] {X Y Z : Scheme.{0}} [Variety 𝕜 X]
    [Variety 𝕜 Y] [Variety 𝕜 Z] (φ : X.BirationalMap Y) (ψ : Y.BirationalMap Z) (x : X)
    (hφ : ¬ IsIsoAt φ x) (h : IsIsoAt (φ.trans ψ) x) :
    ¬ IsIsoAt ψ.symm (phiPt (φ.trans ψ) ⟨x, h⟩) := by
  intro hcon
  refine hφ ⟨h.choose.trans hcon.choose, ?_, ?_⟩
  · rw [mem_trans_source h.choose hcon.choose h.choose_spec.1, toPartialMap_hom_eq_phiPt]
    exact hcon.choose_spec.1
  · have h1 : h.choose.toBirationalMap = φ.trans ψ := BirationalMap.ext _ _
      ((PartialIso.toBirationalMap_hom h.choose).trans h.choose_spec.2)
    have h2 : hcon.choose.toBirationalMap = ψ.symm := BirationalMap.ext _ _
      ((PartialIso.toBirationalMap_hom hcon.choose).trans hcon.choose_spec.2)
    rw [toRationalMap_trans_of_toBirationalMap h1 h2]
    exact congrArg BirationalMap.hom (trans_trans_symm φ ψ)

end Work.Motivic
