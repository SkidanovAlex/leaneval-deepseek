import Mathlib
import Submission.Work.Orient.Boundary.TripleSetup
import Submission.Work.Orient.Boundary.RelFundClassOfCoreIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The chain-level bridge of the ORIENT vocabulary

`Work.Orient.relChainsIncl X (h : A ⊆ B) : C_*(X,A) ⟶ C_*(X,B)` (whose body is the one of the
consumer's `Work.ThomBordism.relChainsIncl`) and the cokernel-level map
`Work.Cohomology.relCokerMap X A B h` are *the same map*.  The two are introduced in different
files for different purposes:

* `relChainsIncl` is the map appearing in `Work.Orient.IsRelFundClass` (through
  `Work.Orient.relPunct`), and hence in the consumer's field `NullBordismFamily.w_fund`;
* `relCokerMap` is the map appearing in `Work.ThomBordism.RelHmap` (hence in `resRelH`) and in the
  localisation isomorphisms of the Hatcher machinery (`Work.Cohomology.convexLocalIso`,
  `Work.Orient.Boundary.HalfRestrictIso`).

This file collects the identifications in the top-level namespace `Work.Orient`; the proofs live in
`Work.Orient.Boundary.TripleSetup` and `Work.Orient.Boundary.RelFundClassOfCoreIso`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Orient

noncomputable section

/-- **The chain-level bridge**: the inclusion of relative chain complexes is the cokernel-level
map `relCokerMap`. -/
theorem relChainsIncl_eq_relCokerMap (X : TopCat) {A B : Set X} (h : A ⊆ B) :
    relChainsIncl X h = Work.Cohomology.relCokerMap X A B h :=
  Work.Orient.Boundary.relChainsIncl_eq_relCokerMap X h

/-- `relChainsIncl` depends on the inclusion only through its truth. -/
theorem relChainsIncl_congr (X : TopCat) {A B : Set X} (h h' : A ⊆ B) :
    relChainsIncl X h = relChainsIncl X h' :=
  Work.Orient.Boundary.relChainsIncl_congr_h h h'

/-- **Functoriality of `relChainsIncl`.** -/
theorem relChainsIncl_trans (X : TopCat) {A B C : Set X} (h₁ : A ⊆ B) (h₂ : B ⊆ C) :
    relChainsIncl X h₁ ≫ relChainsIncl X h₂ = relChainsIncl X (h₁.trans h₂) :=
  Work.Orient.Boundary.relChainsIncl_comp h₁ h₂

/-- `relPunct` is `relChainsIncl`, definitionally. -/
theorem relPunct_eq_relChainsIncl (W : TopCat) (B : Set W) (x : W) (hx : x ∉ B) :
    relPunct W B x hx
      = relChainsIncl W (A := B) (B := {y : W | y ≠ x})
          (fun y hy hyx => hx (hyx ▸ hy)) := rfl

/-- **`resRelH` is the homology of `relChainsIncl`.**  The restriction
`H_n(W, W∖B) → H_n(W, W∖A)` induced by `A ⊆ B` is the map of relative complexes
`C_*(W, Bᶜ) ⟶ C_*(W, Aᶜ)`. -/
theorem resRelH_eq_homologyMap_relChainsIncl (M : TopCat) (n : ℕ) {A B : Set M} (h : A ⊆ B) :
    resRelH M n h
      = (HomologicalComplex.homologyMap (relChainsIncl M (Set.compl_subset_compl.mpr h)) n).hom :=
  Work.Orient.Boundary.resRelH_eq_relChainsIncl M n h (Set.compl_subset_compl.mpr h)

end

end Work.Orient
