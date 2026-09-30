import Mathlib
import Submission.Work.Charts.ChartCg
import Submission.Work.GCBasics.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.Charts

/-- Evaluating a section at the canonical `κ(x)`-point of `X` is the same as evaluating it at
`x` by means of the canonical map `O_{X,x} ⟶ κ(x)` (`Scheme.evaluation`). -/
private lemma evalSection_fromSpecResidueField_eq {X : Scheme.{u}} {U : X.Opens} (x : X)
    (s : Γ(X, U)) (hx : x ∈ U)
    (hpc : (X.fromSpecResidueField x) (IsLocalRing.closedPoint ↥(X.residueField x)) ∈ U) :
    evalSection (X.fromSpecResidueField x) hpc s = X.evaluation U x hx s := by
  -- `X.residue x` is a local homomorphism, so `germ_stalkClosedPointTo_Spec_fromSpecStalk`
  -- applies with `f = X.residue x`.
  haveI : IsLocalHom (CommRingCat.Hom.hom (X.residue x)) := by
    change IsLocalHom (IsLocalRing.residue (X.presheaf.stalk x)); infer_instance
  have hcl : (X.fromSpecResidueField x) (IsLocalRing.closedPoint ↥(X.residueField x)) = x :=
    Scheme.fromSpecResidueField_apply x _
  have hW : (Spec.map (X.residue x) ≫ X.fromSpecStalk x)
      (IsLocalRing.closedPoint ↥(X.residueField x)) ∈ U := by
    have hmix : (Spec.map (X.residue x) ≫ X.fromSpecStalk x) = X.fromSpecResidueField x := rfl
    rw [hmix, hcl]; exact hx
  have key2 := Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (X.residue x) U hW
  have key3 := Scheme.germ_stalkClosedPointTo (X.fromSpecResidueField x) U hpc
  -- The germ of `s` at `x`, pushed to the residue field, is the value of `f.app U s`
  -- read in `Γ(Spec κ(x), ⊤) ≅ κ(x)`.
  have hcombined : X.presheaf.germ U x hx ≫ X.residue x
      = (X.fromSpecResidueField x).app U ≫
        (Functor.mapIso (Spec (X.residueField x)).presheaf
          (Iso.op (eqToIso
            (Scheme.preimage_eq_top_of_closedPoint_mem (X.fromSpecResidueField x) hpc).symm))
          ≪≫ Scheme.ΓSpecIso (X.residueField x)).hom := key2.symm.trans key3
  rw [show X.evaluation U x hx = X.presheaf.germ U x hx ≫ X.residue x from rfl, hcombined]
  simp only [evalSection, Scheme.Hom.appLE, CommRingCat.comp_apply, Iso.trans_hom]
  congr 1

theorem mem_basicOpen_iff_evalSection_ne_zero {K : Type u} [Field K] {X : Work.GCBasics.Sch K}
    (x : X.left) (U : X.left.Opens) (s : (X.left.presheaf.obj (Opposite.op U)))
    (hx : (Work.GCBasics.resPt X x).left
        (IsLocalRing.closedPoint (Work.GCBasics.resField X x)) ∈ U) :
    x ∈ X.left.basicOpen s ↔ Work.Charts.evalSection (Work.GCBasics.resPt X x).left hx s ≠ 0 := by
  have hxU : x ∈ U := by
    have h := Work.GCBasics.resPt_apply X x
      (IsLocalRing.closedPoint (Work.GCBasics.resField X x))
    rwa [h] at hx
  have hkey : Work.Charts.evalSection (Work.GCBasics.resPt X x).left hx s
      = X.left.evaluation U x hxU s :=
    evalSection_fromSpecResidueField_eq (X := X.left) (U := U) x s hxU hx
  rw [hkey]
  exact (Scheme.evaluation_ne_zero_iff_mem_basicOpen X.left x hxU s).symm

end Work.Charts
