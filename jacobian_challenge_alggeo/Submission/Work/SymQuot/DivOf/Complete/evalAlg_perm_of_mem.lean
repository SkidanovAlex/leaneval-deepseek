import Mathlib
import Submission.Work.SymQuot.DivOf.Complete.Setup
import Submission.Work.SymQuot.DivOf.Complete.evalAlg_coordPullbackAt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 2000000

universe u

namespace Work.SymQuot.DivOf.Complete

open CategoryTheory Limits AlgebraicGeometry in
theorem evalAlg_perm_of_mem {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    {V : C.left.Opens} {S : Type u} [CommRing S] [Algebra K S]
    (x : Fin n → Work.SpecLin.RPt C.toOver S)
    (h : ⊤ ≤ (Limits.Pi.lift x : Work.SpecLin.specOf (K := K) S ⟶
      Work.SymQuot.prod C.toOver n).left ⁻¹ᵁ Work.SymQuot.piOpen C.toOver V n)
    (σ : Equiv.Perm (Fin n))
    (h' : ⊤ ≤ (Limits.Pi.lift (x ∘ σ) : Work.SpecLin.specOf (K := K) S ⟶
      Work.SymQuot.prod C.toOver n).left ⁻¹ᵁ Work.SymQuot.piOpen C.toOver V n)
    {a : Γ((Work.SymQuot.prod C.toOver n).left, Work.SymQuot.piOpen C.toOver V n)}
    (ha : a ∈ chartInvariants (C := C) (n := n) (Work.SymQuot.piOpen C.toOver V n)
      (symPiOpen_invariant C n V)) :
    evalAlg C V n (x ∘ σ) h' a = evalAlg C V n x h a := by
  classical
  -- The two lifts of the family of points differ by the permutation of the factors.
  have hlift :
      (Limits.Pi.lift (x ∘ σ) : Work.SpecLin.specOf (K := K) S ⟶
        Work.SymQuot.prod C.toOver n)
        = Limits.Pi.lift x ≫ (Work.SymQuot.permIso C.toOver σ.symm).hom := by
    apply Limits.Pi.hom_ext
    intro m
    rw [Category.assoc, Work.SymQuot.Product.permIso_hom_proj]
    simp only [Limits.Pi.lift_comp_π, Function.comp_apply, Equiv.symm_symm]
  -- We name the objects involved, with the `prod`-spelling of the product `Cⁿ` fixed once and
  -- for all, so that the section rings below are all stated with the same underlying scheme.
  let U : (Work.SymQuot.prod C.toOver n).left.Opens := Work.SymQuot.piOpen C.toOver V n
  let g : Work.SpecLin.specOf (K := K) S ⟶ Work.SymQuot.prod C.toOver n := Limits.Pi.lift x
  let g' : Work.SpecLin.specOf (K := K) S ⟶ Work.SymQuot.prod C.toOver n :=
    Limits.Pi.lift (x ∘ σ)
  have hg : ⊤ ≤ g.left ⁻¹ᵁ U := h
  have hg' : ⊤ ≤ g'.left ⁻¹ᵁ U := h'
  let b : Γ((Work.SymQuot.prod C.toOver n).left, U) := a
  have hU : (Work.SymQuot.symAction C n).IsInvariantOpen U :=
    Work.SymQuot.DivOf.symPiOpen_invariant C n V
  have hgg' : g' = g ≫ (Work.SymQuot.permIso C.toOver σ.symm).hom := by
    rw [show g' = (Limits.Pi.lift (x ∘ σ) : Work.SpecLin.specOf (K := K) S ⟶
          Work.SymQuot.prod C.toOver n) from rfl,
      show g = (Limits.Pi.lift x : Work.SpecLin.specOf (K := K) S ⟶
          Work.SymQuot.prod C.toOver n) from rfl]
    exact hlift
  have hFl : g'.left = g.left ≫ (Work.SymQuot.symAction C n).hom (ULift.up σ.symm) := by
    rw [hgg', CategoryTheory.Over.comp_left]
    rfl
  -- The pullback of a section of `U` along `g' = g ≫ σ` factors through the action on `U`.
  have eF : U ≤ (Work.SymQuot.symAction C n).hom (ULift.up σ.symm) ⁻¹ᵁ U :=
    le_of_eq (hU (ULift.up σ.symm)).symm
  have hcomp := Scheme.Hom.appLE_comp_appLE g.left
    ((Work.SymQuot.symAction C n).hom (ULift.up σ.symm)) U U ⊤ eF hg
  have hsec : (Scheme.Hom.appLE ((Work.SymQuot.symAction C n).hom (ULift.up σ.symm))
        U U eF).hom
      = Work.SymQuot.GAction.sectionHom (Work.SymQuot.symAction C n) U hU
        (ULift.up σ.symm) := rfl
  have hkey : (Scheme.Hom.appLE g'.left U ⊤ hg').hom
      = (Scheme.Hom.appLE g.left U ⊤ hg).hom.comp
        (Work.SymQuot.GAction.sectionHom (Work.SymQuot.symAction C n) U hU
          (ULift.up σ.symm)) := by
    rw [← hsec, ← CommRingCat.hom_comp, hcomp]
    exact congrArg CommRingCat.Hom.hom (Work.SymQuot.appLE_congr_hom hFl hg' _)
  -- An invariant section is fixed by the action of the permutation.
  have hfix : Work.SymQuot.GAction.sectionHom (Work.SymQuot.symAction C n) U hU
        (ULift.up σ.symm) b = b := by
    have h1 := (Work.SymQuot.GAction.mem_invariants_iff
      (Work.SymQuot.symAction C n) hU b).mp ha
    simpa using h1 (ULift.up σ.symm)⁻¹
  have hfinal : (Scheme.Hom.appLE g'.left U ⊤ hg').hom b
      = (Scheme.Hom.appLE g.left U ⊤ hg).hom b := by
    rw [hkey, RingHom.comp_apply, hfix]
  show (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom
      ((Scheme.Hom.appLE g'.left U ⊤ hg').hom b)
    = (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom
      ((Scheme.Hom.appLE g.left U ⊤ hg).hom b)
  exact congrArg (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom hfinal

end Work.SymQuot.DivOf.Complete
