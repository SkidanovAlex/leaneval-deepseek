import Mathlib
import Submission.Work.Domain.Resid.Setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

universe u

namespace Work.Domain.Resid

open Work.GCBasics

/-- A Mathlib gap: the composite `Spec.map (algebraMap O_x K(X)) ≫ fromSpecStalk x` is
`fromSpecStalk (genericPoint X)`. -/
private theorem fromSpecStalk_algebraMap {X : Scheme} [IrreducibleSpace X] (x : X) :
    Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
      X.fromSpecStalk x = X.fromSpecStalk (genericPoint X) :=
  Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := X) (genericPoint_specializes x)

variable {K : Type u} [Field K] {C : CurveBasics.Curve K} [SpecLin.DivBase C]

noncomputable section

theorem residMap_mem_domain {K : Type _} [Field K] {C : Work.CurveBasics.Curve K}
    [Work.SpecLin.DivBase C] {symGeom : ∀ n, Work.SpecLin.SymGeom C n} {g : ℕ}
    (D : Work.Domain.Resid.ResidData (K := K) symGeom g) {X : Work.GCBasics.Sch K}
    [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.IsLocallyNoetherian X.left]
    (hX : ∀ x : X.left, IsIntegrallyClosed (X.left.presheaf.stalk x))
    {r m : ℕ} (a : X ⟶ (symGeom r).S) (b : X ⟶ (symGeom (r + m)).S) (hm : g ≤ m)
    (x : X.left)
    (hx : Work.GCBasics.ell C (Work.Domain.Resid.divD symGeom a b
      (Work.GCBasics.resPt X x)) = 1) :
    x ∈ (D.residMap a b hm).domain := by
  haveI hProper : IsProper ((symGeom m).S.left ↘ Spec (CommRingCat.of K)) := D.isProper m
  haveI hSep : IsSeparated ((symGeom m).S.left ↘ Spec (CommRingCat.of K)) := inferInstance
  haveI hSepY : IsSeparated ((symGeom m).S).hom := hSep
  haveI : (symGeom m).S.left.IsSeparated := inferInstance
  haveI hResOver : (D.residMap a b hm).IsOver (Spec (CommRingCat.of K)) :=
    D.residMap_isOver a b hm
  haveI hPartOver : (D.residMap a b hm).toPartialMap.IsOver (Spec (CommRingCat.of K)) :=
    inferInstance
  obtain ⟨E, hEeff, hEdeg, hElin⟩ := D.rr7 (divD symGeom a b (resPt X x)) (by
    rw [ddeg_divD a b (resPt X x)]; exact_mod_cast hm)
  obtain ⟨yx, hyx⟩ := (symGeom m).divOf_complete E hEeff
    (show Ddeg C (resField X x) E = (m : ℤ) from by
      rw [hEdeg, ddeg_divD a b (resPt X x)])
  have hDx : LinEquiv C ((symGeom m).divOf yx) (divD symGeom a b (resPt X x)) := by
    rw [hyx]; exact hElin.symm
  let y0 : (symGeom m).S.left := yx.left (IsLocalRing.closedPoint (resField X x))
  rw [← Scheme.RationalMap.toRationalMap_toPartialMap (f := D.residMap a b hm)]
  refine Work.Domain.mem_domain_of_unique_extension (S := Spec (CommRingCat.of K)) hX
    (g := (D.residMap a b hm).toPartialMap) (x := x) (y₀ := y0) ?_
  intro A hA hloc ψ h1 h2
  show ψ (IsLocalRing.closedPoint A) = yx.left (IsLocalRing.closedPoint (resField X x))
  let ρ : X.left.presheaf.stalk x →+* A :=
    (algebraMap (X.left.presheaf.stalk x) X.left.functionField).codRestrict A.toSubring hA
  haveI : IsLocalHom ρ := hloc
  letI : Algebra K A := canonAlgebra (K := K) x ρ
  have hKA : (specOf K A).hom =
      Spec.map (CommRingCat.ofHom ρ) ≫ X.left.fromSpecStalk x ≫ X.hom :=
    canonAlgebra_spec (K := K) x ρ
  have hρ : (algebraMap A X.left.functionField).comp ρ =
      algebraMap (X.left.presheaf.stalk x) X.left.functionField := by ext s; rfl
  have hψ : ψ ≫ (symGeom m).S.hom = (specOf K A).hom := by rw [hKA]; exact h1
  have hρcat : CommRingCat.ofHom ρ ≫ CommRingCat.ofHom A.subtype =
      CommRingCat.ofHom (algebraMap (X.left.presheaf.stalk x) X.left.functionField) := by
    rw [← CommRingCat.ofHom_comp]; exact congrArg CommRingCat.ofHom hρ
  have hkey : Spec.map (CommRingCat.ofHom (algebraMap K X.left.functionField)) =
      Spec.map (CommRingCat.ofHom
        ((algebraMap A X.left.functionField).comp (algebraMap K A))) := by
    rw [show (algebraMap A X.left.functionField) = A.subtype from rfl]
    rw [CommRingCat.ofHom_comp, AlgebraicGeometry.Spec.map_comp]
    rw [← Work.GCBasics.specOf_hom K X.left.functionField,
      Work.GCBasics.specOf_functionField_hom]
    rw [← Work.GCBasics.specOf_hom K A, hKA]
    conv_rhs => rw [← Category.assoc]
    rw [← AlgebraicGeometry.Spec.map_comp (CommRingCat.ofHom ρ)
      (CommRingCat.ofHom A.subtype), hρcat]
    conv_rhs => rw [← Category.assoc]
    rw [fromSpecStalk_algebraMap x]
  haveI htower : IsScalarTower K A X.left.functionField := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    have hcat := Spec.map_inj.mp hkey
    have hhom := CommRingCat.hom_ext_iff.mp hcat
    rw [CommRingCat.hom_ofHom, CommRingCat.hom_ofHom] at hhom
    exact hhom
  let φ : RPt X A := canonPt x ρ hKA
  let ψA : RPt (symGeom m).S A := Over.homMk ψ hψ
  let u : RPt (symGeom r).S A := φ ≫ a
  let v : RPt (symGeom (r + m)).S A := φ ≫ b
  let w : RPt (symGeom (r + m)).S A := addMor symGeom D.addMap u ψA
  have hg : Function.Injective ⇑(IsScalarTower.toAlgHom K A X.left.functionField) := by
    intro aa bb h; exact Subtype.val_injective h
  let ι : FractionRing A →ₐ[K] X.left.functionField :=
    IsFractionRing.liftAlgHom (R := K) (A := A) (K := FractionRing A)
      (L := X.left.functionField) (g := IsScalarTower.toAlgHom K A X.left.functionField) hg
  have hι : ι.comp (IsScalarTower.toAlgHom K A (FractionRing A)) =
      IsScalarTower.toAlgHom K A X.left.functionField := by
    ext aa
    rw [AlgHom.comp_apply]
    show ι ((IsScalarTower.toAlgHom K A (FractionRing A)) aa) =
        (IsScalarTower.toAlgHom K A X.left.functionField) aa
    rw [show ι = IsFractionRing.liftAlgHom (R := K) (A := A) (K := FractionRing A)
      (L := X.left.functionField) (g := IsScalarTower.toAlgHom K A X.left.functionField) hg
      from rfl]
    rw [IsScalarTower.toAlgHom_apply K A (FractionRing A) aa,
      IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
    exact IsScalarTower.toAlgHom_apply K A X.left.functionField aa
  let pK : FPt (specOf K A) X.left.functionField :=
    specOfMap (IsScalarTower.toAlgHom K A X.left.functionField)
  have hφgen : pK ≫ φ = genericFPt X := by
    show RPt.map (IsScalarTower.toAlgHom K A X.left.functionField) (canonPt x ρ hKA) =
      genericFPt X
    apply Over.OverMorphism.ext
    simp only [RPt.map, Over.comp_left, Work.Domain.Resid.canonPt_left,
      Work.GCBasics.specOfMap_left, Work.GCBasics.genericFPt, Over.homMk_left]
    conv_lhs => rw [← Category.assoc]
    change (Spec.map (CommRingCat.ofHom (algebraMap A X.left.functionField)) ≫
        Spec.map (CommRingCat.ofHom ρ)) ≫ X.left.fromSpecStalk x = _
    rw [← AlgebraicGeometry.Spec.map_comp (CommRingCat.ofHom ρ)
      (CommRingCat.ofHom (algebraMap A X.left.functionField)),
      show CommRingCat.ofHom ρ ≫ CommRingCat.ofHom (algebraMap A X.left.functionField)
        = CommRingCat.ofHom (algebraMap (X.left.presheaf.stalk x) X.left.functionField)
        from hρcat]
    exact fromSpecStalk_algebraMap x
  have h2' : Spec.map (CommRingCat.ofHom (algebraMap A X.left.functionField)) ≫ ψ =
      (genValue a b D.rr7 hm).left := by
    rw [h2, ← Scheme.RationalMap.fromFunctionField_toRationalMap
      (f := (D.residMap a b hm).toPartialMap), Scheme.RationalMap.toRationalMap_toPartialMap]
    exact D.residMap_fromFunctionField a b hm
  have hψAg : pK ≫ ψA = genValue a b D.rr7 hm := by
    apply Over.OverMorphism.ext
    show Over.Hom.left (pK ≫ ψA) = Over.Hom.left (genValue a b D.rr7 hm)
    rw [Over.comp_left, Work.GCBasics.specOfMap_left]
    change Spec.map (CommRingCat.ofHom (algebraMap A X.left.functionField)) ≫ (Over.Hom.left ψA)
      = Over.Hom.left (genValue a b D.rr7 hm)
    rw [show Over.Hom.left ψA = ψ from rfl]
    exact h2'
  have hgenLin : LinEquiv C ((symGeom (r + m)).divOf (genPt A ≫ w))
      ((symGeom (r + m)).divOf (genPt A ≫ v)) := by
    refine (SpecLin.DivBase.linEquiv_bc_iff (C := C) ι _ _).mp ?_
    rw [← SpecLin.SymGeom.divOf_map ι (genPt A ≫ w),
        ← SpecLin.SymGeom.divOf_map ι (genPt A ≫ v)]
    change Work.GCBasics.LinEquiv C
      (SpecLin.SymGeom.divOf (Work.GCBasics.RPt.map ι (genPt A ≫ w)))
      (SpecLin.SymGeom.divOf (Work.GCBasics.RPt.map ι (genPt A ≫ v)))
    have hmapW : RPt.map ι (genPt A ≫ w) = pK ≫ w := by
      dsimp only [Work.GCBasics.RPt.map, Work.GCBasics.genPt]
      rw [← Category.assoc, ← Work.GCBasics.specOfMap_comp, hι]
    have hmapV : RPt.map ι (genPt A ≫ v) = pK ≫ v := by
      dsimp only [Work.GCBasics.RPt.map, Work.GCBasics.genPt]
      rw [← Category.assoc, ← Work.GCBasics.specOfMap_comp, hι]
    rw [hmapW, hmapV]
    have hpu : pK ≫ u = genericFPt X ≫ a := by
      show pK ≫ (φ ≫ a) = _; rw [← Category.assoc, hφgen]
    have hpv : pK ≫ v = genericFPt X ≫ b := by
      show pK ≫ (φ ≫ b) = _; rw [← Category.assoc, hφgen]
    have hdivW : (symGeom (r + m)).divOf (pK ≫ w)
        = (symGeom r).divOf (pK ≫ u) + (symGeom m).divOf (pK ≫ ψA) :=
      addMor_divOf D.addMap_divOf u ψA pK
    rw [hdivW, hpv, hpu, hψAg, add_comm]
    exact genValue_spec a b D.rr7 hm
  haveI hloc' : IsLocalHom ((IsLocalRing.residue A).comp ρ) := inferInstance
  have hespec : Spec.map (CommRingCat.ofHom (residueAlgHom x ρ)) ≫ Spec.map (X.left.residue x)
      = Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ Spec.map (CommRingCat.ofHom ρ) := by
    rw [show X.left.residue x =
      CommRingCat.ofHom (IsLocalRing.residue (X.left.presheaf.stalk x)) from rfl]
    rw [← AlgebraicGeometry.Spec.map_comp
      (f := CommRingCat.ofHom (IsLocalRing.residue (X.left.presheaf.stalk x)))
      (g := CommRingCat.ofHom (residueAlgHom x ρ))]
    rw [← CommRingCat.ofHom_comp, residueAlgHom_comp]
    rw [CommRingCat.ofHom_comp, AlgebraicGeometry.Spec.map_comp]
  have hklin : (residueAlgHom x ρ).comp (algebraMap K (resField X x))
      = algebraMap K (IsLocalRing.ResidueField A) := by
    have hcat : CommRingCat.ofHom ((residueAlgHom x ρ).comp (algebraMap K (resField X x)))
        = CommRingCat.ofHom (algebraMap K (IsLocalRing.ResidueField A)) := by
      apply Spec.map_inj.mp
      rw [CommRingCat.ofHom_comp, AlgebraicGeometry.Spec.map_comp]
      rw [← Work.GCBasics.specOf_hom K (resField X x), Work.GCBasics.specOf_resField_hom]
      rw [show Scheme.fromSpecResidueField X.left x
        = Spec.map (X.left.residue x) ≫ X.left.fromSpecStalk x from rfl]
      conv_lhs => rw [Category.assoc, ← Category.assoc]
      rw [hespec]
      rw [Category.assoc]
      rw [← hKA, Work.GCBasics.specOf_hom]
      rw [show (algebraMap K (IsLocalRing.ResidueField A))
          = (IsLocalRing.residue A).comp (algebraMap K A) from
        Eq.trans (IsScalarTower.algebraMap_eq K A (IsLocalRing.ResidueField A))
          (congrArg (fun f => f.comp (algebraMap K A))
            (IsLocalRing.ResidueField.algebraMap_eq A))]
      rw [CommRingCat.ofHom_comp, AlgebraicGeometry.Spec.map_comp]
    have hhom := CommRingCat.hom_ext_iff.mp hcat
    rwa [CommRingCat.hom_ofHom, CommRingCat.hom_ofHom] at hhom
  let e : resField X x →ₐ[K] IsLocalRing.ResidueField A :=
    AlgHom.mk (residueAlgHom x ρ) (fun k => RingHom.congr_fun hklin k)
  have hpt : closedPt (K := K) A ≫ canonPt x ρ hKA = RPt.map e (resPt X x) := by
    apply Over.OverMorphism.ext
    show Over.Hom.left (closedPt (K := K) A ≫ canonPt x ρ hKA)
      = Over.Hom.left (RPt.map e (resPt X x))
    rw [Over.comp_left, RPt.map, Over.comp_left]
    rw [show Over.Hom.left (closedPt (K := K) A)
        = Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) from rfl]
    rw [show Over.Hom.left (specOfMap e) = Spec.map (CommRingCat.ofHom e.toRingHom) from rfl]
    rw [Work.Domain.Resid.canonPt_left, Work.GCBasics.resPt_left]
    rw [show e.toRingHom = residueAlgHom x ρ from rfl]
    rw [show Scheme.fromSpecResidueField X.left x
      = Spec.map (X.left.residue x) ≫ X.left.fromSpecStalk x from rfl]
    conv_lhs => rw [← Category.assoc]
    conv_rhs => rw [← Category.assoc]
    rw [hespec]
  have hclosed : LinEquiv C ((symGeom (r + m)).divOf (closedPt (K := K) A ≫ w))
      ((symGeom (r + m)).divOf (closedPt (K := K) A ≫ v)) :=
    D.specLin (symGeom (r + m)) A w v hgenLin
  have hdivWc : (symGeom (r + m)).divOf (closedPt (K := K) A ≫ w)
      = (symGeom r).divOf (closedPt (K := K) A ≫ u)
        + (symGeom m).divOf (closedPt (K := K) A ≫ ψA) :=
    addMor_divOf D.addMap_divOf u ψA (closedPt (K := K) A)
  have hdivUc : (symGeom r).divOf (closedPt (K := K) A ≫ u)
      = SpecLin.DivBase.bc e ((symGeom r).divOf (resPt X x ≫ a)) := by
    rw [show closedPt (K := K) A ≫ u = RPt.map e (resPt X x ≫ a) from by
      show closedPt (K := K) A ≫ (φ ≫ a) = _
      rw [← Category.assoc, hpt]; rfl]
    exact SpecLin.SymGeom.divOf_map e (resPt X x ≫ a)
  have hdivVc : (symGeom (r + m)).divOf (closedPt (K := K) A ≫ v)
      = SpecLin.DivBase.bc e ((symGeom (r + m)).divOf (resPt X x ≫ b)) := by
    rw [show closedPt (K := K) A ≫ v = RPt.map e (resPt X x ≫ b) from by
      show closedPt (K := K) A ≫ (φ ≫ b) = _
      rw [← Category.assoc, hpt]; rfl]
    exact SpecLin.SymGeom.divOf_map e (resPt X x ≫ b)
  have hell : ell C ((symGeom m).divOf yx) = 1 := (ell_eq_of_linEquiv hDx).trans hx
  have hell' : ell C ((symGeom m).divOf (RPt.map e yx)) = 1 := by
    rw [show SpecLin.SymGeom.divOf (RPt.map e yx)
      = SpecLin.DivBase.bc e (SpecLin.SymGeom.divOf yx) from SpecLin.SymGeom.divOf_map e yx]
    rw [D.ell_bc e ((symGeom m).divOf yx)]
    exact hell
  have hbcc : SpecLin.DivBase.bc e (divD symGeom a b (resPt X x))
      = SpecLin.DivBase.bc e ((symGeom (r + m)).divOf (resPt X x ≫ b))
        - SpecLin.DivBase.bc e ((symGeom r).divOf (resPt X x ≫ a)) := by
    rw [divD, sub_eq_add_neg, SpecLin.DivBase.bc_add, SpecLin.DivBase.bc_neg, sub_eq_add_neg]
  have hclosed2 : LinEquiv C ((symGeom r).divOf (closedPt (K := K) A ≫ u)
      + (symGeom m).divOf (closedPt (K := K) A ≫ ψA))
      (SpecLin.DivBase.bc e ((symGeom (r + m)).divOf (resPt X x ≫ b))) := by
    rw [← hdivWc, ← hdivVc]; exact hclosed
  have hDxb0 : LinEquiv C (SpecLin.DivBase.bc e ((symGeom m).divOf yx)
      + SpecLin.DivBase.bc e ((symGeom r).divOf (resPt X x ≫ a)))
      (SpecLin.DivBase.bc e ((symGeom (r + m)).divOf (resPt X x ≫ b))) := by
    rw [show SpecLin.DivBase.bc e ((symGeom (r + m)).divOf (resPt X x ≫ b))
      = (SpecLin.DivBase.bc e ((symGeom (r + m)).divOf (resPt X x ≫ b))
        - SpecLin.DivBase.bc e ((symGeom r).divOf (resPt X x ≫ a)))
        + SpecLin.DivBase.bc e ((symGeom r).divOf (resPt X x ≫ a)) from by abel]
    refine (Work.GCBasics.LinEquiv.add_iff _ _
      (SpecLin.DivBase.bc e ((symGeom r).divOf (resPt X x ≫ a)))).mpr ?_
    rw [← hbcc]
    exact SpecLin.DivBase.linEquiv_bc e hDx
  have hcancel : LinEquiv C ((symGeom m).divOf (closedPt (K := K) A ≫ ψA))
      (SpecLin.DivBase.bc e ((symGeom m).divOf yx)) := by
    have hclosed2' : LinEquiv C ((symGeom m).divOf (closedPt (K := K) A ≫ ψA)
        + (symGeom r).divOf (closedPt (K := K) A ≫ u))
        (SpecLin.DivBase.bc e ((symGeom (r + m)).divOf (resPt X x ≫ b))) := by
      rw [add_comm]; exact hclosed2
    have hDxb : LinEquiv C (SpecLin.DivBase.bc e ((symGeom m).divOf yx)
        + (symGeom r).divOf (closedPt (K := K) A ≫ u))
        (SpecLin.DivBase.bc e ((symGeom (r + m)).divOf (resPt X x ≫ b))) := by
      rw [hdivUc]; exact hDxb0
    exact (Work.GCBasics.LinEquiv.add_iff _ _ ((symGeom r).divOf (closedPt (K := K) A ≫ u))).mp
      (hclosed2'.trans hDxb.symm)
  have hyx_eq : RPt.map e yx = closedPt (K := K) A ≫ ψA := by
    refine divOf_eq_of_linEquiv_of_ell_eq_one ?_ hell'
    rw [show SpecLin.SymGeom.divOf (RPt.map e yx)
      = SpecLin.DivBase.bc e (SpecLin.SymGeom.divOf yx) from SpecLin.SymGeom.divOf_map e yx]
    exact hcancel.symm
  haveI hresloc : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom (IsLocalRing.residue A))) := by
    rw [CommRingCat.hom_ofHom]; infer_instance
  have hψcp : ψ (IsLocalRing.closedPoint A)
      = Over.Hom.left (closedPt (K := K) A ≫ ψA)
          (IsLocalRing.closedPoint (IsLocalRing.ResidueField A)) := by
    rw [Over.comp_left]
    rw [show Over.Hom.left (closedPt (K := K) A)
      = Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) from rfl]
    rw [show Over.Hom.left ψA = ψ from rfl]
    rw [Scheme.Hom.comp_apply]
    exact congrArg (fun p => ψ p)
      (AlgebraicGeometry.Spec_closedPoint (f := CommRingCat.ofHom (IsLocalRing.residue A))).symm
  have hy0 : Over.Hom.left (RPt.map e yx)
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField A))
      = yx.left (IsLocalRing.closedPoint (resField X x)) := by
    rw [RPt.map, Over.comp_left]
    rw [show Over.Hom.left (specOfMap e) = Spec.map (CommRingCat.ofHom e.toRingHom) from rfl]
    rw [Scheme.Hom.comp_apply]
    apply congrArg (Over.Hom.left yx)
    exact AlgebraicGeometry.Spec_closedPoint
  rw [hψcp, ← hyx_eq]
  exact hy0

end

end Work.Domain.Resid
