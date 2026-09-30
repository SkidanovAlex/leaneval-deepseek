import Mathlib
import Submission.Work.SpecLin.Conventions
import Submission.Work.SpecLin.Points.Setup
import Submission.Work.SpecLin.Points.Basic
import Submission.Work.SpecLin.Interface
import Submission.Work.SpecLin.Setup.Ext
import Submission.Work.SpecLin.Setup.Basic
import Submission.Work.SpecLin.Core.range_base_subset_pair
import Submission.Work.SpecLin.Alt.affineOpenContaining
import Submission.Work.SpecLin.Alt.chartCore

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false


namespace Work.SpecLin.Alt

universe u

end Work.SpecLin.Alt

namespace Work.SpecLin

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

noncomputable def resAlg {K : Type u} [Field K] (R : Type u) [CommRing R] [IsDomain R]
    [ValuationRing R] [Algebra K R] (E : Ext K R) :
    IsLocalRing.ResidueField R →ₐ[K] IsLocalRing.ResidueField E.R' :=
  haveI : IsLocalHom (E.e : R →ₐ[K] E.R') := ⟨fun a ha => E.isLocal.map_nonunit a ha⟩
  IsLocalRing.ResidueField.mapAlgHom (R := K) (S := R) (T := E.R') E.e

theorem divOf_closedPt_map {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} [DivBase C]
    {n : ℕ} (G : SymGeom C n) (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [Algebra K R] (E : Ext K R) {p : RPt G.S R} :
    G.divOf (closedPt E.R' ≫ RPt.map E.e p) =
      DivBase.bc (resAlg (K := K) R E) (G.divOf (closedPt R ≫ p)) := by
  haveI : IsLocalHom (E.e : R →ₐ[K] E.R') := ⟨fun a ha => E.isLocal.map_nonunit a ha⟩
  rw [show resAlg (K := K) R E
      = IsLocalRing.ResidueField.mapAlgHom (R := K) (S := R) (T := E.R') E.e from rfl]
  rw [← G.divOf_map (IsLocalRing.ResidueField.mapAlgHom (R := K) (S := R) (T := E.R') E.e)
    (closedPt R ≫ p)]
  congr 1
  have h1 : closedPt (K := K) E.R' ≫ RPt.map E.e p =
      (closedPt (K := K) E.R' ≫ specOfMap (K := K) E.e) ≫ p := by
    simp only [RPt.map, Category.assoc]
  rw [h1, ← specOfMap_residue_eq (K := K) E.e, Category.assoc]
  simp only [RPt.map, Category.assoc]

theorem map_genPt_eq {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} [DivBase C] {n : ℕ}
    (G : SymGeom C n) (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (E : Ext K R) {p : RPt G.S R} :
    RPt.map E.psi (genPt E.R' ≫ RPt.map E.e p) =
      RPt.map (IsScalarTower.toAlgHom K (FractionRing R) E.F) (genPt R ≫ p) := by
  have key : E.psi.comp ((IsScalarTower.toAlgHom K E.R' (FractionRing E.R')).comp E.e) =
      (IsScalarTower.toAlgHom K (FractionRing R) E.F).comp
        (IsScalarTower.toAlgHom K R (FractionRing R)) := by
    ext r
    simp only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply]
    rw [E.psi_algebraMap, E.compat]
  have hmor : specOfMap (K := K) E.psi ≫
        specOfMap (K := K) (IsScalarTower.toAlgHom K E.R' (FractionRing E.R')) ≫
        specOfMap (K := K) E.e =
      specOfMap (K := K) (IsScalarTower.toAlgHom K (FractionRing R) E.F) ≫
        specOfMap (K := K) (IsScalarTower.toAlgHom K R (FractionRing R)) := by
    rw [← specOfMap_comp E.e (IsScalarTower.toAlgHom K E.R' (FractionRing E.R')),
      ← specOfMap_comp ((IsScalarTower.toAlgHom K E.R' (FractionRing E.R')).comp E.e) E.psi,
      ← specOfMap_comp (IsScalarTower.toAlgHom K R (FractionRing R))
        (IsScalarTower.toAlgHom K (FractionRing R) E.F),
      key]
  calc RPt.map E.psi (genPt E.R' ≫ RPt.map E.e p)
      = (specOfMap (K := K) E.psi ≫
          specOfMap (K := K) (IsScalarTower.toAlgHom K E.R' (FractionRing E.R')) ≫
          specOfMap (K := K) E.e) ≫ p := by
        simp only [genPt_eq_specOfMap, RPt.map, Category.assoc]
    _ = (specOfMap (K := K) (IsScalarTower.toAlgHom K (FractionRing R) E.F) ≫
          specOfMap (K := K) (IsScalarTower.toAlgHom K R (FractionRing R))) ≫ p := by rw [hmor]
    _ = RPt.map (IsScalarTower.toAlgHom K (FractionRing R) E.F) (genPt R ≫ p) := by
        simp only [genPt_eq_specOfMap, RPt.map, Category.assoc]

theorem specLin {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    [Work.SpecLin.DivBase C] {n : ℕ} (G : Work.SpecLin.SymGeom C n) (R : Type u)
    [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (a b : Work.SpecLin.RPt G.S R)
    (hF : Work.SpecLin.LinEquiv C (G.divOf (Work.SpecLin.genPt R ≫ a))
      (G.divOf (Work.SpecLin.genPt R ≫ b))) :
    Work.SpecLin.LinEquiv C (G.divOf (Work.SpecLin.closedPt R ≫ a))
      (G.divOf (Work.SpecLin.closedPt R ≫ b)) := by
  obtain ⟨E⟩ := nonempty_ext (K := K) R
  haveI : IsLocalHom (E.e : R →ₐ[K] E.R') := ⟨fun x hx => E.isLocal.map_nonunit x hx⟩
  obtain ⟨x, hx⟩ := G.split (F := FractionRing R) (F' := E.F) (G.divOf (genPt R ≫ a))
    (G.divOf_isEffective _) (G.divOf_deg _)
  obtain ⟨y, hy⟩ := G.split (F := FractionRing R) (F' := E.F) (G.divOf (genPt R ≫ b))
    (G.divOf_isEffective _) (G.divOf_deg _)
  have hx' : G.powMap x =
      RPt.map (IsScalarTower.toAlgHom K (FractionRing R) E.F) (genPt R ≫ a) := by
    apply G.divOf_injective
    rw [G.divOf_powMap, ← hx,
      ← G.divOf_map (IsScalarTower.toAlgHom K (FractionRing R) E.F) (genPt R ≫ a)]
  have hy' : G.powMap y =
      RPt.map (IsScalarTower.toAlgHom K (FractionRing R) E.F) (genPt R ≫ b) := by
    apply G.divOf_injective
    rw [G.divOf_powMap, ← hy,
      ← G.divOf_map (IsScalarTower.toAlgHom K (FractionRing R) E.F) (genPt R ≫ b)]
  choose s hs using fun m => exists_CurvePt_of_FPt (K := K) (C := C) E.R' E.F (x m)
  choose t ht using fun m => exists_CurvePt_of_FPt (K := K) (C := C) E.R' E.F (y m)
  have hcx : RPt.map (IsScalarTower.toAlgHom K E.R' E.F) (G.powMap s) = G.powMap x := by
    rw [show RPt.map (IsScalarTower.toAlgHom K E.R' E.F) (G.powMap s) =
        G.powMap (fun m => RPt.map (IsScalarTower.toAlgHom K E.R' E.F) (s m)) from
      (G.powMap_comp (specOfMap (K := K) (IsScalarTower.toAlgHom K E.R' E.F)) s).symm,
      show (fun m => RPt.map (IsScalarTower.toAlgHom K E.R' E.F) (s m)) = x from
        funext fun m => hs m]
  have hcy : RPt.map (IsScalarTower.toAlgHom K E.R' E.F) (G.powMap t) = G.powMap y := by
    rw [show RPt.map (IsScalarTower.toAlgHom K E.R' E.F) (G.powMap t) =
        G.powMap (fun m => RPt.map (IsScalarTower.toAlgHom K E.R' E.F) (t m)) from
      (G.powMap_comp (specOfMap (K := K) (IsScalarTower.toAlgHom K E.R' E.F)) t).symm,
      show (fun m => RPt.map (IsScalarTower.toAlgHom K E.R' E.F) (t m)) = y from
        funext fun m => ht m]
  have hca : G.powMap s = RPt.map E.e a := by
    refine RPt.eq_of_generic_eq (X := G.S) G.isProper.toIsSeparated E.R' E.F ?_
    rw [hcx, hx', ← RPt.map_comp E.e (IsScalarTower.toAlgHom K E.R' E.F) a, Ext.compat' E,
      RPt.map_comp (IsScalarTower.toAlgHom K R (FractionRing R))
        (IsScalarTower.toAlgHom K (FractionRing R) E.F) a]
    simp only [genPt_eq_specOfMap, RPt.map]
  have hcb : G.powMap t = RPt.map E.e b := by
    refine RPt.eq_of_generic_eq (X := G.S) G.isProper.toIsSeparated E.R' E.F ?_
    rw [hcy, hy', ← RPt.map_comp E.e (IsScalarTower.toAlgHom K E.R' E.F) b, Ext.compat' E,
      RPt.map_comp (IsScalarTower.toAlgHom K R (FractionRing R))
        (IsScalarTower.toAlgHom K (FractionRing R) E.F) b]
    simp only [genPt_eq_specOfMap, RPt.map]
  -- the hypothesis of the core (over `Frac E.R'`), by descent from `E.F`
  have hcore : LinEquiv C (∑ m, ptDiv (genPt E.R' ≫ s m))
      (∑ m, ptDiv (genPt E.R' ≫ t m)) := by
    refine (DivBase.linEquiv_bc_iff E.psi _ _).mp ?_
    have hX : DivBase.bc E.psi (∑ m, ptDiv (genPt E.R' ≫ s m)) =
        DivBase.bc (IsScalarTower.toAlgHom K (FractionRing R) E.F)
          (G.divOf (genPt R ≫ a)) := by
      rw [← G.divOf_powMap (fun m => genPt E.R' ≫ s m),
        G.powMap_comp (genPt E.R') s, hca,
        ← G.divOf_map E.psi (genPt E.R' ≫ RPt.map E.e a),
        ← G.divOf_map (IsScalarTower.toAlgHom K (FractionRing R) E.F) (genPt R ≫ a)]
      exact congrArg (fun q => G.divOf q) (map_genPt_eq G R E)
    have hY : DivBase.bc E.psi (∑ m, ptDiv (genPt E.R' ≫ t m)) =
        DivBase.bc (IsScalarTower.toAlgHom K (FractionRing R) E.F)
          (G.divOf (genPt R ≫ b)) := by
      rw [← G.divOf_powMap (fun m => genPt E.R' ≫ t m),
        G.powMap_comp (genPt E.R') t, hcb,
        ← G.divOf_map E.psi (genPt E.R' ≫ RPt.map E.e b),
        ← G.divOf_map (IsScalarTower.toAlgHom K (FractionRing R) E.F) (genPt R ≫ b)]
      exact congrArg (fun q => G.divOf q) (map_genPt_eq G R E)
    rw [hX, hY]
    exact DivBase.linEquiv_bc (IsScalarTower.toAlgHom K (FractionRing R) E.F) hF
  have hcls : LinEquiv C (∑ m, ptDiv (closedPt E.R' ≫ s m))
      (∑ m, ptDiv (closedPt E.R' ≫ t m)) := by
    -- an affine open containing the (finitely many) images of all the sections
    have hbigS : ((Set.range fun m : Fin n =>
          (s m).left.base (genericPoint (Spec (CommRingCat.of E.R')))) ∪
        (Set.range fun m : Fin n =>
          (s m).left.base (IsLocalRing.closedPoint E.R'))).Finite :=
      (Set.finite_range _).union (Set.finite_range _)
    have hfinS : (⋃ m : Fin n, Set.range (s m).left.base).Finite := by
      refine hbigS.subset ?_
      intro z hz
      rcases Set.mem_iUnion.mp hz with ⟨m, hzm⟩
      rcases (Core.range_base_subset_pair (K := K) (C := C) E.R' (s m)) hzm with h | h
      · exact Set.mem_union_left _ (Set.mem_range.mpr ⟨m, h.symm⟩)
      · exact Set.mem_union_right _ (Set.mem_range.mpr ⟨m, h.symm⟩)
    have hbigT : ((Set.range fun m : Fin n =>
          (t m).left.base (genericPoint (Spec (CommRingCat.of E.R')))) ∪
        (Set.range fun m : Fin n =>
          (t m).left.base (IsLocalRing.closedPoint E.R'))).Finite :=
      (Set.finite_range _).union (Set.finite_range _)
    have hfinT : (⋃ m : Fin n, Set.range (t m).left.base).Finite := by
      refine hbigT.subset ?_
      intro z hz
      rcases Set.mem_iUnion.mp hz with ⟨m, hzm⟩
      rcases (Core.range_base_subset_pair (K := K) (C := C) E.R' (t m)) hzm with h | h
      · exact Set.mem_union_left _ (Set.mem_range.mpr ⟨m, h.symm⟩)
      · exact Set.mem_union_right _ (Set.mem_range.mpr ⟨m, h.symm⟩)
    obtain ⟨W, hW, hS⟩ := Alt.affineOpenContaining (K := K) C
      ((⋃ m : Fin n, Set.range (s m).left.base) ∪ (⋃ m : Fin n, Set.range (t m).left.base))
      (hfinS.union hfinT)
    have hsW : ∀ m, Set.range (s m).left.base ⊆ (W : Set C.left) := by
      intro m z hz
      exact hS (by simp only [Set.mem_union, Set.mem_iUnion]; exact Or.inl ⟨m, hz⟩)
    have htW : ∀ m, Set.range (t m).left.base ⊆ (W : Set C.left) := by
      intro m z hz
      exact hS (by simp only [Set.mem_union, Set.mem_iUnion]; exact Or.inr ⟨m, hz⟩)
    exact Alt.chartCore (K := K) (C := C) E.R' W hW s t hsW htW hcore
  have hX' : (∑ m, ptDiv (closedPt E.R' ≫ s m)) =
      DivBase.bc (resAlg (K := K) R E) (G.divOf (closedPt R ≫ a)) := by
    rw [← G.divOf_powMap (fun m => closedPt E.R' ≫ s m),
      G.powMap_comp (closedPt E.R') s, hca]
    exact divOf_closedPt_map (G := G) (R := R) (E := E) (p := a)
  have hY' : (∑ m, ptDiv (closedPt E.R' ≫ t m)) =
      DivBase.bc (resAlg (K := K) R E) (G.divOf (closedPt R ≫ b)) := by
    rw [← G.divOf_powMap (fun m => closedPt E.R' ≫ t m),
      G.powMap_comp (closedPt E.R') t, hcb]
    exact divOf_closedPt_map (G := G) (R := R) (E := E) (p := b)
  have hfinal : LinEquiv C
      (DivBase.bc (resAlg (K := K) R E) (G.divOf (closedPt R ≫ a)))
      (DivBase.bc (resAlg (K := K) R E) (G.divOf (closedPt R ≫ b))) := by
    rw [← hX', ← hY']
    exact hcls
  exact (DivBase.linEquiv_bc_iff (resAlg (K := K) R E) _ _).mp hfinal

end Work.SpecLin
