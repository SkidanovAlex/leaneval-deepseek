import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

/-- If a morphism of chain complexes of `F`-modules induces an isomorphism on the `k`-th homology,
then it induces an isomorphism on the left homology of the `k`-th short complex
`C.sc' (k+1) k (k-1)`, computed in the explicit `moduleCatLeftHomologyData` model.

The proof conjugates the given isomorphism with the two canonical isomorphisms
`(C.sc' (k+1) k (k-1)).homology ≅ (C.sc' (k+1) k (k-1)).moduleCatLeftHomologyData.H`,
using that `HomologicalComplex.homologyMap φ k` is the homology map of the short complex
`C.sc k`, and that `C.sc k` is naturally isomorphic to `C.sc' (k+1) k (k-1)`. -/
theorem isIso_chainScMap_of_isIso_homologyMap {F : Type} [Field F]
    {C D : ChainComplex (ModuleCat.{0,0} F) ℕ} (φ : C ⟶ D) (k : ℕ)
    (h : IsIso (HomologicalComplex.homologyMap φ k)) :
    IsIso (ShortComplex.leftHomologyMap'
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{0,0} F) (ComplexShape.down ℕ)
        (k + 1) k (k - 1)).map φ)
      (C.sc' (k + 1) k (k - 1)).moduleCatLeftHomologyData
      (D.sc' (k + 1) k (k - 1)).moduleCatLeftHomologyData) := by
  let c := ComplexShape.down ℕ
  let Sc := HomologicalComplex.shortComplexFunctor' (ModuleCat.{0,0} F) c (k + 1) k (k - 1)
  let Fk := HomologicalComplex.shortComplexFunctor (ModuleCat.{0,0} F) c k
  -- `ComplexShape.down ℕ` computes `prev`/`next` as `k + 1`/`k - 1`.
  have hprev : c.prev k = k + 1 := ChainComplex.prev ℕ k
  have hnext : c.next k = k - 1 := by
    obtain _ | j := k
    · simp [c, ChainComplex.next_nat_zero]
    · simp [c, ChainComplex.next_nat_succ]
  -- The canonical natural isomorphism `C.sc k ≅ C.sc' (k+1) k (k-1)`.
  let e := HomologicalComplex.natIsoSc' (ModuleCat.{0,0} F) c (k + 1) k (k - 1) hprev hnext
  have hnat : e.hom.app C ≫ Sc.map φ = Fk.map φ ≫ e.hom.app D := (e.hom.naturality φ).symm
  have hψ : Sc.map φ = e.inv.app C ≫ Fk.map φ ≫ e.hom.app D := by
    calc Sc.map φ = (e.inv.app C ≫ e.hom.app C) ≫ Sc.map φ := by
            rw [Iso.inv_hom_id_app, Category.id_comp]
      _ = e.inv.app C ≫ (e.hom.app C ≫ Sc.map φ) := by rw [Category.assoc]
      _ = e.inv.app C ≫ (Fk.map φ ≫ e.hom.app D) := by rw [hnat]
  -- `HomologicalComplex.homologyMap φ k` is by definition the homology map of `Fk.map φ`.
  have hbase : IsIso (ShortComplex.homologyMap (Fk.map φ)) := h
  -- Hence the homology map of `Sc.map φ` is also an isomorphism.
  have hiso : IsIso (ShortComplex.homologyMap (Sc.map φ)) := by
    rw [hψ]
    rw [ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp]
    infer_instance
  -- Transport along the homology isomorphisms of the explicit left homology data.
  let hC := (Sc.obj C).moduleCatLeftHomologyData
  let hD := (Sc.obj D).moduleCatLeftHomologyData
  have hEq : ShortComplex.homologyMap (Sc.map φ) =
      hC.homologyIso.hom ≫ ShortComplex.leftHomologyMap' (Sc.map φ) hC hD ≫
        hD.homologyIso.inv := by
    have hh := ShortComplex.LeftHomologyMapData.homologyMap_eq (φ := Sc.map φ)
      (γ := ShortComplex.leftHomologyMapData (Sc.map φ) hC hD)
    rwa [← ShortComplex.LeftHomologyMapData.leftHomologyMap'_eq] at hh
  have hEq2 : ShortComplex.leftHomologyMap' (Sc.map φ) hC hD =
      hC.homologyIso.inv ≫ ShortComplex.homologyMap (Sc.map φ) ≫ hD.homologyIso.hom := by
    rw [hEq]
    simp
  have hiso2 : IsIso (ShortComplex.leftHomologyMap' (Sc.map φ) hC hD) := by
    rw [hEq2]
    infer_instance
  exact hiso2

end Work.Serre
