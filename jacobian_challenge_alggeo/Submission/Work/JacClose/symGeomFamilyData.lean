import Mathlib
import Submission.Work.JacClose.Inputs
import Submission.Work.BNChart.Resid
import Submission.Work.SymQuot.SymGeomInst

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory

namespace Work.JacClose

universe u

noncomputable section

variable {K : Type u} [Field K]

/-- The `powMap` of the concrete family `SymQuot.symGeomFamily C` on the family of projections
`Cⁿ ⟶ C` is the quotient map `Cⁿ ⟶ Symⁿ C`, in the case `n = 0`. -/
lemma symGeomFamily_powMap_proj_zero (C : Work.CurveBasics.Curve K) :
    (Work.SymQuot.symGeomFamily C 0).powMap
        (fun m : Fin 0 => Work.SymQuot.proj C.toOver 0 m) = Work.SymQuot.Sym.quot C 0 := by
  have h : Work.SymQuot.Sym.prodZeroPt (K := K) C.toOver (Work.SymQuot.prod C.toOver 0) = 𝟙 _ := by
    apply Limits.Pi.hom_ext
    intro i
    exact Fin.elim0 i
  change Work.SymQuot.Sym.prodZeroPt (K := K) C.toOver (Work.SymQuot.prod C.toOver 0)
      ≫ Work.SymQuot.Sym.quot C 0 = Work.SymQuot.Sym.quot C 0
  rw [h, Category.id_comp]

/-- The `powMap` of the concrete family `SymQuot.symGeomFamily C` on the family of projections
`Cⁿ ⟶ C` is the quotient map `Cⁿ ⟶ Symⁿ C`, in the case `n = k + 1`. -/
lemma symGeomFamily_powMap_proj_succ (C : Work.CurveBasics.Curve K) (k : ℕ) :
    (Work.SymQuot.symGeomFamily C (k + 1)).powMap
        (fun m : Fin (k + 1) => Work.SymQuot.proj C.toOver (k + 1) m)
      = Work.SymQuot.Sym.quot C (k + 1) := by
  change Work.SymQuot.Sym.powMap C (k + 1)
      (fun m : Fin (k + 1) => Work.SymQuot.proj C.toOver (k + 1) m)
    = Work.SymQuot.Sym.quot C (k + 1)
  rw [Work.SymQuot.Sym.powMap]
  have hlift : Limits.Pi.lift (fun m : Fin (k + 1) => Work.SymQuot.proj C.toOver (k + 1) m)
      = 𝟙 (Work.SymQuot.prod C.toOver (k + 1)) := by
    apply Limits.Pi.hom_ext
    intro m
    rw [Limits.Pi.lift_comp_π]
    rfl
  rw [hlift, Category.id_comp]

/-- The quotient property of `Symⁿ C` for the concrete family `SymQuot.symGeomFamily C`: an
`Sₙ`-invariant morphism `Cⁿ ⟶ Z` factors uniquely through the `powMap` of the family on the
projections `Cⁿ ⟶ C` (which is the quotient map). -/
lemma symGeomFamily_desc (C : Work.CurveBasics.Curve K) (n : ℕ) {Z : Work.GCBasics.Sch K}
    (f : Work.SymQuot.prod C.toOver n ⟶ Z)
    (hf : ∀ σ : Equiv.Perm (Fin n), (Work.SymQuot.permIso C.toOver σ).hom ≫ f = f) :
    ∃! g : (Work.SymQuot.symGeomFamily C n).S ⟶ Z,
      (Work.SymQuot.symGeomFamily C n).powMap
        (fun m : Fin n => Work.SymQuot.proj C.toOver n m) ≫ g = f := by
  rcases n with _ | k
  · have h0 : (Work.SymQuot.symGeomFamily C 0).powMap
        (fun m : Fin 0 => Work.SymQuot.proj C.toOver 0 m)
        = (Work.SymQuot.Sym.symZeroIso C).hom := by
      rw [symGeomFamily_powMap_proj_zero C]
      rfl
    refine ⟨(Work.SymQuot.Sym.symZeroIso C).inv ≫ f, ?_, ?_⟩
    · rw [h0]
      exact Iso.hom_inv_id_assoc _ f
    · intro g hg
      have hg' : (Work.SymQuot.Sym.symZeroIso C).hom ≫ g = f := by rw [← h0]; exact hg
      calc g = (Work.SymQuot.Sym.symZeroIso C).inv
              ≫ (Work.SymQuot.Sym.symZeroIso C).hom ≫ g := by
              rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
        _ = (Work.SymQuot.Sym.symZeroIso C).inv ≫ f := by rw [hg']
  · have hq : (Work.SymQuot.symGeomFamily C (k + 1)).powMap
        (fun m : Fin (k + 1) => Work.SymQuot.proj C.toOver (k + 1) m)
        = Work.SymQuot.Sym.quot C (k + 1) := symGeomFamily_powMap_proj_succ C k
    have hf' : ∀ σ : ULift.{u} (Equiv.Perm (Fin (k + 1))),
        (Work.SymQuot.symAction C (k + 1)).hom σ ≫ f.left = f.left := by
      intro σ
      have h : ((Work.SymQuot.permIso C.toOver σ.down).hom ≫ f).left = f.left := by
        rw [hf σ.down]
      simpa [Work.SymQuot.symAction_hom, Work.SymQuot.permGAction] using h
    obtain ⟨g, hg, huniq⟩ := Work.SymQuot.Sym.desc C (k + 1) f hf'
    refine ⟨g, ?_, ?_⟩
    · rw [hq]; exact hg
    · intro g' hg'
      exact huniq g' (by rw [← hq]; exact hg')

/-- `x ↦ x + E` for the concrete family of symmetric powers and an effective `K`-divisor `E`
of degree `g - 1`: existence form, from which `SYData.curveAddOf` is chosen. -/
lemma exists_curveAddOf (C : Work.CurveBasics.Curve K) (g : ℕ) (hg : 1 ≤ g)
    (E : Work.SpecLin.Dv C K) (hE : E.IsEffective) (hd : Work.GCBasics.Ddeg C K E = (g : ℤ) - 1) :
    ∃ f : C.toOver ⟶ (Work.SymQuot.symGeomFamily C g).S,
      ∀ {F : Type u} [Field F] [Algebra K F] (x : Work.SpecLin.FPt C.toOver F),
        (Work.SymQuot.symGeomFamily C g).divOf (x ≫ f)
          = Work.SpecLin.ptDiv x + Work.GroupChunk.bcKF F E := by
  cases g with
  | zero => exact absurd hg (by omega)
  | succ k =>
    haveI : NeZero (k + 1) := ⟨by omega⟩
    have hd' : (C.baseChange K).deg E = ((k + 1 : ℕ) : ℤ) - 1 := hd
    refine ⟨Work.SymQuot.Sym.curveAdd C (k + 1) hg E hE hd', ?_⟩
    intro F _ _ x
    show Work.SymQuot.DivOf.divOf F (x ≫ Work.SymQuot.Sym.curveAdd C (k + 1) hg E hE hd')
        = Work.SpecLin.ptDiv x + Work.GroupChunk.bcKF F E
    rw [Work.SymQuot.OfDiv.curveAdd_divOf (C := C) (g := k + 1) hg E hE hd' x, bc_ofId_eq]

theorem symGeomFamilyData {K : Type u} [Field K] (C : Work.CurveBasics.Curve K)
    (P0 : Work.Charts.unitSch K ⟶ C.toOver) :
    Nonempty (Work.JacClose.SYData C P0 (Work.SymQuot.symGeomFamily C)) := by
  classical
  refine ⟨?_⟩
  refine
    { isProper_Sym := ?_
      geomIntegral_Sym := ?_
      geomIrred_Sym := ?_
      locallyOfFiniteType_Sym := ?_
      addMap := ?_
      addMap_divOf := ?_
      constMap := ?_
      constMap_divOf := ?_
      curveIso := ?_
      curveIso_divOf := ?_
      curveAddOf := ?_
      desc := ?_
      curveAddOf_divOf := ?_ }
  · intro n
    rcases n with _ | k
    · exact Work.SymQuot.Sym.isProper_sym C 0
    · exact Work.SymQuot.Sym.isProper_sym C (k + 1)
  · intro n
    rcases n with _ | k
    · exact Work.SymQuot.Sym.geometricallyIntegral_sym C 0
    · exact Work.SymQuot.Sym.geometricallyIntegral_sym C (k + 1)
  · intro n
    rcases n with _ | k
    · exact Work.SymQuot.Sym.geometricallyIrreducible_sym C 0
    · exact Work.SymQuot.Sym.geometricallyIrreducible_sym C (k + 1)
  · intro n
    rcases n with _ | k
    · exact Work.SymQuot.Sym.locallyOfFiniteType_sym C 0
    · exact Work.SymQuot.Sym.locallyOfFiniteType_sym C (k + 1)
  · exact Work.BNChart.addMapFam C
  · exact Work.BNChart.addMapFam_divOf C
  · exact Work.BNChart.constMapFam C
  · intro n E hE hd X F _ _ p
    rw [Work.BNChart.constMapFam_divOf C n E hE hd X p, bc_ofId_eq]
  · exact Work.BNChart.curveIsoFam C
  · exact Work.BNChart.curveIsoFam_divOf C
  · intro g hg E hE hd
    exact (exists_curveAddOf C g hg E hE hd).choose
  · exact fun n Z f hf => symGeomFamily_desc C n f hf
  · intro g hg E hE hd
    exact (exists_curveAddOf C g hg E hE hd).choose_spec

end

end Work.JacClose
