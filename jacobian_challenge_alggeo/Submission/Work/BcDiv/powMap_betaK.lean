import Mathlib
import Submission.Work.BcDiv.SymPts
import Submission.Work.BcDiv.Points
import Submission.Work.BcDiv.PbPt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.BcDiv

universe u

noncomputable section

variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L]
  {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F]

/-- **Naturality of `pbPtMap`**: the projection of a point of the base change, composed with a
morphism `u : Y ⟶ Y'` of `K`-schemes, is the projection of the point composed with the base
change of `u`. -/
lemma pbPtMap_comp_map (Y Y' : Work.SpecLin.Sch K) (u : Y ⟶ Y')
    (q : Work.SpecLin.FPt ((Over.pullback (Curve.specMap K L)).obj Y) F) :
    pbPtMap Y q ≫ u = pbPtMap Y' (q ≫ (Over.pullback (Curve.specMap K L)).map u) := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, pbPtMap_left, Over.pullback_map_left, Category.assoc,
    pullback.lift_fst]

/-- The inverse of the base-change comparison `(Cⁿ)_L ≅ (C_L)ⁿ`, composed with the `m`-th
projection of `Cⁿ`, is the `m`-th projection of `(C_L)ⁿ`. -/
lemma symPiIso_inv_comp_map_proj {C : Curve K} (n : ℕ) [Work.SymQuot.CurveAffineCover C]
    (m : Fin n) :
    (Work.SymQuot.BaseChange.symPiIso K L C n).inv ≫
        (Over.pullback (Curve.specMap K L)).map (Work.SymQuot.proj C.toOver n m)
      = Work.SymQuot.proj ((Over.pullback (Curve.specMap K L)).obj C.toOver) n m := by
  rw [← Work.SymQuot.BaseChange.pbPiIso_hom_proj (Curve.specMap K L) C.toOver n m]
  simp only [Work.SymQuot.BaseChange.symPiIso, Iso.inv_hom_id_assoc]

/-- The `m`-th projection of the `n`-tuple of points of `C_L` (transported to `Cⁿ`) is the
projection of the `m`-th point to `C`. -/
lemma pbPtMap_piLift_apply {C : Curve K} (n : ℕ) [Work.SymQuot.CurveAffineCover C]
    (x : Fin n → Work.SpecLin.CurveFPt (C.baseChange L) F) (m : Fin n) :
    pbPtMap (Work.SymQuot.prod C.toOver n)
        (Limits.Pi.lift x ≫ (Work.SymQuot.BaseChange.symPiIso K L C n).inv) ≫
      Work.SymQuot.proj C.toOver n m = bcPtK (x m) := by
  calc pbPtMap (Work.SymQuot.prod C.toOver n)
        (Limits.Pi.lift x ≫ (Work.SymQuot.BaseChange.symPiIso K L C n).inv) ≫
      Work.SymQuot.proj C.toOver n m
      = pbPtMap C.toOver ((Limits.Pi.lift x ≫ (Work.SymQuot.BaseChange.symPiIso K L C n).inv) ≫
          (Over.pullback (Curve.specMap K L)).map (Work.SymQuot.proj C.toOver n m)) :=
        pbPtMap_comp_map _ _ _ _
    _ = pbPtMap C.toOver (Limits.Pi.lift x ≫ (Work.SymQuot.BaseChange.symPiIso K L C n).inv ≫
          (Over.pullback (Curve.specMap K L)).map (Work.SymQuot.proj C.toOver n m)) :=
        congrArg (pbPtMap (Y := C.toOver)) (Category.assoc _ _ _)
    _ = pbPtMap C.toOver (Limits.Pi.lift x ≫
          Work.SymQuot.proj ((Over.pullback (Curve.specMap K L)).obj C.toOver) n m) :=
        congrArg (pbPtMap (Y := C.toOver))
          (congrArg (fun t => Limits.Pi.lift x ≫ t)
            (symPiIso_inv_comp_map_proj (K := K) (L := L) (C := C) n m))
    _ = pbPtMap C.toOver (x m) :=
        congrArg (pbPtMap (Y := C.toOver)) (Limits.Pi.lift_comp_π x m)
    _ = bcPtK (x m) := rfl

/-- **The `n`-fold form**: the projection to `Cⁿ` of the `n`-tuple of points of `C_L` is the
`n`-tuple of the projected points. -/
lemma pbPtMap_piLift {C : Curve K} (n : ℕ) [Work.SymQuot.CurveAffineCover C]
    (x : Fin n → Work.SpecLin.CurveFPt (C.baseChange L) F) :
    pbPtMap (Work.SymQuot.prod C.toOver n)
        (Limits.Pi.lift x ≫ (Work.SymQuot.BaseChange.symPiIso K L C n).inv)
      = Limits.Pi.lift (fun m => bcPtK (x m)) := by
  apply Limits.Pi.hom_ext
  intro m
  exact (pbPtMap_piLift_apply (K := K) (L := L) n x m).trans
    (Limits.Pi.lift_comp_π (fun m => bcPtK (x m)) m).symm

/-- **B5, compatibility of `ptsK` with the addition map `powMap`.** The point comparison
`Work.BcDiv.ptsK n` sends the sum of `n` points of `C_L` (i.e. `SymQuot.Sym.powMap (C_L) n x`) to
the sum of their images under `Work.BcDiv.bcPtK` in `Symⁿ C`:
`ptsK (powMap x) = powMap (bcPtK ∘ x)`.

Proof route (do NOT import the in-flight `SymQuot/BaseChange/powMap_symBeta.lean`, which is not
yet complete — prove the statement inside this file): `SymQuot.Sym.powMap` unfolds as
`Pi.lift x ≫ Sym.quot`; compare the two sides of the statement as morphisms over `Spec K` by
composing with the product projections `SymQuot.proj C.toOver n m` (universal property of the
product `Cⁿ`), using `symβ_spec`/`symfL_left`/`symqL_left`, `pbPiIso_hom_proj`
(`Submission/Work/SymQuot/BaseChange/exists_symBaseChangeIso.lean`) and
`Work.BcDiv.ptsK_left` / `Work.BcDiv.bcPtK_left` (both `rfl`).

Namespace `Work.BcDiv`; file `Submission/Work/BcDiv/powMap_betaK.lean`; imports
`Submission.Work.BcDiv.SymPts`, `Submission.Work.BcDiv.Points`. -/
theorem powMap_betaK {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {L : Type u} [Field L]
    [Algebra K L] {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
    (n : ℕ) [Work.SymQuot.CurveAffineCover C] [Work.SymQuot.CurveAffineCover (C.baseChange L)]
    (x : Fin n → Work.SpecLin.CurveFPt (C.baseChange L) F) :
    Work.BcDiv.ptsK (K := K) (L := L) (F := F) n
        (Work.SymQuot.Sym.powMap (C.baseChange L) n x)
      = Work.SymQuot.Sym.powMap C n
          (fun m => Work.BcDiv.bcPtK (K := K) (L := L) (F := F) (x m)) := by
  have hq : Work.SymQuot.Sym.powMap (C.baseChange L) n x ≫
        Work.SymQuot.BaseChange.symβ K L C n
      = Limits.Pi.lift x ≫ (Work.SymQuot.BaseChange.symPiIso K L C n).inv ≫
          (Over.pullback (Curve.specMap K L)).map (Work.SymQuot.Sym.quot C n) := by
    calc Work.SymQuot.Sym.powMap (C.baseChange L) n x ≫ Work.SymQuot.BaseChange.symβ K L C n
        = (Limits.Pi.lift x ≫ Work.SymQuot.Sym.quot (C.baseChange L) n) ≫
            Work.SymQuot.BaseChange.symβ K L C n := rfl
      _ = Limits.Pi.lift x ≫ (Work.SymQuot.Sym.quot (C.baseChange L) n ≫
            Work.SymQuot.BaseChange.symβ K L C n) := Category.assoc _ _ _
      _ = Limits.Pi.lift x ≫ Work.SymQuot.BaseChange.symfL K L C n :=
            congrArg _ (Work.SymQuot.BaseChange.symβ_spec K L C n)
      _ = Limits.Pi.lift x ≫ (Work.SymQuot.BaseChange.symPiIso K L C n).inv ≫
            (Over.pullback (Curve.specMap K L)).map (Work.SymQuot.Sym.quot C n) := rfl
  calc ptsK (K := K) (L := L) (F := F) n
        (Work.SymQuot.Sym.powMap (C.baseChange L) n x)
      = pbPtMap (Work.SymQuot.Sym C n)
          (Work.SymQuot.Sym.powMap (C.baseChange L) n x ≫
            Work.SymQuot.BaseChange.symβ K L C n) := rfl
    _ = pbPtMap (Work.SymQuot.Sym C n)
          (Limits.Pi.lift x ≫ (Work.SymQuot.BaseChange.symPiIso K L C n).inv ≫
            (Over.pullback (Curve.specMap K L)).map (Work.SymQuot.Sym.quot C n)) :=
          congrArg _ hq
    _ = Work.SymQuot.Sym.powMap C n (fun m => bcPtK (x m)) :=
          ((pbPtMap_comp_map (K := K) (L := L) (F := F)
              (Y := Work.SymQuot.prod C.toOver n) (Y' := Work.SymQuot.Sym C n)
              (u := Work.SymQuot.Sym.quot C n)
              (q := Limits.Pi.lift x ≫ (Work.SymQuot.BaseChange.symPiIso K L C n).inv)).symm.trans
            (congrArg (fun t => t ≫ Work.SymQuot.Sym.quot C n)
              (pbPtMap_piLift (K := K) (L := L) (F := F) (C := C) n x)))

end

end Work.BcDiv
