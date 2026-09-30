/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area BcDiv, B5: the comparison of symmetric powers `Symⁿ(C_L) ⟶ Symⁿ C` and its field points

For `K → L → F` and a curve `C` over `K`, area SY's comparison isomorphism
`symBaseChangeIso : Symⁿ(C_L) ≅ (Symⁿ C)_L` (`Submission/Work/SymQuot/BaseChange/
exists_symBaseChangeIso.lean`) gives, on underlying schemes, a morphism

  `βK n : Symⁿ(C_L) ⟶ Symⁿ C`,

and on `F`-points (where `F` is an `L`-algebra as well as, compatibly, a `K`-algebra) a
bijection `ptsK n`: the `K`-structure is obtained by the pullback-point equivalence
`Work.BcDiv.pbPtEquiv`.

## Main definitions

* `Work.BcDiv.βK` — the projection of the comparison of symmetric powers;
* `Work.BcDiv.ptsK` — the induced bijection on field points.

## Main results

* `Work.BcDiv.ptsK_left` — `ptsK` is composition with `βK`.
-/
import Submission.Work.BcDiv.Basic
import Submission.Work.BcDiv.PbPt
import Submission.Work.SymQuot.Sym
import Submission.Work.SymQuot.BaseChange.exists_symBaseChangeIso

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

universe u

namespace Work.BcDiv

noncomputable section

variable {K : Type u} [Field K] {C : Curve K} {L : Type u} [Field L] [Algebra K L]
  {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F]

/-- **The comparison of symmetric powers on underlying schemes**: the projection
`Symⁿ(C_L) ⟶ Symⁿ C`, obtained from area SY's isomorphism
`SymQuot.BaseChange.symBaseChangeIso` by composing with the pullback projection. -/
def βK (n : ℕ) [SymQuot.CurveAffineCover C] [SymQuot.CurveAffineCover (C.baseChange L)] :
    (SymQuot.Sym (C.baseChange L) n).left ⟶ (SymQuot.Sym C n).left :=
  (SymQuot.BaseChange.symβ K L C n).left ≫ pullback.fst (SymQuot.Sym C n).hom (Curve.specMap K L)

/-- **The induced bijection on field points** `Symⁿ(C_L)(F) ≃ Symⁿ C(F)`: a point of the base
change over `L` is the same thing as a point over `K` (via `Work.BcDiv.pbPtEquiv`), and these two
are identified along area SY's comparison isomorphism. -/
def ptsK (n : ℕ) [SymQuot.CurveAffineCover C] [SymQuot.CurveAffineCover (C.baseChange L)] :
    Work.SpecLin.FPt (SymQuot.Sym (C.baseChange L) n) F ≃
      Work.SpecLin.FPt (SymQuot.Sym C n) F where
  toFun p := pbPtEquiv (K := K) (L := L) (F := F) (Y := SymQuot.Sym C n)
    (p ≫ (SymQuot.BaseChange.symBaseChangeIso K L C n).hom)
  invFun q := (pbPtEquiv (K := K) (L := L) (F := F) (Y := SymQuot.Sym C n)).symm q
    ≫ (SymQuot.BaseChange.symBaseChangeIso K L C n).inv
  left_inv p := by
    show (pbPtEquiv (K := K) (L := L) (F := F)
        (Y := SymQuot.Sym C n)).symm
          (pbPtEquiv (K := K) (L := L) (F := F) (Y := SymQuot.Sym C n)
            (p ≫ (SymQuot.BaseChange.symBaseChangeIso K L C n).hom))
        ≫ (SymQuot.BaseChange.symBaseChangeIso K L C n).inv = p
    rw [Equiv.symm_apply_apply, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  right_inv q := by
    show pbPtEquiv (K := K) (L := L) (F := F) (Y := SymQuot.Sym C n)
        (((pbPtEquiv (K := K) (L := L) (F := F)
            (Y := SymQuot.Sym C n)).symm q
          ≫ (SymQuot.BaseChange.symBaseChangeIso K L C n).inv)
        ≫ (SymQuot.BaseChange.symBaseChangeIso K L C n).hom) = q
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Equiv.apply_symm_apply]

/-- `ptsK` is composition with `βK` on underlying schemes. -/
theorem ptsK_left (n : ℕ) [SymQuot.CurveAffineCover C]
    [SymQuot.CurveAffineCover (C.baseChange L)]
    (p : Work.SpecLin.FPt (SymQuot.Sym (C.baseChange L) n) F) :
    (ptsK (K := K) (L := L) (F := F) n p).left = p.left ≫ βK (K := K) (L := L) (C := C) n :=
  rfl

end

end Work.BcDiv
