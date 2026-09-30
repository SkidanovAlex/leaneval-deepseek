import Mathlib
import Submission.Work.SymQuot.DivOf.Complete.RhoData
import Submission.Work.SymQuot.DivOf.Complete.idealOfDiv_ne_bot
import Submission.Work.SymQuot.DivOf.divMap_divOfChart
import Submission.Work.SymQuot.DivOf.Complete.divisorOfIdeal_idealOfDiv
import Submission.Work.SymQuot.DivOf.divisorOfIdeal_injective
import Submission.Work.SymQuot.DivOf.divisorOfIdeal_prod_placeIdeal
import Submission.Work.SymQuot.DivOf.divisorOfIdeal_map_bcSec
import Submission.Work.SymQuot.DivBaseInst

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.SymQuot.DivOf.Complete

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical
universe u

open Work.CurveBasics

open CategoryTheory Limits AlgebraicGeometry in
theorem divIdeal_map_bcSec_eq_prod_placeIdeal {K : Type u} [Field K]
    {C : Work.CurveBasics.Curve K} {n : ℕ} [NeZero n] [Work.SymQuot.CurveAffineCover C]
    {F : Type u} [Field F] [Algebra K F]
    {L : Type u} [Field L] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
    (D : Work.SpecLin.Dv C F) (hD : D.IsEffective)
    {V : C.left.Opens} [Nonempty V] (hV : IsAffineOpen V)
    (hsupp : ∀ z ∈ D.support, z.point ∈ C.bcOpens F V)
    (y : Fin n → Work.SpecLin.CurveFPt C L)
    (hy : Work.SpecLin.DivBase.bc (IsScalarTower.toAlgHom K F L) D =
      ∑ m, Work.SpecLin.ptDiv (y m))
    (hplace : ∀ m, (Work.SpecLin.ptPlace (y m)).point ∈ C.bcOpens L V) :
    (Work.SymQuot.DivOf.Complete.divIdeal (C := C) (F := F) V hV D hsupp).map
        (Work.SymQuot.DivOf.bcSec F L V) =
      ∏ m, Work.SymQuot.DivOf.placeIdeal (C.baseChange L) (C.bcOpens L V)
        (Work.SpecLin.ptPlace (y m)) (hplace m) := by
  classical
  haveI hDF : IsDedekindDomain Γ((C.baseChange F).left, C.bcOpens F V) :=
    isDedekindDomain_sections (C := C.baseChange F) (BaseChange.isAffineOpen_bcOpens F V hV)
  haveI hDL : IsDedekindDomain Γ((C.baseChange L).left, C.bcOpens L V) :=
    isDedekindDomain_sections (C := C.baseChange L) (BaseChange.isAffineOpen_bcOpens L V hV)
  -- the ideal of definition is nonzero
  have hJne : Work.SymQuot.DivOf.Complete.divIdeal (C := C) (F := F) V hV D hsupp ≠ ⊥ :=
    idealOfDiv_ne_bot (C := C.baseChange F) (V := C.bcOpens F V)
      (BaseChange.isAffineOpen_bcOpens F V hV) D hsupp
  -- the divisor of the ideal of definition is `D`
  have hzeroF : Work.SymQuot.DivOf.divisorOfIdeal (C.baseChange F) (C.bcOpens F V)
      (BaseChange.isAffineOpen_bcOpens F V hV)
      (Work.SymQuot.DivOf.Complete.divIdeal (C := C) (F := F) V hV D hsupp) = D :=
    divisorOfIdeal_idealOfDiv (C := C.baseChange F) (V := C.bcOpens F V)
      (BaseChange.isAffineOpen_bcOpens F V hV) hD hsupp
  -- the divisor of the product of the place ideals is the splitting of `D`
  have hzeroL : Work.SymQuot.DivOf.divisorOfIdeal (C.baseChange L) (C.bcOpens L V)
      (BaseChange.isAffineOpen_bcOpens L V hV)
      (∏ m, Work.SymQuot.DivOf.placeIdeal (C.baseChange L) (C.bcOpens L V)
        (Work.SpecLin.ptPlace (y m)) (hplace m)) =
      ∑ m, Work.SpecLin.ptDiv (y m) := by
    rw [Work.SymQuot.DivOf.divisorOfIdeal_prod_placeIdeal (C := C.baseChange L)
      (V := C.bcOpens L V) (BaseChange.isAffineOpen_bcOpens L V hV)
      (fun m => Work.SpecLin.ptPlace (y m)) hplace]
    simp only [Work.SpecLin.ptDiv]
  -- the divisors of the two ideals agree
  have hdiv : Work.SymQuot.DivOf.divisorOfIdeal (C.baseChange L) (C.bcOpens L V)
      (BaseChange.isAffineOpen_bcOpens L V hV)
      ((Work.SymQuot.DivOf.Complete.divIdeal (C := C) (F := F) V hV D hsupp).map
        (Work.SymQuot.DivOf.bcSec F L V)) =
      Work.SymQuot.DivOf.divisorOfIdeal (C.baseChange L) (C.bcOpens L V)
      (BaseChange.isAffineOpen_bcOpens L V hV)
      (∏ m, Work.SymQuot.DivOf.placeIdeal (C.baseChange L) (C.bcOpens L V)
        (Work.SpecLin.ptPlace (y m)) (hplace m)) := by
    rw [Work.SymQuot.DivOf.divisorOfIdeal_map_bcSec F L V hV
      (Work.SymQuot.DivOf.Complete.divIdeal (C := C) (F := F) V hV D hsupp) hJne,
      hzeroF, hzeroL]
    exact hy
  -- the product of the place ideals is nonzero
  have hJLne : (∏ m, Work.SymQuot.DivOf.placeIdeal (C.baseChange L) (C.bcOpens L V)
      (Work.SpecLin.ptPlace (y m)) (hplace m)) ≠ ⊥ :=
    finset_prod_ne_bot Finset.univ
      (fun m => Work.SymQuot.DivOf.placeIdeal (C.baseChange L) (C.bcOpens L V)
        (Work.SpecLin.ptPlace (y m)) (hplace m))
      (fun m _ => placeIdeal_ne_bot (BaseChange.isAffineOpen_bcOpens L V hV)
        (Work.SpecLin.ptPlace (y m)) (hplace m))
  -- and so is its extension
  have hmapne : ((Work.SymQuot.DivOf.Complete.divIdeal (C := C) (F := F) V hV D hsupp).map
      (Work.SymQuot.DivOf.bcSec F L V)) ≠ ⊥ := by
    intro hbot
    obtain ⟨b, hbJ, hb⟩ := (Submodule.ne_bot_iff _).mp hJne
    have hle := (Ideal.map_eq_bot_iff_le_ker
      (I := Work.SymQuot.DivOf.Complete.divIdeal (C := C) (F := F) V hV D hsupp)
      (Work.SymQuot.DivOf.bcSec F L V)).mp hbot
    exact Work.SymQuot.DivOf.bcSec_ne_zero F L V hb (RingHom.mem_ker.mp (hle hbJ))
  exact Work.SymQuot.DivOf.divisorOfIdeal_injective (C := C.baseChange L) (V := C.bcOpens L V)
    (BaseChange.isAffineOpen_bcOpens L V hV) hmapne hJLne hdiv

end Work.SymQuot.DivOf.Complete
