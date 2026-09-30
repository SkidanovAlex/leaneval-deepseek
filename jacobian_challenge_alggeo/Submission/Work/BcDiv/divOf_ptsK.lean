import Mathlib
import Submission.Work.BcDiv.SymPts
import Submission.Work.BcDiv.Points
import Submission.Work.BcDiv.PbPt
import Submission.Work.BcDiv.Tower
import Submission.Work.BcDiv.bcDiv_bc
import Submission.Work.BcDiv.bcDiv_ptDiv
import Submission.Work.BcDiv.powMap_betaK
import Submission.Work.BcDiv.ptsK_map
import Submission.Work.BcDiv.ramIdx_cmp
import Submission.Work.SymQuot.DivOf.divOf_map
import Submission.Work.SymQuot.DivOf.divOf_powMap
import Submission.Work.SymQuot.DivOf.divMap_injective
import Submission.Work.SymQuot.Sym.exists_finite_lift

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option linter.style.haveILetI false

namespace Work.BcDiv

universe u

/-- **B6: `divOf` is compatible with the divisor identification `bcDiv`.** The divisor of a point
`p` of `Symⁿ(C_L)` over `F` corresponds, under the identification `Work.BcDiv.bcDiv` of the
divisor groups of `(C_L)_F` and `C_F`, to the divisor of the image point `Work.BcDiv.ptsK n p` of
`Symⁿ C`.  This is the compatibility of the point/divisor dictionary of area SY with the
base-change comparison.

Proof route (the assistants `Work.BcDiv.bcDiv_ptDiv`, `Work.BcDiv.powMap_betaK`,
`Work.BcDiv.ptsK_map`, `Work.BcDiv.bcDiv_bc` are already available in the sibling files of this
area; `Work.BcDiv.compAlgebra`, `Work.BcDiv.isScalarTower_compAlgebra` and
`Work.BcDiv.isScalarTower_compAlgebra_tower` in `Submission/Work/BcDiv/Tower.lean` provide the
`K`-algebra structure on a field extension of `F` and its compatibility conditions):
1. `SymQuot.Sym.exists_finite_lift (C.baseChange L) n p` produces a finite extension `F'` of `F`
   over `L` (`FiniteDimensional F F'`, `Algebra L F'`, `Algebra F F'`,
   `IsScalarTower L F F'`) and `x : Fin n → CurveFPt (C_L) F'` with
   `Sym.powMap (C_L) n x = RPt.map (IsScalarTower.toAlgHom L F F') p`.  View `F'` as a
   `K`-algebra via `Work.BcDiv.compAlgebra K L F'`, so that the two structure maps
   `IsScalarTower.toAlgHom L F F'` and `IsScalarTower.toAlgHom K F F'` agree up to
   `AlgHom.restrictScalars`.
2. Over `F'`, `divOf F' (ptsK n (RPt.map _ p)) = divOf F' (powMap C n (fun m => bcPtK (x m)))`
   by `Work.BcDiv.powMap_betaK` combined with `Work.BcDiv.ptsK_map`; this is
   `∑ m, ptDiv (bcPtK (x m))` by `Work.SymQuot.DivOf.divOf_powMap`.
3. `bcDiv` of the left-hand side over `F'` equals the same sum:
   `bcDiv (divOf F' (RPt.map _ p)) = bcDiv (∑ m, ptDiv (x m))` by
   `Work.SymQuot.DivOf.divOf_powMap`, and `bcDiv (∑ m, ptDiv (x m)) = ∑ m, ptDiv (bcPtK (x m))`
   by `Work.BcDiv.bcDiv_ptDiv`.
4. Both sides of the goal, base changed along `e' := IsScalarTower.toAlgHom K F F'`, are equal:
   the left by `Work.BcDiv.bcDiv_bc` together with `Work.SymQuot.DivOf.divOf_map`, the right by
   `Work.SymQuot.DivOf.divOf_map` together with `Work.BcDiv.ptsK_map`.  Since the base change is
   injective (`Work.SymQuot.DivOf.divMap_injective` applied to the tower square
   `bcSquareTower F F'`, whose `Algebra F F'` structure is `e'.toRingHom.toAlgebra`), the two
   divisors over `F` are equal.

Namespace `Work.BcDiv`; file `Submission/Work/BcDiv/divOf_ptsK.lean`. -/
theorem divOf_ptsK {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {L : Type u} [Field L]
    [Algebra K L] {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
    (n : ℕ) [NeZero n] [Work.SymQuot.CurveAffineCover C]
    [Work.SymQuot.CurveAffineCover (C.baseChange L)]
    (p : Work.SpecLin.FPt (Work.SymQuot.Sym (C.baseChange L) n) F) :
    Work.BcDiv.bcDiv (Work.SymQuot.DivOf.divOf F p)
      = Work.SymQuot.DivOf.divOf F (Work.BcDiv.ptsK (K := K) (L := L) (F := F) n p) := by
  classical
  -- A finite extension `F'` of `F` over which `p` splits into `n` points of `C_L`.
  obtain ⟨F', hField, hAlgL, hAlgF, hTower, _hFin, x, hx⟩ :=
    Work.SymQuot.Sym.exists_finite_lift (C.baseChange L) n p
  letI : Field F' := hField
  letI : Algebra L F' := hAlgL
  letI : Algebra F F' := hAlgF
  letI : IsScalarTower L F F' := hTower
  -- the `K`-algebra structure on `F'`: the composite `K → L → F'`
  letI : Algebra K F' := Work.BcDiv.compAlgebra K L F'
  haveI : IsScalarTower K L F' := Work.BcDiv.isScalarTower_compAlgebra K L F'
  haveI : IsScalarTower K F F' :=
    Work.BcDiv.isScalarTower_compAlgebra_tower (K := K) (L := L) (F := F) (F' := F')
      (fun _ => rfl)
  -- the two structure maps `F → F'`, over `L` and over `K`
  let e₁ : F →ₐ[L] F' := IsScalarTower.toAlgHom L F F'
  let e' : F →ₐ[K] F' := IsScalarTower.toAlgHom K F F'
  have he₁K : AlgHom.restrictScalars K e₁ = e' := rfl
  have hx₁ : Work.SpecLin.RPt.map e₁ p = Work.SymQuot.Sym.powMap (C.baseChange L) n x := hx.symm
  -- Step 3: `bcDiv` of the left-hand side over `F'` is the sum of the divisors of the `x m`.
  have hL : Work.SpecLin.DivBase.bc e₁ (Work.SymQuot.DivOf.divOf F p)
      = ∑ m, Work.SpecLin.ptDiv (x m) := by
    rw [← Work.SymQuot.DivOf.divOf_map (C := C.baseChange L) (n := n) (e := e₁) p, hx₁]
    exact Work.SymQuot.DivOf.divOf_powMap x
  -- Step 2: likewise for the right-hand side, using `ptsK_map` and `powMap_betaK`.
  have hR : Work.SpecLin.DivBase.bc e'
        (Work.SymQuot.DivOf.divOf F (Work.BcDiv.ptsK (K := K) (L := L) (F := F) n p))
      = ∑ m, Work.SpecLin.ptDiv (Work.BcDiv.bcPtK (x m)) := by
    rw [← Work.SymQuot.DivOf.divOf_map (C := C) (n := n) (e := e')
      (Work.BcDiv.ptsK (K := K) (L := L) (F := F) n p)]
    rw [← he₁K, ← Work.BcDiv.ptsK_map (C := C) (e := e₁) n p, hx₁,
      Work.BcDiv.powMap_betaK (K := K) (L := L) (F := F') n x]
    exact Work.SymQuot.DivOf.divOf_powMap (fun m => Work.BcDiv.bcPtK (x m))
  -- Step 4: the two base changes along `e'` agree.
  have key : Work.SpecLin.DivBase.bc e' (Work.BcDiv.bcDiv (Work.SymQuot.DivOf.divOf F p))
      = Work.SpecLin.DivBase.bc e'
          (Work.SymQuot.DivOf.divOf F (Work.BcDiv.ptsK (K := K) (L := L) (F := F) n p)) := by
    have hbc := Work.BcDiv.bcDiv_bc (C := C) (L := L) (F := F) (F' := F') e₁
      (Work.SymQuot.DivOf.divOf F p)
    rw [he₁K] at hbc
    rw [← hbc, hL, hR, map_sum]
    exact Finset.sum_congr rfl (fun m _ => Work.BcDiv.bcDiv_ptDiv (x m))
  -- the base change is the pullback along the tower square `C_{F'} ⟶ C_F`, which is injective.
  letI : Algebra F F' := e'.toRingHom.toAlgebra
  haveI : IsScalarTower K F F' := Work.SymQuot.isScalarTower_of_algHom e'
  exact Work.SymQuot.DivOf.divMap_injective (Work.SymQuot.DivOf.bcSquareTower (C := C) F F') key

end Work.BcDiv
