import Mathlib
import Submission.Work.SymQuot.DivOf.Complete.RhoData
import Submission.Work.SymQuot.DivBaseInst

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.SymQuot.DivOf.Complete

open CategoryTheory Limits AlgebraicGeometry in
theorem ptPlace_mem_bcOpens_of_bc {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    {F : Type u} [Field F] [Algebra K F] {L : Type u} [Field L] [Algebra K L]
    [Algebra F L] [IsScalarTower K F L]
    (D : Work.SpecLin.Dv C F) {V : C.left.Opens} [Nonempty V]
    (hsupp : ∀ z ∈ D.support, z.point ∈ C.bcOpens F V)
    (y : Fin n → Work.SpecLin.CurveFPt C L)
    (hy : Work.SpecLin.DivBase.bc (IsScalarTower.toAlgHom K F L) D =
      ∑ m, Work.SpecLin.ptDiv (y m)) (m : Fin n) :
    (Work.SpecLin.ptPlace (y m)).point ∈ C.bcOpens L V := by
  classical
  -- `S` is the tower square `C_L ⟶ C_F`, whose projection `S.π` is `towerHom`.
  set S := Work.SymQuot.DivOf.bcSquareTower (C := C) F L with hS
  set Q : (C.baseChange L).Place := Work.SpecLin.ptPlace (y m) with hQ
  -- **Step 1.** `Q` lies in the support of `bc e D`: each `ptDiv (y k)` is effective with
  -- value `1` at `ptPlace (y k)`, so the sum `∑_k ptDiv (y k)` is `≥ 1 > 0` at `Q`.
  have hmem : Q ∈ (Work.SpecLin.DivBase.bc (IsScalarTower.toAlgHom K F L) D).support := by
    rw [hy, Finsupp.mem_support_iff]
    have hle : Work.SpecLin.ptDiv (y m) ≤ ∑ k, Work.SpecLin.ptDiv (y k) := by
      rw [Finsupp.le_def]
      intro W
      rw [Finsupp.finsetSum_apply]
      exact Finset.single_le_sum (fun k _ => Work.SpecLin.ptDiv_isEffective (y k) W)
        (Finset.mem_univ m)
    have h1 : (Work.SpecLin.ptDiv (y m)) Q = 1 := by
      rw [Work.SpecLin.ptDiv_apply]
      simp [hQ]
    have h2 : (1 : ℤ) ≤ (∑ k, Work.SpecLin.ptDiv (y k)) Q := by
      rw [← h1]; exact hle Q
    omega
  -- `bc e` is (definitionally) the `divMap` of the tower square.
  have hmem' : Q ∈ (S.divMap D).support := hmem
  -- **Step 2.** The coefficient of `S.divMap D` at `Q` is `e(Q/Q₀) · D(Q₀)` with `Q₀` the
  -- place below `Q`; as `Q` is in the support this coefficient is nonzero, hence `Q₀ ∈ D.support`.
  rw [Finsupp.mem_support_iff, Work.CurveBasics.Curve.BCSquare.divMap_apply,
      Work.CurveBasics.Curve.BCSquare.divMapCoeff] at hmem'
  have hcl : IsClosed ({S.π Q.point} : Set (C.baseChange F).left) := by
    by_contra h
    exact hmem' (by rw [dite_eq_right h])
  rw [dite_eq_left hcl] at hmem'
  have hD : D (S.under Q hcl) ≠ 0 := fun h0 => hmem' (by rw [h0, zero_mul])
  have hsup : S.under Q hcl ∈ D.support := Finsupp.mem_support_iff.mpr hD
  -- **Step 3.** `S.under Q hcl` lies in `C.bcOpens F V` by hypothesis; transporting along
  -- `towerHom ≫ baseChangeFst F = baseChangeFst L` (`towerHom_fst`) gives the claim.
  have hbc : (C.baseChangeFst F) (S.π Q.point) ∈ V := hsupp _ hsup
  show (C.baseChangeFst L) Q.point ∈ V
  have htf := Work.SymQuot.DivOf.BCSquareBaseChange.towerHom_fst (C := C) (F := F) (F' := L)
  have hfun : (C.baseChangeFst L) Q.point = (C.baseChangeFst F) (S.π Q.point) := by
    have h := congrArg (fun f => f Q.point) htf
    simp only at h
    exact h.symm
  rw [hfun]
  exact hbc

end Work.SymQuot.DivOf.Complete
