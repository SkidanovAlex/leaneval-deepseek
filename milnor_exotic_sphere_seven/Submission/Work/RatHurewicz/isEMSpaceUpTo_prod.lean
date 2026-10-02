import Mathlib
import Submission.Work.Serre.Models
import Submission.Work.Stems.isEMSpace_prod
import Submission.Work.Stems.homotopyGroup_prod

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Products of range models of Eilenberg–MacLane spaces

`Work.Serre.IsEMSpaceUpTo A m hm N X pt` is the *range model* notion: `π_m(X) ≃* A` and
`π_i(X) = 0` for every `i ≠ m` with `i < m` or `i ≤ N`.  The free part of the range-model
computation of `K(ℤ^r ⊕ F, k)` realises the coefficient group as a *product* of models
(`Work.Stems.prod_acyclic_ratH_vanishing` computes the rational homology of the product), so the
product of two range models must itself be a range model — that is the statement of this file.

`Work.Stems.isEMSpace_prod` proves the same for the genuine notion `Work.Serre.IsEMSpace`; the
proof here is the same one, with the extra cases produced by the range in the vanishing clause.
-/

open CategoryTheory Limits

namespace Work.RatHurewicz

noncomputable section

/-- **The product of two range models is a range model.**  If `X` is a range model of `K(A,k)` and
`Y` of `K(B,k)` (both through degree `N`), then `X × Y` is a range model of `K(A × B, k)` through
degree `N`. -/
theorem isEMSpaceUpTo_prod {A B : Type} [AddCommGroup A] [AddCommGroup B] {k N : ℕ}
    (hk : 0 < k) {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (pt : X) (qt : Y)
    (hA : Work.Serre.IsEMSpaceUpTo A k hk N X pt)
    (hB : Work.Serre.IsEMSpaceUpTo B k hk N Y qt) :
    Work.Serre.IsEMSpaceUpTo (A × B) k hk N (X × Y) (pt, qt) := by
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  constructor
  · -- the isomorphism on `π_k`
    obtain ⟨isoX⟩ := hA.1
    obtain ⟨isoY⟩ := hB.1
    obtain ⟨eprod⟩ := Work.Stems.homotopyGroup_prod (N := Fin k) pt qt
    exact ⟨eprod.trans ((isoX.prodCongr isoY).trans
      (MulEquiv.prodMultiplicative (G := A) (H := B)).symm)⟩
  · intro i hi hcase
    by_cases h0 : i = 0
    · -- `π₀` is not a group: go through the path components
      subst h0
      haveI : Subsingleton (HomotopyGroup (Fin 0) X pt) := hA.2 0 (by omega) (Or.inl hk)
      haveI : Subsingleton (HomotopyGroup (Fin 0) Y qt) := hB.2 0 (by omega) (Or.inl hk)
      have hZx : Subsingleton (ZerothHomotopy X) :=
        ⟨fun a b => by
          have h1 := congrArg (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := pt))
            (Subsingleton.elim
              ((HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := pt)).symm a)
              ((HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := pt)).symm b))
          simpa using h1⟩
      have hZy : Subsingleton (ZerothHomotopy Y) :=
        ⟨fun a b => by
          have h1 := congrArg (HomotopyGroup.pi0EquivZerothHomotopy (X := Y) (x := qt))
            (Subsingleton.elim
              ((HomotopyGroup.pi0EquivZerothHomotopy (X := Y) (x := qt)).symm a)
              ((HomotopyGroup.pi0EquivZerothHomotopy (X := Y) (x := qt)).symm b))
          simpa using h1⟩
      haveI : PathConnectedSpace X :=
        pathConnectedSpace_iff_zerothHomotopy.mpr ⟨⟨ZerothHomotopy.mk pt⟩, hZx⟩
      haveI : PathConnectedSpace Y :=
        pathConnectedSpace_iff_zerothHomotopy.mpr ⟨⟨ZerothHomotopy.mk qt⟩, hZy⟩
      have hprod : Subsingleton (ZerothHomotopy (X × Y)) := inferInstance
      exact Equiv.subsingleton (HomotopyGroup.pi0EquivZerothHomotopy (X := X × Y) (x := (pt, qt)))
    · -- `i ≥ 1`: the product formula for homotopy groups applies
      haveI : Nonempty (Fin i) := ⟨⟨0, Nat.pos_of_ne_zero h0⟩⟩
      obtain ⟨eprod⟩ := Work.Stems.homotopyGroup_prod (N := Fin i) pt qt
      haveI hx : Subsingleton (HomotopyGroup (Fin i) X pt) := hA.2 i hi hcase
      haveI hy : Subsingleton (HomotopyGroup (Fin i) Y qt) := hB.2 i hi hcase
      refine ⟨fun a b => ?_⟩
      have h1 : eprod a = eprod b := by
        refine Prod.ext ?_ ?_
        · exact Subsingleton.elim _ _
        · exact Subsingleton.elim _ _
      exact eprod.injective h1

end

end Work.RatHurewicz
