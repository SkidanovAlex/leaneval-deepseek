import Mathlib
import Submission.Work.PiS.Interfaces
import Submission.Work.Serre.serreK2Int
import Submission.Work.ThomBordism.finiteGoodCoverHomology
import Submission.Work.RatHurewicz.ConnectivityBridge

/-!
# EMFG — basic finiteness transfer for integral homology

The `FGUpTo` vocabulary of `Work.PiS` (`H_i(X;ℤ)` finitely generated for `i ≤ N`) with its basic
transport principles:

* monotonicity in the range;
* `H_0` of a path connected space;
* transfer along an isomorphism of integral homology in one degree;
* transfer along a homeomorphism and along a homotopy equivalence
  (`Work.Serre.isIso_intHomologyMap_of_homotopyEquiv`);
* a contractible space has finitely generated homology in every degree
  (`Work.ThomBordism.fgch_moduleFinite_homology_of_contractibleOrEmpty`).
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace Work.EMFG

noncomputable section

/-- Monotonicity of `FGUpTo` in the range. -/
theorem FGUpTo.mono {X : Type} [TopologicalSpace X] {N N' : ℕ} (h : Work.PiS.FGUpTo X N)
    (hNN' : N' ≤ N) : Work.PiS.FGUpTo X N' :=
  fun i hi => h i (le_trans hi hNN')

/-- `H_0` of a path connected space is finitely generated. -/
theorem fgUpTo_zero_of_pathConnected (X : Type) [TopologicalSpace X] [PathConnectedSpace X] :
    Work.PiS.FGUpTo X 0 := by
  intro i hi
  interval_cases i
  haveI : Fintype (ZerothHomotopy (TopCat.of X)) :=
    Fintype.ofFinite (ZerothHomotopy (TopCat.of X))
  exact Work.ThomBordism.fgch_moduleFinite_homology_zero_of_fintype

/-- Transfer of finite generation along an isomorphism of integral homology in one degree. -/
theorem fg_of_homology_iso {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {i : ℕ}
    (e : Work.PiS.HZ X i ≅ Work.PiS.HZ Y i) (h : Module.Finite ℤ (Work.PiS.HZ X i)) :
    Module.Finite ℤ (Work.PiS.HZ Y i) :=
  Module.Finite.equiv e.toLinearEquiv

set_option backward.isDefEq.respectTransparency false in
/-- A homeomorphism induces isomorphisms of integral homology in every degree, hence transfers
`FGUpTo`. -/
theorem fgUpTo_of_homeomorph {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    {N : ℕ} (h : Work.PiS.FGUpTo X N) : Work.PiS.FGUpTo Y N := by
  intro i hi
  haveI : IsIso (Work.Serre.intHomologyMap (e.toHomotopyEquiv.toFun) i) :=
    Work.Serre.isIso_intHomologyMap_of_homotopyEquiv e.toHomotopyEquiv i
  refine fg_of_homology_iso (asIso (Work.Serre.intHomologyMap e.toHomotopyEquiv.toFun i)) ?_
  exact h i hi

/-- Homotopy equivalent spaces have the same `FGUpTo`. -/
theorem fgUpTo_of_homotopyEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) {N : ℕ} (h : Work.PiS.FGUpTo X N) :
    Work.PiS.FGUpTo Y N := by
  intro i hi
  haveI : IsIso (Work.Serre.intHomologyMap (e.toFun) i) :=
    Work.Serre.isIso_intHomologyMap_of_homotopyEquiv e i
  refine fg_of_homology_iso (asIso (Work.Serre.intHomologyMap e.toFun i)) ?_
  exact h i hi

/-- A contractible space has finitely generated integral homology in every degree. -/
theorem fgUpTo_of_contractible (X : Type) [TopologicalSpace X] [ContractibleSpace X] (N : ℕ) :
    Work.PiS.FGUpTo X N :=
  fun i _ => Work.ThomBordism.fgch_moduleFinite_homology_of_contractibleOrEmpty X
    (fun _ => inferInstance) i

end

end Work.EMFG
