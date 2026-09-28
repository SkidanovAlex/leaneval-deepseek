import Mathlib
import Submission.Work.Serre.Models
import Submission.Work.Serre.CWModel.Tower
import Submission.Work.Stems.subsingleton_of_contractible
import Submission.Work.RatHurewicz.attachCells_piMap_bijective
import Submission.Work.RatHurewicz.killFamily_subsingleton
import Submission.Work.Serre.attachIncl_piMap_bijective_of_compress
import Submission.Work.Serre.CWModel.killSub
import Submission.Work.Serre.CWModel.sphereExtend
import Submission.Work.Serre.CWModel.Descent
import Submission.Work.Serre.piMapN_monoidHom
import Submission.Work.StemsB.PiMap
import Submission.Work.RatHurewicz.SimplyConnectedBridge

/-!
# The comparison of two range models of `K(A,k)`: the invariant of the construction

This file fixes the vocabulary of the construction used in
`Submission/Work/StemsB/rangeModel_ratH_iso.lean`.  The degree is written `m + 1` throughout (so
`k = m + 1`), which makes the group structure on `HomotopyGroup (Fin (m+1))` available without any
`Nonempty (Fin ·)` bookkeeping.

Given two range models `Z` and `P` of `K(A, m+1)` through degree `N`, the proof builds, along the CW
model tower `Work.Serre.CWModel.towerA Z z₀ (m+1) …` (which maps a cell complex into `Z` and is a
`π`-isomorphism in degrees `≤ N`), a *second* structure map into `P`, and a comparison isomorphism
`Λ : π_{m+1}(Z, g y₀) ≃* π_{m+1}(P, p₀)` through which the two maps agree on `π_{m+1}`
(`Work.StemsB.SecondMapInv`).  That is all that is needed: for `i ≠ m+1`, `i ≤ N` both `π_i`'s are
trivial, and at `i = m+1` the relation plus the bijectivity of the first map makes the second one
bijective.
-/

namespace Work.StemsB

open CategoryTheory CategoryTheory.Limits
open scoped Topology Topology.Homotopy unitInterval

noncomputable section

variable {A : Type} [AddCommGroup A] {m N : ℕ} {Z : Type} [TopologicalSpace Z] {z₀ : Z}
  {P : Type} [TopologicalSpace P] {p₀ : P}

/-- **The invariant of the second structure map** (at degree `m+1`).

`g : C(Y,Z)` is the structure map of the tower (with `g y₀ = z₀`) and `c : C(Y,P)` is the second
map; the invariant says that `c y₀ = p₀`, that `π_{m+1}(c)` and `π_{m+1}(g)` have the *same kernel*
(this is what lets the killing cells be extended along `c`), and that `π_{m+1}(c)` is *surjective*
(this, together with the equality of kernels and the bijectivity of `π_{m+1}(g)`, makes `π_{m+1}(c)`
an isomorphism at the end). -/
def SecondMapInv {Y : Type*} [TopologicalSpace Y] (y₀ : Y) (g : C(Y, Z)) (c : C(Y, P)) : Prop :=
  c y₀ = p₀ ∧
    (∀ x : HomotopyGroup (Fin (m + 1)) Y y₀,
      Work.Serre.piMapN g (m + 1) y₀ x = 1 ↔ Work.Serre.piMapN c (m + 1) y₀ x = 1) ∧
    Function.Surjective (Work.Serre.piMapN c (m + 1) y₀)


/-- The tower over `Z`, at level `m - 1 + t`. -/
def rmTower (hm : 1 ≤ m) (hZ : Work.Serre.IsEMSpaceUpTo A (m + 1) (by omega) N Z z₀) (t : ℕ) :
    Work.Serre.CWModel.StA Z z₀ (m - 1 + t) :=
  Work.Serre.CWModel.towerA Z z₀ (m + 1) (by omega)
    (fun i hi => hZ.2 i (by omega) (Or.inl hi)) t

theorem rmTower_zero (hm : 1 ≤ m) (hZ : Work.Serre.IsEMSpaceUpTo A (m + 1) (by omega) N Z z₀) :
    rmTower (Z := Z) (z₀ := z₀) (m := m) hm hZ 0
      = Work.Serre.CWModel.baseState Z z₀ (m + 1) (by omega)
          (fun i hi => hZ.2 i (by omega) (Or.inl hi)) := rfl

theorem rmTower_succ (hm : 1 ≤ m) (hZ : Work.Serre.IsEMSpaceUpTo A (m + 1) (by omega) N Z z₀)
    (t : ℕ) :
    rmTower (Z := Z) (z₀ := z₀) (m := m) hm hZ (t + 1)
      = Work.Serre.CWModel.killStep
          (Work.Serre.CWModel.genStep (rmTower (Z := Z) (z₀ := z₀) (m := m) hm hZ t)) := rfl

/-- The path connectedness of `Z` from the range model hypothesis. -/
theorem pathConnected_Z (hm : 1 ≤ m) (hZ : Work.Serre.IsEMSpaceUpTo A (m + 1) (by omega) N Z z₀) :
    PathConnectedSpace Z :=
  Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero z₀
    (hZ.2 0 (by omega) (Or.inl (by omega)))

theorem pathConnected_P (hm : 1 ≤ m) (hP : Work.Serre.IsEMSpaceUpTo A (m + 1) (by omega) N P p₀) :
    PathConnectedSpace P :=
  Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero p₀
    (hP.2 0 (by omega) (Or.inl (by omega)))

end

end Work.StemsB

