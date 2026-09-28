import Submission.Work.Serre.Models
import Submission.Work.Stems.mulEquiv_of_homotopyEquiv
import Submission.Work.RatHurewicz.subsingleton_zerothHomotopy_of_homotopyEquiv

/-!
# `K(A,m)` is a homotopy invariant

The property "`X` is a model of `K(A,m)`" (`Work.Serre.IsEMSpace`) only involves the homotopy
groups of `X`, so it is preserved by homotopy equivalences (with matching base points).  The two
ingredients are the workspace's `Work.Stems.mulEquiv_of_homotopyEquiv` (the `π_i`-transfer for
`i ≥ 1`) and `Work.RatHurewicz.subsingleton_zerothHomotopy_of_homotopyEquiv` (`π₀`).
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.Serre

noncomputable section

theorem isEMSpace_of_homotopyEquiv {A : Type} [AddCommGroup A] {m : ℕ} (hm : 0 < m) {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (e : ContinuousMap.HomotopyEquiv X Y) (hx : e x = y) (h : IsEMSpace A m hm X x) :
    IsEMSpace A m hm Y y := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  constructor
  · obtain ⟨iso⟩ := h.1
    obtain ⟨eiso⟩ := Work.Stems.mulEquiv_of_homotopyEquiv (N := Fin m) e x
    exact ⟨hx ▸ (eiso.symm.trans iso)⟩
  · intro i hi
    by_cases h0 : i = 0
    · -- `π₀`: transfer through `ZerothHomotopy`
      subst h0
      haveI : Subsingleton (HomotopyGroup (Fin 0) X x) := h.2 0 (by omega)
      have hZ : Subsingleton (ZerothHomotopy X) :=
        ⟨fun a b => by
          have h1 := congrArg (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x))
            (Subsingleton.elim
              ((HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x)).symm a)
              ((HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x)).symm b))
          simpa using h1⟩
      have hY : Subsingleton (ZerothHomotopy Y) :=
        Work.RatHurewicz.subsingleton_zerothHomotopy_of_homotopyEquiv e.symm hZ
      haveI : Subsingleton (ZerothHomotopy Y) := hY
      exact ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy (X := Y) (x := y)).injective
        (Subsingleton.elim _ _)⟩
    · -- `π_i`, `i ≥ 1`: transfer through the homotopy equivalence
      haveI : Nonempty (Fin i) := ⟨⟨0, Nat.pos_of_ne_zero h0⟩⟩
      obtain ⟨eiso⟩ := Work.Stems.mulEquiv_of_homotopyEquiv (N := Fin i) e x
      haveI : Subsingleton (HomotopyGroup (Fin i) X x) := h.2 i hi
      have hsub : Subsingleton (HomotopyGroup (Fin i) Y (e x)) :=
        ⟨fun a b => by
          have h1 : eiso (eiso.symm a) = eiso (eiso.symm b) :=
            congrArg eiso (Subsingleton.elim (eiso.symm a) (eiso.symm b))
          simpa using h1⟩
      exact hx ▸ hsub

end

end Work.Serre
