import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Serre.isEMSpace_of_homotopyEquiv
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.EMODD

set_option linter.style.haveILetI false

open scoped Topology

/-- **`IsEMSpaceUpTo` transports along a homotopy equivalence** (the range form of `Work.Serre.isEMSpace_of_homotopyEquiv`, which is the `IsEMSpace` statement). -/
theorem emSpaceTransport (A : Type) [AddCommGroup A] (m : ℕ) (hm : 0 < m) (N : ℕ)
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (e : ContinuousMap.HomotopyEquiv X Y) (hx : e x = y)
    (h : Work.Serre.IsEMSpaceUpTo A m hm N X x) : Work.Serre.IsEMSpaceUpTo A m hm N Y y := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  constructor
  · obtain ⟨iso⟩ := h.1
    obtain ⟨eiso⟩ := Work.Stems.mulEquiv_of_homotopyEquiv (N := Fin m) e x
    exact ⟨hx ▸ (eiso.symm.trans iso)⟩
  · intro i hi hc
    by_cases h0 : i = 0
    · -- `π₀`: transfer through `ZerothHomotopy`
      subst h0
      haveI : Subsingleton (HomotopyGroup (Fin 0) X x) := h.2 0 (by omega) (Or.inl hm)
      have hZx : Subsingleton (ZerothHomotopy X) :=
        ⟨fun a b => by
          have h1 := congrArg (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x))
            (Subsingleton.elim
              ((HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x)).symm a)
              ((HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x)).symm b))
          simpa using h1⟩
      have hZy : Subsingleton (ZerothHomotopy Y) :=
        Work.RatHurewicz.subsingleton_zerothHomotopy_of_homotopyEquiv e.symm hZx
      haveI : Subsingleton (ZerothHomotopy Y) := hZy
      exact ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy (X := Y) (x := y)).injective
        (Subsingleton.elim _ _)⟩
    · -- `π_i`, `i ≥ 1`: transfer through the homotopy equivalence
      haveI : Nonempty (Fin i) := ⟨⟨0, Nat.pos_of_ne_zero h0⟩⟩
      obtain ⟨eiso⟩ := Work.Stems.mulEquiv_of_homotopyEquiv (N := Fin i) e x
      haveI : Subsingleton (HomotopyGroup (Fin i) X x) := h.2 i hi hc
      exact hx ▸ ⟨fun a b => eiso.symm.injective
        (Subsingleton.elim (eiso.symm a) (eiso.symm b))⟩

end Work.Pi6.EMODD
