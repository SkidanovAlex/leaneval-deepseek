import Mathlib
import Submission.Work.Stems.mulEquiv_of_homotopyEquiv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Triviality of homotopy groups transfers along a homotopy equivalence

A homotopy equivalence `e : X ≃ Y` induces an isomorphism `π_N X x ≃* π_N Y (e x)`
(`Work.Stems.mulEquiv_of_homotopyEquiv`), so `π_N X x` is a subsingleton exactly when
`π_N Y (e x)` is.  This is the form in which the connectivity of the pieces of the cofibre
(`↥(cofibreU ι) ≃ E` by `Work.RatHurewicz.cofibreUHomotopyEquiv`, and the collar
`↥(cofibreU ι ∩ cofibreV ι) ≃ F` by `Work.RatHurewicz.collarHomotopyEquiv`) is consumed.
-/

namespace Work.RatHurewicz

/-- **Triviality of `π_N` transfers along a homotopy equivalence.** -/
theorem subsingleton_homotopyGroup_of_homotopyEquiv {N : Type*} {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [DecidableEq N] [Nonempty N]
    (e : ContinuousMap.HomotopyEquiv X Y) (x : X) :
    Subsingleton (HomotopyGroup N X x) ↔ Subsingleton (HomotopyGroup N Y (e.toFun x)) := by
  obtain ⟨φ⟩ := Work.Stems.mulEquiv_of_homotopyEquiv (N := N) e x
  constructor
  · intro h
    exact ⟨fun a b => φ.symm.injective (h.elim (φ.symm a) (φ.symm b))⟩
  · intro h
    exact ⟨fun a b => φ.injective (h.elim (φ a) (φ b))⟩

end Work.RatHurewicz
