import Mathlib
import Submission.Work.Stems.mulEquiv_of_homotopyEquiv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `π₀` of a homotopy equivalence (an import-island-free copy)

The lemma `Work.ThomBordism.Grassmann.subsingleton_piZero_of_homotopyEquiv` is *used* by item 3,
but it is *declared* inside `Submission/Work/ThomBordism/Grassmann/cubedCover.lean`, whose imports
(through `uvHomotopyEquiv`) declare `Work.ThomBordism.Grassmann.Phi` — a name that clashes with
`Work.ThomBordism.Grassmann.CxModel.Phi` of the chapter's **item 2** chain, so `cubedCover` cannot
be imported together with `lowDegreeCohomology` (or with any part of the probe chain).

This module re-proves the lemma under a new name with no such imports, so that the item-3 chain
(`GoodCover/Main.lean`) and the item-2 chain (`lowDegreeCohomology`,
`lowDegreeVanishingAndRanks`) **can** be imported together.
-/

open scoped Topology

namespace Work.ThomBordism.Grassmann

noncomputable section

/-- **`π₀` of a space is trivial if `π₀` of a homotopy equivalent space is.**
(Copy of `Work.ThomBordism.Grassmann.subsingleton_piZero_of_homotopyEquiv`, declared in
`cubedCover.lean`, under a fresh name and without importing the cube-model chain.) -/
theorem subsingleton_piZero_of_homotopyEquiv' {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) {x : X}
    (h : Subsingleton (HomotopyGroup (Fin 0) Y (e.toFun x))) :
    Subsingleton (HomotopyGroup (Fin 0) X x) := by
  have hY : Subsingleton (ZerothHomotopy Y) := by
    haveI : Subsingleton (HomotopyGroup (Fin 0) Y (e.toFun x)) := h
    exact ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy (x := e.toFun x)).symm.injective
      (Subsingleton.elim _ _)⟩
  have key : ∀ x x' : X, Joined x x' := by
    intro x x'
    have h1 : ZerothHomotopy.mk (e x) = ZerothHomotopy.mk (e x') := Subsingleton.elim _ _
    have h2 : Joined (e x) (e x') := Quotient.exact h1
    have h3 : Joined (e.invFun (e x)) (e.invFun (e x')) := h2.map e.invFun.continuous
    obtain ⟨H⟩ := e.left_inv
    have h4 : Joined (e.invFun (e x)) x := ⟨H.evalAt x⟩
    have h5 : Joined (e.invFun (e x')) x' := ⟨H.evalAt x'⟩
    exact (h4.symm.trans h3).trans h5
  have hX : Subsingleton (ZerothHomotopy X) := ⟨fun a b => by
    induction a using ZerothHomotopy.rec with
    | mk x =>
      induction b using ZerothHomotopy.rec with
      | mk y => exact ZerothHomotopy.sound (key x y).somePath⟩
  haveI : Subsingleton (ZerothHomotopy X) := hX
  exact ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy (x := x)).injective
    (Subsingleton.elim _ _)⟩

end

end Work.ThomBordism.Grassmann
