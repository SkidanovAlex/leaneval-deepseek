import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Subsingleton` of the zeroth homotopy is a homotopy invariant

`ZerothHomotopy X` is the quotient of `X` by the relation "joined by a path".  A homotopy
equivalence `e : X ≃ₕ Y` need not be a bijection, but it does induce a bijection on path components:
if `Y` has at most one path component, so does `X`.  This is the `k = 0` case of the basepoint
change for the relative homotopy groups (`Subsingleton (HomotopyGroup (Fin 0) X x)` is
`Subsingleton (ZerothHomotopy X)`).
-/

open scoped Topology

namespace Work.RatHurewicz

/-- Homotopy equivalent spaces have `Subsingleton` zeroth homotopy simultaneously (here: the
forward direction). -/
theorem subsingleton_zerothHomotopy_of_homotopyEquiv {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y)
    (h : Subsingleton (ZerothHomotopy Y)) : Subsingleton (ZerothHomotopy X) := by
  have key : ∀ x x' : X, Joined x x' := by
    intro x x'
    have h1 : ZerothHomotopy.mk (e x) = ZerothHomotopy.mk (e x') := Subsingleton.elim _ _
    have h2 : Joined (e x) (e x') := Quotient.exact h1
    have h3 : Joined (e.invFun (e x)) (e.invFun (e x')) := h2.map e.invFun.continuous
    obtain ⟨H⟩ := e.left_inv
    have h4 : Joined (e.invFun (e x)) x := ⟨H.evalAt x⟩
    have h5 : Joined (e.invFun (e x')) x' := ⟨H.evalAt x'⟩
    exact (h4.symm.trans h3).trans h5
  refine ⟨fun a b => ?_⟩
  induction a using ZerothHomotopy.rec with
  | mk x =>
    induction b using ZerothHomotopy.rec with
    | mk y => exact ZerothHomotopy.sound (key x y).somePath

end Work.RatHurewicz
