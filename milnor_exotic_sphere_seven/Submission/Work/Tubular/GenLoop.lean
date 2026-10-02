import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

/-!
# Cube loops and composition

Mathlib models the `n`-th homotopy group of a based space as `GenLoop (Fin n) X x`, the continuous
maps of the cube `I^n` which are constant at `x` on `∂I^n`.  This file records the elementary fact
that a **based** continuous map of spaces sends the cube loops of the source to the cube loops of the
target; it is used by `Work.Tubular.Interface` (the collapse) and by `Work.Tubular.Gauss` (the
Gauss map and `α_V`).

It is a separate module so that the consumers can use it without pulling in the whole `Interface`
module (and hence the Pontryagin–Thom chapter).
-/

open scoped unitInterval

namespace Work.Tubular

/-- A continuous map of based spaces sends the cube loops of the source to the cube loops of the
target: `GenLoop` is Mathlib's cube model of the `n`-th homotopy group. -/
theorem genLoop_comp {n : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (j : C(X, Y)) (hj : j x = y) {g : C(Fin n → unitInterval, X)}
    (hg : g ∈ GenLoop (Fin n) X x) : j.comp g ∈ GenLoop (Fin n) Y y := by
  intro t ht
  rw [ContinuousMap.comp_apply, hg t ht, hj]

end Work.Tubular
