import Mathlib
import Submission.Work.Stems.Pi

/-!
# `HomotopyGroup.map` is a monoid homomorphism

`Submission.Work.Stems.Pi` defines, for a continuous map `f : C(X, Y)`, the induced map
`HomotopyGroup.map f : HomotopyGroup N X x → HomotopyGroup N Y (f x)` on the homotopy groups,
together with its functoriality (`map_id`, `map_comp`).  This file supplies the remaining
structural fact: `HomotopyGroup.map f` is a monoid (in fact group) homomorphism.

The content is `HomotopyGroup.mapHom f`, the *monoid homomorphism* whose underlying function is
`HomotopyGroup.map f`; this is stated for an arbitrary continuous map `f`, with no hypotheses on
`X`, `Y` or `f` beyond continuity (in particular no projection/section assumption).  It records
exactly the existential statement of `Work.Stems.mapHom`.

The mechanism: the multiplication on `HomotopyGroup N X x` is, by `HomotopyGroup.mul_spec`,
represented by the concatenation `GenLoop.transAt i` of generalized loops in a fixed coordinate
`i`.  Postcomposition with `f` commutes with `GenLoop.transAt` (`mapLoop_transAt`) because
`transAt` is given by an explicit `if … then … else …` formula in which `f` may be pushed to the
branches (`apply_ite`); one representative-level calculation therefore gives multiplicativity.
-/

open scoped Topology Topology.Homotopy unitInterval
open ContinuousMap

namespace HomotopyGroup

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The generalized loop obtained by postcomposing a generalized loop with a continuous map.
This is the loop-level map underlying `HomotopyGroup.map`. -/
def mapLoop {x : X} (f : C(X, Y)) (p : ↑(Ω^ N X x)) : ↑(Ω^ N Y (f x)) :=
  ⟨f.comp p.1, fun y hy => by rw [ContinuousMap.comp_apply, p.2 y hy]⟩

@[simp]
theorem mapLoop_apply {x : X} (f : C(X, Y)) (p : ↑(Ω^ N X x)) (t : N → I) :
    mapLoop f p t = f (p t) := rfl

/-- The defining computation rule of `HomotopyGroup.map`, phrased with `mapLoop`. -/
theorem map_mk_mapLoop {x : X} (f : C(X, Y)) (p : ↑(Ω^ N X x)) :
    map f ⟦p⟧ = ⟦mapLoop f p⟧ := rfl

/-- Postcomposition with `f` commutes with concatenation of loops. -/
theorem mapLoop_transAt {x : X} [DecidableEq N] (f : C(X, Y)) (i : N)
    (p q : ↑(Ω^ N X x)) :
    GenLoop.Homotopic (mapLoop f (GenLoop.transAt i p q))
      (GenLoop.transAt i (mapLoop f p) (mapLoop f q)) := by
  have h : mapLoop f (GenLoop.transAt i p q) = GenLoop.transAt i (mapLoop f p) (mapLoop f q) := by
    ext t
    simp only [mapLoop_apply, GenLoop.transAt, GenLoop.coe_copy]
    apply apply_ite f
  exact h ▸ GenLoop.Homotopic.refl _

/-- `HomotopyGroup.map f`, promoted to a monoid homomorphism.  Stated for an arbitrary continuous
map `f`; there are no additional hypotheses. -/
def mapHom {x : X} [DecidableEq N] [Nonempty N] (f : C(X, Y)) :
    HomotopyGroup N X x →* HomotopyGroup N Y (f x) where
  toFun := map f
  map_one' := by
    rw [HomotopyGroup.one_def, map_mk_mapLoop, HomotopyGroup.one_def]
    apply Quotient.sound
    have h : mapLoop f (GenLoop.const : ↑(Ω^ N X x)) =
        (GenLoop.const : ↑(Ω^ N Y (f x))) := by
      ext t; rfl
    exact h ▸ GenLoop.Homotopic.refl _
  map_mul' := by
    intro a b
    induction a using Quotient.inductionOn with
    | h p =>
      induction b using Quotient.inductionOn with
      | h q =>
        simp only [HomotopyGroup.mul_spec (i := Classical.arbitrary N), map_mk_mapLoop]
        apply Quotient.sound
        exact mapLoop_transAt f (Classical.arbitrary N) q p

@[simp]
theorem mapHom_apply {x : X} [DecidableEq N] [Nonempty N] (f : C(X, Y))
    (a : HomotopyGroup N X x) :
    mapHom f a = map f a := rfl

end HomotopyGroup
