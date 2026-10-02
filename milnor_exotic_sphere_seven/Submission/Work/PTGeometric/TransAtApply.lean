import Submission.Work.PTGeometric.GenuineTransversality

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the block formula of `GenLoop.transAt`

`GenLoop.transAt i f g` is Mathlib's model of the product in `π_N(X, x)`
(`HomotopyGroup.mul_spec : ⟦f⟧ * ⟦g⟧ = ⟦transAt i g f⟧`), so the *concatenation* of the pieces'
collapse loops is the iterated `transAt`, and its homotopy class is the product of the pieces' classes.
For the geometric half of Pontryagin–Thom one must know **where** the concatenation agrees with which
factor — the "block formula" — because the zero set of the concatenation is the union of the
(copies of the) factors' zero sets: the `j`-th block of the cube carries the `j`-th piece's collapse
map, reparametrised in the `i`-th coordinate.

Mathlib defines `transAt i f g` by `GenLoop.copy` of the explicit map
`t ↦ if (t i : ℝ) ≤ 1/2 then f (update t i (2 t i)) else g (update t i (2 t i - 1))`, so the formula
is `rfl` after unfolding `GenLoop.copy`; this file records it (and the two halves), since the block
information is what downstream geometric arguments need.

## Main results

* `Work.PTGeometric.genLoop_transAt_apply` — the `if`-form
* `Work.PTGeometric.genLoop_transAt_apply_of_le` / `_of_gt` — the two branches
* `Work.PTGeometric.genLoop_transAt_mem_iff_of_le` / `_of_gt` — the preimage, block by block
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Topology unitInterval
open Function Set

namespace Work.PTGeometric

noncomputable section

/-- **The block formula of `transAt`.**  Concatenation along the coordinate `i` reads the first
factor on the half `t i ≤ 1/2` and the second factor on the other half, each with the `i`-th
coordinate reparametrised by `x ↦ 2x` resp. `x ↦ 2x - 1`. -/
theorem genLoop_transAt_apply {N : Type*} [DecidableEq N] {X : Type} [TopologicalSpace X] {x : X}
    (i : N) (f g : GenLoop N X x) (t : N → Set.Icc (0 : ℝ) 1) :
    GenLoop.transAt i f g t =
      if ((t i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2
      then f (Function.update t i (Set.projIcc (0 : ℝ) 1 (by norm_num) (2 * (t i : ℝ))))
      else g (Function.update t i (Set.projIcc (0 : ℝ) 1 (by norm_num) (2 * (t i : ℝ) - 1))) := by
  show GenLoop.copy _ _ _ t = _
  rw [GenLoop.coe_copy]

/-- The first block of the concatenation. -/
theorem genLoop_transAt_apply_of_le {N : Type*} [DecidableEq N] {X : Type} [TopologicalSpace X]
    {x : X} (i : N) (f g : GenLoop N X x) {t : N → Set.Icc (0 : ℝ) 1}
    (h : ((t i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2) :
    GenLoop.transAt i f g t =
      f (Function.update t i (Set.projIcc (0 : ℝ) 1 (by norm_num) (2 * (t i : ℝ)))) := by
  rw [genLoop_transAt_apply, if_pos h]

/-- The second block of the concatenation. -/
theorem genLoop_transAt_apply_of_gt {N : Type*} [DecidableEq N] {X : Type} [TopologicalSpace X]
    {x : X} (i : N) (f g : GenLoop N X x) {t : N → Set.Icc (0 : ℝ) 1}
    (h : ¬ (((t i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2)) :
    GenLoop.transAt i f g t =
      g (Function.update t i (Set.projIcc (0 : ℝ) 1 (by norm_num) (2 * (t i : ℝ) - 1))) := by
  rw [genLoop_transAt_apply, if_neg h]

/-- **The preimage of a set under the concatenation, in the first block**: a cube point of the first
half is in the preimage exactly when the reparametrised point is in the first factor's preimage. -/
theorem genLoop_transAt_mem_iff_of_le {N : Type*} [DecidableEq N] {X : Type} [TopologicalSpace X]
    {x : X} (i : N) (f g : GenLoop N X x) {t : N → Set.Icc (0 : ℝ) 1} (S : Set X)
    (h : ((t i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2) :
    GenLoop.transAt i f g t ∈ S ↔
      f (Function.update t i (Set.projIcc (0 : ℝ) 1 (by norm_num) (2 * (t i : ℝ)))) ∈ S := by
  rw [genLoop_transAt_apply_of_le i f g h]

/-- **The preimage of a set under the concatenation, in the second block**. -/
theorem genLoop_transAt_mem_iff_of_gt {N : Type*} [DecidableEq N] {X : Type} [TopologicalSpace X]
    {x : X} (i : N) (f g : GenLoop N X x) {t : N → Set.Icc (0 : ℝ) 1} (S : Set X)
    (h : ¬ (((t i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2)) :
    GenLoop.transAt i f g t ∈ S ↔
      g (Function.update t i (Set.projIcc (0 : ℝ) 1 (by norm_num) (2 * (t i : ℝ) - 1))) ∈ S := by
  rw [genLoop_transAt_apply_of_gt i f g h]

/-- **The preimage of a set under the concatenation is the union of the two blocks.**  This is the
form in which the zero set of a concatenation (e.g. of the pieces' collapse maps) is computed: on the
first half of the cube it is the preimage under the first factor at the reparametrised point, on the
second half the same for the second factor. -/
theorem genLoop_transAt_preimage {N : Type*} [DecidableEq N] {X : Type} [TopologicalSpace X]
    {x : X} (i : N) (f g : GenLoop N X x) (S : Set X) :
    GenLoop.transAt i f g ⁻¹' S =
      {t : N → Set.Icc (0 : ℝ) 1 |
          ((t i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2 ∧
          f (Function.update t i (Set.projIcc (0 : ℝ) 1 (by norm_num) (2 * (t i : ℝ)))) ∈ S} ∪
      {t : N → Set.Icc (0 : ℝ) 1 |
          1 / 2 < ((t i : Set.Icc (0 : ℝ) 1) : ℝ) ∧
          g (Function.update t i (Set.projIcc (0 : ℝ) 1 (by norm_num)
            (2 * (t i : ℝ) - 1))) ∈ S} := by
  ext t
  rw [Set.mem_preimage, Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq, genLoop_transAt_apply]
  by_cases h : ((t i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2
  · rw [if_pos h]
    exact ⟨fun hs => Or.inl ⟨h, hs⟩, fun ho => ho.elim (fun hh => hh.2)
      (fun hh => absurd h (not_le.mpr hh.1))⟩
  · rw [if_neg h]
    exact ⟨fun hs => Or.inr ⟨lt_of_not_ge h, hs⟩, fun ho => ho.elim
      (fun hh => absurd hh.1 (not_le.mpr (lt_of_not_ge h))) (fun hh => hh.2)⟩

end

end Work.PTGeometric
