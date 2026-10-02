/-
# `ELAssembly` — the nest at `b₂`: from `ELNest.NestData` to `Work.ELRig.B2Data`

`Work.ELRig.B2Data hN z₁` is the bundle of the tripod at the branch point `b₂` (the three arms,
the rotation of the cut points by `F c`, the shrinking nest `Δ̂ₙ` and its cut points) that the
equator-leak argument consumes.  This file assembles it from the interface
`Work.ELNest.NestData c`, so that a caller only has to produce a `NestData` (and the single
dynamical input `b₂` is not postcritical).

Provenance of the fields:

* `b₂`, `b2_fix` — fields of `NestData` (`b2_fix` is itself derived there from the three tripod
  rays by `Work.ELNest.b2_fix_of_lands`);
* `tripod` — `Work.ELTop.tripodSides` (T8) applied to the three landings `b₂_lands`, `b₂_lands'`;
* `z1_mem_A`, `z0_notMem_clA`, `cut_mem`, `cut_unique` — `Work.ELNest.z1_mem_armA`,
  `Work.ELNest.z0_notMem_clA`, `Work.ELNest.cut_mem_A`, `Work.ELNest.cut_unique_A` together with
  the arm identifications `armOf_tripodSides_A/B/C` (`Arms.lean`) and the two missing arms
  (`Cut.lean`);
* `Δ`, `isOpen_Δ`, `b2_mem_Δ`, `Δ_shrinks` — `S.D`, `Work.ELNest.isOpen_D`, `S.b2_mem_D`,
  `Work.ELNest.Dnest_shrinks`;
* `rot_cut` — `Work.ELNest.rot_cut`.

`b2_not_postcrit` is the one input that is *not* produced by `ELNest`: it is the statement that
no iterate of the critical point hits `b₂` (the critical orbit converges to the parabolic point
`z₁ ≠ b₂`).  It enters as an explicit parameter here and is a named hypothesis of the assembly
bundle (`Work.ELAssembly.AssemblyInputs`).
-/
import Mathlib
import Submission.Work.ELAssembly.Arms
import Submission.Work.ELAssembly.Cut
import Submission.Work.ELNest.z1_mem_armA
import Submission.Work.ELNest.z0_notMem_clA
import Submission.Work.ELNest.rot_cut
import Submission.Work.ELNest.isOpen_D
import Submission.Work.ELNest.Dnest_shrinks

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELAssembly

variable {c : ℂ}

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- The cut point function of `Work.EL.B2Data`, from the three cut points of the `NestData`. -/
noncomputable def cutOf (S : Work.ELNest.NestData c) : Work.EL.ArmIdx → ℕ → ℂ
  | Work.EL.ArmIdx.A => S.cutA
  | Work.EL.ArmIdx.B => S.cutB
  | Work.EL.ArmIdx.C => S.cutC

@[simp] theorem cutOf_A (S : Work.ELNest.NestData c) (n : ℕ) :
    cutOf S Work.EL.ArmIdx.A n = S.cutA n := rfl

@[simp] theorem cutOf_B (S : Work.ELNest.NestData c) (n : ℕ) :
    cutOf S Work.EL.ArmIdx.B n = S.cutB n := rfl

@[simp] theorem cutOf_C (S : Work.ELNest.NestData c) (n : ℕ) :
    cutOf S Work.EL.ArmIdx.C n = S.cutC n := rfl

/-- **The tripod at `b₂`.**  From a `NestData` and the non-postcriticality of `b₂`, the bundle
`Work.ELRig.B2Data` that the equator-leak argument consumes. -/
noncomputable def toB2Data (S : Work.ELNest.NestData c) (hJ : Work.Top.JordanForm)
    (hpost : ∀ n : ℕ, (Tantibar c)^[n] 0 ≠ S.b2) :
    Work.EL.B2Data S.d.hN S.d.z₁ := by
  let T : Work.EL.TripodSides S.d.hN S.b2 :=
    Work.ELTop.tripodSides S.d.hN hJ S.b2_lands.1 S.b2_lands.2.1 S.b2_lands.2.2 S.b2_lands'
  have hA : Work.EL.armOf T Work.EL.ArmIdx.A = S.armA := by
    show Work.EL.armA S.d.hN S.b2 T.lands_a T.lands_b = S.armA
    exact armA_eq S
  have hB : Work.EL.armOf T Work.EL.ArmIdx.B = S.armB := by
    show Work.EL.armB S.d.hN S.b2 T.lands_b T.lands_c = S.armB
    exact armB_eq S
  have hC : Work.EL.armOf T Work.EL.ArmIdx.C = S.armC := by
    show Work.EL.armC S.d.hN S.b2 T.lands_c T.lands_a' = S.armC
    exact armC_eq S
  refine
    { b₂ := S.b2
      b2_fix := S.b2_fix
      b2_not_postcrit := hpost
      tripod := T
      z1_mem_A := ?_
      z0_notMem_clA := ?_
      Δ := S.D
      isOpen_Δ := Work.ELNest.isOpen_D S
      b2_mem_Δ := S.b2_mem_D
      Δ_shrinks := Work.ELNest.Dnest_shrinks S
      cut := cutOf S
      cut_mem := ?_
      cut_unique := ?_
      rot_cut := ?_ }
  · rw [hA]; exact Work.ELNest.z1_mem_armA S
  · rw [hA]; exact Work.ELNest.z0_notMem_clA S
  · intro Z n
    match Z with
    | Work.EL.ArmIdx.A =>
        rw [cutOf_A, hA]; exact Work.ELNest.cut_mem_A S n
    | Work.EL.ArmIdx.B =>
        rw [cutOf_B, hB]; exact cut_mem_B S n
    | Work.EL.ArmIdx.C =>
        rw [cutOf_C, hC]; exact cut_mem_C S n
  · intro Z n
    match Z with
    | Work.EL.ArmIdx.A =>
        rw [cutOf_A, hA]; exact Work.ELNest.cut_unique_A S n
    | Work.EL.ArmIdx.B =>
        rw [cutOf_B, hB]; exact cut_unique_B S n
    | Work.EL.ArmIdx.C =>
        rw [cutOf_C, hC]; exact cut_unique_C S n
  · obtain ⟨N, hN⟩ := Work.ELNest.rot_cut S
    refine ⟨N, fun Z n hn => ?_⟩
    match Z with
    | Work.EL.ArmIdx.A =>
        rw [cutOf_A]
        show Work.EL.F c (S.cutA n) ∈ Work.EL.armOf T Work.EL.ArmIdx.C
        rw [hC]; exact (hN n hn).1
    | Work.EL.ArmIdx.B =>
        rw [cutOf_B]
        show Work.EL.F c (S.cutB n) ∈ Work.EL.armOf T Work.EL.ArmIdx.A
        rw [hA]; exact (hN n hn).2.1
    | Work.EL.ArmIdx.C =>
        rw [cutOf_C]
        show Work.EL.F c (S.cutC n) ∈ Work.EL.armOf T Work.EL.ArmIdx.B
        rw [hB]; exact (hN n hn).2.2

end Work.ELAssembly
