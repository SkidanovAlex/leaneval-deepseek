/-
# EL nest, part 4: the two consumption bundles

The two structures `Work.ELRig.Z1Nest` and `Work.ELRig.B2Data` of the ELRig area consist of data
plus the geometric facts proved in this area.  For a caller's convenience these two bundles
collect, in one statement each, exactly the *facts* (as opposed to the data) of those structures,
with the mapping
* `Z1Nest.shrinks ← Qnest_shrinks`, `Z1Nest.SP ← sidePreserve`, `Z1Nest.shift ← Qp_shift`,
  `Z1Nest.z1_near_Q`, `Z1Nest.Q_ne_z1`, `Z1Nest.base_shift`, `Z1Nest.Pa_far` are fields;
* `B2Data.Δ_shrinks ← Dnest_shrinks`, `isOpen_Δ ← isOpen_D`, `b2_mem_Δ`, `cut_mem`,
  `cut_unique ← cut_mem_A`, `cut_unique_A`, `rot_cut`, `z1_mem_A ← z1_mem_armA`,
  `z0_notMem_clA ← z0_notMem_clA`.
-/
import Mathlib
import Submission.Work.ELNest.Qnest_shrinks
import Submission.Work.ELNest.Dnest_shrinks
import Submission.Work.ELNest.cut_mem_A
import Submission.Work.ELNest.cut_unique_A
import Submission.Work.ELNest.rot_cut
import Submission.Work.ELNest.z0_notMem_clA
import Submission.Work.ELNest.z1_mem_armA
import Submission.Work.ELNest.isOpen_D
import Submission.Work.ELNest.arms_basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Topology Function
open scoped Topology ComplexConjugate

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELNest

open Work.EL

variable {c : ℂ}

/-- **The facts of `Z1Nest`** (the nest at the parabolic point `z₁`), for a given `NestData`. -/
theorem Z1_facts (S : NestData c) :
    (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ K c, z ∈ pairSideNear (S.Qp n) →
        z ∈ pairSideNear S.P0 → ‖z - S.d.z₁‖ < ε) ∧
    (∃ ρ > 0, ∀ z ∈ Metric.ball S.d.z₁ ρ, z ∉ pairCurve S.P0 →
        (z ∈ pairSide S.P0 ↔ F c z ∈ pairSide S.P0)) ∧
    (∀ n : ℕ, F c ((S.Qp (n + 1)).y) = (S.Qp n).y) ∧
    (∀ n : ℕ, S.d.z₁ ∈ pairSideNear (S.Qp n)) ∧
    (∀ n : ℕ, (S.Qp n).y ≠ S.d.z₁) ∧
    F c ((S.Qp 0).y) = (LeanEval.ComplexAnalysis.Tantibar c)^[4] S.d.z₁ ∧
    S.fl.Pa ⊆ pairSide S.P0 :=
  ⟨Qnest_shrinks S, sidePreserve S, Qp_shift S, S.z1_near_Q, S.Qne, S.base_shift, S.Pa_far⟩

/-- **The facts of `B2Data`** (the nest at the branch point `b₂`). -/
theorem B2_facts (S : NestData c) :
    (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, S.D n ⊆ Metric.ball S.b2 ε) ∧
    (∀ n : ℕ, IsOpen (S.D n)) ∧
    (∀ n : ℕ, S.b2 ∈ S.D n) ∧
    (∀ n : ℕ, S.cutA n ∈ S.armA ∩ K c ∩ frontier (S.D n)) ∧
    (∀ n : ℕ, frontier (S.D n) ∩ K c ∩ S.armA = {S.cutA n}) ∧
    (∃ N : ℕ, ∀ n ≥ N, F c (S.cutA n) ∈ S.armC ∧ F c (S.cutB n) ∈ S.armA ∧
      F c (S.cutC n) ∈ S.armB) ∧
    S.d.z₁ ∈ S.armA ∧
    (LeanEval.ComplexAnalysis.Tantibar c)^[4] S.d.z₁ ∉ closure S.armA ∧
    (IsOpen S.armA ∧ IsOpen S.armB ∧ IsOpen S.armC ∧
      Disjoint S.armA S.armB ∧ Disjoint S.armB S.armC ∧ Disjoint S.armC S.armA ∧
      S.armA ∪ S.armB ∪ S.armC = (Work.EL.Tripod.curve S.tripod)ᶜ) :=
  ⟨Dnest_shrinks S, isOpen_D S, S.b2_mem_D, cut_mem_A S, cut_unique_A S, rot_cut S,
   z1_mem_armA S, z0_notMem_clA S, arms_basic S⟩

end Work.ELNest
