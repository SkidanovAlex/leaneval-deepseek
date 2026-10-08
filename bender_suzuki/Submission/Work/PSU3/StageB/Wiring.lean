import Mathlib
import Submission.Work.PSU3.StageB.Step1

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageB.Wiring` — shared bricks of the `centralizer_oddResidual_isPSU3_v2` assembly

Small, reusable facts that several of the assembly's pieces need.  Keeping them in their own module
(rather than in `Work.PSU3.StageB.centralizer_oddResidual_isPSU3_v2`, which holds the target) is
what makes the dependency graph acyclic: `Work.PSU3.StageB.card_centralizer_eq_cube` needs
`inf_center_centralizerOddResidual_eq_bot`, so it must import *this* module, not the target's.

Contents:

* `inf_center_centralizerOddResidual_eq_bot` — `S ⊓ Z(U) = ⊥` for a `2`-subgroup `S ≤ Q` given
  `Z(U) ≤ P`; this is the injectivity half of the map `S → U/Z(U)` used by
  `Work.PSU3.StageB.card_map_sylow_eq` (step 4, bookkeeping (i)).
-/

namespace Work.PSU3.StageB

open LeanEval.GroupTheory.Defs

/-- **Step 4, bookkeeping (i).**  For a `2`-subgroup `S ≤ Q` and `Z(U) ≤ P`, the intersection
`S ⊓ Z(U)` is trivial: `S ≤ Q` and `Z(U) ≤ P` while `P ⊓ Q ⊆ D ⊓ Q = ⊥`
(`hS.split.inf_eq`).  This is what makes the map `S → U/Z(U)` injective, so that the Sylow of
`F ⊓ H` and the corresponding unipotent radical of `Y = U/Z(U)` have the same order. -/
theorem inf_center_centralizerOddResidual_eq_bot {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t : G} (hS : Work.PSU3.PSU3Hyp H Q t) {P : Subgroup G}
    (hPV : P ≤ Submission.Blueprint.centD H t)
    (hZP : (Subgroup.center ↥(Work.PSU3.StageB.centralizerOddResidual P)).map
        (Work.PSU3.StageB.centralizerOddResidual P).subtype ≤ P)
    {S : Subgroup G} (hSQ : S ≤ Q) :
    S ⊓ (Subgroup.center ↥(Work.PSU3.StageB.centralizerOddResidual P)).map
        (Work.PSU3.StageB.centralizerOddResidual P).subtype = ⊥ := by
  have hP2 : P ≤ Submission.Blueprint.twoPoint H t :=
    fun y hy => (Subgroup.mem_inf.mp (hPV hy)).1
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxS, hxZ⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hxZ
  have hxP : x ∈ P := by
    rw [← hzx]
    exact hZP (Subgroup.mem_map_of_mem _ hz)
  have hxT : x ∈ Q ⊓ Submission.Blueprint.twoPoint H t := ⟨hSQ hxS, hP2 hxP⟩
  rw [hS.split.inf_eq] at hxT
  simpa using hxT

end Work.PSU3.StageB
