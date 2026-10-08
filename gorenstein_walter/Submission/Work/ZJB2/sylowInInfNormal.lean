import Mathlib
import Submission.Work.ZJB2.Defs
import Submission.Work.ZJB2.Step1.sylowInInfNormal

/-!
# G2 — `Work.ZJB2.sylowInInfNormal`

`Work.ZJB.SylowInInfNormalProp p G` (see `Submission/Work/ZJB2/Defs.lean`) is the leaf

  a Sylow `p`-subgroup `T` of `M` meets a subgroup `L` with `L ≤ M` and `M ≤ N_G(L)`
  in a Sylow `p`-subgroup `T ⊓ L` of `L`.

The mathematical content is proved (unfolded, over a universe-polymorphic ambient group) in
`Submission/Work/ZJB2/Step1/sylowInInfNormal.lean` as `Work.ZJB2.Step1.sylowInInfNormal`.
Here we merely package it as the `Prop` `SylowInInfNormalProp`, which is the same statement
with the three subgroup quantifiers moved out.
-/

namespace Work.ZJB2

open Work.ZJB

/-- **G2.** A Sylow subgroup of `M` meets a normal subgroup `L` of `M` in a Sylow subgroup
of `L`.  Immediate from `Work.ZJB2.Step1.sylowInInfNormal`. -/
theorem sylowInInfNormal (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] :
    Work.ZJB.SylowInInfNormalProp p G := by
  intro T M L hT hLM hML
  exact Step1.sylowInInfNormal hT hLM hML

end Work.ZJB2
