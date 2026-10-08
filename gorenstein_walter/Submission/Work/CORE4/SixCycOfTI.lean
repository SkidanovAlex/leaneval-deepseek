/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# Design-19 leaf `CY`: the TI property forces `F` cyclic

Bender §4 (6) (1981, p. 225): the witness `g ∈ N_G(K₁F) ∖ M` with `F^g ≤ K₁F` makes `F`
isomorphic to a subgroup of the cyclic quotient `(K₁F)/F` of the cyclic group `K₁`, hence cyclic.

Formally:
* `Work.CORE4.Case2Six9Aux.exists_witness_of_case2pre` (proved) produces `g ∉ M` with
  `F^g ≤ F(U) ⊓ M`;
* `Work.CORE4.IsCyclicFOfWitness` (proved, `Submission/Work/CORE4/IsCyclicFOfWitness.lean`)
  turns that witness plus the TI property into `IsCyclic D.F` (it is stated with the input bundle
  `I` and `BenderCtx G` so that Bender's (3) `F(U) ⊓ M = K₀ ⊔ F`, available as the proved
  `Work.CORE4.K0_sup_F_eq`, can be used).

So the whole leaf is the two-liner below.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs19
import Submission.Work.CORE4.Case2Six9Aux.exists_witness_of_case2pre
import Submission.Work.CORE4.IsCyclicFOfWitness

namespace Work.CORE4

/-- **Design-19 leaf `CY`** (`Work.GW2.C19.SixCycOfTIProp`): for `BenderCtx G`, `B : BenderSetup G`,
`D : Case2Data B` with `Case2Pre B D` and the TI property `∀ g ∉ D.M, D.F ⊓ F^g = ⊥`, the subgroup
`D.F` is cyclic.

Proof: Bender's witness `g ∉ M` with `F^g ≤ F(U) ⊓ M` (`exists_witness_of_case2pre`), then
`IsCyclicFOfWitness` with the TI property at that `g`. -/
theorem SixCycOfTI (I : Work.GW2.C4Inputs) : Work.GW2.C19.SixCycOfTIProp I := by
  intro G _ _ hbc B D hpre hTI
  obtain ⟨g, hgM, hwit⟩ := Work.CORE4.Case2Six9Aux.exists_witness_of_case2pre I hbc D hpre
  exact Work.CORE4.IsCyclicFOfWitness I hbc D hpre hgM hwit (hTI g hgM)

end Work.CORE4
