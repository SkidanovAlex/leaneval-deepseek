import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.CosetInvCountAPI
import Submission.Work.CORE3.BCountOneEqNcardJ
import Submission.Work.CORE3.FreeActionDvdJ

namespace Work.CORE3

namespace Work.CORE3

open Work.GW2

/-- Design pass 5 (`Submission/Work/_design_gw/Core5.lean`, B81 p. 224): `8 ∣ b₁`, because
`S` acts fixed-point-freely on the set `J₁` of involutions `y ∉ Ĥ` whose coset contains exactly
one involution.  (`hSetup` is used for `|S| = 8` and `S ≤ C(t) ≤ Ĥ`: if `y ∈ J₁` and `y^s = y`
for `1 ≠ s ∈ S`, then `s` and `t` commute with `y`, and for `s = t` this contradicts `y ∉ Ĥ`,
while for `s ≠ t` the commuting involutions `y, s` give a *second* involution of the coset
`yĤ`; `s` of order 4 has `s² = t`.) -/
theorem Case1bOne (I : Case1Inputs) (hSetup : Case1bSetupProp) (hCount : Case1bCountProp)
    (h89 : Case1bEightNineProp) : Case1bOneProp := by
  intro G _ _ hFT hBc B h1 h4
  -- `Ĥ`, `S`, `t` of Bender's notation, and the Case (1b) data `D`
  obtain ⟨D⟩ := hSetup G hFT hBc B h1 h4
  -- `S ≤ C(t) = H ≤ Ĥ`, so conjugation by `S` permutes the cosets of `Ĥ`
  have hSH : (B.S : Subgroup G) ≤ B.H := Work.CORE2A.bSetup_S_le_H B
  have hSHh : (B.S : Subgroup G) ≤ B.Hhat := le_trans hSH B.H_le_Hhat
  -- `S` is a `2`-subgroup containing the involution `t = B.t`
  have hS2 : IsPGroup 2 ↥(B.S : Subgroup G) := B.S.isPGroup'
  have htS : B.t ∈ (B.S : Subgroup G) := B.S0_le B.t_mem
  -- `b₁` counts the involutions `y ∉ Ĥ` whose coset contains exactly one involution ...
  rw [Work.CORE3.BCountOneEqNcardJ B.Hhat]
  -- ... and `S` acts freely on them, so `|S| = 8` divides their number
  rw [← D.S8]
  exact Work.CORE3.FreeActionDvdJ B.Hhat (B.S : Subgroup G) B.t hSHh hS2 htS B.t_order
    B.H_le_Hhat

end Work.CORE3

open Work.GW2

/-- The same statement, exposed under the name `Work.CORE3.Case1bOne` requested by the lead
(the module's main declaration sits in the doubly nested namespace `Work.CORE3.Work.CORE3`, as
in the sibling leaves `Case1bFalse`, `Case1bIndex`, …). -/
theorem Case1bOne (I : Case1Inputs) (hSetup : Case1bSetupProp) (hCount : Case1bCountProp)
    (h89 : Case1bEightNineProp) : Case1bOneProp :=
  _root_.Work.CORE3.Work.CORE3.Case1bOne I hSetup hCount h89

end Work.CORE3
