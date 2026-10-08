import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.Basic
import Submission.Work.ThmF.ChV12.fpf_oddPart
import Submission.Work.ThmG.Defs
import Submission.Work.ThmG.nilpotent_of_K_ne_one
import Submission.Work.ThreePoints.BenderPrelim

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.fpfOddPartProp` — the exportable form of Ch. V §2 Lemma 2 (c)

The requested statement is `Work.ThmG.FpfOddPartProp` (field 4 of area `ThmG`'s
`RankOneStructure`), derived here from `FeitThompsonProp`, `ChIIFourProp` and
`ThompsonFrobeniusProp`:

```lean
def FpfOddPartProp : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (H Q : Subgroup G) (t : G),
    RankOneHyp G H Q t → ∀ d ∈ twoPoint H t, d ≠ 1 → ∀ x ∈ oddPart Q, d * x * d⁻¹ = x → x = 1
```

The mathematical content (`D = H ⊓ Hᵗ` acts fixed-point-freely on `Q₁ = O_{2'}(Q)`) is proved in
`Submission/Work/ThmF/ChV12/fpf_oddPart.lean` as `fpf_oddPart`, under the extra hypothesis
`Group.IsNilpotent ↥Q` of Ch. V §1 Prop. 1 b).  That nilpotency is a consequence of

* `Work.ThreePoints.kNeOneProp` (`K = J(D,t) ≠ 1`, Ch. I §2), and
* `Work.ThmG.nilpotent_of_K_ne_one` (Ch. V §1 Prop. 1 b): an element of `K#` of prime order acts
  fixed-point-freely on `Q` (Ch. II §4 Prop. 2 (c)), so Thompson's theorem on Frobenius kernels
  (`ThompsonFrobeniusProp`) makes `Q` nilpotent.

`RankOneHyp` supplies exactly `Situation G`, `IsSplitRankOne H Q t` and hypothesis (B3), which is
all that `fpf_oddPart` and the nilpotency step consume; `FeitThompsonProp` is part of the
interface but unused here.
-/

set_option linter.unusedVariables false

namespace Work.ThmF.ChV12

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF in theorem fpfOddPartProp (hFT : FeitThompsonProp) (hC4 : ChIIFourProp) (hTF : ThompsonFrobeniusProp) : Work.ThmG.FpfOddPartProp := by
  intro G _ _ H Q t hhyp
  -- Ch. I §2: `K = J(D,t) ≠ 1`, so Ch. V §1 Prop. 1 b) gives that `Q` is nilpotent.
  have hK : ∃ x ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t, x ≠ 1 :=
    Work.ThreePoints.kNeOneProp G H Q t hhyp
  obtain ⟨hSit, _hsimple, hsplit, _hnotZ, hB3⟩ := hhyp
  exact fpf_oddPart hSit hC4 H Q t hsplit hB3
    (Work.ThmG.nilpotent_of_K_ne_one hSit hC4 hTF hsplit hK)

end Work.ThmF.ChV12
