import Mathlib
import Submission.Work.BSIntegrate.Defs
import Submission.Work.FeitSibley.ThmGBridge.degreeProp_of_fsdata
import Submission.Work.ThmG.nilpotent_of_K_ne_one
import Submission.Work.ThmG.nilpotent_two_odd_split
import Submission.Work.ThmG.rankOne_isTI
import Submission.Work.ThreePoints.BenderPrelim

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSIntegrate

theorem degreeProp_prime (hC4 : Submission.Blueprint.ChIIFourProp) (hTh : Submission.Blueprint.ThompsonFrobeniusProp) (hFpf : Work.ThmG.FpfOddPartProp) (hCop : Work.ThmG.CoprimeDQProp) : Work.BSIntegrate.DegreeProp' := by
  intro G _ _ H Q t hh hnot2
  -- the split rank-one datum underlying `hh`
  have hsplit : Submission.Blueprint.IsSplitRankOne H Q t := hh.2.2.1
  -- `K = J(D,t) ≠ 1` (Ch. I §2), so Thompson's theorem gives that `Q` is nilpotent
  have hQnil : Group.IsNilpotent Q :=
    Work.ThmG.nilpotent_of_K_ne_one hh.1 hC4 hTh hsplit
      (Work.ThreePoints.kNeOneProp G H Q t hh)
  -- `Q` not a 2-group means `Q₁ = O_{2'}(Q) ≠ 1`
  have hQ1 : Work.ThmG.oddPart Q ≠ ⊥ :=
    (Work.ThmG.nilpotent_two_odd_split Q hQnil).2.2.2.2.2.2.2 hnot2
  -- assemble the Feit–Sibley hypotheses and apply App. XII (3)–(4)
  exact Work.FeitSibley.ThmGBridge.degreeProp_of_fsdata H Q t hh
    (Work.ThmG.rankOne_isTI hsplit)
    (hsplit.stronglyEmbedded.2.2 t hsplit.not_mem)
    hQnil hQ1 (hFpf G H Q t hh) (hCop G H Q t hh)

end Work.BSIntegrate
