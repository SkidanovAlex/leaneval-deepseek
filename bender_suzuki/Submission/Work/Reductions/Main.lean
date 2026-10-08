import Mathlib
import Submission.Blueprint.Interfaces
import Submission.Work.Reductions.Defs
import Submission.Work.Reductions.OddResidual
import Submission.Work.Reductions.Quotient
import Submission.Work.Reductions.Cases
import Submission.Work.Reductions.SimpleCase
import Submission.Work.Reductions.stronglyEmbedded_normalizer_eq
import Submission.Work.Reductions.stronglyEmbedded_normalizer_le
import Submission.Work.Reductions.stronglyEmbedded_centralizer_le
import Submission.Work.Reductions.stronglyEmbedded_index_odd
import Submission.Work.Reductions.stronglyEmbedded_conj
import Submission.Work.Reductions.stronglyEmbedded_exists_conj_mem
import Submission.Work.Reductions.stronglyEmbedded_eq_of_mem_conj
import Submission.Work.Reductions.stronglyEmbedded_subgroupOf
import Submission.Work.Reductions.stronglyEmbedded_involutions_conj
import Submission.Work.Reductions.hasFourGroup_quotient
import Submission.Work.Reductions.isSimpleGroup_of_oddCore_eq_bot
import Submission.Work.Reductions.isPretransitive_of_involutions
import Submission.Work.Reductions.transfer_twoTransitive
import Submission.Work.Reductions.odd_index_of_sup_eq_top

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `Reductions`: the deliverable

`Work.Reductions.reductions : Submission.Blueprint.ReductionsProp`, from
`FeitThompsonProp` and `ThmAProp`.

The three cases are `benderConclusion_of_oddCore_ne_bot` (apply the induction hypothesis to
`G ⧸ O(G)` and lift), `benderConclusion_of_oddResidual_ne_top` (apply it to `O^{2'}(G)`, which
contains every involution and is idempotent) and `simple_and_benderConclusion_of_top`
(`G` is simple and `L = ⊤` works).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.Blueprint
open LeanEval.GroupTheory.Defs

namespace Work.Reductions

/-- **Area `Reductions`.** The elementary reductions of Theorem B (Peterfalvi I Ch. II §4,
Ch. I §6 Cor. 3, and II Ch. VI §3). -/
theorem reductions (hFT : FeitThompsonProp) (hA : ThmAProp) : ReductionsProp := by
  intro G _ _ hB hBelow
  obtain ⟨hfour, H, hH⟩ := hB
  refine ⟨?_, ?_⟩
  · intro h
    by_cases hne : oddCore G = ⊥
    · have hr : oddResidual G ≠ ⊤ := by
        rcases h with h1 | h2
        · exact absurd hne h1
        · exact h2
      exact benderConclusion_of_oddResidual_ne_top hFT hA hfour hH hBelow hne hr
    · exact benderConclusion_of_oddCore_ne_bot hFT hfour hH hBelow hne
  · intro hc hr
    exact simple_and_benderConclusion_of_top hFT hA hfour hH hc hr

end Work.Reductions
