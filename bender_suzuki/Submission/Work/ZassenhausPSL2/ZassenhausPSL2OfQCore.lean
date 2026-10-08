import Submission.Work.ZassenhausPSL2.Defs
import Submission.Work.ZassenhausPSL2.Basic
import Submission.Work.ZassenhausPSL2.ZData.card_Q_eq
import Submission.Work.ZassenhausPSL2.ZData.psl2_coords
import Submission.Work.ZassenhausPSL2.Model.psl2_datum
import Submission.Work.ZassenhausPSL2.Feit.card_excl
import Submission.Work.ZassenhausPSL2.FeitCln.card_excl_eq_one
import Submission.Work.RankOneUniqueness.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausPSL2.zassenhausPSL2` — the deliverable (design step `Z7`)

The chapter's endgame, in the lead's `Q`-only design (`NOTES_LEAD_bs_psl2core.md`):

* `F2b` (`Feit.card_excl`) and `F8` (`FeitCln.card_excl_eq_one`) give `|𝒮| · |D| = |Q| - 1` and
  `|𝒮| = 1`, hence `|Q| = |D| + 1` (`ZData.card_Q_eq`);
* `ZData.psl2_coords` coordinatises `Q` by `Multiplicative (GF(2ⁿ))`, `n ≥ 2`, in such a way
  that the Zassenhaus `f`-relation becomes `b ↦ b⁻¹ = psl2F n b`;
* `Model.psl2_datum` is the model datum of `PSL(2, 2ⁿ)` with the same `f`-map;
* `Work.RankOneUniqueness.recognize` (unconditional, via the delivered
  `rankOneQUniqueness`) turns a matched `(Q, f)` into `G ≃* PSL2Model n`.

All hypotheses of `ZassenhausPSL2Prop` enter here; nothing is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausPSL2

/-- **Area `ZassenhausPSL2`.** Abelian root group `Q` in a simple Zassenhaus group of split
rank one: `G ≅ PSL(2, 2ⁿ)` for some `n ≥ 2`. -/
theorem zassenhausPSL2 : Submission.Blueprint.ZassenhausPSL2Prop := by
  intro G _ _ hsimple H Q t hsplit hz h2 hab
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : IsSimpleGroup G := hsimple
  -- `F8`: `|𝒮| = 1`
  have hS : (Submission.Blueprint.excludingKernel H Q).card = 1 :=
    Work.ZassenhausPSL2.FeitCln.card_excl_eq_one hsplit hz h2 hab
  -- `F2b`: `|𝒮| · |D| = |Q| - 1`
  have hmul : (Submission.Blueprint.excludingKernel H Q).card *
      Nat.card (Submission.Blueprint.twoPoint H t) = Nat.card Q - 1 :=
    Work.ZassenhausPSL2.Feit.card_excl hsplit hz h2 hab
  -- `Z1'`: `|Q| = |D| + 1`
  have hcard : Nat.card Q = Nat.card (Submission.Blueprint.twoPoint H t) + 1 :=
    Work.ZassenhausPSL2.ZData.card_Q_eq hS hmul
  -- `Z6`: field coordinates making the `f`-relation `b ↦ b⁻¹`
  obtain ⟨n, hn, e, hf⟩ :=
    Work.ZassenhausPSL2.ZData.psl2_coords hsplit hz h2 hab hcard
  -- `M1`: the model datum of `PSL(2, 2ⁿ)`
  obtain ⟨M⟩ := Work.ZassenhausPSL2.Model.psl2_datum n hn
  -- recognition
  exact ⟨n, hn, Work.RankOneUniqueness.recognize Work.RankOneUniqueness.rankOneQUniqueness
    hsplit M e hf⟩

end Work.ZassenhausPSL2
