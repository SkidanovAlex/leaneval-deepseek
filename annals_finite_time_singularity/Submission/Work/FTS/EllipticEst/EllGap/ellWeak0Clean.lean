import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.TT.weakGradBound2
import Submission.Work.FTS.EllipticEst.TT.weakAngularTermClean
import Submission.Work.FTS.EllipticEst.TT.weakIPMems
import Submission.Work.FTS.EllipticEst.H2W.AeWAux.aeI4Of
import Submission.Work.FTS.EllipticEst.H2W.AeWAux.i4SliceIneq
import Submission.Work.FTS.EllipticEst.remov.AeStep1FullHolds
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.Prop.Level0

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.EllGap

/-- The level-`0` (`η`-weighted) elliptic estimate `TT.EllWeak0` (Elgindi, `prop:L2` + Steps 1-2 of
`prop:H2`). Pure copying job: see `Submission/Work/FTS/EllipticEst/EllGap/NOTES_ellWeak0Clean.md`
for the complete recipe (which declarations to copy from which file, and the three arity fixes
needed because `TT.EllWeakPos` gained a tenth field `memZPth2`). Nothing new has to be proved.

The copy has in fact already been made in the tree, under the `Prop` namespace, in exactly the
`TT.EllWeakPos`-flavoured class the recipe asks for (so the forbidden `AeData` route of
`Prop/ellWeak0Clean.lean` is *not* used):

* `Submission/Work/FTS/EllipticEst/Prop/l2etaL0Asm.lean` — `Prop.L0.l2eta_weak_of_pieces`, the
  assembly of the level-`0` estimate from the four analytic pieces (verbatim copy of
  `TT.l2eta_weak_of_pieces`, the original module being over the build guard's per-file size
  limit), already carrying the tenth `memZPth2` hypothesis in its curried conclusion;
* `Prop.l0_first` (`Prop/l0_first.lean`, via the arity-fixed bridge `Prop.aeData_of_ellWeakPos`),
  `Prop.l0_grad` (`Prop/l0_grad.lean`) and `Prop.l0_second` (`Prop/l0_second.lean`, from
  `Prop.i1_bare_hh` — the copy of `TT.target_of_mixedHon`'s `I₁` coercivity, which consumes
  precisely the tenth field `EllWeakPos.memZPth2`) — the three analytic inputs;
* `TT.weakAngularTermClean` — the (already clean) angular term.

`Prop.level0` (`Prop/Level0.lean`) is their assembly into the exact statement below, and
`#print axioms` reports `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).  Since the
statement of `Prop.level0` is *syntactically identical* to the one requested here, its proof is
re-exported rather than reproduced line by line. -/
theorem ellWeak0Clean : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllWeak0 C :=
  Work.FTS.EllipticEst.Prop.level0

end Work.FTS.EllipticEst.EllGap
