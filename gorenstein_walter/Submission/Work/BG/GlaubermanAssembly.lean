import Submission.Work.BG.Glauberman
import Submission.Work.BG.centralInvolution
import Submission.Work.BG.restrictToFixed
import Submission.Work.BG.fixedRestrict
import Submission.Work.BG.rangeCardLt
import Submission.Work.BG.invariantOddConstituent
import Submission.Work.BG.parityTransfer
import Submission.Work.BG.oddMultUniqueTransport
import Submission.Work.BG.baseOddMult

/-!
# Area BG: Bender–Glauberman 1981, Lemma 1.9 — assembly of the induction

`Submission/Work/BG/Glauberman.lean` (copied from the lead's design pass 11,
`_design_gw/Core11BG.lean`) proves the two assembly steps

* `Work.BG.glaubAtMost_of_leaves` — the seven leaves give `GlaubAtMost n` for every `n`, by
  strong induction on `|φ(S)|`;
* `Work.BG.glaubermanGeneral_of_glaubAtMost` — `GlaubAtMost n` for all `n` plus the instance
  bridge `Work.BG.oddMultBridge` give `Work.BG.glaubermanGeneralProp`;

and the seven leaves are proved in the modules imported above
(`centralInvolution`, `restrictToFixed`, `fixedRestrict`, `rangeCardLt`,
`invariantOddConstituent`, `parityTransfer`, `oddMultUniqueTransport`, `baseOddMult`).

This module performs the assembly, giving the **general Glauberman correspondence for a
2-group acting on a 2'-group** (BG Lemma 1.9, the odd-multiplicity form), of which
`Work.BG.glauberman_two` (`glauberman_two.lean`) is the `|S| = 2` case.  The companion
bijection form of the paper's Lemma 1.9 is not stated here.
-/

namespace Work.BG

/-- **The induction of Bender–Glauberman 1981, Lemma 1.9, assembled**: `GlaubAtMost n` holds
for every `n` — i.e. for a 2-group `S` acting on a group `U` of odd order and an `S`-invariant
`α ∈ Irr(U)`, there is a unique `β ∈ Irr(C_U(S))` with `(α|_{C_U(S)}, β)` odd, whenever the
image of `S` in `Aut U` has cardinality `≤ n`. -/
theorem glaubAtMost (n : ℕ) : GlaubAtMost n :=
  glaubAtMost_of_leaves baseOddMult centralInvolution restrictToFixed fixedRestrict
    rangeCardLt invariantOddConstituent parityTransfer oddMultUniqueTransport n

/-- **Bender–Glauberman 1981, Lemma 1.9** (general case), in the area's own vocabulary
(`Work.BG.glaubermanGeneralProp`): for a 2-group `S` acting by automorphisms on a group `U`
of odd order, every `S`-invariant `α ∈ Irr(U)` has a unique `β ∈ Irr(C_U(S))` whose
multiplicity in `α|_{C_U(S)}` is odd. -/
theorem glauberman_general_assembled : glaubermanGeneralProp :=
  glaubermanGeneral_of_glaubAtMost glaubAtMost oddMultBridge

end Work.BG
