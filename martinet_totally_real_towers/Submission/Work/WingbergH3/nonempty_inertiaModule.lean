import Mathlib
import Submission.Work.WingbergH3.Defs

/-!
# `Work.WingbergH3.nonempty_inertiaModule`

The bare generating-family harness `Work.WingbergH3.InertiaModule m` is inhabited for every `m`:
its mathematical content lies entirely in the companion predicates (`SalleKochDetects`,
`ConstructiveDatum`), not in the existence of the carrier.

Concretely we take the trivial pro-`2` group as carrier `X`, together with the (unique) family
`Fin m → X`.  Being a subsingleton it is a finite `p`-group for every `p`, hence a pro-`p` group,
and the closure of the range of the generating family is `⊤` by subsingleton-ness.
-/

open Work.RelatorRank

namespace Work.WingbergH3

theorem nonempty_inertiaModule (m : ℕ) : Nonempty (Work.WingbergH3.InertiaModule m) := by
  refine ⟨{ X := PUnit, proX := ?_, gen := fun _ => PUnit.unit, dense := ?_ }⟩
  · intro U
    exact IsPGroup.of_subsingleton 2 _
  · rw [Work.RelatorRank.denseGenerating_iff]
    exact Subsingleton.elim _ _

end Work.WingbergH3
