import Mathlib
import Submission.Work.ShafarevichKoch.SupportedGroupExt
import Submission.Work.ShafarevichKoch.natCard_ker_H2Res_le_card_invariantHom

/-!
# `Work.ShafarevichKoch.ConjBridge` -- matching the two spellings of conjugation

The invariant counting engine `natCard_ker_H2Res_le_card_invariantHom` states invariance with
`E.conj g n` (the `Classical.choose`-defined conjugation datum of `Work.ConCohomology.GroupExt`),
while the tower theorem `natCard_invariantHom_HSupported_le` states it with the explicit element
`⟨g * n * g⁻¹, _⟩`.  This module records that the two agree -- `GroupExt.i_conj` plus injectivity of
`i` -- so that the engine applies to the tower comparison `groupExtHSupported`, which is the only
spelling bridge needed to combine (C) with the engine.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Classical

noncomputable section

namespace Work.ShafarevichKoch

variable {G Q N : Type*} [Group G] [Group Q] [Group N]

/-- **The two spellings of conjugation agree.**  For a `GroupExt` with `i` the inclusion of `N` in
`G`, the `Classical.choose`-defined `E.conj g n` is the unique element of `N` whose image is
`g * i n * g⁻¹`. -/
theorem conj_eq_subtype {G Q N : Type*} [Group G] [Group Q] [Group N] (E : Work.ConCohomology.GroupExt G Q N)
    (g : G) (n : N) (y : N) (hy : E.i y = g * E.i n * g⁻¹) : E.conj g n = y :=
  E.injective_i (by rw [E.i_conj, hy])

end Work.ShafarevichKoch
