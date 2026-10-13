/-
# `FTS/StrongPersist/StarPkg6OfCore.lean` — the order-six star package from `StarCore`

**Target.** `StarCore α Cs Φs → StarPkg6 α (C·Cs) Φs` for `0 < α ≤ 1/4`, `Cs > 0`, with a
universal (α-independent) constant `C`.

`StarPkg6` (`FTS/StrongPersist/Clauses.lean`) extends the level-four star package `StarPkgo2`
(`Work.FTS.VocabO2`) by the five order-six fields `RW6`, `VW6`, `VzW6`, `UsW6`, `UszW6`: the
flat `𝒲^{6,∞}`-bounds of `((z+1)/z)·ℛ(Φ̃_*)`, `𝒱(Φ̃_*)`, `((z+1)/z)·𝒱(Φ̃_*)`, `𝒰(Φ̃_*)/σ`,
`((z+1)/z)·𝒰(Φ̃_*)/σ`.

**Route** (the order-six lift of `FTS/PhiStar/CoreAux/Assembly`):

1. `FTS/PhiStar/StarPkgo2OfCore` supplies the level-four package at the constant `C₁·Cs`;
2. `StarCore` gives `FlatW 7 Ŷ (Cs·α)` and hence, by `CoreAux.Fb_of_FlatW`,
   `Fb 6 (CB·Cs·α) Ŷ`, while `SP6.F0SixYblk` gives `F0 6 (CD·Cs·α) (Yblk Ŷ)`
   (`Yblk Ŷ = z ∂_z Ŷ`);
3. `SP6.FlatW6FieldsAlpha` gives the five order-six flat bounds with constant
   `C·(α+1)·(K+KY+KD)`.  The factor `(α+1)` is necessary: `EH`, `EUz` and `EU` grow linearly
   in `α` (the α-free pricing is machine-refuted in `SP6/FlatW6Fields.lean`,
   `not_FlatW6Fields`);
4. `SP6.WlInf6OfFlatW` turns a `FlatW 6`-bound into `WlInfMem α 6` together with a
   `WlInf α 6`-bound, using the vanishing off the open quadrant (`CoreAux.fields_vanish`) and
   the open-quadrant smoothness (`CoreAux.fields_smooth`); the flat bounds are transferred to
   the five transport-coefficient fields along the identities `CoreAux.fields_ident`;
5. `StarPkg6OfPieces` (`FTS/StrongPersist/StarPkg6Assembly.lean`) assembles the package,
   enlarging the level-four constant to the final one (`StarPkgo2_raise_Cs`).

(An alternative route to step 3, from the five per-field lemmas
`SP6.FieldEH/EVz/EV/EUz/EU`, is available through `FlatW6Fields_of_fields`
(`StarPkg6Combine.lean`).)
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.StarPkg6Aux
import Submission.Work.FTS.StrongPersist.StarPkg6Assembly
import Submission.Work.FTS.StrongPersist.SP6.WlInf6OfFlatW
import Submission.Work.FTS.StrongPersist.SP6.F0SixYblk
import Submission.Work.FTS.StrongPersist.SP6.FlatW6FieldsAlpha

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

set_option autoImplicit false
set_option linter.unusedVariables false

theorem StarPkg6OfCore : ∃ C : ℝ, 0 < C ∧ ∀ (α Cs : ℝ) (Φs : Work.FTS.Galerkin.Fn),
    0 < α → α ≤ 1 / 4 → 0 < Cs → Work.FTS.VocabO2.StarCore α Cs Φs →
    Work.FTS.StrongPersist.StarPkg6 α (C * Cs) Φs :=
  StarPkg6OfPieces Work.FTS.StrongPersist.SP6.WlInf6OfFlatW
    Work.FTS.StrongPersist.SP6.F0SixYblk Work.FTS.StrongPersist.SP6.FlatW6FieldsAlpha

end Work.FTS.StrongPersist
