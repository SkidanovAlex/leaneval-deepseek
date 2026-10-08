/-
Area A7F of the Gorenstein--Walter project: **the deliverable**, the model facts on `A₇`.

`Work.A7F.a7ModelProp` proves `Work.GW2.A7ModelProp` (Bender 1.8), the verbatim Prop of the area
contract `Submission/Work/_design_gw/Contracts2.lean`:

* `|A₇| = 2520`;
* every Sylow `2`-subgroup of `A₇` is isomorphic to `DihedralGroup 4` (the dihedral group of
  order `8`);
* the centralizer of every involution of `A₇` has order `24`;
* every odd-order subgroup of `A₇` has order at most `21`.

`Work.GW2.a7ModelProp` is the same statement in the contract's namespace, so a caller can use it
directly as the `a7` field of `GW2.LocalToolkit`.
-/
import Mathlib
import Submission.Work.A7F.Defs
import Submission.Work.A7F.Facts
import Submission.Work.A7F.OddSubgroup
import Submission.Work.A7F.sylow2_iso
import Submission.Work.A7F.card_point_stabilizer

open scoped MatrixGroups

namespace Work.A7F

/-- **Bender 1.8, the `A₇` model facts**: the deliverable of area A7F. -/
theorem a7ModelProp : Work.GW2.A7ModelProp :=
  ⟨nat_card_alternatingGroup_fin_seven, sylow2_iso, card_centralizer_of_involution,
    odd_subgroup_card_le_21⟩

end Work.A7F

namespace Work.GW2

/-- The area deliverable `Work.A7F.a7ModelProp`, stated directly on the contract's Prop so that it
can be used as the `a7` field of `LocalToolkit`. -/
theorem a7ModelProp : A7ModelProp := Work.A7F.a7ModelProp

end Work.GW2
