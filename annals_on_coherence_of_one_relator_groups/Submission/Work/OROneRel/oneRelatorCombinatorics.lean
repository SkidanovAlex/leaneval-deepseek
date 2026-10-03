/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The four classical theorems of one-relator group theory, unconditionally

This is the capstone of node `N2`: the `Prop`-valued structure `OneRelatorCombinatorics` of
`Submission.Work.OROneRel.Interface`, built from the four theorem-level results of the node:

* `Work.OROneRel.freiheitssatz_at` — the Freiheitssatz (Magnus 1930), plus its consequence that
  Magnus subgroups are free (`Work.OROneRel.isFreeGroup_of_isMagnusSubgroup`);
* `Work.OROneRel.magnus_moldavanskii_at` — the Magnus--Moldavanskii--Masters hierarchy;
* `Work.OROneRel.weinbaum_at` — Weinbaum's theorem;
* `Work.OROneRel.kms_torsion_at` — the Karrass--Magnus--Solitar torsion theorem.

Consumers: `Work.OROneRel.freiheitssatz`, `magnus_moldavanskii`, `weinbaum`, `kms_torsion`
(each taking `C : OneRelatorCombinatorics`), as used by nodes `N3`, `N4`, `N9`, `N14`.
-/
import Submission.Work.OROneRel.Interface
import Submission.Work.OROneRel.FreiheitssatzUnconditional
import Submission.Work.OROneRel.freiheitssatz_at
import Submission.Work.OROneRel.magnus_moldavanskii_at
import Submission.Work.OROneRel.weinbaum_at
import Submission.Work.OROneRel.kms_torsion_at

set_option autoImplicit false

namespace Work.OROneRel

universe u

/-- **Node `N2`, unconditionally**: every one-relator relator has a Freiheitssatz, a
Magnus--Moldavanskii hierarchy, Weinbaum's subword theorem, and Karrass--Magnus--Solitar torsion. -/
theorem oneRelatorCombinatorics : OneRelatorCombinatorics.{u} :=
  OneRelatorCombinatorics'.toOneRelatorCombinatorics
    ⟨fun r => magnus_moldavanskii_at r, fun r => weinbaum_at r, fun r => kms_torsion_at r⟩

end Work.OROneRel
