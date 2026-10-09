import Mathlib
import Submission.Work.SSGRoute.ArchDictionary.archPlaceDictBranches
import Submission.Work.SSGRoute.ArchDictionary.archPlaceDict_of_nonsplit_p2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The remaining case of `ArchPlaceDict`: the complex (`p = 2`, nonsplit) place

`Work.SSGRoute.ArchDictionary.archPlaceDictBranches` discharges two of the three cases of
`Work.SSGRoute.LeadNatWit.ArchPlaceDict` at an archimedean place:

* `archPlaceDict_of_split` — `decompK w = ⊥` (real place, `p = 2`), from A1–A3 of
  `_lead_design/ssg_arch2_2320.md`;
* `archPlaceDict_of_nonsplit_odd` — `decompK w ≠ ⊥` and `p ≠ 2`, where both sides are subsingletons.

The third case — `decompK w ≠ ⊥` (the place is complex, `K_w = ℂ`) and `p = 2` — is the arithmetic
content of the archimedean dictionary, and it is now stated and assembled **in a module of its own**,
`Submission/Work/SSGRoute/ArchDictionary/archPlaceDict_of_nonsplit_p2.lean` (lead design
`_lead_design/archp2_1008`), where the `E`-indexed, coefficient-natural comparison square between the
canonical *global* dictionary (`E1aClean.globalDictionaryCanon`) and the involution cohomology
`Ac c E = H¹(⟨c⟩,E)` is built from the seam dictionary.

This file is kept as the **stable re-export point** for the theorem: it used to hold the statement
with the only `sorry` of the archimedean lane, and several modules import it by path.  It now simply
re-exports the theorem from the dedicated module, so that consumers keep working unchanged and the
declaration `Work.SSGRoute.ArchDictionary.archPlaceDict_of_nonsplit_p2` has exactly one definition.
-/
