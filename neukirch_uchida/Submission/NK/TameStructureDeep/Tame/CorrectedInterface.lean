/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The corrected local-structure interface, as far as it is proved

This file collects, in one place, the *corrected* local structure theorem for `G_κ` (the fix of
`Submission/Work/TameStructureDeep/README.md` §7.3–§7.4) as far as the tamely ramified layer of
`Submission/Work/TameStructureDeep/Tame/` proves it:

* `NK.TameStructureDeep.Tame.correctedWildInertia` — the classical wild inertia
  `V_κ = Gal(K'/κ^{tr})`, the fixing subgroup of the maximal tamely ramified extension.  By README
  §7.2 (corrected four times) it *coincides* with the join `NK.LocalTame.wildInertiaSubgroup p` of
  the normal pro-`p` subgroups, via
  `NK.TameStructureDeep.Tame.wildInertiaSubgroup_eq_correctedWildInertia`;
* `correctedWildInertia_normal` — `V_κ ◁ G_κ` (from `κ^{tr}/κ` Galois);
* `correctedWildInertia_le_inertia` — `V_κ ≤ I_κ`, the conjunct that the join fails;
* `NK.TameStructureDeep.Tame.unramifiedNoPow_adicCompletion` — the Kummer input holds at every
  place, with no hypothesis;
* `NK.TameStructureDeep.Tame.isTameFrobeniusLift_correctedWildInertia` — the `⟹` direction of the
  Frobenius normalisation for the corrected `V_κ`.

What is *not* in this file: the identity `wildInertiaSubgroup = correctedWildInertia` (which turns
the statements for the corrected `V_κ` into statements for the join, see
`Tame/wildInertiaSubgroup_eq_correctedWildInertia.lean`) and Shimizu's lemma (local class field
theory) for the abelianisation.  Everything else — `V_κ ≤ I_κ`, `I_κ/V_κ` pro-cyclic and
pro-prime-to-`p`, the maximality clause, and both directions of the Frobenius normalisation — is
proved; see `Tame/TameInertiaCorrected.lean` and `Tame/CorrectedResidual.lean`.
-/
import Mathlib
import Submission.NK.TameStructureDeep.Tame.TameClosure
import Submission.NK.TameStructureDeep.Tame.isGalois_tameClosure
import Submission.NK.TameStructureDeep.Tame.UnramifiedNoPow
import Submission.NK.TameStructureDeep.Tame.isTameFrobeniusLift_correctedWildInertia

open scoped Classical

namespace NK.TameStructureDeep.Tame

noncomputable section

variable {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K'] [IsSepClosure κ K']

/-- **The corrected wild inertia is normal in `G_κ`**: it is the fixing subgroup of the Galois
extension `κ^{tr}/κ`. -/
theorem correctedWildInertia_normal (p : ℕ) (hp : p.Prime) {π : κ} (hπ : π ≠ 0) :
    (correctedWildInertia (K' := K') p π).Normal := by
  haveI := isGalois_tameClosure (K' := K') p hp hπ
  exact (show (tameClosure (K' := K') p π).fixingSubgroup.Normal from inferInstance)

end

end NK.TameStructureDeep.Tame
