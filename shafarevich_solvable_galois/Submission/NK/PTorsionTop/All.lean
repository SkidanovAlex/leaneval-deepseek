/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `NK.PTorsionTop`: the corrected `p`-torsion detector for the local input

The whole chapter, in one import.

* `NK.PTorsionTop.Basic` — the predicate `HasPTorsionAbelianizationTop p G` (the
  *topological* abelianisation), `HasPTorsion`, and their invariance.
* `NK.PTorsionTop.CompletionTorsion` — `p`-torsion of the profinite completion of a commutative
  group: no new `p`-torsion (`completion_pow_eq_one_of`) and survival of `p`-torsion
  (`hasPTorsion_completion_of_exponent`).
* `NK.PTorsionTop.UnitsTorsion` — the units chapter: the `p`-torsion of `κˣ^{∧}` is `μ_p(κ)`.
* `NK.PTorsionTop.Main` — the corrected `δ`-detection
  (`hasPTorsionAbelianizationTop_iff_zeta`), the topological abelianisation
  (`quotientTopologicalClosureCommEquivAbGal`) and the composite
  `Gal(K'/κ) ⧸ closure([G,G]) ≃* κˣ^{∧}` (`quotientTopologicalClosureCommEquiv`).
* `NK.PTorsionTop.InputsTop` — the corrected bundles `PadicGaloisInputsTop`,
  `LocalGaloisInputsTop` and the corrected transport lemmas.
* `NK.PTorsionTop.GlobalTop` — the corrected global corollary.
* `NK.PTorsionTop.Verdict` — the honest verdict on the old abstract predicate.
-/
import Submission.NK.PTorsionTop.Basic
import Submission.NK.PTorsionTop.CompletionTorsion
import Submission.NK.PTorsionTop.UnitsTorsion
import Submission.NK.PTorsionTop.Main
import Submission.NK.PTorsionTop.InputsTop
import Submission.NK.PTorsionTop.GlobalTop
import Submission.NK.PTorsionTop.Verdict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
