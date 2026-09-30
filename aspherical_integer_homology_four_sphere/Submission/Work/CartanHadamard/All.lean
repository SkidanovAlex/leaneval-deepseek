/-
# Area `CH` (`CartanHadamard/`): the complete import surface

`import Submission.Work.CartanHadamard.All` gives every declaration of the Cartan–Hadamard area:

* `Basic.lean`     — `curvLe_all`, `isLocalHomeomorph_gexpMap`/`_GExp`, `lift_unique_GExp`,
                     discreteness of the fibres;
* `Translate.lean` — the geodesic translate `translate` and its universal property,
                     `exists_translate_eq`;
* `exists_lift_from_vector.lean` — the lifting theorem from an arbitrary tangent vector;
* `lift_family_continuity_core.lean` — joint continuity of a family of lifts;
* `continuousOn_translate.lean`, `isOpen_translate_image.lean` — continuity and openness of the
                     translate map (the two analytic inputs of the even-covering argument);
* `isCoveringMap_of_sheets.lean` — the abstract even-covering packaging lemma;
* `surjective_of_isCoveringMap_of_connectedSpace.lean` — surjectivity of a covering over a connected
                     base;
* `Cover.lean`     — `isCoveringMap_GExp`, `isCoveringMap_gexp`;
* `Main.lean`      — the four deliverables of the area;
* `AxiomCheck.lean` — the `#print axioms` audit of the area.
-/
import Submission.Work.CartanHadamard.Basic
import Submission.Work.CartanHadamard.Translate
import Submission.Work.CartanHadamard.exists_lift_from_vector
import Submission.Work.CartanHadamard.lift_family_continuity_core
import Submission.Work.CartanHadamard.continuousOn_translate
import Submission.Work.CartanHadamard.isOpen_translate_image
import Submission.Work.CartanHadamard.isCoveringMap_of_sheets
import Submission.Work.CartanHadamard.surjective_of_isCoveringMap_of_connectedSpace
import Submission.Work.CartanHadamard.Cover
import Submission.Work.CartanHadamard.Main

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

