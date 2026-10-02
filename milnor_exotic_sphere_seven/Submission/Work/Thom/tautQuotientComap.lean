import Mathlib
import Submission.Work.Thom.chernClass
import Submission.Work.Thom.complexPullback
import Submission.Work.Thom.exists_punctMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The canonical map of punctured total spaces, and the first rung of the splitting principle

For `f : B' → B` and a complex bundle `Z` of rank `m+1` over `B`, `Work.Thom.bundleComap Z f` is
the pullback; there is a canonical continuous map of punctured total spaces

`punctMap Z f : ↥(zeroComplement (realification (bundleComap Z f))) → ↥(zeroComplement (realification Z))`,
`p ↦ (f p.1, p.2)`,

which is the underlying map of the bundle map `f^*Z → Z` (on the complement of the zero section).
`Work.Thom.punctMap` is the (unique, hence canonical) witness of `Work.Thom.exists_punctMap`.

`Work.Thom.tautQuotientCore_comap` is the statement that the tautological quotient commutes with
pullback along it: `f^*(π^*Z/ℂ·s) = π^*(f^*Z)/ℂ·s`.  Together with the fact that
`Work.Thom.thomClassRank` is the canonical construction `Work.Thom.thomClassOf`, this is the first
rung of the splitting principle (G2a of `README.md` ADDENDUM 21).
-/

namespace Work.Thom

open Work.TangentClasses

noncomputable section

variable {B B' : Type} [TopologicalSpace B] [TopologicalSpace B'] {ι : Type}

/-- **The canonical map of punctured total spaces over `f : B' → B`**: on the underlying bundles it
is `⟨f p.1, p.2⟩`.  It is the (unique) witness of `Work.Thom.exists_punctMap`. -/
noncomputable def punctMap {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (f : C(B', B)) :
    C(↥(zeroComplement (realification (bundleComap Z f))),
      ↥(zeroComplement (realification Z))) :=
  Classical.choose (exists_punctMap Z f)

/-- The defining equation of `Work.Thom.punctMap`. -/
theorem punctMap_apply {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (f : C(B', B))
    (p : ↥(zeroComplement (realification (bundleComap Z f)))) :
    (punctMap Z f p).1 = (⟨f p.1.1, p.1.2⟩ : (realification Z).TotalSpace) :=
  Classical.choose_spec (exists_punctMap Z f) p

end

end Work.Thom
