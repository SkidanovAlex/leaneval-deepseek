/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFTdeep.Herbrand.FiberValue
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_fiberIdeles_ofInfinite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Milne's Proposition 2.7 at one place: finite and archimedean cases together

`herbrandEq_fiberIdeles_ofFinite` computes the Herbrand quotient of the fibre `∏_{w|v}L_wˣ` at a
*nite* place and `herbrandEq_fiberIdeles_ofInfinite` at an archimedean one.  This file records the
combined statement, for an arbitrary place of `K`: the case distinction is the one of
`NK.GlobalCFT.Place.LiesOver`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

/-- **Milne, *CFT*, Proposition 2.7 at one place, finite or archimedean.**  For any place `v` of
`K` and any place `w` of `L` above it, with commutative decomposition group `D_w` (automatic at an
archimedean place, and the hypothesis of the local computation at a finite one), the Herbrand
quotient of the fibre `∏_{w' | v} L_{w'}ˣ` is the local degree, in the form `|D_w|`. -/
theorem herbrandEq_fiberIdeles {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : Place K) (w : Place L) (hw : Place.LiesOver w v)
    [Fintype (decompositionSubgroup (K := K) (L := L) w)]
    (hcomm : ∀ a b : decompositionSubgroup (K := K) (L := L) w, a * b = b * a) :
    HerbrandEq (fiberIdelesRep (K := K) (L := L) v)
      (Nat.card (decompositionSubgroup (K := K) (L := L) w)) := by
  rcases hw with ⟨w', v', hw1, hv1, hL⟩ | ⟨q, Q, hw1, hv1, hL⟩
  · subst hw1; subst hv1
    exact Herbrand.herbrandEq_fiberIdeles_ofInfinite v' w' hL
  · subst hw1; subst hv1
    exact herbrandEq_fiberIdeles_ofFinite Q q hcomm

end NK.GlobalCFTdeep
