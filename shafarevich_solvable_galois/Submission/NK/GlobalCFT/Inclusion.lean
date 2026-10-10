import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFT.Place
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local embeddings and the inclusion of idèles

For `L / K` a finite extension of number fields and places `w` of `L` over `v` of `K`, the local
fields are related by a canonical ring homomorphism `K_v → L_w` (the completion of the inclusion
`K → L`).  This file records the induced *units* map `K_vˣ →* L_wˣ`, which is the input to the
inclusion of idèle groups `𝕀 K →* 𝕀 L` (the "diagonal" of the local embeddings), used to identify
`C_K` with the Galois invariants of `C_L` (the `H⁰`-computation).

## Main definitions

* `NK.GlobalCFT.Place.localAlgebraMapUnits`: the canonical `K_vˣ →* L_wˣ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT

namespace Place

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The canonical embedding of the local unit groups `K_vˣ →* L_wˣ` for a place `w` of `L` lying
over `v` of `K`: at an archimedean place the completion of the inclusion `K → L`, at a
nonarchimedean place the map on the adic completions. -/
noncomputable def localAlgebraMapUnits (w : Place L) (v : Place K) (h : LiesOver w v) :
    (localField K v)ˣ →* (localField L w)ˣ := by
  classical
  rcases w with w | q <;> rcases v with v | Q
  · by_cases hL : w.LiesOver v
    · exact Units.map (haveI := hL;
        (NumberField.LiesOver.completionMap (v := v) (w := w)).toMonoidHom)
    · exact 1
  · exact 1
  · exact 1
  · by_cases hL : q.asIdeal.LiesOver Q.asIdeal
    · exact Units.map ((Commons.RingTheory.Henselian.adicCompletionMap Q q hL).toMonoidHom)
    · exact 1

end Place

end NK.GlobalCFT
