import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.Herbrand.hOne_fiberIdelesRep_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Positivity of `Ĥ¹` of the idèles supported on a finite set of places

The cross-multiplied form of Herbrand multiplicativity

  `|Ĥ⁰(𝕀_{L,T})| · |Ĥ¹(∏_{w∉T}U_w)| · |Ĥ¹(supported)| = |Ĥ⁰(∏_{w∉T}U_w)| · |Ĥ⁰(supported)| · |Ĥ¹(𝕀_{L,T})|`

can be cancelled by `|Ĥ¹(supported)|` only when that number is non-zero, i.e. when `Ĥ¹` of the
idèles supported on `T` is *finite*.  This file supplies that: `Ĥ¹` of the fibre `∏_{w|v}L_wˣ` is
trivial at every place `v` (`hOne_fiberIdelesRep_eq_one`, Hilbert 90 transported along Shapiro), so
`|Ĥ¹|` of the finite product over `v ∈ S` is `1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep.Herbrand

open NK.GlobalCFT
open NK.GlobalCFTdeep

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **`Ĥ¹` of the idèles supported on `T` is trivial.**  For a finite set `S` of places of `K` and
`T` the set of places of `L` above it, the first Tate cohomology of the module of idèles supported
on `T` (the product `∏_{v∈S}∏_{w|v}L_wˣ`) is trivial: `h(∏_{w|v}L_wˣ) = |D_w|` and
`Ĥ¹(∏_{w|v}L_wˣ) = 0` at every `v`. -/
theorem hposSup_supportedIdelesRep [IsCyclic (L ≃ₐ[K] L)]
    (S : Finset (Place K)) (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v) :
    0 < hOne (supportedIdelesRep (L := L) T hT) := by
  classical
  rw [hOne_def, natCard_tateCohomology_supportedIdelesRep (K := K) (L := L) S T hT hTS 1]
  rw [Nat.card_pi]
  refine Finset.prod_pos fun v _ => ?_
  rw [show Nat.card (tateCohomology (fiberIdelesRep (K := K) (L := L) (v : Place K)) 1) = 1 by
    simpa only [hOne_def] using hOne_fiberIdelesRep_eq_one (K := K) (L := L) (v : Place K)]
  exact one_pos

end NK.GlobalCFTdeep.Herbrand
