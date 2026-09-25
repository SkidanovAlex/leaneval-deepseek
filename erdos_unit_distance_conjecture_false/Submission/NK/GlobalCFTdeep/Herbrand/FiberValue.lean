/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFTdeep.Herbrand.RepIso
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_localUnitsRep_ofFinite

/-!
# Milne's Proposition 2.7 for one place: `h(∏_{w | v} L_wˣ) = [L_w : K_v]`

This file assembles the two halves of Milne's Proposition 2.7 at a single finite place `v` of `K`
(`v = ofFinite Q`), namely

* the orbit identification `∏_{w | v} L_wˣ ≅ Coind_{D_w}^{G} L_wˣ`
  (`NK.GlobalCFTdeep.Herbrand.fiberIdelesRep_iso_coind`), which with Shapiro's lemma gives
  `h(∏_{w|v} L_wˣ) = h(D_w, L_wˣ)` for a chosen `w | v`
  (`NK.GlobalCFTdeep.herbrandEq_fiberIdeles_iff`), and
* the local computation `h(D_w, L_wˣ) = |D_w| = [L_w : K_v]` for commutative `D_w`
  (`NK.GlobalCFTdeep.Herbrand.herbrandEq_localUnitsRep_ofFinite`),

into the statement

  `HerbrandEq (fiberIdelesRep (ofFinite Q)) (Nat.card D_q)`,

i.e. the contribution of one place of `K` to the Herbrand quotient of the `T`-idèles.  What remains
of Milne's Proposition 2.7 is only the finite-product bookkeeping over `v ∈ S`
(`𝕀_{L,T} = ∏_{v ∈ S} ∏_{w|v} L_wˣ`, one fibre split off at a time with
`NK.GlobalCFTdeep.herbrandEq_iff_of_shortExact_finite`) and the archimedean places.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

/-- **Milne, *CFT*, Proposition 2.7 at one finite place**: for a finite place `Q` of `K` and a
finite place `q` of `L` above it, with commutative decomposition group `D_q`, the Herbrand quotient
of the fibre `∏_{w | Q} L_wˣ` is the local degree, in the form `|D_q|`. -/
theorem herbrandEq_fiberIdeles_ofFinite {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : HeightOneSpectrum (NumberField.RingOfIntegers L))
    [hqQ : q.asIdeal.LiesOver Q.asIdeal]
    [Fintype (decompositionSubgroup (K := K) (L := L) (Place.ofFinite q))]
    (hcomm : ∀ a b : decompositionSubgroup (K := K) (L := L) (Place.ofFinite q),
      a * b = b * a) :
    HerbrandEq (fiberIdelesRep (K := K) (L := L) (Place.ofFinite Q))
      (Nat.card (decompositionSubgroup (K := K) (L := L) (Place.ofFinite q))) :=
  (herbrandEq_fiberIdeles_iff (K := K) (L := L) (Place.ofFinite Q) (Place.ofFinite q)
    (Place.liesOver_ofFinite hqQ) _).mpr
    (Herbrand.herbrandEq_localUnitsRep_ofFinite (K := K) (L := L) Q q hcomm)

end NK.GlobalCFTdeep
