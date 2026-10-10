import Mathlib
import Submission.Work.CY3Stab.Defs
import Submission.Work.CY3Stab.Variety
import Submission.Work.CY3Stab.Prod.height_map_mvPolynomial
import Submission.Work.CY3Stab.Prod.specTensorTo_bot_mem_closure
import Submission.Work.CY3Stab.Prod.coheight_specTensorTo_bot
import Submission.Work.CY3Stab.Prod.not_isIsoAt_prodMap_prodPtGen

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

/-!
# `Work.CY3Stab.Prod.prodPtGen_mem_exDiv` — the surjectivity half of the `exDiv` analysis

Lin–Shinder's stabilisation step (`c(φ × Id_W) = [Z × ℙ¹ × W] − [Z' × ℙ¹ × W]`, proof of
`thm:bir-generation` (c)) requires the `exDiv` analysis of the product map `φ × id_𝔸ᵏ`: the
exceptional divisors of `φ × id` are exactly the cylinder points over the exceptional divisors
of `φ`.  This file proves the *surjectivity* half, i.e. the missing Mathlib input recorded in
`Submission/Work/CY3Stab/NOTES.md` §2(d)/§6:

> if `x` is an exceptional divisor of `φ`, then the generic point
> `p := (cylTriplet X x k).SpecTensorTo ⊥` of the cylinder `𝔸ᵏ × \overline{x}` over `x` is an
> exceptional divisor of `φ × id_𝔸ᵏ`.

`exDiv Ψ = {q | coheight q = 1 ∧ ¬ IsIsoAt Ψ q}`, and the two components are supplied by the
delegated pieces:

* `Work.CY3Stab.Prod.coheight_specTensorTo_bot` — the codimension transfer
  `coheight p = coheight x` (the local computation on an affine chart of the cylinder, where the
  prime of `p` is the extension of the prime of `x`, together with Matsumura's height formula);
* `Work.CY3Stab.Prod.not_isIsoAt_prodMap_prodPtGen` — the isomorphism-point descent
  `¬ IsIsoAt φ x → ¬ IsIsoAt (prodMap k φ) p`;
* `Work.CY3Stab.Prod.specTensorTo_bot_mem_closure` — the geometric input that every point of the
  fibre of the cylinder over `x` lies in the closure of `p`;
* `Work.CY3Stab.Prod.height_map_mvPolynomial` — the commutative-algebra input (the extension of a
  height-one prime to a polynomial ring has height one).
-/

namespace Work.CY3Stab.Prod

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants Order

/-- The cylinder triplet over `x` has first component the generic point of `𝔸ᵏ`. -/
theorem cylTriplet_x (𝕜 : Type) [Field 𝕜] (k : ℕ) (X : AlgebraicGeometry.Scheme.{0})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))] (x : X) :
    (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) X x k).x =
      genericPoint (Work.CY3Stab.AffineK (𝕜 := 𝕜) k) := rfl

/-- The cylinder triplet over `x` has second component `x`. -/
theorem cylTriplet_y (𝕜 : Type) [Field 𝕜] (k : ℕ) (X : AlgebraicGeometry.Scheme.{0})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))] (x : X) :
    (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) X x k).y = x := rfl

/-- A variety is locally noetherian (so that the codimension transfer on the cylinder applies). -/
theorem isLocallyNoetherian_of_variety (𝕜 : Type) [Field 𝕜] (X : AlgebraicGeometry.Scheme.{0})
    [MotivicInvariants.Variety 𝕜 X] : IsLocallyNoetherian X :=
  Work.K3Inputs.isLocallyNoetherian_of_variety 𝕜 X

/-- **The surjectivity half of the `exDiv` analysis of the product map** `φ × id_𝔸ᵏ`: the
cylinder point over an exceptional divisor of `φ` is an exceptional divisor of `φ × id_𝔸ᵏ`. -/
theorem prodPtGen_mem_exDiv (𝕜 : Type) [Field 𝕜] (k : ℕ) {X Y : AlgebraicGeometry.Scheme.{0}}
    [MotivicInvariants.Variety 𝕜 X] [MotivicInvariants.Variety 𝕜 Y] (φ : X.BirationalMap Y)
    [φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [MotivicInvariants.Variety 𝕜 (Work.CY3Stab.WProd (𝕜 := 𝕜) X k)]
    [MotivicInvariants.Variety 𝕜 (Work.CY3Stab.WProd (𝕜 := 𝕜) Y k)]
    (x : X) [IsDomain (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) X x k).tensor]
    (hx : x ∈ exDiv φ) :
    (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) X x k).SpecTensorTo
      (⊥ : PrimeSpectrum (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) X x k).tensor) ∈
      exDiv (Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ) := by
  obtain ⟨hco, hiso⟩ := hx
  have hln : IsLocallyNoetherian X := isLocallyNoetherian_of_variety 𝕜 X
  refine ⟨?_, ?_⟩
  · rw [coheight_specTensorTo_bot (𝕜 := 𝕜) (n := Fin k) X x (Work.CY3Stab.cylTriplet X x k)
      (cylTriplet_x 𝕜 k X x) (cylTriplet_y 𝕜 k X x)]
    exact hco
  · exact not_isIsoAt_prodMap_prodPtGen 𝕜 k φ x hiso

end Work.CY3Stab.Prod
