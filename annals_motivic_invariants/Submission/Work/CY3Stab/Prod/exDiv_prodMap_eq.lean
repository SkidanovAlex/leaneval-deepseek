import Mathlib
import Submission.Work.CY3Stab.Defs
import Submission.Work.CY3Stab.Variety
import Submission.Work.CY3Stab.Prod.prodPtGen_mem_exDiv
import Submission.Work.CY3Stab.Prod.specTensorTo_bot_mem_closure

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

/-!
# `Work.CY3Stab.Prod.exDiv_prodMap_eq` — the `exDiv` analysis of the product map

Lin–Shinder's stabilisation step (`thm:bir-generation` (c)) needs the `exDiv` analysis of the
product map `φ × id_{𝔸ᵏ}`: the exceptional divisors of `φ × id` are exactly the cylinder points
over the exceptional divisors of `φ`,

`exDiv (φ × id_{𝔸ᵏ}) = prodPt · k '' exDiv φ`.

The two inclusions are the two delivered halves:

* `⊇`: `Work.CY3Stab.Prod.prodPtGen_mem_exDiv` — the cylinder point over an exceptional divisor
  of `φ` is an exceptional divisor of `φ × id_{𝔸ᵏ}` (the codimension transfer
  `coheight (prodPt x k) = coheight x` together with the isomorphism-point descent);
* `⊆`: let `p ∈ exDiv (φ × id_{𝔸ᵏ})` and put `x := pr p`, an exceptional divisor of `φ` by
  `Work.CY3Stab.exDiv_prodMap_subset`.  The fibre of the projection over `x` is irreducible with
  generic point `prodPt x k`, so `p ∈ closure {prodPt x k}`
  (`Work.CY3Stab.Prod.specTensorTo_bot_mem_closure`), and both points have coheight `1`.  A
  *strict* specialisation strictly increases the coheight in a scheme
  (`Work.CY3Stab.Prod.coheight_add_one_le_of_mem_closure`, proved here from Mathlib's
  `Order.coheight_add_one_le` and `specializes_iff_mem_closure`), so `p ≠ prodPt x k` would force
  `coheight p ≥ 2`, contradicting `p ∈ exDiv`.

This is the point-identity `p = prodPt (pr p) k` of the residual list in
`Submission/Work/CY3Stab/NOTES.md` §6; with it the `exDiv` input of the counting
(`Work.CY3Stab.Prod.excCount_eq_of_exDiv_image`) is available.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.CY3Stab.Prod

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-- **A strict specialisation strictly increases the coheight.**  If `p` lies in the closure of
`{q}` and `p ≠ q`, then `q` is a *strict* specialisation of `p` in the specialisation order on
the points of `X` (which is `x ≤ y ↔ x ⤳ y`), so `coheight p ≥ coheight q + 1`
(`Order.coheight_add_one_le`).

The inequality is the order-theoretic content of "a point of the closure of an irreducible
`codimension one` closed set which is not its generic point has codimension at least two": for a
scheme, `Order.coheight z = ringKrullDim (𝒪_z)`
(`AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`), so strict specialisation is a strict
inclusion of primes, which lengthens every chain of primes by one. -/
theorem coheight_add_one_le_of_mem_closure {X : AlgebraicGeometry.Scheme.{0}} {p q : X}
    (h : p ∈ closure ({q} : Set X)) (hne : p ≠ q) :
    Order.coheight q + 1 ≤ Order.coheight p := by
  -- `p ∈ closure {q}` says that `q` specialises to `p`
  have hpq : q ⤳ p := specializes_iff_mem_closure.mpr h
  have hp_le : p ≤ q := by
    rw [Scheme.le_iff_specializes]
    exact hpq
  -- and `q ≤ p` would make the two points inseparable, hence equal (`X` is a `T0Space`)
  have hnotle : ¬ (q ≤ p) := by
    intro hle
    rw [Scheme.le_iff_specializes] at hle
    exact hne (inseparable_iff_eq.mp (inseparable_iff_specializes_and.mpr ⟨hle, hpq⟩))
  exact Order.coheight_add_one_le (show p < q from ⟨hp_le, hnotle⟩)

/-- **The `exDiv` analysis of the product map**: the exceptional divisors of `φ × id_{𝔸ᵏ}` are
exactly the cylinder points over the exceptional divisors of `φ`. -/
theorem exDiv_prodMap_eq (𝕜 : Type) [Field 𝕜] (k : ℕ) {X Y : AlgebraicGeometry.Scheme.{0}}
    [MotivicInvariants.Variety 𝕜 X] [MotivicInvariants.Variety 𝕜 Y] (φ : X.BirationalMap Y)
    [φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [MotivicInvariants.Variety 𝕜 (Work.CY3Stab.WProd (𝕜 := 𝕜) X k)]
    [MotivicInvariants.Variety 𝕜 (Work.CY3Stab.WProd (𝕜 := 𝕜) Y k)]
    [hD : ∀ (x : X), IsDomain (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) X x k).tensor] :
    exDiv (Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ) =
      (fun x => Work.CY3Stab.prodPt (𝕜 := 𝕜) X x k) '' exDiv φ := by
  ext p
  constructor
  · -- `⊆`: `p` is the cylinder point over its projection
    intro hp
    have hx : Work.K3.baseChangeAlongProj
        (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) X p
        ∈ exDiv φ :=
      exDiv_prodMap_subset k φ hp
    haveI hln : IsLocallyNoetherian X := isLocallyNoetherian_of_variety 𝕜 X
    set x := Work.K3.baseChangeAlongProj
      (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) X p
      with hxdef
    haveI hdx : IsDomain (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) X x k).tensor := hD x
    -- the projection of `p` is `x`
    have hsnd : pullback.snd (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘
        AlgebraicGeometry.Spec (CommRingCat.of 𝕜))
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) p = x := rfl
    -- `p` lies in the closure of the generic point of the fibre over `x`
    have hclos : p ∈ closure ({Work.CY3Stab.prodPt (𝕜 := 𝕜) X x k} :
        Set (Work.CY3Stab.WProd (𝕜 := 𝕜) X k)) := by
      have h := specTensorTo_bot_mem_closure (𝕜 := 𝕜) (n := Fin k) X x
        (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) X x k) rfl rfl p hsnd
      simpa only [Work.CY3Stab.prodPt] using h
    -- and the cylinder point has coheight one, `x` being an exceptional divisor
    have hqco : Order.coheight (Work.CY3Stab.prodPt (𝕜 := 𝕜) X x k) = 1 := by
      have h := coheight_specTensorTo_bot (𝕜 := 𝕜) (n := Fin k) X x
        (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) X x k) rfl rfl
      rw [Work.CY3Stab.prodPt, h]
      exact hx.1
    have hpeq : p = Work.CY3Stab.prodPt (𝕜 := 𝕜) X x k := by
      by_contra hne
      have hpq : (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) X x k).SpecTensorTo
          (⊥ : PrimeSpectrum (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) X x k).tensor) ⤳ p :=
        specializes_iff_mem_closure.mpr (by simpa only [Work.CY3Stab.prodPt] using hclos)
      have hp_le : p ≤ Work.CY3Stab.prodPt (𝕜 := 𝕜) X x k := by
        rw [Scheme.le_iff_specializes]
        simpa only [Work.CY3Stab.prodPt] using hpq
      have hnotle : ¬ (Work.CY3Stab.prodPt (𝕜 := 𝕜) X x k ≤ p) := by
        intro hle
        rw [Scheme.le_iff_specializes] at hle
        exact hne (inseparable_iff_eq.mp (inseparable_iff_specializes_and.mpr
          ⟨hle, by simpa only [Work.CY3Stab.prodPt] using hpq⟩))
      have hlt : p < Work.CY3Stab.prodPt (𝕜 := 𝕜) X x k := ⟨hp_le, hnotle⟩
      have hmono := Order.coheight_add_one_le hlt
      rw [hqco, hp.1] at hmono
      norm_num at hmono
    exact ⟨x, hx, hpeq.symm⟩
  · -- `⊇`: the cylinder point over an exceptional divisor is an exceptional divisor
    rintro ⟨x, hx, rfl⟩
    haveI : IsDomain (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) X x k).tensor := hD x
    exact prodPtGen_mem_exDiv 𝕜 k φ x hx

end

end Work.CY3Stab.Prod
