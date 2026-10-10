import Mathlib
import Submission.Work.Motivic.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Coheight does not increase along a flat morphism

For a flat morphism of schemes `f : X ⟶ Y` and a point `x : X`, the coheight of the image point
`f x` is at most the coheight of `x`:

`Order.coheight (f x) ≤ Order.coheight x`.

Here `Order.coheight` is taken with respect to the specialisation order on the points of a scheme.
Since `Order.coheight z = ↑(ringKrullDim (X.presheaf.stalk z))`
(`AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`), the statement is the local statement

`dim O_{Y,f x} ≤ dim O_{X,x}`

for the (flat, local) stalk map `O_{Y,f x} ⟶ O_{X,x}`.  That in turn is the usual
"flat ⟹ going down" dimension inequality: every chain of primes ending at the maximal ideal of
`O_{Y,f x}` lifts, by going down, to a chain of the same length ending at the maximal ideal of
`O_{X,x}` (which lies over it, because the stalk map is local).
-/

set_option linter.style.haveILetI false

namespace Work.K3

open CategoryTheory AlgebraicGeometry

/-- **Dimension inequality for flat local homomorphisms.**  If `φ : A →+* B` is a flat local
homomorphism of local rings, then `ringKrullDim A ≤ ringKrullDim B`.

Flatness gives going-down (`Algebra.HasGoingDown.of_flat`); a chain of primes of `A` ending at the
maximal ideal `m_A` then lifts to a chain of the same length in `B` ending at any prime lying over
`m_A` (`Ideal.exists_ltSeries_of_hasGoingDown`), and the maximal ideal `m_B` of `B` lies over `m_A`
because `φ` is local (`IsLocalRing.maximalIdeal_comap`). -/
theorem ringKrullDim_le_of_flat_localRingHom {A B : Type} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (φ : A →+* B) [IsLocalHom φ] (hφ : φ.Flat) :
    ringKrullDim A ≤ ringKrullDim B := by
  letI : Algebra A B := φ.toAlgebra
  have hflat : Module.Flat A B := hφ
  haveI : Algebra.HasGoingDown A B := Algebra.HasGoingDown.of_flat
  -- The maximal ideal of `A` is minimal in `PrimeSpectrum A` (which carries the inclusion order),
  -- so it suffices to bound the length of chains ending exactly at it.
  have key : Order.height (⟨IsLocalRing.maximalIdeal A, inferInstance⟩ : PrimeSpectrum A)
      ≤ Order.height (⟨IsLocalRing.maximalIdeal B, inferInstance⟩ : PrimeSpectrum B) := by
    rw [Order.height_eq_iSup_last_eq]
    refine iSup₂_le fun l hl => ?_
    -- The maximal ideal of `B` lies over the maximal ideal of `A`.
    haveI : (IsLocalRing.maximalIdeal B).LiesOver l.last.asIdeal := by
      rw [hl]
      refine ⟨?_⟩
      rw [Ideal.under_def, RingHom.algebraMap_toAlgebra]
      exact (IsLocalRing.maximalIdeal_comap φ).symm
    obtain ⟨L, hlen, hlastL, -⟩ :=
      Ideal.exists_ltSeries_of_hasGoingDown l (IsLocalRing.maximalIdeal B)
    rw [← hlen]
    exact Order.length_le_height (le_of_eq hlastL)
  have key' : (IsLocalRing.maximalIdeal A).height ≤ (IsLocalRing.maximalIdeal B).height := by
    rw [PrimeSpectrum.height_eq_orderHeight (⟨_, inferInstance⟩ : PrimeSpectrum A),
      PrimeSpectrum.height_eq_orderHeight (⟨_, inferInstance⟩ : PrimeSpectrum B)]
    exact key
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A),
      ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := B)]
  exact WithBot.coe_le_coe.mpr key'

/-- Coheight does not increase along a flat morphism: for a flat `f : X ⟶ Y` and `x : X`,
`coheight (f x) ≤ coheight x`.  This is the local dimension inequality for the flat stalk map
`O_{Y,f x} ⟶ O_{X,x}` transported through `ringKrullDim_stalk_eq_coheight`. -/
theorem coheight_le_of_flat {X Y : AlgebraicGeometry.Scheme.{0}} (f : X ⟶ Y)
    [AlgebraicGeometry.Flat f] (x : X) :
    Order.coheight (f x) ≤ Order.coheight x := by
  suffices h : (↑(Order.coheight (f x)) : WithBot ℕ∞) ≤ ↑(Order.coheight x) from
    WithBot.coe_le_coe.mp h
  rw [← ringKrullDim_stalk_eq_coheight (f x), ← ringKrullDim_stalk_eq_coheight x]
  exact ringKrullDim_le_of_flat_localRingHom (f.stalkMap x).hom (Flat.stalkMap f x)

end Work.K3
