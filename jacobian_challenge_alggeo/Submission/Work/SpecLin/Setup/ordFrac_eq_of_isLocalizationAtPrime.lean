import Mathlib
import Submission.Work.SpecLin.Alt.ordIso

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.style.haveILetI false

namespace Work.SpecLin.Setup

universe u

/-- **The order of vanishing is the same for two presentations of the same localisation.**
`S` and `T` are two localisations of the domain `A` at the same prime `P` (e.g. the localisation
`A_P` and the stalk of `Spec A` at `P`), each sitting inside the same fraction field `K` of `A`
as a fraction ring.  Then the order functions `Ring.ordFrac` computed in `S` and in `T` agree.

This is the bridge used to compute orders of vanishing of rational functions on a curve in terms
of the coordinate ring of an affine chart: `Scheme.ord` at a point is `Ring.ordFrac` of the
*stalk*, and this result identifies it with `Ring.ordFrac` of the corresponding *localisation of
the coordinate ring*.

Proof (suggested).  `IsLocalization.algEquiv P.primeCompl S T` is an `A`-algebra isomorphism
`φ : S ≃ₐ[A] T`.  Both `algebraMap S K` and `algebraMap T K ∘ φ` are `A`-algebra maps `S → K`
(`IsScalarTower` gives compatibility on the image of `A`), so they are equal by
`IsLocalization.ringHom_ext`.  `Ring.ordMonoidWithZeroHom` is invariant under ring
isomorphisms (`Work.SpecLin.Alt.ordMonoidWithZeroHom_ringEquiv`), and `Ring.ordFrac` is the
localisation of `ordMonoidWithZeroHom`, so the two `ordFrac` monoid-with-zero homs agree on the
common fraction field `K`; conclude by `MonoidWithZeroHom.ext`.  Alternatively use
`Work.SpecLin.Alt.ordFrac_ringEquiv` (in `Submission/Work/SpecLin/Alt/ordIso.lean`) with
`φ` and `ψ := RingHom.id K`. -/
theorem ordFrac_eq_of_isLocalizationAtPrime {A S T K : Type u} [CommRing A] [IsDomain A]
    (P : Ideal A) [P.IsPrime] [CommRing S] [Algebra A S] [IsLocalization.AtPrime S P]
    [CommRing T] [Algebra A T] [IsLocalization.AtPrime T P]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra S K] [IsScalarTower A S K] [Algebra T K] [IsScalarTower A T K]
    [IsFractionRing S K] [IsFractionRing T K] [Nontrivial S] [Nontrivial T]
    [IsNoetherianRing S] [Ring.KrullDimLE 1 S] [IsNoetherianRing T] [Ring.KrullDimLE 1 T] :
    Ring.ordFrac (K := K) S = Ring.ordFrac (K := K) T := by
  -- Both `S` and `T` are localisations of the domain `A` at the prime `P`, hence domains.
  have hSdom : IsDomain S := IsLocalization.isDomain_of_atPrime S P
  have hTdom : IsDomain T := IsLocalization.isDomain_of_atPrime T P
  letI : IsDomain S := hSdom
  letI : IsDomain T := hTdom
  -- The `A`-algebra isomorphism between the two localisations.
  let φ : T ≃ₐ[A] S := (IsLocalization.algEquiv P.primeCompl S T).symm
  -- The two structure maps `T → K` agree: both are ring homs out of the localisation `T`
  -- which agree on the image of `A`.
  have hψ : ∀ t : T, algebraMap T K t = algebraMap S K (φ t) := fun t => by
    have h : (algebraMap T K : T →+* K) = (algebraMap S K).comp φ.toRingHom := by
      refine IsLocalization.ringHom_ext P.primeCompl ?_
      have hφ : φ.toRingHom.comp (algebraMap A T) = algebraMap A S :=
        RingHom.ext fun a => AlgEquiv.commutes φ a
      rw [RingHom.comp_assoc, hφ]
      exact (IsScalarTower.algebraMap_eq A T K).symm.trans (IsScalarTower.algebraMap_eq A S K)
    exact RingHom.congr_fun h t
  -- Since `Ring.ordFrac` is natural under compatible ring isomorphisms
  -- (`Work.SpecLin.Alt.ordFrac_ringEquiv`), the two monoid-with-zero homs on `K` coincide.
  exact MonoidWithZeroHom.ext fun x =>
    Work.SpecLin.Alt.ordFrac_ringEquiv φ.toRingEquiv (RingHom.id K) hψ x

end Work.SpecLin.Setup
