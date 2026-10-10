import Mathlib
import Submission.Work.MotK.TGen.FwVec4Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.FwVec4ResF` — the residue field at the divisor `⟨f̂₄⟩` is `RatFunc (RatFunc K)`

The point `x := ⟨(f̂₄), hprime⟩` of `𝔸³_K`, where `f̂₄ = fwVec a b h 4` is the fourth component of
the forward link map of the `T`-twisted Crauder–Katz link (see
`Submission/Work/MotK/TGen/FwVec4Rational.lean`), has residue field `κ(x) = K[x₀,x₁,x₂]/(f̂₄)`.

The point of this file is *bookkeeping*: once one knows

* that `(f̂₄)` is prime (`hprime`),
* that `(f̂₄)` is exactly the kernel of the parametrisation map
  `fwTheta a b h : K[x₀,x₁,x₂] →ₐ[K] K(u,v)` (`hker`), and
* that the fraction field of the image of `fwTheta a b h` is `K(u)(v) = RatFunc (RatFunc K)`
  (`e`),

then the residue field `resF K x` of `x` is `RatFunc (RatFunc K)` — i.e. `x` is a *junk* divisor:
the "surface" `{f̂₄ = 0}` is a rational surface, so its generic point carries no information.

The formal content is the first isomorphism theorem for the *surjective* map
`AlgHom.rangeRestrict (fwTheta a b h)` (whose codomain is the range of `fwTheta a b h`, so that
`Ideal.quotientKerAlgEquivOfSurjective` applies without assuming `fwTheta` itself surjective),
composed with the transport of fraction rings along an isomorphism of `K`-algebras
(`IsFractionRing.algEquivOfAlgEquiv`).
-/

namespace Work.MotK.TGen

/-- **The residue field at the kernel of an algebra homomorphism.**

For a `K`-algebra homomorphism `f : R →ₐ[K] S` into a domain `S`, the fraction ring of the quotient
of `R` by the kernel of `f` is the fraction ring of the range of `f`.

This is `Ideal.quotientKerAlgEquivOfSurjective` applied to the *surjective* map
`f.rangeRestrict : R →ₐ[K] f.range` (which has the same kernel as `f`, `AlgHom.ker_rangeRestrict`),
transported to fraction rings by `IsFractionRing.algEquivOfAlgEquiv`. -/
theorem fractionRing_quotient_ker_algEquiv {K R S : Type} [Field K] [CommRing R] [Algebra K R]
    [CommRing S] [IsDomain S] [Algebra K S] (f : R →ₐ[K] S) :
    Nonempty (FractionRing (R ⧸ RingHom.ker f) ≃ₐ[K] FractionRing f.range) := by
  have i : (R ⧸ RingHom.ker f) ≃ₐ[K] ↥f.range :=
    (AlgHom.ker_rangeRestrict f).symm ▸
      Ideal.quotientKerAlgEquivOfSurjective (AlgHom.rangeRestrict_surjective f)
  exact ⟨IsFractionRing.algEquivOfAlgEquiv i⟩

theorem FwVec4ResF {K : Type} [Field K] (a b h : K)
    (hprime : (Ideal.span {Work.MotK.TGen.fwVec a b h 4} :
        Ideal (MvPolynomial (Fin 3) K)).IsPrime)
    (hker : RingHom.ker (Work.MotK.TGen.fwTheta a b h) =
        Ideal.span {Work.MotK.TGen.fwVec a b h 4})
    (e : FractionRing (Work.MotK.TGen.fwTheta a b h).range ≃ₐ[K] RatFunc (RatFunc K)) :
    Nonempty (Work.MotV.resF K
        ⟨Ideal.span {Work.MotK.TGen.fwVec a b h 4}, hprime⟩ ≃ₐ[K] RatFunc (RatFunc K)) := by
  -- the residue field of the point is the fraction ring of the quotient `K[x₀,x₁,x₂] ⧸ ker fwTheta`
  have key : Nonempty (Work.MotV.resF K
      ⟨Ideal.span {Work.MotK.TGen.fwVec a b h 4}, hprime⟩ ≃ₐ[K]
        FractionRing (Work.MotK.TGen.fwTheta a b h).range) := by
    have i : (MvPolynomial (Fin 3) K ⧸ RingHom.ker (Work.MotK.TGen.fwTheta a b h)) ≃ₐ[K]
        ↥(Work.MotK.TGen.fwTheta a b h).range :=
      (AlgHom.ker_rangeRestrict (Work.MotK.TGen.fwTheta a b h)).symm ▸
        Ideal.quotientKerAlgEquivOfSurjective
          (AlgHom.rangeRestrict_surjective (Work.MotK.TGen.fwTheta a b h))
    rw [hker] at i
    exact ⟨IsFractionRing.algEquivOfAlgEquiv i⟩
  obtain ⟨g⟩ := key
  exact ⟨g.trans e⟩

end Work.MotK.TGen
