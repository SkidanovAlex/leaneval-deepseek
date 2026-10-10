import Submission.Work.MotK.TGen.FwVec4Defs
import Submission.Work.MotK.TGen.FwVec4ParamClean
import Submission.Work.MotK.TGen.FwVec4Prime2
import Submission.Work.MotK.TGen.FwVec4Height2
import Submission.Work.MotK.TGen.FwVec4FracRange
import Submission.Work.MotK.TGen.FwVec4ResF

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.FwVec4Rational` — the quartic `f̂₄ = fwVec a b h 4` is a rational (junk) divisor

`fwVec a b h 4 = f̂₄` is the fourth component of the forward link map `f = kleinTwP ∘ kleinTwStereo`
of the `T`-twisted Crauder–Katz link on the affine chart `chart3 = ![0, x₀, x₁, x₂, 1]`; it is the
denominator of the affine coordinates of `f`, so that `{f̂₄ = 0}` is the preimage of the hyperplane
at infinity of the target chart.  The parametrisation of that surface is the inverse link map
`χ = π_p ∘ kleinTwR` restricted to the target plane `{w₀ = 0, w₄ = 0}`, read in the chart `w₃ = 1`
of that plane with coordinates `u, v` (definitions in `Work.MotK.TGen.FwVec4Defs`).

## The proof

* `FwVec4ParamClean` — the identities of the composite `f ∘ χ = λ · id` at the plane
  (`Work.MotK.KleinTwLinkComp1`): `θ f̂₄ = 0`, `θ f̂₃ ≠ 0`, `u · θ f̂₃ = θ f̂₁`, `v · θ f̂₃ = θ f̂₂`;
* `FwVec4FracRange` — hence the fraction field of the range of `θ` is `K(u,v)`, so that `θ`
  presents a two-dimensional domain;
* `FwVec4Height2` — the kernel of `θ` therefore has height `3 - trdeg_K K(u,v) = 1`;
* `FwVec4Prime2` — `f̂₄` is irreducible, equivalently prime in the UFD `K[x₀,x₁,x₂]`, so that
  `(f̂₄)` is a height-one prime;
* the two height-one primes `(f̂₄) ⊆ ker θ` coincide (`Work.MotK.CensusPrime.eq_span_of_height_one`);
* `FwVec4ResF` — the residue field of the principal prime `(f̂₄)` is the fraction field of the
  range of `θ`, i.e. `K(u,v) = RatFunc (RatFunc K)`.

Everything is characteristic-free and holds for all `a b h ≠ 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace Work.MotK.TGen

open MvPolynomial

theorem FwVec4Rational (K : Type) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    ∃ hpr : (Ideal.span {Work.MotK.TGen.fwVec a b h 4} :
        Ideal (MvPolynomial (Fin 3) K)).IsPrime,
      Ideal.height (Ideal.span {Work.MotK.TGen.fwVec a b h 4} :
        Ideal (MvPolynomial (Fin 3) K)) = 1 ∧
      Nonempty (Work.MotV.resF K ⟨Ideal.span {Work.MotK.TGen.fwVec a b h 4}, hpr⟩ ≃ₐ[K]
        RatFunc (RatFunc K)) := by
  obtain ⟨hp4, hp3, hp1, hp2⟩ := FwVec4ParamClean a b h ha hb hh
  have hirr : Irreducible (Work.MotK.TGen.fwVec a b h 4) := FwVec4Prime2 a b h ha hb hh
  have hprim : Prime (Work.MotK.TGen.fwVec a b h 4) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  have hF0 : Work.MotK.TGen.fwVec a b h 4 ≠ 0 := hprim.ne_zero
  have hspan_prime :
      (Ideal.span {Work.MotK.TGen.fwVec a b h 4} :
        Ideal (MvPolynomial (Fin 3) K)).IsPrime :=
    (Ideal.span_singleton_prime hF0).mpr hprim
  have hspan_height :
      Ideal.height (Ideal.span {Work.MotK.TGen.fwVec a b h 4} :
        Ideal (MvPolynomial (Fin 3) K)) = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hF0) hprim.not_isUnit
  have hheight : (RingHom.ker (Work.MotK.TGen.fwTheta a b h)).height = 1 :=
    FwVec4Height2 a b h ha hb hh hp4 hp3 hp1 hp2
  have hker : RingHom.ker (Work.MotK.TGen.fwTheta a b h) =
      Ideal.span {Work.MotK.TGen.fwVec a b h 4} := by
    haveI : (RingHom.ker (Work.MotK.TGen.fwTheta a b h)).IsPrime := RingHom.ker_isPrime _
    refine Work.MotK.CensusPrime.eq_span_of_height_one (Work.MotK.TGen.fwVec a b h 4)
      hspan_prime hspan_height (RingHom.ker (Work.MotK.TGen.fwTheta a b h)) hheight ?_
    rw [RingHom.mem_ker]
    exact hp4
  obtain ⟨e⟩ := FwVec4FracRange a b h ha hb hh hp3 hp1 hp2
  exact ⟨hspan_prime, hspan_height, FwVec4ResF a b h hspan_prime hker e⟩

end Work.MotK.TGen
