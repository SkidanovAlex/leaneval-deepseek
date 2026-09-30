import Mathlib
import Submission.Work.CurveBasics.Place.valuationSubring_ne_top
import Submission.Work.CurveBasics.Order.SumPrimesAux
import Submission.Work.CurveBasics.Order.valuationSubring_eq_atPrime
import Submission.Work.CurveBasics.Order.integralClosure_adjoin_finite_of_transcendental
import Submission.Work.CurveBasics.Place.mem_valuationSubring_iff
import Submission.Work.RiemannRoch.RR.riemann_exists_polynomial_ordAt_pos

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


open scoped IntermediateField.algebraAdjoinAdjoin

set_option linter.style.haveILetI false

namespace Work.CurveBasics.Order

/-- **Every element of the valuation subring at a place where `h` is regular is a fraction of
elements of `k[h]^int` with denominator outside the prime attached to the place.**

Let `C` be a curve over `k`, `h ∈ K(C)` transcendental with `[K(C) : k(h)]` finite, and let
`Q` be a place of `C` at which `h` is regular, i.e. `0 ≤ ord_Q h`.  Write `B = k[h]^int` for the
integral closure of `k[h] = k[h]` in `K(C)` and `q = B ∩ 𝔪_Q` for the prime of `B` attached to
`Q` (this is `kxPrimeOfPlace C h Q hQ`).  Then every `y` which is regular at `Q` can be written as
`y = b / s` with `b ∈ B` and `s ∈ B ∖ q`.

Equivalently, the valuation subring `𝒪_Q` is the localisation of the Dedekind domain `B` at the
prime `q`.  The proof splits on whether `q` is zero:

* if `q = ⊥` the statement is the trivial one that `K(C)` is the fraction field of `B`;
* otherwise `q` is a nonzero prime and
  `valuationSubring_eq_atPrime` identifies `𝒪_Q` with the localisation of `B` at `q`, whose
  elements are fractions `b * s⁻¹` with `s ∉ q`; this is applied through
  `IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer`.

The Dedekind hypothesis on `B` is supplied by the Japanese property of `k[h]`
(`ordClosure_finite_general`). -/
theorem kxPrimeOfPlace_fraction_of_nonneg {k : Type*} [Field k] (C : Work.CurveBasics.Curve k) (h : C.functionField)
    (hht : Transcendental k h)
    [FiniteDimensional (IntermediateField.adjoin k ({h} : Set C.functionField)) C.functionField]
    (Q : C.Place) (hQ : 0 ≤ C.ordAt h Q) (y : C.functionField) (hy : y ∈ Q.valuationSubring) :
    ∃ (b s : ↥(C.ordClosure h)), s ∉ Work.CurveBasics.kxPrimeOfPlace C h Q hQ ∧
      (s : C.functionField) * y = (b : C.functionField) := by
  classical
  -- `k[h]^int` is a finite `k[h]`-module, hence a Dedekind domain with fraction field `K(C)`.
  haveI hfin : Module.Finite (C.ordBase h) (C.ordClosure h) :=
    ordClosure_finite_general C h hht
  haveI hfr : IsFractionRing (C.ordClosure h) C.functionField :=
    IsIntegralClosure.isFractionRing_of_finite_extension (C.ordBase h)
      ↥(IntermediateField.adjoin k ({h} : Set C.functionField)) C.functionField (C.ordClosure h)
  haveI hDD : IsDedekindDomain (C.ordClosure h) := by
    haveI hdomA : IsDomain (C.ordBase h) := by
      have hinj : Function.Injective (algebraMap (C.ordBase h) C.functionField) :=
        fun a b hab => Subtype.ext hab
      exact Function.Injective.isDomain _ hinj
    haveI hdimA : Ring.DimensionLEOne (C.ordBase h) := by
      haveI : IsPrincipalIdealRing (C.ordBase h) := inferInstance
      exact Ring.DimensionLEOne.principal_ideal_ring _
    refine (isDedekindDomain_iff (A := C.ordClosure h) C.functionField).mpr
      ⟨inferInstance, IsNoetherianRing.of_finite (C.ordBase h) (C.ordClosure h), ?_, ?_⟩
    · exact Ring.DimensionLEOne.of_isIntegral (C.ordBase h) (C.ordClosure h)
    · intro x hx
      exact (IsIntegrallyClosedIn.isIntegral_iff (R := C.ordClosure h)
        (A := C.functionField)).mp hx
  by_cases hbot : Work.CurveBasics.kxPrimeOfPlace C h Q hQ = ⊥
  · -- the prime is zero: the fraction field presentation of `K(C)` over `B` suffices
    obtain ⟨⟨b, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors (C.ordClosure h)) y
    refine ⟨b, (s : C.ordClosure h), ?_, ?_⟩
    · rw [hbot, Ideal.mem_bot]
      exact mem_nonZeroDivisors_iff_ne_zero.mp s.2
    · rw [mul_comm]
      simpa using hs
  · -- the prime is nonzero: `𝒪_Q` is the localisation of the Dedekind domain `B` at it
    set q : Ideal (C.ordClosure h) := Work.CurveBasics.kxPrimeOfPlace C h Q hQ with hqdef
    have hqprime : q.IsPrime := Work.CurveBasics.kxPrimeOfPlace_isPrime C h Q hQ
    have hle : (C.ordClosure h).toSubring ≤ Q.valuationSubring.toSubring :=
      kxClosure_le_valuationSubring C h Q hQ
    let φ : (C.ordClosure h) →+* ↥(Q.valuationSubring) := Subring.inclusion hle
    have hφ : ∀ a : C.ordClosure h, (φ a : C.functionField) =
        algebraMap (C.ordClosure h) C.functionField a := fun a => Subring.coe_inclusion hle a
    have hcenter : Ideal.comap φ (IsLocalRing.maximalIdeal ↥(Q.valuationSubring)) = q := rfl
    have hW := valuationSubring_eq_atPrime q hqprime hbot
      (Place.valuationSubring_ne_top Q) φ hφ hcenter
    have hyW : y ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime C.functionField
        ⟨q, hqprime, hbot⟩ := by
      rw [← hW]; exact hy
    have hv : (IsDedekindDomain.HeightOneSpectrum.valuation C.functionField
        ⟨q, hqprime, hbot⟩) y ≤ 1 := by
      refine (Valuation.mem_valuationSubring_iff _ y).mp ?_
      rw [← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      exact hyW
    obtain ⟨n, d, hnd⟩ := IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer
        ⟨q, hqprime, hbot⟩ y hv
    refine ⟨n, (d : C.ordClosure h), ?_, ?_⟩
    · exact Ideal.mem_primeCompl_iff.mp d.2
    · rw [mul_comm]; simpa using hnd

end Work.CurveBasics.Order
