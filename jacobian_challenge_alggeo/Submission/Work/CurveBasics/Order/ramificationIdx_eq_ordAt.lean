import Mathlib
import Submission.Work.CurveBasics.Order.Bridge
import Submission.Work.CurveBasics.Place.mem_valuationSubring_iff
import Submission.Work.CurveBasics.Order.RamifIdxSetup
import Submission.Work.CurveBasics.Order.finiteDimensional_adjoin_functionField
import Submission.Work.CurveBasics.Order.isNoetherianRing_integralClosure_of_isFractionRing
import Submission.Work.CurveBasics.Order.kxPrimeOfPlace_liesOver
import Submission.Work.CurveBasics.Order.valuation_eq_of_surjective_of_valuationSubring_eq
import Submission.Work.CurveBasics.Order.valuationSubring_eq_atPrime
import Submission.Work.CurveBasics.Order.ramificationIdx_eq_neg_log_valuation

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# The ramification index of the prime of `k[x]^int` at a zero of `x`

Let `C` be a smooth proper geometrically irreducible curve over a field `k`, let `x ∈ K(C)` be
transcendental over `k`, let `Q` be a place at which `x` vanishes and let
`q = k[x]^int ∩ 𝔪_Q` be the prime of the integral closure `B = k[x]^int` of `k[x]` attached to
`Q`.  This file proves that the ramification index of `q` over `k[x]` is the order of vanishing
of `x` at `Q`:

`ramificationIdx_eq_ordAt : e(q | (x)) = ord_Q x`.

The proof has two halves.

* `ramificationIdx_eq_neg_log_valuation` (imported): the ramification index is `- log V x`,
  where `V` is the `q`-adic valuation of `K(C)`, viewed as a height one prime valuation of `B`
  (`V x = exp (-(e : ℤ))`).
* The `q`-adic valuation subring of `K(C)` is the valuation subring of the place `Q`: indeed
  `k[x]^int ⊆ Q.valuationSubring` (`kxClosure_le_valuationSubring`), the contraction of the
  maximal ideal of `Q.valuationSubring` along this inclusion is `q` by definition of
  `kxPrimeOfPlace`, so `valuationSubring_eq_atPrime` (proved for an arbitrary Dedekind domain
  contained in a field, with a proper target valuation subring) gives
  `Q.valuationSubring = valuationSubringAtPrime K q = V.valuationSubring`, i.e. the two
  valuation subrings agree.  Since both valuations are surjective onto `ℤᵐ⁰`
  (`HeightOneSpectrum.valuation_surjective` on the Dedekind side and the same statement for the
  discrete valuation ring `𝒪_Q` on the geometric side),
  `valuation_eq_of_surjective_of_valuationSubring_eq` gives `V = Q.valuation`, and hence
  `-(V x).log = -(Q.valuation x).log = ord_Q x` (`Curve.Place.ord_eq_neg_log_valuation`).
-/

open scoped Classical IntermediateField.algebraAdjoinAdjoin
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open CategoryTheory Limits AlgebraicGeometry Polynomial IntermediateField

namespace Work.CurveBasics.Order

open Work.CurveBasics

open Work.CurveBasics in
/-- **Auxiliary form.**  The ramification index of the prime of `k[x]^int` attached to a place at
which `x` vanishes equals the order of vanishing of `x` there, assuming that the integral
closure of `k[x]` in `K(C)` is Noetherian (which holds for any transcendental `x` by
Krull–Akizuki for the PID `k[x]`, see
`Work.CurveBasics.Order.isNoetherianRing_integralClosure_of_isFractionRing`). -/
theorem ramificationIdx_eq_ordAt_of_noetherian {k : Type*} [Field k] (C : Curve k)
    (x : C.functionField) (hx : Transcendental k x) (Q : C.Place) (hQ : 0 < C.ordAt x Q)
    [IsNoetherianRing ↥(kxInt C x)] :
    ((kxPrimeOfPlace C x Q hQ.le).ramificationIdx ↥(Algebra.adjoin k ({x} : Set C.functionField)) : ℤ)
      = C.ordAt x Q := by
  classical
  -- the integral closure of `k[x]` in `K(C)` is a Dedekind domain
  haveI hFindim : FiniteDimensional ↥(IntermediateField.adjoin k ({x} : Set C.functionField))
      C.functionField := finiteDimensional_adjoin_functionField C hx
  haveI hFrac : IsFractionRing ↥(kxInt C x) C.functionField :=
    IsIntegralClosure.isFractionRing_of_finite_extension
      ↥(Algebra.adjoin k ({x} : Set C.functionField))
      ↥(IntermediateField.adjoin k ({x} : Set C.functionField))
      C.functionField
      ↥(kxInt C x)
  haveI hDed : IsDedekindDomain ↥(kxInt C x) := by
    rw [isDedekindDomain_iff (↥(kxInt C x)) C.functionField]
    refine ⟨inferInstance, ‹IsNoetherianRing ↥(kxInt C x)›,
      Ring.DimensionLEOne.of_isIntegral ↥(Algebra.adjoin k ({x} : Set C.functionField))
        ↥(kxInt C x), ?_⟩
    intro y hy
    exact ⟨⟨y, isIntegral_trans (R := ↥(Algebra.adjoin k ({x} : Set C.functionField))) y hy⟩, rfl⟩
  -- the local ring of the curve at `Q` is a discrete valuation ring, so `Q.valuation` is a
  -- height one prime valuation of a Dedekind domain and in particular surjective
  haveI hDVR : IsDiscreteValuationRing (C.left.presheaf.stalk Q.point) :=
    Work.CurveBasics.Place.isDiscreteValuationRing Q
  have hqprime := kxPrimeOfPlace_isPrime C x Q hQ.le
  have hqne := kxPrimeOfPlace_ne_bot C x hx Q hQ
  -- `Q.valuationSubring` is a proper valuation subring
  have hWne : Q.valuationSubring ≠ ⊤ := by
    intro htop
    have hnt : Q.valuation.IsNontrivial := by
      have h : Q.valuation = IsDedekindDomain.HeightOneSpectrum.valuation C.functionField
          (IsDiscreteValuationRing.maximalIdeal (C.left.presheaf.stalk Q.point)) := rfl
      rw [h]
      infer_instance
    exact (Valuation.valuationSubring_eq_top_iff (Q.valuation)).mp htop hnt
  -- the centre of `Q.valuationSubring` on `k[x]^int` is `q`, by definition of `kxPrimeOfPlace`
  have hcenter : Ideal.comap (Subring.inclusion (kxClosure_le_valuationSubring C x Q hQ.le))
      (IsLocalRing.maximalIdeal ↥(Q.valuationSubring)) = kxPrimeOfPlace C x Q hQ.le := rfl
  -- hence `Q.valuationSubring` is the localisation of `k[x]^int` at `q`
  have hval_eq : Q.valuationSubring
      = (IsDedekindDomain.HeightOneSpectrum.valuation C.functionField
          (kxHeightOne C x hx Q hQ)).valuationSubring := by
    rw [valuationSubring_eq_atPrime (p := kxPrimeOfPlace C x Q hQ.le) hqprime hqne hWne
      (Subring.inclusion (kxClosure_le_valuationSubring C x Q hQ.le)) (fun a => rfl) hcenter]
    exact IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring
      (kxHeightOne C x hx Q hQ)
  -- both valuations are surjective
  have hVsurj : Function.Surjective (IsDedekindDomain.HeightOneSpectrum.valuation
      C.functionField (kxHeightOne C x hx Q hQ)) :=
    IsDedekindDomain.HeightOneSpectrum.valuation_surjective C.functionField _
  have hWsurj : Function.Surjective Q.valuation := by
    have h : Q.valuation = IsDedekindDomain.HeightOneSpectrum.valuation C.functionField
        (IsDiscreteValuationRing.maximalIdeal (C.left.presheaf.stalk Q.point)) := rfl
    rw [h]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_surjective C.functionField _
  -- hence the two valuations coincide
  have hVW : IsDedekindDomain.HeightOneSpectrum.valuation C.functionField (kxHeightOne C x hx Q hQ)
      = Q.valuation :=
    valuation_eq_of_surjective_of_valuationSubring_eq _ _ hVsurj hWsurj hval_eq.symm
  -- the ramification index is the order of vanishing
  have h1 := ramificationIdx_eq_neg_log_valuation C x hx Q hQ
  calc ((kxPrimeOfPlace C x Q hQ.le).ramificationIdx
        ↥(Algebra.adjoin k ({x} : Set C.functionField)) : ℤ)
      = -(IsDedekindDomain.HeightOneSpectrum.valuation C.functionField
          (kxHeightOne C x hx Q hQ) x).log := h1
    _ = -(Q.valuation x).log := by rw [hVW]
    _ = C.ordAt x Q := (Curve.Place.ord_eq_neg_log_valuation C Q x).symm

open Work.CurveBasics in
/-- The ramification index of the prime of `k[x]^int` at a place where `x` vanishes is the order
of vanishing of `x` at that place. -/
theorem ramificationIdx_eq_ordAt {k : Type*} [Field k] (C : Curve k) (x : C.functionField)
    (hx : Transcendental k x) (Q : C.Place) (hQ : 0 < C.ordAt x Q) :
    ((kxPrimeOfPlace C x Q hQ.le).ramificationIdx ↥(Algebra.adjoin k ({x} : Set C.functionField)) : ℤ)
      = C.ordAt x Q := by
  -- Krull–Akizuki for the PID `k[x]`: the integral closure of `k[x]` in `K(C)` is Noetherian
  haveI hfd : FiniteDimensional ↥(IntermediateField.adjoin k ({x} : Set C.functionField))
      C.functionField := finiteDimensional_adjoin_functionField C hx
  haveI hN : IsNoetherianRing ↥(kxInt C x) :=
    isNoetherianRing_integralClosure_of_isFractionRing
      (A := ↥(Algebra.adjoin k ({x} : Set C.functionField)))
      (K := ↥(IntermediateField.adjoin k ({x} : Set C.functionField))) (L := C.functionField)
  exact ramificationIdx_eq_ordAt_of_noetherian C x hx Q hQ

end Work.CurveBasics.Order
