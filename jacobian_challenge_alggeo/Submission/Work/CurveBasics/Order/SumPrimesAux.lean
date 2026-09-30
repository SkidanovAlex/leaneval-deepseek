/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Separability-free bridge between the zeros of `x` and the primes of `k[x]^int` over `(x)`

Let `C` be a curve over a field `k`, let `x ∈ K(C)` be transcendental over `k` with `[K(C) : k(x)]`
finite, and put `A = k[x]`, `B = k[x]^int ⊆ K(C)` (the two finiteness hypotheses are
`FiniteDimensional` and `Module.Finite` below; note `Module.Finite` is *not* automatic in
characteristic `p`, where `K(C)/k(x)` can be inseparable).

This file proves, without any separability hypothesis, that the map

  `Q ↦ kxPrimeOfPlace C x Q = B ∩ 𝔪_Q`

is a bijection from the places `Q` at which `x` vanishes onto the primes of `B` lying over `(x)`:

* `Order.spso_dedekind` : `B` is a Dedekind domain;
* `Order.spso_isFractionRing` : `K(C)` is the fraction field of `B`;
* `Order.spso_val_eq_atPrime` : the valuation subring `𝒪_Q` is
  `IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K (B ∩ 𝔪_Q)`;
* `Order.spso_inj` : `Q ↦ B ∩ 𝔪_Q` is injective;
* `Order.spso_surj` : `Q ↦ B ∩ 𝔪_Q` is surjective onto the primes over `(x)`.

The proofs are the separability-free counterparts of
`Work.CurveBasics.Order.kxPrimeOfPlace_injective` and
`Work.CurveBasics.Order.kxPrimeOfPlace_surjective`; the only change is that the Dedekindness and
fraction-ring structures of `B` are obtained from `Module.Finite` and `FiniteDimensional`
(`isDedekindDomain_iff`, `IsNoetherianRing.of_finite`, `Ring.DimensionLEOne.of_isIntegral`,
`integralClosure.isIntegrallyClosedOfFiniteExtension`,
`integralClosure.isFractionRing_of_finite_extension`) rather than from separability.
-/
import Mathlib
import Submission.Work.CurveBasics.Order.Setup
import Submission.Work.CurveBasics.Order.ordPosSetup
import Submission.Work.CurveBasics.Order.Bridge
import Submission.Work.CurveBasics.Order.kxPrimeOfPlace_liesOver
import Submission.Work.CurveBasics.Order.RamifIdxSetup
import Submission.Work.CurveBasics.Order.valuationSubring_eq_atPrime
import Submission.Work.CurveBasics.Place.place_eq_of_valuationSubring_eq
import Submission.Work.CurveBasics.Place.exists_place_of_valuationSubring
import Submission.Work.CurveBasics.Place.mem_valuationSubring_iff
import Submission.Work.CurveBasics.Place.isDiscreteValuationRing
import Submission.Work.CurveBasics.Order.finiteDimensional_adjoin_functionField
import Submission.Work.CurveBasics.Order.valuation_eq_of_surjective_of_valuationSubring_eq
import Submission.Work.CurveBasics.Order.ramificationIdx_eq_neg_log_valuation

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


open Work.CurveBasics
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical IntermediateField.algebraAdjoinAdjoin
set_option maxHeartbeats 1000000

namespace Work.CurveBasics.Order

open Work.CurveBasics

variable {k : Type*} [Field k] (C : Curve k) (x : C.functionField) (hx : Transcendental k x)
  [FiniteDimensional (IntermediateField.adjoin k ({x} : Set C.functionField)) C.functionField]
  [Module.Finite (C.ordBase x) (C.ordClosure x)]

/-- **The integral closure `k[x]^int` is a Dedekind domain**, assuming only that it is a finite
`k[x]`-module (`k[x]` is a PID, so it suffices to add Noetherianity, Krull dimension ≤ 1 and
integral closedness, all of which are separately available without separability). -/
theorem spso_dedekind : IsDedekindDomain (Curve.kxClosure C x) := by
  haveI hnoeth : IsNoetherianRing ↥(C.ordClosure x) :=
    IsNoetherianRing.of_finite ↥(C.ordBase x) ↥(C.ordClosure x)
  haveI hint : IsIntegrallyClosed ↥(C.ordClosure x) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (K :=
      ↥(IntermediateField.adjoin k ({x} : Set C.functionField)))
  exact (isDedekindDomain_iff ↥(C.ordClosure x) (FractionRing ↥(C.ordClosure x))).mpr
    ⟨inferInstance, hnoeth, inferInstance, (isIntegrallyClosed_iff _).mp hint⟩

/-- **`K(C)` is the fraction field of `k[x]^int`** (no separability needed). -/
theorem spso_isFractionRing : IsFractionRing (Curve.kxClosure C x) C.functionField :=
  integralClosure.isFractionRing_of_finite_extension (A := ↥(C.ordBase x))
    (K := ↥(IntermediateField.adjoin k ({x} : Set C.functionField))) (L := C.functionField)

/-- At a place where `x` vanishes the valuation ring `𝒪_Q` is a proper subring of `K(C)`
(because `x ∈ 𝒪_Q` but `x⁻¹ ∉ 𝒪_Q`). -/
lemma spso_val_ne_top (hx : Transcendental k x) {Q : C.Place} (hQ : 0 < C.ordAt x Q) :
    Q.valuationSubring ≠ ⊤ := by
  intro hV
  have hx0 : x ≠ 0 := fun h => hx (h ▸ isAlgebraic_zero)
  have hxmem : x ∈ Q.valuationSubring := by
    rw [Place.mem_valuationSubring_iff]
    change 0 ≤ C.ordAt x Q
    linarith
  have hinv : x⁻¹ ∈ Q.valuationSubring := by rw [hV]; trivial
  rw [Place.mem_valuationSubring_iff] at hinv
  change 0 ≤ C.ordAt x⁻¹ Q at hinv
  rw [C.ordAt_inv hx0] at hinv
  linarith

/-- **The prime `B ∩ 𝔪_Q` determines the valuation ring.**  For a place `Q` at which `x` vanishes,
the valuation ring `𝒪_Q` is the localization of the Dedekind domain `B = k[x]^int` at the nonzero
prime `q = B ∩ 𝔪_Q`, i.e. the valuation subring `valuationSubringAtPrime` of the `q`-adic
valuation. -/
lemma spso_val_eq_atPrime [IsDedekindDomain (Curve.kxClosure C x)]
    [IsFractionRing (Curve.kxClosure C x) C.functionField]
    (hx : Transcendental k x) {Q : C.Place} (hQ : 0 < C.ordAt x Q) :
    Q.valuationSubring =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime C.functionField
        ⟨kxPrimeOfPlace C x Q hQ.le, kxPrimeOfPlace_isPrime C x Q hQ.le,
          kxPrimeOfPlace_ne_bot C x hx Q hQ⟩ := by
  exact Work.CurveBasics.Order.valuationSubring_eq_atPrime (A := Curve.kxClosure C x)
    (K := C.functionField) (p := kxPrimeOfPlace C x Q hQ.le)
    (hprime := kxPrimeOfPlace_isPrime C x Q hQ.le) (hne := kxPrimeOfPlace_ne_bot C x hx Q hQ)
    (W := Q.valuationSubring) (hW := spso_val_ne_top C x hx hQ)
    (φ := Subring.inclusion (kxClosure_le_valuationSubring C x Q hQ.le))
    (hφ := fun a => by rw [Subring.coe_inclusion]; rfl)
    (hcenter := rfl)

/-- **Every element of `𝒪_Q` is a quotient `b/s` of integral elements with `s ∉ B ∩ 𝔪_Q`.** -/
lemma spso_fraction (hx : Transcendental k x) {Q : C.Place} (hQ : 0 < C.ordAt x Q)
    (y : C.functionField) (hy : y ∈ Q.valuationSubring) :
    ∃ (b s : ↥(C.ordClosure x)),
      s ∉ kxPrimeOfPlace C x Q hQ.le ∧ (s : C.functionField) * y = (b : C.functionField) := by
  haveI : IsDedekindDomain (Curve.kxClosure C x) := spso_dedekind C x
  haveI : IsFractionRing (Curve.kxClosure C x) C.functionField := spso_isFractionRing C x
  have hV := spso_val_eq_atPrime C x hx hQ
  have hy' : y ∈ (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime C.functionField
      ⟨kxPrimeOfPlace C x Q hQ.le, kxPrimeOfPlace_isPrime C x Q hQ.le,
        kxPrimeOfPlace_ne_bot C x hx Q hQ⟩ : ValuationSubring C.functionField).toSubring :=
    hV ▸ hy
  rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_toSubring] at hy'
  rw [Subalgebra.mem_toSubring] at hy'
  rcases hy' with ⟨a, s, hs, rfl⟩
  refine ⟨a, s, ?_, ?_⟩
  · simpa using hs
  · have hs0 : (s : C.functionField) ≠ 0 := by
      intro h0
      refine hs ?_
      have h1 : s = 0 :=
        (IsFractionRing.injective (Curve.kxClosure C x) C.functionField) (by simpa using h0)
      rw [h1]
      exact Ideal.zero_mem _
    have hmid : (↑s : C.functionField) *
        ((algebraMap (Curve.kxClosure C x) C.functionField) s)⁻¹ = 1 :=
      mul_inv_cancel₀ hs0
    calc (↑s : C.functionField) * ((algebraMap (Curve.kxClosure C x) C.functionField) a *
          ((algebraMap (Curve.kxClosure C x) C.functionField) s)⁻¹)
        = (algebraMap (Curve.kxClosure C x) C.functionField) a *
            ((↑s : C.functionField) * ((algebraMap (Curve.kxClosure C x) C.functionField) s)⁻¹) :=
          by ring
      _ = (algebraMap (Curve.kxClosure C x) C.functionField) a * 1 := by rw [hmid]
      _ = (algebraMap (Curve.kxClosure C x) C.functionField) a := by rw [mul_one]

/-- The map from the zeros of `x` to the primes over `(x)` is injective. -/
theorem spso_inj (hx : Transcendental k x) {Q Q' : C.Place} (hQ : 0 < C.ordAt x Q)
    (hQ' : 0 < C.ordAt x Q')
    (h : kxPrimeOfPlace C x Q hQ.le = kxPrimeOfPlace C x Q' hQ'.le) : Q = Q' := by
  haveI : IsDedekindDomain (Curve.kxClosure C x) := spso_dedekind C x
  haveI : IsFractionRing (Curve.kxClosure C x) C.functionField := spso_isFractionRing C x
  have hV := spso_val_eq_atPrime C x hx hQ
  have hV' := spso_val_eq_atPrime C x hx hQ'
  have hv : (⟨kxPrimeOfPlace C x Q hQ.le, kxPrimeOfPlace_isPrime C x Q hQ.le,
        kxPrimeOfPlace_ne_bot C x hx Q hQ⟩ : IsDedekindDomain.HeightOneSpectrum (Curve.kxClosure C x)) =
      ⟨kxPrimeOfPlace C x Q' hQ'.le, kxPrimeOfPlace_isPrime C x Q' hQ'.le,
        kxPrimeOfPlace_ne_bot C x hx (Q := Q') hQ'⟩ :=
    IsDedekindDomain.HeightOneSpectrum.ext h
  refine Place.place_eq_of_valuationSubring_eq C ?_
  exact hV.trans
    ((congrArg (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime C.functionField)
      hv).trans hV'.symm)


/-- The map from the zeros of `x` to the primes over `(x)` is surjective. -/
theorem spso_surj (hx : Transcendental k x) (q : (C.ordIdeal x).primesOver (C.ordClosure x)) :
    ∃ (Q : C.Place) (hQ : 0 < C.ordAt x Q), kxPrimeOfPlace C x Q hQ.le = q.1 := by
  classical
  haveI hDed : IsDedekindDomain (Curve.kxClosure C x) := spso_dedekind C x
  haveI hFr : IsFractionRing (Curve.kxClosure C x) C.functionField := spso_isFractionRing C x
  have hx0 : x ≠ 0 := fun h => hx (h ▸ isAlgebraic_zero)
  have hgen_ne : (Curve.kxGen C x : ↥(Algebra.adjoin k ({x} : Set C.functionField))) ≠ 0 := by
    intro h
    exact hx0 (congrArg Subtype.val h)
  have hIdeal_ne_bot : Curve.kxIdeal C x ≠ ⊥ := by
    rw [Curve.kxIdeal]
    exact fun h => hgen_ne (Ideal.span_singleton_eq_bot.mp h)
  haveI hlies : q.1.LiesOver (C.ordIdeal x) := q.2.2
  have hgen_in_q : algebraMap ↥(Algebra.adjoin k ({x} : Set C.functionField))
      (Curve.kxClosure C x) (Curve.kxGen C x) ∈ q.1 :=
    (Ideal.mem_of_liesOver (P := q.1) (p := C.ordIdeal x) (Curve.kxGen C x)).mp (Ideal.mem_span_singleton_self _)
  have hq_ne_bot : q.1 ≠ ⊥ := by
    intro hbot
    have h0 : algebraMap ↥(Algebra.adjoin k ({x} : Set C.functionField))
        (Curve.kxClosure C x) (Curve.kxGen C x) = 0 := by
      rw [hbot] at hgen_in_q
      exact Ideal.mem_bot.mp hgen_in_q
    have h1 : (Curve.kxGen C x : C.functionField) = 0 := by
      have h2 : algebraMap (Curve.kxClosure C x) C.functionField
          (algebraMap ↥(Algebra.adjoin k ({x} : Set C.functionField)) (Curve.kxClosure C x)
            (Curve.kxGen C x)) = 0 := by
        rw [h0, map_zero]
      rw [← IsScalarTower.algebraMap_apply ↥(Algebra.adjoin k ({x} : Set C.functionField))
        (Curve.kxClosure C x) C.functionField] at h2
      exact h2
    exact hx0 h1
  let v : IsDedekindDomain.HeightOneSpectrum (Curve.kxClosure C x) :=
    ⟨q.1, q.2.1, hq_ne_bot⟩
  let W : ValuationSubring C.functionField :=
    (IsDedekindDomain.HeightOneSpectrum.valuation (K := C.functionField) v).valuationSubring
  have hWne : W ≠ ⊤ := by
    intro htop
    have hnt : (IsDedekindDomain.HeightOneSpectrum.valuation (K := C.functionField)
        v).IsNontrivial := inferInstance
    exact (Valuation.valuationSubring_eq_top_iff _).mp htop hnt
  have hV : ∀ c : k, algebraMap k C.functionField c ∈ W := by
    intro c
    refine (Valuation.mem_valuationSubring_iff
      (IsDedekindDomain.HeightOneSpectrum.valuation (K := C.functionField) v) _).mpr ?_
    rw [IsScalarTower.algebraMap_apply k ↥(Algebra.adjoin k ({x} : Set C.functionField))
        C.functionField,
      IsScalarTower.algebraMap_apply ↥(Algebra.adjoin k ({x} : Set C.functionField))
        (Curve.kxClosure C x) C.functionField]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := C.functionField) v _
  have key_iff : ∀ b : Curve.kxClosure C x,
      (b : C.functionField) ∈ W.nonunits ↔ b ∈ q.1 := by
    intro b
    refine (ValuationSubring.mem_nonunits_iff W).trans ?_
    refine (((Valuation.IsEquiv.lt_one_iff_lt_one (Valuation.isEquiv_valuation_valuationSubring
      (IsDedekindDomain.HeightOneSpectrum.valuation (K := C.functionField) v))).symm).trans ?_)
    exact IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := C.functionField) v b
  have hx_nonunits_W : x ∈ W.nonunits :=
    (key_iff (algebraMap ↥(Algebra.adjoin k ({x} : Set C.functionField)) (Curve.kxClosure C x)
      (Curve.kxGen C x))).mpr hgen_in_q
  obtain ⟨Q, hQeq⟩ := Place.exists_place_of_valuationSubring C W hV hWne
  have hx_nonunits_Q : x ∈ Q.valuationSubring.nonunits := by
    rw [show (Q.valuationSubring).nonunits = W.nonunits from
      congrArg (fun A : ValuationSubring C.functionField => A.nonunits) hQeq.symm]
    exact hx_nonunits_W
  obtain ⟨hxQmem, hxQmax⟩ :=
    ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hx_nonunits_Q
  have hQpos : 0 < C.ordAt x Q :=
    (mem_maximalIdeal_iff_ord_pos C Q ⟨x, hxQmem⟩ hx0).mp hxQmax
  refine ⟨Q, hQpos, ?_⟩
  have hle : (kxInt C x).toSubring ≤ Q.valuationSubring.toSubring :=
    kxClosure_le_valuationSubring C x Q hQpos.le
  have key2 : ∀ b : Curve.kxClosure C x,
      Subring.inclusion hle b ∈ IsLocalRing.maximalIdeal ↥(Q.valuationSubring) ↔ b ∈ q.1 := by
    intro b
    have h1 : Subring.inclusion hle b ∈ IsLocalRing.maximalIdeal ↥(Q.valuationSubring)
        ↔ (b : C.functionField) ∈ (Q.valuationSubring).nonunits := by
      rw [← ValuationSubring.coe_mem_nonunits_iff, Subring.coe_inclusion]
    have h2 : (b : C.functionField) ∈ (Q.valuationSubring).nonunits ↔ b ∈ q.1 := by
      rw [show (Q.valuationSubring).nonunits = W.nonunits from
        congrArg (fun A : ValuationSubring C.functionField => A.nonunits) hQeq.symm]
      exact key_iff b
    exact h1.trans h2
  refine Ideal.ext fun b => ?_
  refine (show b ∈ kxPrimeOfPlace C x Q hQpos.le ↔ Subring.inclusion hle b
      ∈ IsLocalRing.maximalIdeal ↥(Q.valuationSubring) from Ideal.mem_comap).trans (key2 b)


/-- **The ramification index of the prime attached to a place is the order of vanishing.** -/
theorem spso_ramificationIdx_eq (hx : Transcendental k x) {Q : C.Place} (hQ : 0 < C.ordAt x Q) :
    ((kxPrimeOfPlace C x Q hQ.le).ramificationIdx (C.ordBase x) : ℤ) = C.ordAt x Q := by
  classical
  haveI hNoeth : IsNoetherianRing ↥(kxInt C x) :=
    IsNoetherianRing.of_finite (C.ordBase x) (C.ordClosure x)
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
    refine ⟨inferInstance, hNoeth,
      Ring.DimensionLEOne.of_isIntegral ↥(Algebra.adjoin k ({x} : Set C.functionField))
        ↥(kxInt C x), ?_⟩
    intro y hy
    exact ⟨⟨y, isIntegral_trans (R := ↥(Algebra.adjoin k ({x} : Set C.functionField))) y hy⟩, rfl⟩
  haveI hDVR : IsDiscreteValuationRing (C.left.presheaf.stalk Q.point) :=
    Work.CurveBasics.Place.isDiscreteValuationRing Q
  have hqprime := kxPrimeOfPlace_isPrime C x Q hQ.le
  have hqne := kxPrimeOfPlace_ne_bot C x hx Q hQ
  have hWne : Q.valuationSubring ≠ ⊤ := by
    intro htop
    have hnt : Q.valuation.IsNontrivial := by
      have h : Q.valuation = IsDedekindDomain.HeightOneSpectrum.valuation C.functionField
          (IsDiscreteValuationRing.maximalIdeal (C.left.presheaf.stalk Q.point)) := rfl
      rw [h]
      infer_instance
    exact (Valuation.valuationSubring_eq_top_iff (Q.valuation)).mp htop hnt
  have hcenter : Ideal.comap (Subring.inclusion (kxClosure_le_valuationSubring C x Q hQ.le))
      (IsLocalRing.maximalIdeal ↥(Q.valuationSubring)) = kxPrimeOfPlace C x Q hQ.le := rfl
  have hval_eq : Q.valuationSubring
      = (IsDedekindDomain.HeightOneSpectrum.valuation C.functionField
          (kxHeightOne C x hx Q hQ)).valuationSubring := by
    rw [valuationSubring_eq_atPrime (p := kxPrimeOfPlace C x Q hQ.le) hqprime hqne hWne
      (Subring.inclusion (kxClosure_le_valuationSubring C x Q hQ.le)) (fun a => rfl) hcenter]
    exact IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring
      (kxHeightOne C x hx Q hQ)
  have hVsurj : Function.Surjective (IsDedekindDomain.HeightOneSpectrum.valuation
      C.functionField (kxHeightOne C x hx Q hQ)) :=
    IsDedekindDomain.HeightOneSpectrum.valuation_surjective C.functionField _
  have hWsurj : Function.Surjective Q.valuation := by
    have h : Q.valuation = IsDedekindDomain.HeightOneSpectrum.valuation C.functionField
        (IsDiscreteValuationRing.maximalIdeal (C.left.presheaf.stalk Q.point)) := rfl
    rw [h]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_surjective C.functionField _
  have hVW : IsDedekindDomain.HeightOneSpectrum.valuation C.functionField (kxHeightOne C x hx Q hQ)
      = Q.valuation :=
    valuation_eq_of_surjective_of_valuationSubring_eq _ _ hVsurj hWsurj hval_eq.symm
  have h1 := ramificationIdx_eq_neg_log_valuation C x hx Q hQ
  calc ((kxPrimeOfPlace C x Q hQ.le).ramificationIdx
        ↥(Algebra.adjoin k ({x} : Set C.functionField)) : ℤ)
      = -(IsDedekindDomain.HeightOneSpectrum.valuation C.functionField
          (kxHeightOne C x hx Q hQ) x).log := h1
    _ = -(Q.valuation x).log := by rw [hVW]
    _ = C.ordAt x Q := (Curve.Place.ord_eq_neg_log_valuation C Q x).symm

end Work.CurveBasics.Order
