/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The residue field of a place is the residue field of `k[x]^int`

Let `C` be a smooth proper geometrically irreducible curve over a field `k`, let `x ∈ K(C)` be
transcendental over `k` and let `Q` be a place at which `x` vanishes (`0 < ord_Q x`).  Write
`B = k[x]^int` for the integral closure of `k[x]` in `K(C)` and `q = B ∩ 𝔪_Q` for the prime of `B`
attached to `Q` (this is `kxPrimeOfPlace`).

The main result of this file, `kxClosure_residue_surjective`, says that the natural map
`B → κ(Q) = 𝓞_Q/𝔪_Q` is surjective, i.e. that every element of the residue field of `Q` is the
residue class of an integral element.  Consequently `B/q ≅ κ(Q)` is an isomorphism of fields.

The mathematical argument is the following.

* `B` is a Dedekind domain with fraction field `K(C)` (finiteness of `B` over `k[x]` is assumed;
  `K(C)` is finite over `k(x)` because a curve has transcendence degree one over `k`
  ([`finiteDimensional_adjoin_functionField`]), and `B` is the integral closure).
* `q` is a nonzero prime of `B`, hence maximal, with `B/q` a finite field extension of `k`.
* The valuation subring `𝓞_Q` of `K(C)` is the localisation `B_q` of `B` at `q`
  (`Work.CurveBasics.Order.valuationSubring_eq_atPrime`).  In particular every element of `𝓞_Q`
  can be written as `n/s` with `n ∈ B` and `s ∈ B`, `s ∉ q`
  (`IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer`).
* If `c ∈ κ(Q)` is the residue class of `y ∈ 𝓞_Q` and `y = n/s` as above, then
  `c = ψ(n)ψ(s)^{-1}` where `ψ : B → κ(Q)` is the residue map.  Since `q = ker ψ`, `ψ` factors
  through the field `B/q`; the inverse of `ψ(s)` in `κ(Q)` is therefore the image of an element of
  `B`.  Concretely, as `q` is maximal and `s ∉ q`, there is `t ∈ B` with `s t ≡ 1 (mod q)`, so
  `ψ(s)ψ(t) = 1` and `c = ψ(n)ψ(s)^{-1} = ψ(n)ψ(t) = ψ(nt)`.  Thus `c` is the residue class of the
  integral element `n t`.
-/
import Mathlib
import Submission.Work.CurveBasics.Order.Bridge
import Submission.Work.CurveBasics.Place.Valuation
import Submission.Work.CurveBasics.Order.RamifIdxSetup
import Submission.Work.CurveBasics.Order.valuationSubring_eq_atPrime
import Submission.Work.CurveBasics.Order.finiteDimensional_adjoin_functionField

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

open scoped IntermediateField.algebraAdjoinAdjoin

namespace Work.CurveBasics.Order

open Work.CurveBasics

open Curve in
set_option synthInstance.maxHeartbeats 400000 in
/-- Every element of the residue field of the place `Q` is the residue class of an element of the
integral closure of `k[x]` in the function field. -/
theorem kxClosure_residue_surjective {k : Type*} [Field k] (C : Curve k) (x : C.functionField)
    (hx : Transcendental k x) (Q : C.Place) (hQ : 0 < C.ordAt x Q)
    [Module.Finite ↥(Algebra.adjoin k ({x} : Set C.functionField))
      ↥(integralClosure ↥(Algebra.adjoin k ({x} : Set C.functionField)) C.functionField)] :
    Function.Surjective fun b : ↥(integralClosure ↥(Algebra.adjoin k ({x} : Set C.functionField)) C.functionField) =>
      IsLocalRing.residue ↥(Q.valuationSubring) ⟨(b : C.functionField), kxClosure_le_valuationSubring C x Q hQ.le b.2⟩ := by
  classical
  -- `K(C)` is finite over `k(x)`, as `x` is transcendental and a curve has transcendence degree
  -- one over `k`.
  haveI hFD : FiniteDimensional ↥(IntermediateField.adjoin k ({x} : Set C.functionField))
      C.functionField :=
    finiteDimensional_adjoin_functionField C hx
  -- `K(C)` is the fraction field of the integral closure `B = k[x]^int`.
  haveI hFrac : IsFractionRing (Curve.kxClosure C x) C.functionField :=
    integralClosure.isFractionRing_of_finite_extension
      (A := ↥(Algebra.adjoin k ({x} : Set C.functionField)))
      (K := ↥(IntermediateField.adjoin k ({x} : Set C.functionField))) (L := C.functionField)
  -- `B = k[x]^int` is a Dedekind domain: Noetherian because it is a finite `k[x]`-module,
  -- dimension one because it is integral over the principal ideal domain `k[x]`, and integrally
  -- closed because it is an integral closure.
  haveI hNoeth : IsNoetherianRing (Curve.kxClosure C x) :=
    IsNoetherianRing.of_finite ↥(Algebra.adjoin k ({x} : Set C.functionField)) (Curve.kxClosure C x)
  haveI hInt : Algebra.IsIntegral ↥(Algebra.adjoin k ({x} : Set C.functionField))
      (Curve.kxClosure C x) :=
    IsIntegralClosure.isIntegral_algebra (R := ↥(Algebra.adjoin k ({x} : Set C.functionField)))
      (B := C.functionField)
  haveI hDim : Ring.DimensionLEOne (Curve.kxClosure C x) :=
    Ring.DimensionLEOne.of_isIntegral ↥(Algebra.adjoin k ({x} : Set C.functionField))
      (Curve.kxClosure C x)
  haveI hIC : IsIntegrallyClosed (Curve.kxClosure C x) := by
    rw [isIntegrallyClosed_iff C.functionField]
    intro z hz
    exact ⟨⟨z, isIntegral_trans z hz⟩, rfl⟩
  haveI hDed : IsDedekindDomain (Curve.kxClosure C x) :=
    (isDedekindDomain_iff (Curve.kxClosure C x) C.functionField).mpr
      ⟨inferInstance, hNoeth, hDim,
        fun {z} hz => (isIntegrallyClosed_iff (K := C.functionField)).mp hIC hz⟩
  -- the valuation subring at `Q` is a proper subring of `K(C)` (it contains `x` but not `x⁻¹`)
  have hWne : Q.valuationSubring ≠ ⊤ := by
    intro htop
    have hx0 : x ≠ 0 := fun h => hx (h ▸ isAlgebraic_zero)
    have hxmem : x ∈ Q.valuationSubring := by
      rw [Place.mem_valuationSubring_iff]; change 0 ≤ C.ordAt x Q; linarith
    have hinv : x⁻¹ ∈ Q.valuationSubring := by rw [htop]; trivial
    rw [Place.mem_valuationSubring_iff] at hinv
    change 0 ≤ C.ordAt x⁻¹ Q at hinv
    rw [C.ordAt_inv hx0] at hinv
    linarith
  -- the prime `q = B ∩ 𝔪_Q`, its height one spectrum, and the inclusion `B ⊆ 𝓞_Q`
  let q : Ideal (Curve.kxClosure C x) := kxPrimeOfPlace C x Q hQ.le
  have hqprime : q.IsPrime := kxPrimeOfPlace_isPrime C x Q hQ.le
  have hqne : q ≠ ⊥ := kxPrimeOfPlace_ne_bot C x hx Q hQ
  haveI hqmax : q.IsMaximal := hqprime.isMaximal hqne
  let v : IsDedekindDomain.HeightOneSpectrum (Curve.kxClosure C x) := ⟨q, hqprime, hqne⟩
  let hle := kxClosure_le_valuationSubring C x Q hQ.le
  let phi : (Curve.kxClosure C x) →+* ↥(Q.valuationSubring) := Subring.inclusion hle
  -- the prime determines the place: `𝓞_Q` is the localisation of `B` at `q`
  have hVeq : Q.valuationSubring =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime C.functionField v :=
    valuationSubring_eq_atPrime (A := Curve.kxClosure C x) (K := C.functionField) q hqprime hqne hWne
      phi (fun a => by simp only [phi]; rfl) rfl
  -- the residue map on `B`
  let psi : (Curve.kxClosure C x) →+* IsLocalRing.ResidueField ↥(Q.valuationSubring) :=
    (IsLocalRing.residue ↥(Q.valuationSubring)).comp phi
  have hker : RingHom.ker psi = q := by
    show RingHom.ker ((IsLocalRing.residue ↥(Q.valuationSubring)).comp phi) = q
    rw [← RingHom.comap_ker (IsLocalRing.residue ↥(Q.valuationSubring)) phi, IsLocalRing.ker_residue]
    rfl
  suffices Function.Surjective psi by
    intro c
    obtain ⟨b, hb⟩ := this c
    exact ⟨b, hb⟩
  intro c
  -- every residue class is the residue of an element of the valuation subring
  obtain ⟨y, hy⟩ := IsLocalRing.residue_surjective c
  rw [← hy]
  -- which is a quotient `y = n / d` of integral elements, `d ∉ q`
  have hy_mem : (y : C.functionField) ∈
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime C.functionField v := by
    rw [← hVeq]; exact y.2
  have hy_le : IsDedekindDomain.HeightOneSpectrum.valuation C.functionField v (y : C.functionField)
      ≤ 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at hy_mem
    exact (Valuation.mem_valuationSubring_iff _ _).mp hy_mem
  obtain ⟨n, d, hnd⟩ :=
    IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v (y : C.functionField)
      hy_le
  have hd_notMem : (d : Curve.kxClosure C x) ∉ q := d.2
  -- `d` is invertible modulo `q`: `exists_inv` gives `s' * d + i = 1` with `i ∈ q`
  obtain ⟨s', i, hi, hsi⟩ := hqmax.exists_inv hd_notMem
  have hs'i : (d : Curve.kxClosure C x) * s' - 1 ∈ q := by
    have h2 : (d : Curve.kxClosure C x) * s' - 1 = -i := by
      rw [show (d : Curve.kxClosure C x) * s' = 1 - i by
            rw [mul_comm (d : Curve.kxClosure C x) s', eq_sub_iff_add_eq, hsi],
          show (1 : Curve.kxClosure C x) - i - 1 = -i by ring]
    rw [h2]; exact neg_mem hi
  have hψ1 : psi ((d : Curve.kxClosure C x) * s') = 1 := by
    have h : psi ((d : Curve.kxClosure C x) * s' - 1) = 0 := by
      rw [← RingHom.mem_ker, hker]
      exact hs'i
    rw [map_sub, map_one, sub_eq_zero] at h
    exact h
  have hψm : psi (d : Curve.kxClosure C x) * psi s' = 1 := by
    rw [← map_mul]; exact hψ1
  -- the identity `y * d = n` holds already in `𝓞_Q`, hence survives the residue map
  have hO : y * phi (d : Curve.kxClosure C x) = phi n := by
    apply Subtype.ext
    show (y : C.functionField) * (d : C.functionField) = (n : C.functionField)
    exact hnd
  have hres : IsLocalRing.residue ↥(Q.valuationSubring) y * psi (d : Curve.kxClosure C x) = psi n := by
    have h := congrArg (IsLocalRing.residue ↥(Q.valuationSubring)) hO
    simpa only [psi, RingHom.comp_apply, map_mul] using h
  -- hence `residue y = psi n * psi s'`, and `n * s'` is the required lift
  refine ⟨n * s', ?_⟩
  rw [map_mul, ← hres, mul_assoc, hψm, mul_one]

end Work.CurveBasics.Order
