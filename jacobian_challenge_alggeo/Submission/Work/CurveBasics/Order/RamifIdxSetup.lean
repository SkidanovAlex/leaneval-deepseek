import Mathlib
import Submission.Work.CurveBasics.Order.Bridge
import Submission.Work.CurveBasics.Order.kxPrimeOfPlace_liesOver
import Submission.Work.CurveBasics.Place.mem_valuationSubring_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Setup for the comparison of the two valuations at a place

Let `C` be a curve over a field `k`, let `x ∈ K(C)` be transcendental and let `Q` be a place at
which `x` vanishes.  This file collects the elementary data shared by the proof that the
ramification index of the prime `q = k[x]^int ∩ 𝔪_Q` of `k[x]^int` equals `ord_Q x`:

* `kxPrimeOfPlace_ne_bot`: `q` is a nonzero prime, so it is a height one prime of the integral
  closure `k[x]^int`;
* `kxHeightOne`: that height one prime;
* `kxClosure_le_valuationSubringAtPlace`: `k[x]^int` is contained in the valuation ring at `Q`.
-/

open scoped Classical IntermediateField.algebraAdjoinAdjoin
set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.CurveBasics.Order

open Work.CurveBasics

variable {k : Type*} [Field k]

/-- The image of the generator of `k[x]` in the function field is `x`. -/
lemma algebraMap_kxGen_eq_functionField (C : Curve k) (x : C.functionField) :
    algebraMap ↥(Algebra.adjoin k ({x} : Set C.functionField)) C.functionField
      (Curve.kxGen C x) = x := rfl

/-- `x` is integral over `k[x]`. -/
lemma kxGen_isIntegral (C : Curve k) (x : C.functionField) :
    IsIntegral ↥(Algebra.adjoin k ({x} : Set C.functionField)) x :=
  (algebraMap_kxGen_eq_functionField C x) ▸
    (isIntegral_algebraMap (A := C.functionField) (x := Curve.kxGen C x))

/-- The image of the generator of `k[x]` in the integral closure `k[x]^int` is `x`. -/
lemma algebraMap_kxGen_eq (C : Curve k) (x : C.functionField) :
    algebraMap ↥(Algebra.adjoin k ({x} : Set C.functionField)) ↥(kxInt C x)
      (Curve.kxGen C x) = ⟨x, kxGen_isIntegral C x⟩ :=
  Subtype.ext (algebraMap_kxGen_eq_functionField C x)

/-- The prime of `k[x]^int` attached to a place at which `x` vanishes is nonzero. -/
theorem kxPrimeOfPlace_ne_bot (C : Curve k) (x : C.functionField) (hx : Transcendental k x)
    (Q : C.Place) (hQ : 0 < C.ordAt x Q) : kxPrimeOfPlace C x Q hQ.le ≠ ⊥ := by
  intro hbot
  have hx0 : x ≠ 0 := hx.ne_zero
  have hmem := kxGen_mem_kxPrimeOfPlace C x hx Q hQ
  rw [hbot, Ideal.mem_bot] at hmem
  have h1 : algebraMap ↥(Algebra.adjoin k ({x} : Set C.functionField)) C.functionField
      (Curve.kxGen C x) = 0 := by
    rw [IsScalarTower.algebraMap_apply ↥(Algebra.adjoin k ({x} : Set C.functionField))
      ↥(kxInt C x) C.functionField, hmem, map_zero]
  rw [algebraMap_kxGen_eq_functionField C x] at h1
  exact hx0 h1

/-- The height one prime of the integral closure `k[x]^int` attached to a place at which `x`
vanishes. -/
noncomputable def kxHeightOne (C : Curve k) (x : C.functionField) (hx : Transcendental k x)
    (Q : C.Place) (hQ : 0 < C.ordAt x Q) [IsDedekindDomain ↥(kxInt C x)] :
    IsDedekindDomain.HeightOneSpectrum ↥(kxInt C x) :=
  ⟨kxPrimeOfPlace C x Q hQ.le, kxPrimeOfPlace_isPrime C x Q hQ.le,
    kxPrimeOfPlace_ne_bot C x hx Q hQ⟩

/-- The `k[x]^int`-image of `x` is a nonunit in the valuation ring at a place where `x`
vanishes; in particular `x ≠ 0`. -/
lemma kxInt_mem_valuationSubringAtPlace (C : Curve k) (x : C.functionField) (Q : C.Place)
    (hQ : 0 ≤ C.ordAt x Q) (b : ↥(kxInt C x)) : (b : C.functionField) ∈ Q.valuationSubring :=
  kxClosure_le_valuationSubring C x Q hQ b.property

end Work.CurveBasics.Order
