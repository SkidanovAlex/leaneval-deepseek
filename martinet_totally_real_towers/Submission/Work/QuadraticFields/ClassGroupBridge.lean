import Mathlib
import Submission.Work.QuadraticFields.RankTwo
import Submission.Work.QuadraticFields.Ramification
import Submission.Work.QuadraticFields.GenusCertificate

/-!
# The class-group form of the genus certificate

This file records the class-field-theoretic bridge between the Kummer form of the genus-theory
input (an unramified extension of degree `2^k`, i.e. `k` independent unramified quadratic
extensions) and the `2`-rank of the ideal class group.

The bridge itself is global class field theory (Artin reciprocity plus the Galois correspondence
for the Hilbert class field); it is not proved in this chapter.  What *is* proved here is the
`2`-rank apparatus (`rankTwo`, `Work.QuadraticFields.rankTwo`) and the transport of the explicit
numerical certificate along the bridge.

## Main definitions

* `Work.QuadraticFields.UnramifiedRankBridge F k`: the class-field-theoretic input, stating that an
  unramified Galois extension of `F` of degree `2 ^ k` forces `k ≤ rankTwo (Cl F)`.

## Main results

* `rankTwo_classGroup_ge_of_unramified`: the transport of the bridge input.
* `rankTwo_classGroup_certificate`: for the certificate field `F = ℚ(√-3556995)`, the bridge
  yields `5 ≤ rankTwo (Cl F)`.
-/

namespace Work.QuadraticFields

set_option autoImplicit false

open NumberField

noncomputable section

/-- **The Artin-reciprocity bridge** (class field theory, not proved in this chapter).

If a number field `F` admits an unramified finite Galois extension `M` (at all finite primes) of
degree `2 ^ k`, then `k ≤ rankTwo (Cl F)`: by Artin reciprocity the unramified abelian extensions
of `F` are the quotients of the class group, so `Gal(M/F)` (or at least its exponent-`2` part) is a
quotient of `Cl F ⧸ Cl F²`. -/
def UnramifiedRankBridge (F : Type*) [Field F] [NumberField F] (k : ℕ) : Prop :=
  (∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : Algebra F M) (_ : IsGalois F M),
      Module.finrank F M = 2 ^ k ∧ IsUnramifiedAtFinitePrimes F M) →
    k ≤ rankTwo (ClassGroup (𝓞 F))

/-- Transport of the numerical certificate along the class-field-theoretic bridge. -/
theorem rankTwo_classGroup_ge_of_unramified {F : Type*} [Field F] [NumberField F] {k : ℕ}
    (h : UnramifiedRankBridge F k) {M : Type} [Field M] [NumberField M] [Algebra F M]
    [IsGalois F M] (hdeg : Module.finrank F M = 2 ^ k)
    (hunr : IsUnramifiedAtFinitePrimes F M) :
    k ≤ rankTwo (ClassGroup (𝓞 F)) :=
  h ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, hdeg, hunr⟩

/-- **The class-group form of the certificate.**  Assuming the Artin-reciprocity bridge
`UnramifiedRankBridge`, the explicit unramified extension `M/F` of degree `32` of the certificate
shows that the class group of `F = ℚ(√-3556995)` satisfies `5 ≤ rankTwo (Cl F)`. -/
theorem rankTwo_classGroup_certificate (h : UnramifiedRankBridge ↥certF 5) :
    5 ≤ rankTwo (ClassGroup (𝓞 ↥certF)) := by
  haveI : IsGalois ℚ certM := multiQuad_isGalois certPrimesQ
  haveI : IsGalois ↥certF certM := IsGalois.tower_top_of_isGalois ℚ ↥certF certM
  have h5 : (2 : ℕ) ^ 5 = 32 := by norm_num
  exact rankTwo_classGroup_ge_of_unramified h (by rw [cert_finrank, h5]) cert_unramified

end

end Work.QuadraticFields
