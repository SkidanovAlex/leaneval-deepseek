import Mathlib
import Submission.Work.QuadraticFields.GenusCertificate
import Submission.Work.QuadraticFields.cert_unramified_at_infinite_places
import Submission.Work.QuadraticFields.certM_eq_multiquad_five
import Submission.Work.QuadraticFields.WideNarrow
import Submission.Work.QuadraticFields.rankTwo_pi_zmod_two
import Submission.Work.QuadraticFields.rankTwo_multiplicative_finrank
import Submission.Work.QuadraticFields.independentModSquares_iff_finset


/-!
# The numerical certificate, in final form

The explicit input of the unramified `2`-tower route over an imaginary quadratic field:

* the base field `F = ℚ(√-3556995)` (inside `M`), with `disc F = -3556995 = -3·5·13·17·29·37`,
  so `ω(|disc F|) = 6`;
* the extension `M = ℚ(√-3, √5, √13, √17, √29, √37)`, which is unramified over `F` at all finite
  primes *and* at the infinite places, of degree `2 ^ 5 = 32`;
* the five prime discriminants `-3, 5, 13, 17, 29` whose square roots generate `M` over `F`
  (`certM_eq_multiquad_five`), so their square classes in `Fˣ` are independent modulo squares — the
  five independent unramified quadratic extensions of `F` of genus theory.

## Main results

* `cert_full`: unramified (finite and infinite places) with `[M : F] = 32`.
* `cert_five_generators`: `M` is generated over `F` by the five square roots `√-3, √5, √13, √17,
  √29`, and `[M : F] = 32`.
-/

namespace Work.QuadraticFields

set_option autoImplicit false

noncomputable section

/-- **The numerical certificate in final form.**  The multiquadratic field
`M = ℚ(√-3, √5, √13, √17, √29, √37)` is an unramified extension of `F = ℚ(√-3556995)` at all
finite primes and at the infinite places, of degree `2 ^ 5 = 32`. -/
theorem cert_full : IsUnramifiedAtFinitePrimes ↥certF certM ∧
    IsUnramifiedAtInfinitePlaces ↥certF certM ∧ Module.finrank ↥certF certM = 32 :=
  ⟨cert_unramified, cert_unramified_at_infinite_places, cert_finrank⟩

/-- **The five independent unramified quadratic extensions.**  `M` is generated over `F` by the
chosen square roots of `-3, 5, 13, 17, 29`, and `[M : F] = 2 ^ 5 = 32`; hence the classes of these
five elements in `Fˣ ⧸ (Fˣ)²` are independent, and each `F(√Δ)` is unramified over `F` (being an
intermediate subfield of the unramified extension `M/F`). -/
theorem cert_five_generators :
    (multiquadSub certPrimes5 certRoot ⊔ certF : IntermediateField ℚ certM) = ⊤ ∧
      Module.finrank ↥certF certM = 32 :=
  ⟨certM_eq_multiquad_five, cert_finrank⟩

end

end Work.QuadraticFields
