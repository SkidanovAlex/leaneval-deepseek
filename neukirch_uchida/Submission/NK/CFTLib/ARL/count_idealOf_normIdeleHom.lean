import Mathlib
import Submission.NK.GlobalCFT.IdeleClassGroup
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_exists_finset_isBoundedIntegral
import Submission.NK.GlobalCFT.Place
import Submission.NK.GlobalCFT.NormFunctorial
import Submission.NK.GlobalCFT.Norm.globalCFT_abs_normIdeleHom
import Submission.NK.CFTLib.normIdeleHom_ideleOfPrime_div_mem_integralIdeles

/-!
# The ideal of the idèlic norm

For a finite extension of number fields `L / K` and an idèle `y` of `L`, the fractional ideal of
`K` attached to the idèlic norm `N_{L/K} y` has, at a prime `𝔭` of `K`, the exponent given by the
inertia-degree weighted sum of the exponents of `y` at the primes `𝔓` of `L` above `𝔭`:

`v_𝔭(idealOf (N_{L/K} y)) = ∑_{𝔓 | 𝔭} f(𝔓/𝔭) · v_𝔓(idealOf y)`.

This is the ideal-theoretic shadow of the local valuation formula
`v_𝔭(N_{L_𝔓/K_𝔭} x) = v_𝔓(x)^{f(𝔓/𝔭)}` (`NK.GlobalCFT.Norm.globalCFT_val_norm_adicCompletion_eq_pow_inertiaDeg`).

## Main results

* `NK.CFTLib.ARL.count_idealOf_normIdeleHom`: the statement above.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.ARL

open NK.GlobalCFT

/-- **The exponent of the ideal of the idèlic norm.**  For a finite extension of number fields
`L / K`, an idèle `y` of `L` and a finite place `𝔭` of `K`, the `𝔭`-adic exponent of the idèlic
norm `N_{L/K} y` is the inertia-degree weighted sum of the exponents of `y` above `𝔭`.

This is `NK.CFTLib.exp_normIdeleHom_eq_sum'`, rewritten in terms of
`NK.GlobalCFT.Idele.exp`; it is proved from the local valuation formula
`NK.CFTLib.val_localNormFinite`. -/
theorem exp_normIdeleHom_eq_sum_idealOf {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (y : Idele L)
    (𝔭 : HeightOneSpectrum (𝓞 K)) :
    Idele.exp 𝔭 (Idele.normIdeleHom K L y) =
      ∑ 𝔓 ∈ Place.primesOverFinite (K := K) (L := L) 𝔭,
        ((𝔓.asIdeal.inertiaDeg (𝓞 K) : ℤ) * Idele.exp 𝔓 y) :=
  exp_normIdeleHom_eq_sum' K L y 𝔭

theorem count_idealOf_normIdeleHom {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (y : NK.GlobalCFT.Idele L)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    FractionalIdeal.count K 𝔭
        (NK.GlobalCFT.Idele.idealOf (NK.GlobalCFT.Idele.normIdeleHom K L y))
      = ∑ 𝔓 ∈ NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) 𝔭,
          ((𝔓.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) : ℤ) *
            FractionalIdeal.count L 𝔓 (NK.GlobalCFT.Idele.idealOf y)) := by
  rw [Idele.count_idealOf, exp_normIdeleHom_eq_sum_idealOf]
  exact Finset.sum_congr rfl fun 𝔓 _ => by rw [Idele.count_idealOf]

end NK.CFTLib.ARL
