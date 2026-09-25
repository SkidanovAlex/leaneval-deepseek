import Mathlib

namespace Work.CMRealSubfield.RealSubfield

open NumberField

/-- For a CM field `K` with maximal real subfield `K⁺`, the square of the absolute discriminant
of `K⁺` divides the absolute discriminant of `K`.

This is the different-conductor computation in the quadratic tower `ℚ ⊆ K⁺ ⊆ K`.  The different
is multiplicative in a tower, so `𝔡_{K/ℚ} = 𝔡_{K/K⁺} · 𝔡_{K⁺/ℚ}` in `𝓞 K`, and taking norms
along `K/ℚ`, using `N_{K/ℚ} = N_{K⁺/ℚ} ∘ N_{K/K⁺}` and `[K : K⁺] = 2`, gives

`|disc K| = N_{K⁺/ℚ}(𝔡_{K/K⁺}) · |disc K⁺| ^ 2`.

Both factors on the right are positive natural numbers, which is exactly the claimed
divisibility.  In Lean this is Mathlib's
`NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow` for the tower
`K⁺ / ℚ`, with the exponent `Module.finrank K⁺ K` rewritten to `2` by
`Algebra.IsQuadraticExtension.finrank_eq_two`. -/
theorem natAbs_discr_maximalRealSubfield_sq_dvd (K : Type*) [Field K] [NumberField K]
    [NumberField.IsCMField K] :
    ((NumberField.discr (NumberField.maximalRealSubfield K)).natAbs) ^ 2 ∣
      (NumberField.discr K).natAbs := by
  have hfin : Module.finrank (NumberField.maximalRealSubfield K) K = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have h := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    (K := NumberField.maximalRealSubfield K) (𝒪 := 𝓞 (NumberField.maximalRealSubfield K))
    (L := K) (𝒪' := 𝓞 K)
  rw [hfin] at h
  rw [h]
  exact dvd_mul_left _ _

end Work.CMRealSubfield.RealSubfield
