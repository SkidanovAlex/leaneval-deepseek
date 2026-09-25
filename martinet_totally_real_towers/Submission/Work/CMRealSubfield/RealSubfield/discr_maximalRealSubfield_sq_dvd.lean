import Mathlib

namespace Work.CMRealSubfield.RealSubfield

open NumberField

/-- For a CM field `K` with maximal real subfield `K⁺ = maximalRealSubfield K`, the square of
the discriminant of `K⁺` divides the discriminant of `K`.

This is the tower discriminant formula applied to the quadratic extension `K⁺ ⊆ K`: for a tower
`F ⊆ L` of number fields,
`|disc L| = |N_{F/ℚ} (𝔡_{L/F})| · |disc F| ^ [L : F]`,
and here `[K : K⁺] = 2`, so `|disc K| = m · |disc K⁺| ^ 2` for some natural number `m`. -/
theorem discr_maximalRealSubfield_sq_dvd (K : Type*) [Field K] [NumberField K]
    [NumberField.IsCMField K] :
    (NumberField.discr (NumberField.maximalRealSubfield K)) ^ 2 ∣ NumberField.discr K := by
  -- Divisibility of integers by a square only depends on absolute values.
  have h : (NumberField.discr (NumberField.maximalRealSubfield K)).natAbs ^ 2 ∣
      (NumberField.discr K).natAbs := by
    -- The discriminant formula of a tower `K⁺ ⊆ K`, with `[K : K⁺] = 2`.
    have hmain := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
      (K := NumberField.maximalRealSubfield K) (𝒪 := 𝓞 (NumberField.maximalRealSubfield K))
      (L := K) (𝒪' := 𝓞 K)
    have hfr : Module.finrank (NumberField.maximalRealSubfield K) K = 2 :=
      Algebra.IsQuadraticExtension.finrank_eq_two (NumberField.maximalRealSubfield K) K
    rw [hmain, hfr]
    exact ⟨_, mul_comm _ _⟩
  rw [← Int.natAbs_pow] at h
  exact (Int.natAbs_dvd_natAbs).mp h

end Work.CMRealSubfield.RealSubfield
