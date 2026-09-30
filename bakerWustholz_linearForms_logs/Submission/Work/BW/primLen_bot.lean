import Mathlib
import Submission.Work.BW.DefsMult


namespace Work.BW

/-- The multiplicity of the zero ideal at its (only) minimal prime `⊥` is `1`: the localization of
`R = ℂ[X]` at `⊥` is the fraction field of `R` (a domain), so `(R/⊥)_⊥ = R_⊥` is a one-dimensional
module over a division ring, whose `Module.length` is `1`. -/
theorem primLen_bot (N : ℕ) :
    ((primLen (⊥ : Ideal (MR N)) (⊥ : Ideal (MR N))).toNat : ℚ) = 1 := by
  -- `⊥` is prime in the domain `MR N = ℂ[X_{ij}]`.
  have hpr : (⊥ : Ideal (MR N)).IsPrime := inferInstance
  rw [primLen, dite_eq_left hpr]
  -- The image of `⊥` under the structure map into the localization at `⊥` is again `⊥`.
  rw [Ideal.map_bot]
  -- `A ⧸ ⊥ ≃ₗ[A] A` and `Module.length` is invariant under linear equivalences.
  rw [(Submodule.quotEquivOfEqBot
    (⊥ : Ideal (Localization.AtPrime (⊥ : Ideal (MR N)))) rfl).length_eq]
  -- Localizing a domain at `⊥` yields its fraction field, which is a field.
  have hFR : IsFractionRing (MR N) (Localization.AtPrime (⊥ : Ideal (MR N))) := by
    simpa [Ideal.primeCompl_bot] using
      Localization.isLocalization (M := (⊥ : Ideal (MR N)).primeCompl)
  letI : Field (Localization.AtPrime (⊥ : Ideal (MR N))) := IsFractionRing.toField (MR N)
  -- A division ring is one-dimensional over itself, so its `Module.length` is `1`.
  have hlen : Module.length (Localization.AtPrime (⊥ : Ideal (MR N)))
      (Localization.AtPrime (⊥ : Ideal (MR N))) = 1 := by
    rw [Module.length_eq_finrank, Module.finrank_self]
    norm_num
  rw [hlen]
  norm_num

end Work.BW
