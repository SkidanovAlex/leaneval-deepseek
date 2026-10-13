import Mathlib

open scoped nonZeroDivisors

namespace Work.DSREG.DomainIdealBot

/-- If `R` is a domain and `I` an ideal with `dim (R ⧸ I) = dim R`, then `I = ⊥`.

Indeed, were `I ≠ ⊥` there is `0 ≠ r ∈ I`; in a domain `r` is a non-zero-divisor, so the
surjection `R →+* R ⧸ I` whose kernel contains `r` lowers the Krull dimension by at least one
(`ringKrullDim_succ_le_of_surjective`): `dim (R ⧸ I) + 1 ≤ dim R`, contradicting the equality
of the two dimensions. -/
theorem eq_bot_of_ringKrullDim_quotient_eq (R : Type*) [CommRing R] [IsDomain R]
    (I : Ideal R) (n : ℕ) (hR : ringKrullDim R = n) (hI : ringKrullDim (R ⧸ I) = n) :
    I = ⊥ := by
  by_contra hne
  obtain ⟨r, hr_mem, hr_ne⟩ := I.ne_bot_iff.mp hne
  have hr_nzd : r ∈ R⁰ := by simpa using hr_ne
  have hle : ringKrullDim (R ⧸ I) + 1 ≤ ringKrullDim R :=
    ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective hr_nzd
      (Ideal.Quotient.eq_zero_iff_mem.mpr hr_mem)
  rw [hR, hI] at hle
  have h3 : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by simpa using hle
  exact absurd (Nat.cast_le.mp (WithBot.coe_le_coe.mp h3)) (Nat.not_succ_le_self n)

end Work.DSREG.DomainIdealBot
