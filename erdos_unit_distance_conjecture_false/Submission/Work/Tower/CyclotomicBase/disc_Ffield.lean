import Mathlib
import Submission.Work.Tower.CyclotomicBase.Defs
import Submission.Work.Tower.CyclotomicBase.Basic
import Submission.Work.Tower.CyclotomicBase.disc_Mfield
import Submission.Work.Tower.CyclotomicBase.finrank_Mfield
import Submission.Work.Tower.CyclotomicBase.finrank_Ffield_eq_three
import Submission.Work.Tower.CyclotomicBase.finrank_Mfield_over_FMfield
import Submission.Work.Tower.CyclotomicBase.ramificationIdxIn_Ffield_ne_one
import Submission.Work.Tower.CyclotomicBase.dvd_discr_of_ramificationIdxIn_ne_one
import Submission.Work.Tower.CyclotomicBase.isSquare_natAbs_discr_Ffield
import Submission.Work.Tower.CyclotomicBase.eq_prod_sq_of_pow_dvd_pow_of_isSquare_of_dvd
import Submission.Work.Tower.CubicDiscriminant

/-!
# The discriminant of `F` (paper Proposition 3.2)

For a family `r : Fin ℓ → ℕ` of pairwise distinct primes `≡ 1 (mod 3)`, the field
`F = Ffield r hr hr3`, cut out of `ℚ(ζ_D)` (`D = ∏ rᵢ`) by the product cubic character
`χ₁⋯χ_ℓ`, has discriminant of absolute value `(∏ rᵢ) ^ 2`.

The proof avoids the conductor–discriminant formula.  In the tower `M / F / ℚ`, where
`M = Mfield r hr hr3` is the field cut out by all `ℓ` characters, the discriminant formula gives
`|disc M| = N(𝔡_{M/F}) · |disc F| ^ [M : F]`; with `|disc M| = (∏ rᵢ²) ^ 3^(ℓ-1)`
(`disc_Mfield`), `[M : F] = 3 ^ (ℓ - 1)` (`finrank_Mfield_over_FMfield`) this yields the upper
bound `|disc F| ^ 3^(ℓ-1) ∣ (∏ rᵢ²) ^ 3^(ℓ-1)`, i.e. `|disc F| ∣ ∏ rᵢ²`.  Conversely `disc F` is a
square (`isSquare_natAbs_discr_Ffield`, from the Vandermonde square root of a discriminant of a
Galois extension) and each `rᵢ` ramifies in `F` (`ramificationIdxIn_Ffield_ne_one`), so
`rᵢ² ∣ |disc F|` for every `i`, giving `∏ rᵢ² ∣ |disc F|`.  The two divisibilities meet and
`eq_prod_sq_of_pow_dvd_pow_of_isSquare_of_dvd` concludes.
-/

set_option linter.style.haveILetI false

namespace Work.Tower.CyclotomicBase

open NumberField

/-- **Upper bound.** In the tower `M / F / ℚ` the discriminant formula gives
`|disc M| = N(𝔡_{M/F}) · |disc F| ^ [M : F]`, and `[M : F] = 3 ^ (ℓ - 1)`,
`|disc M| = (∏ rᵢ²) ^ 3^(ℓ-1)`.  Hence `|disc F| ^ 3^(ℓ-1)` divides `(∏ rᵢ²) ^ 3^(ℓ-1)`. -/
theorem natAbs_discr_Ffield_pow_dvd {ℓ : ℕ} (hℓ : 0 < ℓ) (r : Fin ℓ → ℕ)
    (hr : ∀ i, Nat.Prime (r i)) (hr3 : ∀ i, r i % 3 = 1) (hrinj : Function.Injective r)
    [NeZero (D r)] :
    (NumberField.discr ↥(Ffield r hr hr3)).natAbs ^ (3 ^ (ℓ - 1)) ∣
      (∏ i, (r i) ^ 2) ^ (3 ^ (ℓ - 1)) := by
  have htower := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    ↥(FMfield r hr hr3) (𝓞 ↥(FMfield r hr hr3)) ↥(Mfield r hr hr3) (𝓞 ↥(Mfield r hr hr3))
  rw [finrank_Mfield_over_FMfield hℓ r hr hr3 hrinj] at htower
  have hM : (NumberField.discr ↥(Mfield r hr hr3)).natAbs =
      (∏ i, (r i) ^ 2) ^ (3 ^ (ℓ - 1)) := by
    have h := congrArg Int.natAbs (disc_Mfield r hr hr3 hrinj)
    simpa only [Int.natAbs_abs, Int.natAbs_pow, Int.natAbs_natCast] using h
  have hFM : (NumberField.discr ↥(FMfield r hr hr3)).natAbs =
      (NumberField.discr ↥(Ffield r hr hr3)).natAbs :=
    (congrArg Int.natAbs (NumberField.discr_eq_discr_of_algEquiv (↥(Ffield r hr hr3))
      (IntermediateField.restrictAlgEquiv (Ffield_le_Mfield r hr hr3)))).symm
  rw [hM, hFM] at htower
  exact ⟨_, htower.trans (mul_comm _ _)⟩

/-- **The discriminant of `F`.**  For pairwise distinct primes `rᵢ ≡ 1 (mod 3)`, the cubic field
`Ffield r hr hr3 ⊆ ℚ(ζ_{∏ rᵢ})` has `|disc F| = (∏ rᵢ) ^ 2`. -/
theorem disc_Ffield {ℓ : ℕ} (hℓ : 0 < ℓ) (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i))
    (hr3 : ∀ i, r i % 3 = 1) (hrinj : Function.Injective r) [NeZero (D r)] :
    |NumberField.discr ↥(Ffield r hr hr3)| = (((∏ i, r i : ℕ)) : ℤ) ^ 2 := by
  set m : ℕ := (NumberField.discr ↥(Ffield r hr hr3)).natAbs with hm
  have hn : 0 < 3 ^ (ℓ - 1) := pow_pos (by norm_num) _
  have hpow : m ^ (3 ^ (ℓ - 1)) ∣ (∏ i, (r i) ^ 2) ^ (3 ^ (ℓ - 1)) := by
    rw [hm]; exact natAbs_discr_Ffield_pow_dvd hℓ r hr hr3 hrinj
  have hsq : IsSquare m := by
    rw [hm]; exact isSquare_natAbs_discr_Ffield hℓ r hr hr3 hrinj
  have hdvd : ∀ i, r i ∣ m := by
    intro i
    haveI : IsGalois ℚ ↥(Ffield r hr hr3) := isGalois_Ffield r hr hr3
    have hz : (r i : ℤ) ∣ NumberField.discr ↥(Ffield r hr hr3) :=
      dvd_discr_of_ramificationIdxIn_ne_one (K := ↥(Ffield r hr hr3)) (hr i)
        (ramificationIdxIn_Ffield_ne_one r hr hr3 hrinj i)
    rw [hm]
    obtain ⟨c, hc⟩ := hz
    refine ⟨c.natAbs, ?_⟩
    rw [hc, Int.natAbs_mul, Int.natAbs_natCast]
  have hmP : m = ∏ i, r i ^ 2 :=
    eq_prod_sq_of_pow_dvd_pow_of_isSquare_of_dvd hn hr hrinj hsq hdvd hpow
  rw [← Int.natCast_natAbs, ← hm, hmP, Finset.prod_pow, Nat.cast_pow]

end Work.Tower.CyclotomicBase
