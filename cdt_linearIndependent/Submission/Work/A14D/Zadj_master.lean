import Mathlib
import Submission.Work.A14D.Zadj_defs
import Submission.Work.A14D.Zadj_clearing

namespace Work.A14D

open Polynomial

/-- The clearing identity `DZ³ = QZ·(x³(x−1))` for the universal denominator data. -/
private lemma DZ_pow_three_eq : DZ ^ 3 = QZ * (X ^ 3 * (X - 1)) := by
  unfold DZ QZ
  ring

theorem Zadj_master {β : RatFunc ℂ} {c : Fin 3 → ℂ} (h : LZf β = RhsZ c)
    (hrhs : RhsZ c = algebraMap (Polynomial ℂ) (RatFunc ℂ) (PsiZ c)
        / algebraMap (Polynomial ℂ) (RatFunc ℂ) QZ)
    {W : Polynomial ℂ} (hβW : algebraMap (Polynomial ℂ) (RatFunc ℂ) W
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) DZ * β) :
    PhiNumZ W = PsiZ c * (X ^ 3 * (X - 1)) := by
  have hcl := Zadj_clearing hβW
  rw [h, hrhs] at hcl
  have hQZ : algebraMap (Polynomial ℂ) (RatFunc ℂ) QZ ≠ 0 := fun hzero =>
    QZ_ne_zero (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ) (by simpa using hzero))
  have hmap : (algebraMap (Polynomial ℂ) (RatFunc ℂ) DZ) ^ 3
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) QZ
        * algebraMap (Polynomial ℂ) (RatFunc ℂ) (X ^ 3 * (X - 1)) := by
    rw [← map_pow, DZ_pow_three_eq, map_mul]
  have key : algebraMap (Polynomial ℂ) (RatFunc ℂ) (PhiNumZ W)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (PsiZ c * (X ^ 3 * (X - 1))) := by
    rw [map_mul, hcl, hmap]
    field_simp
  exact IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ) key

end Work.A14D
