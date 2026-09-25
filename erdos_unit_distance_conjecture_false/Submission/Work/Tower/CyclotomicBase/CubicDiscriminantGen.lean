import Mathlib
import Submission.Work.Tower.CubicDiscriminant

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.Tower.CyclotomicBase

open NumberField Module

/-- For a prime `r ≡ 1 (mod 3)`, any cubic intermediate field `F` of a `r`-th cyclotomic
extension `L/ℚ` has discriminant of absolute value `r ^ 2`.

This is the same statement as `Work.Tower.CubicDiscriminant`, but for an abstract cyclotomic
extension `L` of `ℚ` rather than the concrete model `CyclotomicField r ℚ`: the proof only uses
the abstract properties of `IsCyclotomicExtension {r} ℚ L`.

Since `F/ℚ` is abelian (as a subfield of the cyclotomic field `L`), the tower formula for
the different ideal gives
`r ^ (r - 2) = |disc L| = |disc F| ^ ((r-1)/3) * N(different of L/F)`,
so `|disc F|` is a power `r ^ a` of `r`, with `a * (r-1)/3 ≤ r - 2`, hence `a ≤ 2`.
Moreover `disc F` is a square in `ℚ`: the Vandermonde determinant exhibits a square root of
`disc F` inside `F`, and taking norms gives that `(disc F) ^ 3 = (disc F) ^ [F : ℚ]` is a square,
so `disc F` itself is a square. Hence `a = 2` and `|disc F| = r ^ 2`. -/
theorem CubicDiscriminantGen (r : ℕ) (hr : Nat.Prime r) (hr3 : r % 3 = 1)
    (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {r} ℚ L]
    (F : IntermediateField ℚ L) (h3 : Module.finrank ℚ ↥F = 3)
    (hreal : NumberField.IsTotallyReal ↥F) :
    |NumberField.discr ↥F| = (r : ℤ) ^ 2 := by
  haveI : Fact (Nat.Prime r) := ⟨hr⟩
  haveI : NeZero r := ⟨hr.ne_zero⟩
  haveI hab : IsAbelianGalois ℚ L :=
    IsCyclotomicExtension.isAbelianGalois {r} ℚ L
  have hmul : 3 * ((r - 1) / 3) = r - 1 := by omega
  have hL : Module.finrank ℚ L = r - 1 := by
    rw [IsCyclotomicExtension.Rat.finrank r L, Nat.totient_prime hr]
  have hm : Module.finrank ↥F L = (r - 1) / 3 := by
    have h := Module.finrank_mul_finrank ℚ ↥F L
    rw [h3, hL] at h
    rw [← h, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]
  have hdiscL : (NumberField.discr L).natAbs = r ^ (r - 2) := by
    rw [IsCyclotomicExtension.Rat.discr_prime r L]
    simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    norm_num
  have htower := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    ↥F (𝓞 ↥F) L (𝓞 L)
  rw [hm, hdiscL] at htower
  have hdiv : (NumberField.discr ↥F).natAbs ^ ((r - 1) / 3) ∣ r ^ (r - 2) := by
    refine ⟨Ideal.absNorm (differentIdeal (𝓞 ↥F) (𝓞 L)), ?_⟩
    rw [htower]; exact mul_comm _ _
  have hx1 : (NumberField.discr ↥F).natAbs ≠ 1 := by
    have h := NumberField.abs_discr_gt_two (K := ↥F) (by rw [h3]; norm_num)
    rw [← Int.natCast_natAbs] at h
    omega
  obtain ⟨d, hd⟩ := exists_sq_eq_algebraMap_discr ↥F
  have hsq3 : IsSquare ((NumberField.discr ↥F : ℚ) ^ 3) := by
    refine ⟨Algebra.norm ℚ d, ?_⟩
    have h := congrArg (Algebra.norm ℚ) hd
    simp only [map_pow] at h
    rw [Algebra.norm_algebraMap, h3] at h
    rw [← h, pow_two]
  have hsq : IsSquare ((NumberField.discr ↥F : ℚ)) := by
    obtain ⟨q, hq⟩ := hsq3
    have hx0' : (NumberField.discr ↥F : ℚ) ≠ 0 := by
      rw [Int.cast_ne_zero]; exact NumberField.discr_ne_zero ↥F
    refine ⟨q / (NumberField.discr ↥F : ℚ), ?_⟩
    field_simp
    nlinarith [hq]
  have hsqZ : IsSquare (NumberField.discr ↥F) := Rat.isSquare_intCast_iff.mp hsq
  have hsqNat : IsSquare (NumberField.discr ↥F).natAbs := by
    obtain ⟨m, hm'⟩ := hsqZ
    rw [hm', Int.natAbs_mul]
    exact ⟨m.natAbs, rfl⟩
  have hres := sq_eq_prime_sq_of_dvd hr hmul hdiv hx1 hsqNat
  rw [← Int.natCast_natAbs, hres, Nat.cast_pow]

end Work.Tower.CyclotomicBase

