import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.CycLevel

/-- If a `q`-th power of a rational number is a natural number, then that natural
number is itself a `q`-th power (of the absolute value of the numerator of the rational). -/
theorem rat_pow_eq_nat_pow {q m : ℕ} (hm : 0 < m) {y : ℚ} (hy : y ^ q = (m : ℚ)) :
    ∃ m' : ℕ, 0 < m' ∧ m = m' ^ q := by
  rcases Nat.eq_zero_or_pos q with hq0 | hq
  · -- q = 0 : then `m = 1 = 1 ^ 0`
    subst hq0
    refine ⟨1, Nat.one_pos, ?_⟩
    have h1 : (m : ℚ) = 1 := by simpa using hy.symm
    have hm1 : m = 1 := Nat.cast_injective h1
    rw [hm1]
    norm_num
  · -- q > 0 : `y` is integral over `ℤ`, hence an integer, since `ℤ` is integrally closed in `ℚ`.
    obtain ⟨z, hz⟩ : ∃ z : ℤ, (z : ℚ) = y := by
      have hx : IsIntegral ℤ (y ^ q) := by
        rw [hy]
        exact isIntegral_algebraMap
      obtain ⟨z, hz⟩ :=
        IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := ℤ) (K := ℚ) hq hx
      exact ⟨z, by simpa using hz⟩
    -- lift `y ^ q = m` to `ℤ`
    have hzq : z ^ q = (m : ℤ) := by
      have hc : ((z ^ q : ℤ) : ℚ) = (m : ℚ) := by
        rw [Int.cast_pow, hz]
        exact hy
      exact Int.cast_injective hc
    refine ⟨z.natAbs, ?_, ?_⟩
    · -- positivity: `z ≠ 0`, else `m = 0`
      rw [Int.natAbs_pos]
      rintro rfl
      rw [zero_pow hq.ne'] at hzq
      have hm0 : m = 0 := by exact_mod_cast hzq.symm
      omega
    · -- `m = |z| ^ q`
      have hpq : z.natAbs ^ q = m := by
        rw [← Int.natAbs_pow, hzq, Int.natAbs_natCast]
      exact hpq.symm

end Work.SSGRoute.CycLevel
