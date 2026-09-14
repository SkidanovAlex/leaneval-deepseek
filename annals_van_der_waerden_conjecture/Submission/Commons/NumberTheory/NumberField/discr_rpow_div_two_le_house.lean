import Mathlib
import Submission.Commons.NumberTheory.NumberField.abs_discr_le_two_house_pow

namespace Commons.NumberTheory.NumberField

/-- Elementary real inequality: if `0 ≤ D`, `0 ≤ H` and `D ≤ (2H)^E` with `0 < E`, then
`D ^ (1/E) / 2 ≤ H`. -/
theorem rpow_one_div_two_le_of_le_pow {D H : ℝ} {E : ℕ} (hE : 0 < E)
    (hD : 0 ≤ D) (hH : 0 ≤ H) (h : D ≤ (2 * H) ^ E) :
    D ^ (1 / (E : ℝ)) / 2 ≤ H := by
  have hEpos : (0 : ℝ) < (E : ℝ) := by exact_mod_cast hE
  have hbase : (0 : ℝ) ≤ 2 * H := by positivity
  have h' : D ≤ (2 * H) ^ ((E : ℝ)) := by rwa [Real.rpow_natCast]
  have step1 : D ^ (1 / (E : ℝ)) ≤ ((2 * H) ^ ((E : ℝ))) ^ (1 / (E : ℝ)) :=
    Real.rpow_le_rpow hD h' (by positivity)
  have step2 : ((2 * H) ^ ((E : ℝ))) ^ (1 / (E : ℝ)) = 2 * H := by
    have hm : (2 * H) ^ ((E : ℝ) * (1 / (E : ℝ))) =
        ((2 * H) ^ ((E : ℝ))) ^ (1 / (E : ℝ)) :=
      Real.rpow_mul hbase (E : ℝ) (1 / (E : ℝ))
    rw [mul_one_div, div_self hEpos.ne', Real.rpow_one] at hm
    exact hm.symm
  have step3 : D ^ (1 / (E : ℝ)) ≤ 2 * H := step1.trans (le_of_eq step2)
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

theorem discr_rpow_div_two_le_house {K : Type*} [Field K] [NumberField K] {N : ℕ}
    (hN : Module.finrank ℚ K = N) (h2 : 2 ≤ N)
    (hgen : ∀ α : K, α ∉ Set.range (algebraMap ℚ K) → Algebra.adjoin ℚ ({α} : Set K) = ⊤)
    {α : NumberField.RingOfIntegers K}
    (hα : ((α : K)) ∉ Set.range (algebraMap ℤ K)) :
    |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / ((N : ℝ) * ((N : ℝ) - 1))) / 2
      ≤ NumberField.house ((α : K)) := by
  have hE : 0 < N * (N - 1) := Nat.mul_pos (by omega) (by omega)
  have hintK : IsIntegral ℤ ((α : K)) := α.isIntegral_coe
  have hαQ : ((α : K)) ∉ Set.range (algebraMap ℚ K) := by
    rintro ⟨q, hq⟩
    have hIntq : IsIntegral ℤ q := by
      have h1 : IsIntegral ℤ (algebraMap ℚ K q) := by
        have := hintK
        rwa [← hq] at this
      exact (isIntegral_algebraMap_iff (RingHom.injective (algebraMap ℚ K))).mp h1
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hIntq
    exact hα ⟨z, by rw [← hq, ← hz, IsScalarTower.algebraMap_apply ℤ ℚ K z]⟩
  have hgenK : Algebra.adjoin ℚ ({((α : K))} : Set K) = ⊤ := hgen _ hαQ
  have hbound := abs_discr_le_two_house_pow hN hgenK hintK
  have hcast : ((N * (N - 1) : ℕ) : ℝ) = (N : ℝ) * ((N : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : (1 : ℕ) ≤ N)]
    push_cast
    ring
  have hgoal : |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / ((N * (N - 1) : ℕ) : ℝ)) / 2
      ≤ NumberField.house ((α : K)) :=
    rpow_one_div_two_le_of_le_pow hE (abs_nonneg _) (NumberField.house_nonneg _) hbound
  rwa [hcast] at hgoal

end Commons.NumberTheory.NumberField
