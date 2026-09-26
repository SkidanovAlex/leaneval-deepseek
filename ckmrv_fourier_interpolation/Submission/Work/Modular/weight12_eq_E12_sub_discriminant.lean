import Mathlib
import Submission.Work.Modular.EisensteinDelta

namespace Work.Modular

open Work.Modular
open scoped MatrixGroups ModularForm
open UpperHalfPlane ModularForm

/-- The constant `q`-expansion coefficient of `E₁₂` is `1`
(`E₁₂` is the normalised Eisenstein series of weight twelve). -/
private lemma E12_qExpansion_coeff_zero : (qExpansion 1 E12).coeff 0 = 1 :=
  EisensteinSeries.E_qExpansion_coeff_zero (by norm_num : (3 : ℕ) ≤ 12) (by norm_num)

/-- The first `q`-expansion coefficient of `E₁₂` is `65520/691`, i.e. `-(2·12)/B₁₂`
with `B₁₂ = -691/2730`. -/
private lemma E12_qExpansion_coeff_one : (qExpansion 1 E12).coeff 1 = 65520 / 691 := by
  rw [EisensteinSeries.E_qExpansion_coeff (by norm_num : (3 : ℕ) ≤ 12) (by norm_num) 1]
  norm_num [ArithmeticFunction.sigma_one, show bernoulli 12 = -691 / 2730 by decide +kernel]

/-- The constant `q`-expansion coefficient of `Δ` vanishes: `Δ` is a cusp form. -/
private lemma Delta_qExpansion_coeff_zero : (qExpansion 1 Delta).coeff 0 = 0 := by
  rw [show Delta = ⇑(CuspForm.discriminant) from CuspForm.coe_discriminant.symm]
  exact CuspFormClass.qExpansion_coeff_zero _ one_pos one_mem_strictPeriods_SL

/-- The first `q`-expansion coefficient of `Δ` is `1`. -/
private lemma Delta_qExpansion_coeff_one : (qExpansion 1 Delta).coeff 1 = 1 :=
  ModularForm.discriminant_qExpansion_coeff_one

/-- `CuspForm.discriminant`, viewed as a modular form of weight twelve, is `Δ`. -/
private lemma coe_discriminant_fun :
    ((CuspForm.discriminant : ModularForm 𝒮ℒ 12) : ℍ → ℂ) = Delta := by
  ext z
  simp [CuspForm.coe_discriminant]

/-- A level-one modular form of weight `12` whose `q`-expansion starts `1 + 0·q + …` is
`E₁₂ - (65520/691) Δ`.  Indeed the difference from `E₁₂ - (65520/691) Δ` has vanishing
`q`-coefficients in degrees `0` and `1`, so it vanishes by the Sturm bound
(`ModularForm.sturm_bound_levelOne`, which for weight `12` allows exactly order `> 1`). -/
theorem weight12_eq_E12_sub_discriminant (g : ModularForm 𝒮ℒ 12)
    (h0 : (UpperHalfPlane.qExpansion 1 (⇑g : ℍ → ℂ)).coeff 0 = 1)
    (h1 : (UpperHalfPlane.qExpansion 1 (⇑g : ℍ → ℂ)).coeff 1 = 0) :
    (⇑g : ℍ → ℂ) = fun τ => E12 τ - (65520 / 691) * Delta τ := by
  have hE0 := E12_qExpansion_coeff_zero
  have hE1 := E12_qExpansion_coeff_one
  have hD0 := Delta_qExpansion_coeff_zero
  have hD1 := Delta_qExpansion_coeff_one
  -- The candidate modular form `F = E₁₂ - (65520/691) Δ`.
  set F : ModularForm 𝒮ℒ 12 :=
    ModularForm.E (by norm_num : (3 : ℕ) ≤ 12) - (65520 / 691 : ℂ) •
      (CuspForm.discriminant : ModularForm 𝒮ℒ 12) with hF
  have hFfun : ⇑F = ⇑(ModularForm.E (by norm_num : (3 : ℕ) ≤ 12))
      - ⇑((65520 / 691 : ℂ) • (CuspForm.discriminant : ModularForm 𝒮ℒ 12)) := by
    rw [hF]; rfl
  -- The `q`-expansion of `F`.
  have hFq : qExpansion 1 ⇑F
      = qExpansion 1 E12 - (65520 / 691 : ℂ) • qExpansion 1 Delta := by
    rw [hFfun, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL _ _]
    rw [show qExpansion 1 ⇑((65520 / 691 : ℂ) • (CuspForm.discriminant : ModularForm 𝒮ℒ 12))
          = (65520 / 691 : ℂ) • qExpansion 1 Delta from by
        rw [show ⇑((65520 / 691 : ℂ) • (CuspForm.discriminant : ModularForm 𝒮ℒ 12))
              = (65520 / 691 : ℂ) • ⇑(CuspForm.discriminant : ModularForm 𝒮ℒ 12) from by simp,
            ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL _ _,
            coe_discriminant_fun]]
  -- Its two lowest `q`-coefficients: `1` and `0`.
  have hFc0 : (qExpansion 1 ⇑F).coeff 0 = 1 := by
    have h := congrArg (fun p : PowerSeries ℂ => p.coeff 0) hFq
    simp only [map_sub, PowerSeries.coeff_smul, smul_eq_mul, hE0, hD0, mul_zero,
      sub_zero] at h
    exact h
  have hFc1 : (qExpansion 1 ⇑F).coeff 1 = 0 := by
    have h := congrArg (fun p : PowerSeries ℂ => p.coeff 1) hFq
    simp only [map_sub, PowerSeries.coeff_smul, smul_eq_mul, hE1, hD1, mul_one,
      sub_self] at h
    exact h
  -- Sturm's bound: `g - F` vanishes because its first two `q`-coefficients do.
  have hgF : g = F := by
    rw [← sub_eq_zero]
    apply ModularForm.sturm_bound_levelOne
    have hord : ((12 : ℤ).toNat / 12 : ℕ) = 1 := by decide
    rw [hord]
    simp only [Nat.cast_one]
    refine lt_of_lt_of_le (by norm_num : (1 : ℕ∞) < 2) (PowerSeries.nat_le_order _ 2 ?_)
    intro i hi
    have hgs : qExpansion 1 ⇑(g - F) = qExpansion 1 ⇑g - qExpansion 1 ⇑F := by
      have h := ModularForm.qExpansion_sub (Γ := 𝒮ℒ) one_pos one_mem_strictPeriods_SL g F
      simpa using h
    rw [hgs]
    interval_cases i
    · simp only [map_sub, h0, hFc0, sub_self]
    · simp only [map_sub, h1, hFc1, sub_self]
  rw [hgF, hFfun]
  ext τ
  simp [E12]

end Work.Modular
