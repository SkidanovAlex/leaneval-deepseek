import Mathlib
import Submission.Work.LinnikAreas.SiegelBase

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

/-- **Siegel's bound with `ε = 1/200`, in the `λ`-normalisation.** There is an absolute constant
`C > 0` such that for every `q ≥ 2` and every Siegel datum `(χ₁, β₁)` mod `q` (`χ₁ ≠ 1` real,
`β₁ < 1`, `zeroMult χ₁ β₁ ≠ 0`) one has `C·log q / q^{1/200} ≤ λ₁ = lamOf q β₁`.

Recipe: `Commons.NumberTheory.DirichletCharacter.LFunction_realZero_siegel_uniform` at `ε = 1/200`
gives `C·N^{-1/200} ≤ 1 - β` for the primitive character `χ₁.primitiveCharacter` inducing `χ₁`,
where `N = χ₁.conductor`. Chasing it through `λ₁ = (1-β)·log q` exactly as
`Work.LinnikAreas.Siegel.lamOf_lower_bound` (in `Submission/Work/LinnikAreas/SiegelBase.lean`)
does with `ε = 1/2` (there via `√(conductor) ≤ √q`) yields the claim, using
`conductor ≤ q ⟹ q^{-1/200} ≤ conductor^{-1/200}` (both exponents negative). -/
theorem lamOfEps200 :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], 2 ≤ q →
      ∀ (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
      χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → Work.LinnikContract.zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
      C * Real.log q / (q : ℝ) ^ (1 / 200 : ℝ) ≤ Work.LinnikContract.lamOf q (β₁ : ℂ) := by
  obtain ⟨C, hCpos, hC⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_realZero_siegel_uniform (1 / 200)
      (by norm_num)
  refine ⟨C, hCpos, ?_⟩
  intro q _ hq2 χ β hχ hsq hβ1 hz
  have hβ0 : 0 < β := Siegel.re_mem_Ioo hχ hβ1 hz
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hprim := DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hne : χ.primitiveCharacter ≠ 1 := Siegel.primitive_ne_one hχ
  have hsq' : χ.primitiveCharacter * χ.primitiveCharacter = 1 := by
    have h2 := Siegel.primitive_sq_one hsq
    rwa [pow_two] at h2
  have hzL : LFunction χ.primitiveCharacter (β : ℂ) = 0 := by
    rw [@DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ.conductor
      ⟨χ.conductor_ne_zero⟩ χ.primitiveCharacter (β : ℂ)
      (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt hβ0))),
      Siegel.completedLFunction_eq_zero_of_zeroMult χ hz, zero_div]
  have hSie := hC χ.conductor χ.primitiveCharacter hprim hne hsq' β hβ0 hβ1 hzL
  have hcond_pos : 0 < (χ.conductor : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hcond_le : (χ.conductor : ℝ) ≤ (q : ℝ) :=
    by exact_mod_cast Nat.le_of_dvd (by omega) χ.conductor_dvd_level
  have hexpneg : -(1 / 200 : ℝ) ≤ 0 := by norm_num
  have h1 : (q : ℝ) ^ (-(1 / 200 : ℝ)) ≤ (χ.conductor : ℝ) ^ (-(1 / 200 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hcond_pos hcond_le hexpneg
  have h2 : C * (q : ℝ) ^ (-(1 / 200 : ℝ)) * Real.log q ≤ (1 - β) * Real.log q :=
    le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hCpos.le) hlogq.le)
      (mul_le_mul_of_nonneg_right hSie hlogq.le)
  have h3 : C * (q : ℝ) ^ (-(1 / 200 : ℝ)) * Real.log q
      = C * Real.log q / (q : ℝ) ^ (1 / 200 : ℝ) := by
    rw [Real.rpow_neg (le_of_lt hqpos)]
    ring
  rw [h3] at h2
  rw [Work.LinnikContract.lamOf, Complex.ofReal_re]
  linarith [h2]

end

end Work.LinnikAreas
