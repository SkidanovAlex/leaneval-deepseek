import Mathlib
import Submission.Work.LinnikAreas.SiegelBase
import Submission.Work.LinnikAreas.siegelZeroSimple_ldUpper
import Submission.Work.LinnikAreas.siegelZeroSimple_zeroSum
import Submission.Work.LinnikAreas.siegelZeroSimple_arith

/-!
# AREA 6 (Siegel case): Landau's simplicity of the exceptional zero

`Work.LinnikAreas.siegelSimpleInput : Work.LinnikAreas.Siegel.SimpleInput`, i.e. for every
sufficiently large modulus `q`, a real (`χ₁² = 1`) non-principal character `χ₁ (mod q)` whose
completed `L`-function vanishes at a real point `β₁ < 1` with `λ₁ = (1-β₁)log q ≤ 1/100` has `β₁`
as a *simple* zero.

The argument is the classical one, assembled here from the three ingredient lemmas imported
above.  Write `χ*` for the primitive character inducing `χ₁` (modulus `N = χ₁.conductor ∣ q`),
`Λ` for its completed `L`-function, and `m` for the order of `Λ` at `β₁`.  With
`σ = 1 + √λ₁ / log q`:

* `siegelZeroSimple_ldUpper` bounds the logarithmic derivative above on the real axis,
  `Re (Λ′/Λ)(σ) ≤ 1/(σ-1) + C`, uniformly in the character;
* `siegelZeroSimple_zeroSum` (the multiplicity-aware Hadamard partial fraction bound) turns this
  into the *lower* bound `m/(σ-β₁) ≤ Re (Λ′/Λ)(σ) + log N + log 2/2 + 3/2` at the zero;
* comparing the two, `m ≤ (1/(σ-1) + C + log N + log 2/2 + 3/2)·(σ-β₁)`, and
  `siegelZeroSimple_arith` shows the right-hand side is `< 2` for `q ≥ q₀(C)`, whence `m = 1`.
-/

open DirichletCharacter Complex
open scoped Classical

noncomputable section

namespace Work.LinnikAreas

open Work.LinnikContract

/-- **(S3) Landau's theorem: the exceptional zero is simple.**  Restated in the `Prop` form
`Siegel.SimpleInput` used by the AREA 6 assembly. -/
theorem siegelSimpleInput : Work.LinnikAreas.Siegel.SimpleInput := by
  unfold Work.LinnikAreas.Siegel.SimpleInput
  obtain ⟨C, hC⟩ := siegelZeroSimple_ldUpper
  obtain ⟨q0, hq0⟩ := siegelZeroSimple_arith C
  refine ⟨max q0 2, ?_⟩
  intro q hq hne χ₁ β₁ hχ1 hsq hβ1 hz hlam
  have hq2 : 2 ≤ q := le_trans (le_max_right _ _) hq
  have hq0le : q0 ≤ q := le_trans (le_max_left _ _) hq
  have hq1 : 1 < q := by omega
  have hlogq_pos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq1)
  have hlogq_ne : Real.log (q : ℝ) ≠ 0 := ne_of_gt hlogq_pos
  letI : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  have hχ'ne : χ₁.primitiveCharacter ≠ 1 := Siegel.primitive_ne_one hχ1
  have hχ'sq : χ₁.primitiveCharacter ^ 2 = 1 := Siegel.primitive_sq_one hsq
  have hχ'prim : (χ₁.primitiveCharacter).IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ₁
  have hz' : completedLFunction χ₁.primitiveCharacter (β₁ : ℂ) = 0 :=
    Siegel.completedLFunction_eq_zero_of_zeroMult χ₁ hz
  have hβ0 : 0 < β₁ := Siegel.re_mem_Ioo hχ1 hβ1 hz
  have hNne : χ₁.conductor ≠ 0 := χ₁.conductor_ne_zero
  have hN2 : 2 ≤ χ₁.conductor := by
    by_contra hcon
    have hN1 : χ₁.conductor = 1 := by omega
    exact hχ'ne (DirichletCharacter.level_one' (χ := χ₁.primitiveCharacter) hN1)
  have hNdvd : χ₁.conductor ∣ q := χ₁.conductor_dvd_level
  have hNle : χ₁.conductor ≤ q := Nat.le_of_dvd (by omega) hNdvd
  have hlam_eq : lamOf q (β₁ : ℂ) = (1 - β₁) * Real.log (q : ℝ) := by
    simp [Work.LinnikContract.lamOf]
  have hlam_pos : 0 < lamOf q (β₁ : ℂ) := by
    rw [hlam_eq]; exact mul_pos (by linarith) hlogq_pos
  have hbeta_eq : β₁ = 1 - lamOf q (β₁ : ℂ) / Real.log (q : ℝ) := by
    rw [hlam_eq]; field_simp; ring
  set σ : ℝ := 1 + Real.sqrt (lamOf q (β₁ : ℂ)) / Real.log (q : ℝ) with hσdef
  have hσ_gt1 : 1 < σ := by
    rw [hσdef]
    have h1 : 0 < Real.sqrt (lamOf q (β₁ : ℂ)) := Real.sqrt_pos.mpr hlam_pos
    have h2 : 0 < Real.sqrt (lamOf q (β₁ : ℂ)) / Real.log (q : ℝ) := div_pos h1 hlogq_pos
    linarith
  have hsqrt_le : Real.sqrt (lamOf q (β₁ : ℂ)) ≤ 1 / 10 := by
    have h := Real.sqrt_le_sqrt hlam
    rwa [show Real.sqrt (1 / 100 : ℝ) = 1 / 10 by
      rw [show (1:ℝ)/100 = (1/10)^2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
  have hlogq_ge : (2 : ℝ) / 5 ≤ Real.log (q : ℝ) := by
    have h1 : (2 : ℝ) / 5 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    exact le_trans h1 (Real.log_le_log (by norm_num) (by exact_mod_cast hq2))
  have hσ_le : σ ≤ 5 / 4 := by
    have hle : Real.sqrt (lamOf q (β₁ : ℂ)) / Real.log (q : ℝ) ≤ 1 / 4 := by
      rw [div_le_iff₀ hlogq_pos]; nlinarith [hsqrt_le, hlogq_ge]
    rw [hσdef]; linarith
  have hB : (logDeriv (completedLFunction χ₁.primitiveCharacter) (σ : ℂ)).re ≤ 1 / (σ - 1) + C :=
    hC χ₁.conductor χ₁.primitiveCharacter hχ'ne σ hσ_gt1 hσ_le
  have hsum := siegelZeroSimple_zeroSum χ₁.conductor χ₁.primitiveCharacter hχ'ne hχ'prim β₁ σ
    (1 / (σ - 1) + C) hβ0 hβ1 hz' hσ_gt1 hσ_le hB
  have hm_eq : ((zeroMult χ₁ (β₁ : ℂ) : ℕ) : ℝ) =
      ((analyticOrderNatAt (completedLFunction χ₁.primitiveCharacter) (β₁ : ℂ)) : ℝ) := by
    simp only [Work.LinnikContract.zeroMult]
  have hspos : 0 < σ - β₁ := by linarith
  have hmul : (zeroMult χ₁ (β₁ : ℂ) : ℝ) ≤
      (1 / (σ - 1) + C + Real.log (χ₁.conductor : ℝ) + Real.log 2 / 2 + 3 / 2) * (σ - β₁) := by
    rw [← hm_eq] at hsum
    have h2 := mul_le_mul_of_nonneg_right hsum hspos.le
    rw [div_mul_cancel₀ _ (ne_of_gt hspos)] at h2
    linarith [h2]
  have harith := hq0 q hq0le (χ₁.conductor : ℝ) (lamOf q (β₁ : ℂ))
    (by exact_mod_cast hq2) (by exact_mod_cast hN2) (by exact_mod_cast hNle) hlam_pos hlam
  have e1 : 1 / (σ - 1) = 1 / ((1 + Real.sqrt (lamOf q (β₁ : ℂ)) / Real.log (q : ℝ)) - 1) := by
    rw [hσdef]
  have e2 : σ - β₁ = (1 + Real.sqrt (lamOf q (β₁ : ℂ)) / Real.log (q : ℝ)) -
      (1 - lamOf q (β₁ : ℂ) / Real.log (q : ℝ)) := by
    rw [hσdef]; linarith only [hbeta_eq]
  have hlt : (zeroMult χ₁ (β₁ : ℂ) : ℝ) < 2 := by
    have h3 : (1 / (σ - 1) + C + Real.log (χ₁.conductor : ℝ) + Real.log 2 / 2 + 3 / 2) *
        (σ - β₁) < 2 := by
      rw [e1, e2]
      exact harith
    linarith [hmul, h3]
  have hge : 1 ≤ zeroMult χ₁ (β₁ : ℂ) := Nat.one_le_iff_ne_zero.mpr hz
  have h2 : zeroMult χ₁ (β₁ : ℂ) < 2 := by exact_mod_cast hlt
  omega

end Work.LinnikAreas
