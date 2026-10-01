import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_realZero_siegel_uniform
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip

/-!
# Small `λ` forces a large conductor

For a real (quadratic) non-principal character `χ₀` of level `q` carrying a **real** zero `ρ₀`
with `λ(ρ₀) = (1 - Re ρ₀)·log q ≤ 1/100`, the conductor of `χ₀` is large: for every bound `Q`
there is a threshold `q₀` such that `q₀ ≤ q` forces `Q ≤ χ₀.conductor`.

The input is Siegel's ineffective uniform zero-free region
(`Commons.NumberTheory.DirichletCharacter.LFunction_realZero_siegel_uniform`, with `ε = 1/2`):
for a real primitive character of conductor `N` and a real zero `β ∈ (0,1)` of its
`L`-function, `C·N^{-1/2} ≤ 1 - β`.  Applied to the primitive character inducing `χ₀`
(of conductor `f = χ₀.conductor`) this gives

`(1 - ρ₀.re)·log q = λ(ρ₀) ≥ C·(log q)/√f`,

so the hypothesis `λ(ρ₀) ≤ 1/100` forces `f ≥ (100·C·log q)²`.  Choosing the threshold `q₀` so
that `log q ≥ √Q/(100·C)` for `q ≥ q₀` then gives `Q ≤ f`, as required.
-/

namespace Work.LinnikAreas.DhExplicit

open DirichletCharacter
open scoped Classical

/-- A non-principal character has non-principal primitive character. -/
private lemma primitiveCharacter_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (h : χ ≠ 1) : χ.primitiveCharacter ≠ 1 := by
  intro h1
  refine h ?_
  rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h1]
  exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level

/-- A real (quadratic) character has a real primitive character. -/
private lemma primitiveCharacter_sq_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (h : χ ^ 2 = 1) : χ.primitiveCharacter * χ.primitiveCharacter = 1 := by
  have h2 : χ.primitiveCharacter ^ 2 = 1 := by
    refine (DirichletCharacter.changeLevel_eq_one_iff χ.conductor_dvd_level).mp ?_
    rw [map_pow, DirichletCharacter.changeLevel_primitiveCharacter, h]
  rwa [pow_two] at h2

theorem conductor_large_of_lambda_small : ∀ Q : ℕ, ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ),
    χ₀ ≠ 1 → χ₀ ^ 2 = 1 → ρ₀.im = 0 → Work.LinnikContract.zeroMult χ₀ ρ₀ ≠ 0 →
    Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 → Q ≤ χ₀.conductor := by
  intro Q
  -- Siegel's uniform zero-free region with `ε = 1/2`
  obtain ⟨C, hCpos, hC⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_realZero_siegel_uniform (1 / 2)
      (by norm_num)
  -- the threshold: `log q ≥ √Q/(100 C)` for `q ≥ q₀`
  obtain ⟨N, hN⟩ := exists_nat_ge (Real.exp (Real.sqrt (Q : ℝ) / (100 * C)))
  refine ⟨max 2 N, ?_⟩
  intro q hq
  have hq2 : 2 ≤ q := le_trans (le_max_left 2 N) hq
  have hqN : N ≤ q := le_trans (le_max_right 2 N) hq
  have hq1 : 1 < q := by omega
  have hNpos : 0 < N := by
    have h : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hN
    exact_mod_cast h
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq1)
  have hlog_ge : Real.sqrt (Q : ℝ) / (100 * C) ≤ Real.log q := by
    have h1 : Real.log (Real.exp (Real.sqrt (Q : ℝ) / (100 * C))) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (Real.exp_pos _) hN
    have h2 : Real.log (N : ℝ) ≤ Real.log (q : ℝ) :=
      Real.log_le_log (by exact_mod_cast hNpos) (by exact_mod_cast hqN)
    rw [Real.log_exp] at h1
    linarith
  have hsqrtQ : Real.sqrt (Q : ℝ) ≤ 100 * C * Real.log q := by
    have hC100 : 0 < 100 * C := by positivity
    have h := (div_le_iff₀ hC100).mp hlog_ge
    calc Real.sqrt (Q : ℝ) ≤ Real.log q * (100 * C) := h
      _ = 100 * C * Real.log q := by ring
  intros _ χ₀ ρ₀ hχ1 hχ2 him hzm hlam
  letI : NeZero χ₀.conductor := ⟨χ₀.conductor_ne_zero⟩
  -- `ρ₀` is the real number `ρ₀.re`
  have hβeq : ρ₀ = ((ρ₀.re : ℂ)) := by
    refine Complex.ext ?_ ?_ <;> simp [him]
  have hzm' : Work.LinnikContract.zeroMult χ₀ ((ρ₀.re : ℂ)) ≠ 0 := by
    rw [hβeq] at hzm; exact hzm
  -- `ρ₀.re` is a zero of the completed `L`-function of the primitive character
  have hΛ : completedLFunction χ₀.primitiveCharacter ((ρ₀.re : ℂ)) = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero
      (by simpa only [Work.LinnikContract.zeroMult] using hzm')
  -- hence it lies in the critical strip
  obtain ⟨hβ0, hβ1⟩ :=
    Commons.NumberTheory.Linnik.completedL_zero_strip χ₀.primitiveCharacter
      (primitiveCharacter_ne_one hχ1)
      (DirichletCharacter.primitiveCharacter_isPrimitive χ₀) hΛ
  have hsq' := primitiveCharacter_sq_one hχ2
  have hLz : DirichletCharacter.LFunction χ₀.primitiveCharacter ((ρ₀.re : ℂ)) = 0 := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ₀.primitiveCharacter ((ρ₀.re : ℂ))
        (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt hβ0))), hΛ, zero_div]
  -- Siegel's theorem at the level of the conductor of `χ₀`
  have hsie := hC χ₀.conductor χ₀.primitiveCharacter
      (DirichletCharacter.primitiveCharacter_isPrimitive χ₀)
      (primitiveCharacter_ne_one hχ1) hsq' ρ₀.re hβ0 hβ1 hLz
  have hcond_nonneg : (0 : ℝ) ≤ (χ₀.conductor : ℝ) := Nat.cast_nonneg _
  have hsqrt_pos : 0 < Real.sqrt (χ₀.conductor : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero χ₀.conductor_ne_zero)
  have hsie' : C / Real.sqrt (χ₀.conductor : ℝ) ≤ 1 - ρ₀.re := by
    have h : (χ₀.conductor : ℝ) ^ (-(1 / 2) : ℝ) = (Real.sqrt (χ₀.conductor : ℝ))⁻¹ := by
      rw [Real.rpow_neg hcond_nonneg, ← Real.sqrt_eq_rpow]
    rw [h] at hsie
    simpa [div_eq_mul_inv] using hsie
  have hkey : C * Real.log q / Real.sqrt (χ₀.conductor : ℝ) ≤ Work.LinnikContract.lamOf q ρ₀ := by
    have h1 : (C / Real.sqrt (χ₀.conductor : ℝ)) * Real.log q ≤ (1 - ρ₀.re) * Real.log q :=
      mul_le_mul_of_nonneg_right hsie' hlogq.le
    calc C * Real.log q / Real.sqrt (χ₀.conductor : ℝ)
        = (C / Real.sqrt (χ₀.conductor : ℝ)) * Real.log q := by ring
      _ ≤ (1 - ρ₀.re) * Real.log q := h1
      _ = Work.LinnikContract.lamOf q ρ₀ := rfl
  have hmain : C * Real.log q / Real.sqrt (χ₀.conductor : ℝ) ≤ 1 / 100 := le_trans hkey hlam
  have h100 : 100 * C * Real.log q ≤ Real.sqrt (χ₀.conductor : ℝ) := by
    have h := (div_le_iff₀ hsqrt_pos).mp hmain
    nlinarith [h]
  have hfinal : (Q : ℝ) ≤ (χ₀.conductor : ℝ) := by
    have h1 : (Real.sqrt (Q : ℝ)) ^ 2 ≤ (100 * C * Real.log q) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrtQ 2
    have h2 : (100 * C * Real.log q) ^ 2 ≤ (Real.sqrt (χ₀.conductor : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h100 2
    have h3 : (Real.sqrt (Q : ℝ)) ^ 2 = (Q : ℝ) := Real.sq_sqrt (Nat.cast_nonneg Q)
    have h4 : (Real.sqrt (χ₀.conductor : ℝ)) ^ 2 = (χ₀.conductor : ℝ) := Real.sq_sqrt hcond_nonneg
    linarith [h1, h2, h3, h4]
  exact_mod_cast hfinal

end Work.LinnikAreas.DhExplicit
