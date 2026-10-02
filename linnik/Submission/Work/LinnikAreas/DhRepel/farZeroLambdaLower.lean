import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
import Submission.Commons.NumberTheory.DirichletCharacter.lFunction_order_eq_completed_order_on_strip
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Work.LinnikContract.Defs

namespace Work.LinnikAreas.DhRepel

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option autoImplicit false
set_option linter.style.haveILetI false

/-- A non-principal character of level `q ≠ 0` has a non-principal primitive character. -/
theorem primitive_ne_one' {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (h : χ ≠ 1) :
    χ.primitiveCharacter ≠ 1 := by
  intro h1
  refine h ?_
  rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h1]
  exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level

/-- `zeroMult χ u ≠ 0` means that `u` is a zero of the completed `L`-function of the primitive
character inducing `χ`. -/
theorem completedLFunction_primitive_eq_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {u : ℂ} (h : Work.LinnikContract.zeroMult χ u ≠ 0) :
    @completedLFunction χ.conductor ⟨χ.conductor_ne_zero⟩ χ.primitiveCharacter u = 0 :=
  apply_eq_zero_of_analyticOrderNatAt_ne_zero (by simpa only [Work.LinnikContract.zeroMult] using h)

/-- `zeroMult χ u ≠ 0` means that `u` is a zero of the ordinary `L`-function of the primitive
character inducing `χ`. -/
theorem LFunction_primitive_eq_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [hcond : NeZero χ.conductor] (hχ : χ ≠ 1) {u : ℂ}
    (h : Work.LinnikContract.zeroMult χ u ≠ 0) :
    DirichletCharacter.LFunction χ.primitiveCharacter u = 0 := by
  have hΛ : completedLFunction χ.primitiveCharacter u = 0 := completedLFunction_primitive_eq_zero χ h
  have hstrip := Commons.NumberTheory.Linnik.completedL_zero_strip χ.primitiveCharacter
    (primitive_ne_one' hχ) (DirichletCharacter.primitiveCharacter_isPrimitive χ) hΛ
  have hordC : analyticOrderNatAt (completedLFunction χ.primitiveCharacter) u ≠ 0 := by
    simpa only [Work.LinnikContract.zeroMult] using h
  have hord := Commons.NumberTheory.DirichletCharacter.lFunction_order_eq_completed_order_on_strip
    χ.primitiveCharacter (primitive_ne_one' hχ) hstrip.1 hstrip.2
  have hordL : analyticOrderNatAt (DirichletCharacter.LFunction χ.primitiveCharacter) u ≠ 0 := by
    rw [hord]; exact hordC
  exact apply_eq_zero_of_analyticOrderNatAt_ne_zero hordL

/-- **Far zeros of non-principal `L`-functions have bounded `λ`.**  There is an absolute
constant `c > 0` such that for every sufficiently large modulus `q`, every non-principal
character `χ` of level `q` and every zero `u` of `L(s,χ)` with `1 ≤ |Im u| ≤ 4` satisfy
`λ(u) = (1 - Re u)·log q ≥ c`.  This is the classical (de la Vallée Poussin) zero-free region,
applied to the primitive character inducing `χ`: off the real axis there is no exceptional zero,
so the zero-free region is uniform in the character. -/
theorem farZeroLambdaLower : ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 →
    1 ≤ |u.im| → |u.im| ≤ 4 → c ≤ Work.LinnikContract.lamOf q u := by
  obtain ⟨c₀, hc₀pos, hc₀⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
  refine ⟨c₀ / 2, by linarith, 6, ?_⟩
  intro q hq inst χ hχ u hzm him1 him4
  haveI hcond : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  -- `u` is a zero of the `L`-function of the primitive character `χ*`
  have hL0 : DirichletCharacter.LFunction χ.primitiveCharacter u = 0 :=
    LFunction_primitive_eq_zero χ hχ hzm
  have hu_eq : u = (u.re : ℂ) + (u.im : ℂ) * Complex.I := (Complex.re_add_im u).symm
  have hL0' : DirichletCharacter.LFunction χ.primitiveCharacter
      ((u.re : ℂ) + (u.im : ℂ) * Complex.I) = 0 := by
    rw [← hu_eq]; exact hL0
  -- the imaginary part is non-zero
  have hγ0 : u.im ≠ 0 := by
    intro h
    rw [h] at him1
    norm_num at him1
  -- the zero-free region forbids `u.re` from being too large
  have hnoZF := hc₀ (χ := χ.primitiveCharacter)
    (DirichletCharacter.primitiveCharacter_isPrimitive χ) (primitive_ne_one' hχ) u.re u.im hγ0
  have hkey : u.re < 1 - c₀ / Real.log ((χ.conductor : ℝ) * (|u.im| + 2)) := by
    by_contra hcon
    push_neg at hcon
    exact (hnoZF hcon) hL0'
  -- numeric bounds
  have hq6 : (6 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) < (q : ℝ) := by linarith
  have hlogq : 0 < Real.log q := Real.log_pos hq1
  have hNpos : 0 < (χ.conductor : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hNle : (χ.conductor : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have h2 : |u.im| + 2 ≤ 6 := by linarith [abs_nonneg u.im]
  have hPpos : 0 < (χ.conductor : ℝ) * (|u.im| + 2) := by
    have : 0 < |u.im| + 2 := by linarith [abs_nonneg u.im]
    positivity
  have hN6 : (χ.conductor : ℝ) * (|u.im| + 2) ≤ 6 * (q : ℝ) := by
    calc (χ.conductor : ℝ) * (|u.im| + 2) ≤ (q : ℝ) * 6 :=
          mul_le_mul hNle h2 (by linarith [abs_nonneg u.im]) (by positivity)
      _ = 6 * (q : ℝ) := by ring
  have hlogPpos : 0 < Real.log ((χ.conductor : ℝ) * (|u.im| + 2)) := by
    apply Real.log_pos
    have hN1 : (1 : ℝ) ≤ (χ.conductor : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr χ.conductor_ne_zero
    nlinarith [hN1, abs_nonneg u.im]
  have hlog_le : Real.log ((χ.conductor : ℝ) * (|u.im| + 2)) ≤ 2 * Real.log q := by
    have h1 : Real.log ((χ.conductor : ℝ) * (|u.im| + 2)) ≤ Real.log (6 * (q : ℝ)) :=
      Real.log_le_log hPpos hN6
    have h2' : Real.log (6 * (q : ℝ)) = Real.log 6 + Real.log q :=
      Real.log_mul (by norm_num) (by linarith : (q : ℝ) ≠ 0)
    have h3 : Real.log 6 ≤ Real.log q := Real.log_le_log (by norm_num) hq6
    rw [h2'] at h1
    linarith
  -- `1 - u.re > c₀/log(N(|t|+2))`
  have h1u : c₀ / Real.log ((χ.conductor : ℝ) * (|u.im| + 2)) < 1 - u.re := by linarith
  -- hence `λ > c₀ log q / log(N(|t|+2))`
  have hlam : c₀ * Real.log q / Real.log ((χ.conductor : ℝ) * (|u.im| + 2))
      < Work.LinnikContract.lamOf q u := by
    rw [Work.LinnikContract.lamOf]
    have := mul_lt_mul_of_pos_right h1u hlogq
    rwa [div_mul_eq_mul_div] at this
  -- and the latter is `≥ c₀/2`
  have hfirst : c₀ / 2 ≤ c₀ * Real.log q / Real.log ((χ.conductor : ℝ) * (|u.im| + 2)) := by
    rw [le_div_iff₀ hlogPpos]
    nlinarith [hlog_le, hc₀pos, hlogq]
  exact le_trans hfirst hlam.le

end

end Work.LinnikAreas.DhRepel
