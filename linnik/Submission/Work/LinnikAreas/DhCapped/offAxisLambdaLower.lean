import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.DhCapped.offAxisArith
import Submission.Work.LinnikAreas.DhCapped.LFunctionPrimitiveZero
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform

namespace Work.LinnikAreas.DhCapped

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- The primitive character inducing a non-principal character is non-principal: otherwise
`changeLevel χ.conductor_dvd_level` of `1` would be `χ` itself. -/
private lemma primitiveCharacter_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (h : χ ≠ 1) : χ.primitiveCharacter ≠ 1 := by
  intro h1
  refine h ?_
  rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h1]
  exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level

/-- Zeros off the real axis, with imaginary part bounded by `10 log q`, are repelled from the line
`Re s = 1` by an absolute amount: their `λ` is bounded below by a positive constant.

Proof route: `zeroMult χ u ≠ 0` gives `u` in the critical strip (`completedL_zero_strip`), and
`LFunction χ.primitiveCharacter u = 0` (`lFunction_order_eq_completed_order_on_strip`).  The uniform
off-axis zero-free region `Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform`
gives `1 - u.re > c / log (N (|u.im| + 2))` with `N = χ.conductor ≤ q`; since
`|u.im| ≤ 10 log q` and `N ≤ q`, one has `N (|u.im| + 2) ≤ q^2` for `q` large, so
`λ(u) = (1 - u.re) log q > c/2`. -/
theorem offAxisLambdaLower : ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ : DirichletCharacter ℂ q) (u : ℂ), χ ≠ 1 → Work.LinnikContract.zeroMult χ u ≠ 0 →
    u.im ≠ 0 → |u.im| ≤ 10 * Real.log (q : ℝ) → c ≤ Work.LinnikContract.lamOf q u := by
  obtain ⟨c₁, hc₁pos, hc₁⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
  refine ⟨c₁ / 14, by linarith, 3, ?_⟩
  intro q hq hqne χ u hχ hzm him himle
  haveI : NeZero q := hqne
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  -- `u` is a zero of the ordinary `L`-function of the primitive character inducing `χ`
  have hL0 : DirichletCharacter.LFunction χ.primitiveCharacter u = 0 :=
    LFunctionPrimitiveZero χ hχ hzm
  have hu_eq : u = (u.re : ℂ) + (u.im : ℂ) * Complex.I := (Complex.re_add_im u).symm
  have hL0' : DirichletCharacter.LFunction χ.primitiveCharacter
      ((u.re : ℂ) + (u.im : ℂ) * Complex.I) = 0 := by rw [← hu_eq]; exact hL0
  -- the uniform off-axis zero-free region forbids `u.re` from being too large
  have hnoZF := hc₁ (χ := χ.primitiveCharacter)
    (DirichletCharacter.primitiveCharacter_isPrimitive χ) (primitiveCharacter_ne_one hχ)
    u.re u.im him
  have hkey : c₁ / Real.log ((χ.conductor : ℝ) * (|u.im| + 2)) < 1 - u.re := by
    by_contra hcon
    push Not at hcon
    exact (hnoZF (by linarith :
      1 - c₁ / Real.log ((χ.conductor : ℝ) * (|u.im| + 2)) ≤ u.re)) hL0'
  -- elementary arithmetic: `|u.im| = O(log q)` and `conductor ≤ q` give `λ(u) ≥ c₁/14`
  rw [Work.LinnikContract.lamOf]
  exact offAxisArith hc₁pos (Nat.one_le_iff_ne_zero.mpr χ.conductor_ne_zero)
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level) hq himle hkey

end

end Work.LinnikAreas.DhCapped
