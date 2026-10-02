import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_uniform_realAxis
import Submission.Work.ZeroDensity.LogFree.Defs
import Submission.Work.LinnikContract.Defs
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
import Submission.Work.A7.exists_isMin1

/-!
# `Work.ZeroDensity.LogFree.excZeroReal` — exceptional zeros are real zeros of real characters

The zero-free regions of Dirichlet `L`-functions give: a zero `ρ` of `L(·,χ)` with
`(1 - Re ρ)·log(q(T+2))` below an absolute constant `c₀` must be

* *on the real axis*, by the uniform zero-free region off the real axis
  (`Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform`), and
* *a zero of a real (quadratic) character*, by the uniform zero-free region on the real axis
  (`..._uniform_realAxis`).

Both zero-free regions are uniform in the modulus, and the logarithmic parameter `log(q(T+2))`
dominates both `log(N(|t|+2))` (`N = χ.conductor ≤ q`, `|t| = |Im ρ| ≤ T`) and `log(2N)`, so an
absolute constant `c₀` works.
-/

namespace Work.ZeroDensity.LogFree

open DirichletCharacter

/-- If `ρ` is a zero of `L(·,χ)` in the sense of `zeroMult` (a zero of the completed
`L`-function of the primitive character inducing `χ`) and `χ ≠ 1`, then
`L(ρ, χ.primitiveCharacter) = 0`. -/
private lemma zeroMult_LFunction_primitive_eq_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hχ : χ ≠ 1) {ρ : ℂ}
    (hz : Work.LinnikContract.zeroMult χ ρ ≠ 0) :
    DirichletCharacter.LFunction χ.primitiveCharacter ρ = 0 := by
  have hcond : χ.conductor ≠ 1 := fun hc =>
    hχ ((DirichletCharacter.eq_one_iff_conductor_eq_one (χ := χ)).mpr hc)
  have hcomp : DirichletCharacter.completedLFunction χ.primitiveCharacter ρ = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero
      (by simpa only [Work.LinnikContract.zeroMult] using hz)
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor _ _ (Or.inr hcond), hcomp,
    zero_div]

theorem excZeroReal :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q]
      (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ (ρ : ℂ) (T : ℝ), 1 ≤ T → |ρ.im| ≤ T →
        Work.LinnikContract.zeroMult χ ρ ≠ 0 →
        (1 - ρ.re) * Work.ZeroDensity.LogFree.Lscale q T < c₀ →
        ρ.im = 0 ∧ χ.primitiveCharacter ^ 2 = 1 := by
  obtain ⟨c₁, hc₁pos, hoff⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
  obtain ⟨c₂, hc₂pos, hreal⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_uniform_realAxis
  refine ⟨min c₁ c₂, lt_min hc₁pos hc₂pos, ?_⟩
  intro q hq _inst χ hχ ρ T hT him hz hsmall
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  -- elementary size comparisons between the conductor, the level and the height
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hCq_nat : χ.conductor ≤ q := Nat.le_of_dvd (by omega) χ.conductor_dvd_level
  have hCq : ((χ.conductor : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hCq_nat
  have hC1 : (1 : ℝ) ≤ ((χ.conductor : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr χ.conductor_ne_zero)
  have hLdef : Lscale q T = Real.log ((q : ℝ) * (T + 2)) := by
    simp [Lscale, scale]
  have hLpos : 0 < Lscale q T := by
    rw [hLdef]
    exact Real.log_pos (by nlinarith)
  have hlt : 1 - ρ.re < (min c₁ c₂) / Lscale q T :=
    (lt_div_iff₀ hLpos).mpr hsmall
  have hzprim : DirichletCharacter.LFunction χ.primitiveCharacter ρ = 0 :=
    zeroMult_LFunction_primitive_eq_zero χ hχ hz
  have hne1 : χ.primitiveCharacter ≠ 1 := Work.A7.primitiveCharacter_ne_one hχ
  have hprim : χ.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  -- the off-axis zero-free region rules out any zero with non-zero imaginary part
  have him0 : ρ.im = 0 := by
    by_contra himne
    have harg1 : (1 : ℝ) < ((χ.conductor : ℕ) : ℝ) * (|ρ.im| + 2) := by
      have h := mul_le_mul hC1 (show (2 : ℝ) ≤ |ρ.im| + 2 by linarith [abs_nonneg ρ.im])
        (by norm_num) (by linarith)
      linarith
    have hargpos : 0 < ((χ.conductor : ℕ) : ℝ) * (|ρ.im| + 2) := lt_trans zero_lt_one harg1
    have hlearg : ((χ.conductor : ℕ) : ℝ) * (|ρ.im| + 2) ≤ (q : ℝ) * (T + 2) :=
      mul_le_mul hCq (by linarith [him]) (by linarith [abs_nonneg ρ.im]) hq0
    have hlogle : Real.log (((χ.conductor : ℕ) : ℝ) * (|ρ.im| + 2)) ≤ Lscale q T := by
      rw [hLdef]
      exact Real.log_le_log hargpos hlearg
    have hlogpos : 0 < Real.log (((χ.conductor : ℕ) : ℝ) * (|ρ.im| + 2)) :=
      Real.log_pos harg1
    have hle1 : (min c₁ c₂) / Lscale q T ≤ c₁ / Lscale q T :=
      div_le_div_of_nonneg_right (min_le_left _ _) (le_of_lt hLpos)
    have hle2 : c₁ / Lscale q T ≤ c₁ / Real.log (((χ.conductor : ℕ) : ℝ) * (|ρ.im| + 2)) :=
      div_le_div_of_nonneg_left (le_of_lt hc₁pos) hlogpos hlogle
    have hineq : 1 - c₁ / Real.log (((χ.conductor : ℕ) : ℝ) * (|ρ.im| + 2)) ≤ ρ.re := by
      linarith
    have hne := hoff (χ := χ.primitiveCharacter) hprim hne1 ρ.re ρ.im himne hineq
    rw [Complex.re_add_im] at hne
    exact hne hzprim
  refine ⟨him0, ?_⟩
  -- a real zero in the narrow region must belong to a real character
  by_contra hsqne
  have hmul : χ.primitiveCharacter * χ.primitiveCharacter ≠ 1 := by
    intro hh
    exact hsqne (by rw [pow_two]; exact hh)
  have harg2 : (1 : ℝ) < 2 * ((χ.conductor : ℕ) : ℝ) := by nlinarith [hC1]
  have hlearg2 : 2 * ((χ.conductor : ℕ) : ℝ) ≤ (q : ℝ) * (T + 2) := by
    have h1 : 2 * ((χ.conductor : ℕ) : ℝ) ≤ 2 * (q : ℝ) := by linarith
    have h2 : 2 * (q : ℝ) ≤ (q : ℝ) * (T + 2) := by nlinarith
    linarith
  have hlogle2 : Real.log (2 * ((χ.conductor : ℕ) : ℝ)) ≤ Lscale q T := by
    rw [hLdef]
    exact Real.log_le_log (lt_trans zero_lt_one harg2) hlearg2
  have hlogpos2 : 0 < Real.log (2 * ((χ.conductor : ℕ) : ℝ)) := Real.log_pos harg2
  have hle1 : (min c₁ c₂) / Lscale q T ≤ c₂ / Lscale q T :=
    div_le_div_of_nonneg_right (min_le_right _ _) (le_of_lt hLpos)
  have hle2 : c₂ / Lscale q T ≤ c₂ / Real.log (2 * ((χ.conductor : ℕ) : ℝ)) :=
    div_le_div_of_nonneg_left (le_of_lt hc₂pos) hlogpos2 hlogle2
  have hineq2 : 1 - c₂ / Real.log (2 * ((χ.conductor : ℕ) : ℝ)) ≤ ρ.re := by
    linarith
  have hrealne := hreal χ.conductor χ.primitiveCharacter hprim hne1 hmul ρ.re hineq2
  have hρeq : ρ = (ρ.re : ℂ) := by
    apply Complex.ext <;> simp [him0]
  have hzero' : DirichletCharacter.LFunction χ.primitiveCharacter (ρ.re : ℂ) = 0 := by
    rw [hρeq] at hzprim
    exact hzprim
  exact hrealne hzero'

end Work.ZeroDensity.LogFree
