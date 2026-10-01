import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.A7.exists_isMin1
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFree_near_axis

open DirichletCharacter Complex
open scoped Classical BigOperators

set_option linter.style.haveILetI false

namespace Work.LinnikAreas

/-!
# Zero-free region for the principal character: the `ζ`-case of Siegel zero-freeness

For the principal character `1 : DirichletCharacter ℂ q` the multiplicity `zeroMult 1 ρ` is the
multiplicity of `ρ` as a zero of the completed Riemann zeta function: the primitive character
inducing `1` is `1 : DirichletCharacter ℂ 1` (`primitiveCharacter_one`, `conductor_one`), and
`completedLFunction (1 : DirichletCharacter ℂ 1) = completedRiemannZeta`
(`completedLFunction_modOne_eq`).

The zero-free strip `zeta_zeroFree_near_axis` (`ζ σ+it ≠ 0` for `|t| ≤ 4`, `1 - ε₀ ≤ σ ≤ 2`)
therefore gives a *positive* lower bound for `(1 - Re ρ) log q` over all zeros `ρ` with
`|Im ρ| ≤ 1` and all `q ≥ 2`: zeros with `Re ρ ≤ 0` are harmless (`1 - Re ρ ≥ 1`), and zeros with
`Re ρ > 0` lie in the non-trivial strip `0 < Re ρ < 1` and hence are pushed to `1 - Re ρ ≥ ε₀` by
the zero-free strip.  Multiplying by `log q ≥ log 2` closes the argument.
-/

/-- The completed `L`-function at (propositionally) level `1` is the completed Riemann zeta
function.  (`DirichletCharacter.completedLFunction_modOne_eq` after transporting the level.) -/
lemma completedLFunction_principal_of_eq_one {N : ℕ} [NeZero N] (hN : N = 1)
    (χ : DirichletCharacter ℂ N) :
    DirichletCharacter.completedLFunction χ = completedRiemannZeta := by
  subst hN
  exact DirichletCharacter.completedLFunction_modOne_eq (χ := χ)

/-- `zeroMult` at the principal character is the order of vanishing of the completed Riemann zeta
function. -/
lemma zeroMult_principal_eq (q : ℕ) [NeZero q] (ρ : ℂ) :
    Work.LinnikContract.zeroMult (1 : DirichletCharacter ℂ q) ρ =
      analyticOrderNatAt completedRiemannZeta ρ := by
  haveI : NeZero ((1 : DirichletCharacter ℂ q).conductor) :=
    ⟨DirichletCharacter.conductor_ne_zero (1 : DirichletCharacter ℂ q)⟩
  unfold Work.LinnikContract.zeroMult
  congr 1
  exact completedLFunction_principal_of_eq_one DirichletCharacter.conductor_one _

theorem siegelZetaZeroFree : ∃ c : ℝ, 0 < c ∧ ∀ {q : ℕ} [NeZero q], 2 ≤ q → ∀ (ρ : ℂ),
    Work.LinnikContract.zeroMult (1 : DirichletCharacter ℂ q) ρ ≠ 0 → |ρ.im| ≤ 1 →
    c ≤ Work.LinnikContract.lamOf q ρ := by
  obtain ⟨ε₀, hε₀pos, hε₀⟩ := Commons.NumberTheory.Zeta.zeta_zeroFree_near_axis
  refine ⟨min ε₀ 1 * Real.log 2, mul_pos (lt_min hε₀pos one_pos) (Real.log_pos one_lt_two), ?_⟩
  intro q _ hq ρ hzm him
  -- `hzm` is the non-vanishing of the order of `ρ` as a zero of the completed zeta function.
  rw [zeroMult_principal_eq q ρ] at hzm
  have hz : completedRiemannZeta ρ = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero hzm
  -- A zero of the completed zeta function has real part `< 1`, since `ζ` is non-zero there.
  have hre1 : ρ.re < 1 := by
    by_contra hcon
    rw [not_lt] at hcon
    have hne0 : ρ ≠ 0 := by
      intro h0
      have : ρ.re = (0 : ℂ).re := by rw [h0]
      simp at this
      linarith
    have hζ : riemannZeta ρ = 0 := by
      rw [riemannZeta_def_of_ne_zero hne0, hz, zero_div]
    exact riemannZeta_ne_zero_of_one_le_re hcon hζ
  -- The two cases for the real part of `ρ`.
  have key : min ε₀ 1 ≤ 1 - ρ.re := by
    by_cases hle : ρ.re ≤ 0
    · have : min ε₀ 1 ≤ 1 := min_le_right _ _
      linarith
    · rw [not_le] at hle
      have hge : ε₀ ≤ 1 - ρ.re := by
        by_contra hcon
        rw [not_le] at hcon
        have hσ1 : 1 - ε₀ ≤ ρ.re := by linarith
        have hσ2 : ρ.re ≤ 2 := by linarith
        have him4 : |ρ.im| ≤ 4 := by
          have := abs_nonneg ρ.im
          linarith
        have hzf := hε₀ ρ.im ρ.re him4 hσ1 hσ2
        have hne0 : ρ ≠ 0 := by
          intro h0
          have : ρ.re = (0 : ℂ).re := by rw [h0]
          simp at this
          linarith
        have hζ : riemannZeta ρ = 0 := by
          rw [riemannZeta_def_of_ne_zero hne0, hz, zero_div]
        have heq : ((ρ.re : ℂ) + Complex.I * (ρ.im : ℂ)) = ρ := by
          rw [mul_comm Complex.I (ρ.im : ℂ), Complex.re_add_im]
        rw [heq] at hzf
        exact hzf hζ
      have := min_le_left ε₀ 1
      linarith
  -- Multiply by `log q ≥ log 2 > 0`.
  have hlog2 : Real.log 2 ≤ Real.log q :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hq)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [Work.LinnikContract.lamOf]
  have h1 : min ε₀ 1 * Real.log 2 ≤ (1 - ρ.re) * Real.log 2 :=
    mul_le_mul_of_nonneg_right key hlog2pos.le
  have h2 : (1 - ρ.re) * Real.log 2 ≤ (1 - ρ.re) * Real.log q :=
    mul_le_mul_of_nonneg_left hlog2 (by linarith)
  linarith

end Work.LinnikAreas
