import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.BGTZZFR
import Submission.Work.LinnikAreas.siegelZetaZeroFree

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.BGTZ

/-- **A zero of the completed `ζ` with `|Im ρ| ≤ 4` is to the left of `1 - min ε₀ 1`.**

Let `ε₀ > 0` be the width of the zero-free strip of `zeta_zeroFree_near_axis`, i.e.
`ζ(σ+it) ≠ 0` for `|t| ≤ 4`, `1 - ε₀ ≤ σ ≤ 2`.  Then every zero `ρ` of the completed Riemann zeta
function with `|Im ρ| ≤ 4` satisfies `min ε₀ 1 ≤ 1 - Re ρ`.  Indeed, a zero of the completed `ζ`
is a zero of `ζ` away from `0`; `riemannZeta_ne_zero_of_one_le_re` forces `Re ρ < 1`, and if
`Re ρ > 0` the zero-free strip applies (a zero of `ζ` with `Re ρ > 0` is not the origin). -/
lemma one_sub_re_ge_of_completedZeta_zero {ε₀ : ℝ} (_hε₀pos : 0 < ε₀)
    (hε₀ : ∀ (t σ : ℝ), |t| ≤ 4 → 1 - ε₀ ≤ σ → σ ≤ 2 →
      riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) ≠ 0)
    {ρ : ℂ} (hz : completedRiemannZeta ρ = 0) (him : |ρ.im| ≤ 4) :
    min ε₀ 1 ≤ 1 - ρ.re := by
  -- A zero of the completed zeta function has real part `< 1`.
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
  by_cases hle : ρ.re ≤ 0
  · have : min ε₀ 1 ≤ 1 := min_le_right _ _
    linarith
  · rw [not_le] at hle
    have hge : ε₀ ≤ 1 - ρ.re := by
      by_contra hcon
      rw [not_le] at hcon
      have hσ1 : 1 - ε₀ ≤ ρ.re := by linarith
      have hσ2 : ρ.re ≤ 2 := by linarith
      have hzf := hε₀ ρ.im ρ.re him hσ1 hσ2
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
    linarith [min_le_left ε₀ 1]

/-- **Zero-free region for the principal character in the working region.**

There is an absolute `ε > 0` such that for every `q` and every zero `ρ` of the *completed*
`L`-function of the principal character `1 : DirichletCharacter ℂ q` with `|Im ρ| ≤ 1` one has
`λ(ρ) = (1 - Re ρ)·log q ≥ ε·log q`, i.e. `Re ρ ≤ 1 - ε`.

This is the `ζ`-input `hzete` of `Work.LinnikAreas.RepulsionWith_of_ZeroFreeCert`.  Route: the
principal character's completed `L`-function is the completed `ζ`, so `zeroMult 1 ρ ≠ 0` gives
`riemannZeta ρ = 0` (unfold `zeroMult`, and use the identification of `completedLFunction` for the
trivial character with the completed `ζ`); the seeded commons'
`Commons.NumberTheory.Zeta.zeta_zeroFree_near_axis` gives an absolute `ε₀ > 0` with
`ζ(σ+it) ≠ 0` for `|t| ≤ 4`, `1-ε₀ ≤ σ ≤ 2`, and `riemannZeta_ne_zero_of_one_le_re` excludes
`σ ≥ 1`; every zero of `ζ` in the strip therefore has `1 - Re ρ ≥ ε₀` (take `ε = ε₀`; the
threshold `q₁` in the conclusion may be taken to be `1`, since `λ(ρ) = (1-Re ρ)·log q` and
`1 - Re ρ ≥ ε₀` is uniform in `q`, with `log q > 0` for `q ≥ 2`). -/
theorem zetaZFR_working :
    ∃ ε : ℝ, 0 < ε ∧ ∃ q₁ : ℕ, ∀ q : ℕ, q₁ ≤ q → ∀ [NeZero q] (ρ : ℂ),
      Work.LinnikContract.zeroMult (1 : DirichletCharacter ℂ q) ρ ≠ 0 → |ρ.im| ≤ 1 →
      ε * Real.log q ≤ Work.LinnikContract.lamOf q ρ := by
  obtain ⟨ε₀, hε₀pos, hε₀⟩ := Commons.NumberTheory.Zeta.zeta_zeroFree_near_axis
  refine ⟨min ε₀ 1, lt_min hε₀pos one_pos, 1, ?_⟩
  intro q hq nq ρ hzm him
  -- `zeroMult 1 ρ ≠ 0` is the statement that `ρ` is a zero of the completed Riemann zeta.
  rw [Work.LinnikAreas.zeroMult_principal_eq q ρ] at hzm
  have hz : completedRiemannZeta ρ = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero hzm
  have hkey : min ε₀ 1 ≤ 1 - ρ.re :=
    one_sub_re_ge_of_completedZeta_zero hε₀pos hε₀ hz (by linarith [abs_nonneg ρ.im])
  have hlogq : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hq : (1 : ℝ) ≤ (q : ℝ))
  rw [Work.LinnikContract.lamOf]
  exact mul_le_mul_of_nonneg_right hkey hlogq

end Work.LinnikAreas.BGTZ
