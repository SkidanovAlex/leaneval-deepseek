import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_small
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_neg_one_small
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip

open Complex DirichletCharacter
open scoped Real Topology
set_option autoImplicit false

namespace Commons.NumberTheory.DirichletCharacter

/-- The logarithmic derivative of the completed Dirichlet L-function is continuous wherever the
completed L-function itself does not vanish (it is entire, by `χ ≠ 1`, and its derivative is
again entire by `Differentiable.deriv`; `logDeriv F z = deriv F z / F z`). -/
private lemma contOn_logDeriv_completedLFunction {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) :
    ContinuousOn (fun z : ℂ => logDeriv (DirichletCharacter.completedLFunction χ) z)
      {z | DirichletCharacter.completedLFunction χ z ≠ 0} := by
  let F : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  have hdF : Differentiable ℂ F := DirichletCharacter.differentiable_completedLFunction hχ
  have hderv : ContinuousOn (deriv F) {z | F z ≠ 0} := hdF.deriv.continuous.continuousOn
  have hFc : ContinuousOn F {z | F z ≠ 0} := hdF.continuous.continuousOn
  have hdiv : ContinuousOn (fun z : ℂ => deriv F z / F z) {z | F z ≠ 0} := by
    exact ContinuousOn.div hderv hFc (by intro z hz; exact hz)
  apply ContinuousOn.congr hdiv
  intro z hz
  rfl

/-- On a vertical line `Re s = c` with `c ∉ (0,1)` the completed L-function of a primitive
nontrivial character does not vanish (all its zeros lie in the critical strip by `zerosInStrip`). -/
private lemma line_ne_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (c : ℂ) (y : ℝ) (hc : c.re ≤ 0 ∨ 1 ≤ c.re) :
    DirichletCharacter.completedLFunction χ (c + Complex.I * (y : ℂ)) ≠ 0 := by
  intro hz
  have hstrip := zerosInStrip χ hχ hχprim (c + Complex.I * (y : ℂ)) hz
  have hre : (c + Complex.I * (y : ℂ)).re = c.re := by simp
  rcases hc with hlow | hhigh
  · have hre0 : 0 < c.re := by simpa [hre] using hstrip.1
    linarith
  · have hre1 : c.re < 1 := by simpa [hre] using hstrip.2
    linarith

/-- The integrand `y ↦ ‖logDeriv Λ(χ)(c + iy)‖` is continuous on all of `ℝ` whenever the line
`Re = c.re` misses the critical strip. -/
private lemma cont_integrand {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (c : ℂ) (hc : c.re ≤ 0 ∨ 1 ≤ c.re) :
    Continuous (fun y : ℝ => ‖logDeriv (DirichletCharacter.completedLFunction χ)
      (c + Complex.I * (y : ℂ))‖) := by
  let g : ℂ → ℂ := fun z => logDeriv (DirichletCharacter.completedLFunction χ) z
  let cur : ℝ → ℂ := fun y => c + Complex.I * (y : ℂ)
  have hg : ContinuousOn g {z | DirichletCharacter.completedLFunction χ z ≠ 0} := by
    simpa [g] using contOn_logDeriv_completedLFunction χ hχ
  have hcur : Continuous cur := by
    dsimp [cur]
    fun_prop
  have hmaps : ∀ y : ℝ, DirichletCharacter.completedLFunction χ (cur y) ≠ 0 := by
    intro y
    exact line_ne_zero χ hχ hχprim c y hc
  have hcomp : ContinuousOn (fun y : ℝ => g (cur y)) Set.univ := by
    exact hg.comp hcur.continuousOn (by intro y hy; exact hmaps y)
  have hldc : Continuous (fun y : ℝ => g (cur y)) := continuousOn_univ.mp hcomp
  have hnorm : Continuous (fun y : ℝ => ‖g (cur y)‖) := Continuous.norm hldc
  simpa [g, cur] using hnorm

/-- Integrate a pointwise bound of the shape
`‖logDeriv Λ(χ)(c + iT)‖ ≤ (1/2)·log (2 + |T|) + A`
(valid for every real `T`) over `y ∈ [u, v]` with `0 ≤ u ≤ v`.  Since `|y| = y ≤ v` on that
interval and `log` is monotone, each integrand value is at most the constant
`(1/2)·log (2 + v) + A`; continuity supplies interval-integrability. -/
private lemma vertical_integral_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v)
    {c : ℂ} (hc : c.re ≤ 0 ∨ 1 ≤ c.re) {A : ℝ}
    (hbound : ∀ T : ℝ,
      ‖logDeriv (DirichletCharacter.completedLFunction χ) (c + Complex.I * (T : ℂ))‖ ≤
        (1 / 2) * Real.log (2 + |T|) + A) :
    (∫ y : ℝ in u..v,
        ‖logDeriv (DirichletCharacter.completedLFunction χ) (c + Complex.I * (y : ℂ))‖) ≤
      (v - u) * ((1 / 2) * Real.log (2 + v) + A) := by
  let f : ℝ → ℝ := fun y => ‖logDeriv (DirichletCharacter.completedLFunction χ)
    (c + Complex.I * (y : ℂ))‖
  let g : ℝ → ℝ := fun _ : ℝ => (1 / 2) * Real.log (2 + v) + A
  have hcf : Continuous f := by
    simpa [f] using cont_integrand χ hχ hχprim c hc
  have hf : IntervalIntegrable f MeasureTheory.volume u v := hcf.intervalIntegrable u v
  have hcg : Continuous g := continuous_const
  have hg : IntervalIntegrable g MeasureTheory.volume u v := hcg.intervalIntegrable u v
  have hpt : ∀ y ∈ Set.Icc u v, f y ≤ g y := by
    intro y hy
    have hyu : 0 ≤ y := le_trans hu0 hy.1
    have hyv : y ≤ v := hy.2
    have hlog : Real.log (2 + |y|) ≤ Real.log (2 + v) := by
      apply Real.log_le_log
      · nlinarith [abs_nonneg y]
      · have hyabs : |y| = y := abs_of_nonneg hyu
        rw [hyabs]
        linarith
    have hb := hbound y
    have hmul : (1 / 2 : ℝ) * Real.log (2 + |y|) ≤ (1 / 2) * Real.log (2 + v) :=
      mul_le_mul_of_nonneg_left hlog (by norm_num)
    dsimp [f, g]
    linarith
  have hmono := intervalIntegral.integral_mono_on huv hf hg hpt
  have hconst : (∫ y : ℝ in u..v, g y) = (v - u) * ((1 / 2) * Real.log (2 + v) + A) := by
    dsimp [g]
    rw [intervalIntegral.integral_const]
    simp
  calc
    (∫ y : ℝ in u..v, ‖logDeriv (DirichletCharacter.completedLFunction χ)
        (c + Complex.I * (y : ℂ))‖) = ∫ y : ℝ in u..v, f y := by
          simp [f]
    _ ≤ (∫ y : ℝ in u..v, g y) := hmono
    _ = (v - u) * ((1 / 2) * Real.log (2 + v) + A) := hconst

/-- Vertical-side integral bounds for the logarithmic derivative of the completed Dirichlet
L-function of a primitive non-trivial character.

For real heights `0 ≤ u ≤ v`, integrating the two published pointwise bounds
(`Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_small`:
`‖logDeriv Λ(χ)(2+iT)‖ ≤ (1/2)·log(2+|T|) + 5`, and
`Commons.NumberTheory.DirichletCharacter.completedLogDeriv_neg_one_small`:
`‖logDeriv Λ(χ)(−1+iT)‖ ≤ log N + (1/2)·log(2+|T|) + 5`) over `y ∈ [u,v]`
(`|y| = y` since `0 ≤ u`) gives

    ∫_{u..v} ‖logDeriv Λ(χ)(2+iy)‖ dy + ∫_{u..v} ‖logDeriv Λ(χ)(−1+iy)‖ dy
        ≤ (v − u) · (log N + log (2+v) + 10).

Method: `‖logDeriv Λ(χ)(x+iy)‖` is continuous in `y` on `[u,v]` for `x ∈ {−1,2}`
(`Λ(χ,·)` is entire and non-zero on the lines `Re = −1` and `Re = 2`: any zero would
lie in `0 < Re < 1` by `zerosInStrip`; `logDeriv` of a nonzero differentiable function
is continuous), hence interval-integrable (`ContinuousOn.intervalIntegrable`,
`intervalIntegral`).  Apply `intervalIntegral.integral_mono_on` pointwise against the
constant bounds and use `intervalIntegral.integral_const`; monotonicity of `log` and
`2+|y| ≤ 2+v` on `[u,v]` (with `0 ≤ u`) finish.  Do this for `Re = 2` and `Re = −1`
separately and add. -/
theorem verticalLogDeriv_integral_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v) :
    (∫ y : ℝ in u..v, ‖logDeriv (DirichletCharacter.completedLFunction χ)
        ((2 : ℂ) + Complex.I * (y : ℂ))‖) +
      (∫ y : ℝ in u..v, ‖logDeriv (DirichletCharacter.completedLFunction χ)
        ((-1 : ℂ) + Complex.I * (y : ℂ))‖) ≤
      (v - u) * (Real.log (N : ℝ) + Real.log (2 + v) + 10) := by
  have hb2 : ∀ T : ℝ,
      ‖logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + Complex.I * (T : ℂ))‖ ≤
        (1 / 2) * Real.log (2 + |T|) + 5 := by
    intro T
    exact completedLogDeriv_two_small χ hχ T
  have hI2 : (∫ y : ℝ in u..v, ‖logDeriv (DirichletCharacter.completedLFunction χ)
        ((2 : ℂ) + Complex.I * (y : ℂ))‖) ≤
      (v - u) * ((1 / 2) * Real.log (2 + v) + 5) := by
    exact vertical_integral_bound χ hχ hχprim hu0 huv (c := (2 : ℂ))
      (hc := Or.inr (by norm_num : (1 : ℝ) ≤ ((2 : ℂ).re))) (A := (5 : ℝ)) hb2
  have hb1 : ∀ T : ℝ,
      ‖logDeriv (DirichletCharacter.completedLFunction χ) ((-1 : ℂ) + Complex.I * (T : ℂ))‖ ≤
        (1 / 2) * Real.log (2 + |T|) + (Real.log (N : ℝ) + 5) := by
    intro T
    have h := completedLogDeriv_neg_one_small χ hχ hχprim T
    nlinarith
  have hI1 : (∫ y : ℝ in u..v, ‖logDeriv (DirichletCharacter.completedLFunction χ)
        ((-1 : ℂ) + Complex.I * (y : ℂ))‖) ≤
      (v - u) * ((1 / 2) * Real.log (2 + v) + (Real.log (N : ℝ) + 5)) := by
    exact vertical_integral_bound χ hχ hχprim hu0 huv (c := (-1 : ℂ))
      (hc := Or.inl (by norm_num : ((-1 : ℂ).re) ≤ (0 : ℝ))) (A := Real.log (N : ℝ) + 5) hb1
  have hsum := add_le_add hI2 hI1
  nlinarith

end Commons.NumberTheory.DirichletCharacter
