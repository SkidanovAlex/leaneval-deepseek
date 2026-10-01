import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.Analytic.Order

open Complex Filter
open scoped Real Topology
set_option autoImplicit false
set_option linter.unusedVariables false

namespace Commons.NumberTheory.DirichletCharacter

/-!
# Vanishing orders of an L-function and its completion on the critical strip

For a non-trivial Dirichlet character `χ`, the ordinary and the completed L-functions are both
entire, and on the open right half-plane they are related by

`completedLFunction χ s = LFunction χ s * gammaFactor χ s`.

The Archimedean Gamma factor `gammaFactor χ` is analytic and non-vanishing on the right
half-plane (its only singularities/zeros lie in the closed left half-plane), so multiplying by it
does not change the vanishing order at any point `ρ` with `0 < Re ρ`.  In particular the orders
agree throughout the critical strip `0 < Re ρ < 1`.
-/

/-- `Gammaℝ` is analytic at every point of the open right half-plane. -/
private lemma Gammaℝ_analyticAt_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ Complex.Gammaℝ z := by
  have hinv : Differentiable ℂ (fun s : ℂ => s.Gammaℝ⁻¹) := Complex.differentiable_Gammaℝ_inv
  have hinvz : (fun s : ℂ => s.Gammaℝ⁻¹) z ≠ 0 := by
    dsimp
    exact inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hz)
  have han0 : AnalyticAt ℂ (fun s : ℂ => (s.Gammaℝ⁻¹)⁻¹) z :=
    (hinv.analyticAt z).inv hinvz
  convert han0 with s
  · rw [inv_inv]

/-- The archimedean Gamma factor of a Dirichlet character is analytic on the open right
half-plane. -/
private lemma gammaFactor_analyticAt_of_re_pos {N : ℕ} (χ : DirichletCharacter ℂ N) {z : ℂ}
    (hz : 0 < z.re) : AnalyticAt ℂ (DirichletCharacter.gammaFactor χ) z := by
  rcases χ.even_or_odd with hE | hO
  · have hγ : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ := by
      funext s
      exact DirichletCharacter.Even.gammaFactor_def hE s
    rw [hγ]
    exact Gammaℝ_analyticAt_of_re_pos hz
  · have hγ : DirichletCharacter.gammaFactor χ = (fun s : ℂ => Complex.Gammaℝ (s + 1)) := by
      funext s
      exact DirichletCharacter.Odd.gammaFactor_def hO s
    rw [hγ]
    refine AnalyticAt.comp (g := Complex.Gammaℝ) (f := fun s : ℂ => s + 1) (x := z) ?_ ?_
    · have hz1 : 0 < (z + 1).re := by simp; linarith
      exact Gammaℝ_analyticAt_of_re_pos hz1
    · fun_prop

/-- The archimedean Gamma factor of a Dirichlet character does not vanish on the open right
half-plane. -/
private lemma gammaFactor_ne_zero_of_re_pos {N : ℕ} (χ : DirichletCharacter ℂ N) {z : ℂ}
    (hz : 0 < z.re) : DirichletCharacter.gammaFactor χ z ≠ 0 := by
  rcases χ.even_or_odd with hE | hO
  · rw [DirichletCharacter.Even.gammaFactor_def hE]
    exact Complex.Gammaℝ_ne_zero_of_re_pos hz
  · rw [DirichletCharacter.Odd.gammaFactor_def hO]
    have hz1 : 0 < (z + 1).re := by simp; linarith
    exact Complex.Gammaℝ_ne_zero_of_re_pos hz1

/-- On the right half-plane `{s | 0 < s.re}` the completed L-function factors as
`LFunction χ s * gammaFactor χ s`. -/
private lemma completedLFunction_eq_mul_gammaFactor_of_re_pos {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.completedLFunction χ s =
      DirichletCharacter.LFunction χ s * DirichletCharacter.gammaFactor χ s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst h
    norm_num at hs
  have hG : DirichletCharacter.gammaFactor χ s ≠ 0 := gammaFactor_ne_zero_of_re_pos χ hs
  have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (.inl hs0)
  rw [h, div_mul_cancel₀ _ hG]

/-- If `g` agrees in a neighbourhood of `z` with `f * h`, where `h` is analytic and non-zero at
`z`, then the analytic orders of `f` and `g` at `z` agree.  (The factor `h` is a unit in the local
ring of analytic functions.) -/
private lemma analyticOrderAt_eq_of_eventuallyEq_mul {f g h : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hh : AnalyticAt ℂ h z) (hne : h z ≠ 0)
    (hfg : g =ᶠ[𝓝 z] f * h) :
    analyticOrderAt g z = analyticOrderAt f z := by
  rw [analyticOrderAt_congr hfg, analyticOrderAt_mul hf hh,
    (hh.analyticOrderAt_eq_zero).mpr hne, add_zero]

/-- In the critical strip `0 < Re rho < 1` the Archimedean gamma factor is analytic and
non-vanishing, hence the vanishing orders of the ordinary and of the completed Dirichlet
L-function agree there.  (Both are entire for a non-trivial character.) -/
theorem lFunction_order_eq_completed_order_on_strip {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {ρ : ℂ} (hρ : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ =
      analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ := by
  have hL : AnalyticAt ℂ (DirichletCharacter.LFunction χ) ρ :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt ρ
  have hγ : AnalyticAt ℂ (DirichletCharacter.gammaFactor χ) ρ :=
    gammaFactor_analyticAt_of_re_pos χ hρ
  have hγ0 : DirichletCharacter.gammaFactor χ ρ ≠ 0 := gammaFactor_ne_zero_of_re_pos χ hρ
  have hfac : DirichletCharacter.completedLFunction χ =ᶠ[𝓝 ρ]
      DirichletCharacter.LFunction χ * DirichletCharacter.gammaFactor χ := by
    have hmem : {s : ℂ | 0 < s.re} ∈ 𝓝 ρ :=
      (isOpen_lt continuous_const continuous_re).mem_nhds hρ
    filter_upwards [hmem] with s hs
    exact completedLFunction_eq_mul_gammaFactor_of_re_pos χ hs
  have horder : analyticOrderAt (DirichletCharacter.completedLFunction χ) ρ =
      analyticOrderAt (DirichletCharacter.LFunction χ) ρ :=
    analyticOrderAt_eq_of_eventuallyEq_mul hL hγ hγ0 hfac
  exact congrArg ENat.toNat horder.symm

end Commons.NumberTheory.DirichletCharacter