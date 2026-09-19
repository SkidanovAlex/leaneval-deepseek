import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_conj
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_tight

open Complex DirichletCharacter
open scoped Real Topology

namespace Commons.NumberTheory.DirichletCharacter

/-!
# Conjugation symmetry of the completed Dirichlet L-function

We prove that for a non-trivial Dirichlet character `χ` the completed L-function satisfies

`Λ(χ⁻¹, s) = conj (Λ(χ, conj s))`   for all `s : ℂ`,

and deduce the corresponding symmetry of the logarithmic derivatives:

`(logDeriv Λ(χ⁻¹)) (conj s) = conj ((logDeriv Λ(χ)) s)`.

The proof of the value-level statement uses the identity theorem: on the half-plane `1 < re s`
the completed L-function factors as `Λ(χ,s) = L(χ,s) * gammaFactor χ s`, and both factors are
compatible with complex conjugation (`LFunction_conj`, conjugation of `Gammaℝ`), so that the two
entire functions `s ↦ conj (Λ(χ, conj s))` and `Λ(χ⁻¹, s)` agree on an open set and hence
everywhere. The logarithmic-derivative statement then follows by differentiating.
-/

/-- Complex conjugation of Deligne's archimedean Gamma factor. -/
lemma conj_GammaR (z : ℂ) : (starRingEnd ℂ) (Gammaℝ ((starRingEnd ℂ) z)) = Gammaℝ z := by
  have h1 : (starRingEnd ℂ) (-(starRingEnd ℂ) z / 2) = -z / 2 := by
    rw [map_div₀, map_neg, Complex.conj_conj, map_ofNat]
  have h2 : (starRingEnd ℂ) ((starRingEnd ℂ) z / 2) = z / 2 := by
    rw [map_div₀, Complex.conj_conj, map_ofNat]
  rw [Gammaℝ_def, Gammaℝ_def, map_mul, conj_cpow_ofReal_pos Real.pi Real.pi_pos, h1,
    ← Complex.Gamma_conj, h2]

private lemma even_inv' {N : ℕ} {χ : DirichletCharacter ℂ N} (h : χ.Even) : (χ⁻¹).Even := by
  show χ⁻¹ (-1) = 1
  rw [MulChar.inv_apply_eq_inv', show χ (-1) = 1 from h, inv_one]

private lemma odd_inv' {N : ℕ} {χ : DirichletCharacter ℂ N} (h : χ.Odd) : (χ⁻¹).Odd := by
  show χ⁻¹ (-1) = -1
  rw [MulChar.inv_apply_eq_inv', show χ (-1) = -1 from h, inv_neg, inv_one]

/-- Conjugation of the archimedean Gamma factor of a Dirichlet character: the Gamma factor of
`χ⁻¹` is the conjugate of the Gamma factor of `χ` at the conjugate point. -/
lemma conj_gammaFactor {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {z : ℂ} :
    (starRingEnd ℂ) (gammaFactor χ ((starRingEnd ℂ) z)) = gammaFactor χ⁻¹ z := by
  rcases χ.even_or_odd with hE | hO
  · rw [hE.gammaFactor_def, (even_inv' hE).gammaFactor_def]
    exact conj_GammaR z
  · rw [hO.gammaFactor_def, (odd_inv' hO).gammaFactor_def]
    have := conj_GammaR (z + 1)
    rw [map_add, map_one] at this
    exact this

/-- The completed L-function as `LFunction` times the Gamma factor, at points where the Gamma
factor does not vanish (in particular on `1 < re s`). -/
lemma completedLFunction_eq_gammaFactor_mul {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hN : N ≠ 1) {s : ℂ} (h : gammaFactor χ s ≠ 0) :
    completedLFunction χ s = LFunction χ s * gammaFactor χ s := by
  have h1 := LFunction_eq_completed_div_gammaFactor χ s (Or.inr hN)
  rw [h1, div_mul_cancel₀ _ h]

private lemma gammaFactor_ne_zero_of_one_lt_re {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) : gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with hE | hO
  · rw [hE.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos (by linarith)
  · rw [hO.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos (by simp only [add_re, one_re]; linarith)

/-- **Conjugation identity for the completed L-function**: for a non-trivial Dirichlet character
`χ` the function `s ↦ conj (Λ(χ, conj s))` is the completed L-function of `χ⁻¹`. -/
theorem starComp_completedLFunction {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) : starComp (completedLFunction χ) = completedLFunction χ⁻¹ := by
  have hN : N ≠ 1 := fun h => hχ (level_one' χ h)
  have hχinv : χ⁻¹ ≠ 1 := by
    intro h
    exact hχ (by simpa using congrArg (fun ψ : DirichletCharacter ℂ N => ψ⁻¹) h)
  have hF : AnalyticOnNhd ℂ (starComp (completedLFunction χ)) (Set.univ : Set ℂ) := fun z _ =>
    Differentiable.analyticAt (differentiable_starComp (differentiable_completedLFunction hχ)) z
  have hG : AnalyticOnNhd ℂ (completedLFunction χ⁻¹) (Set.univ : Set ℂ) := fun z _ =>
    Differentiable.analyticAt (differentiable_completedLFunction hχinv) z
  let z₀ : ℂ := 2
  have hz₀re : (1 : ℝ) < z₀.re := by dsimp [z₀]; norm_num
  have hset : {x : ℂ | 1 < x.re} ∈ 𝓝 z₀ := (isOpen_lt continuous_const continuous_re).mem_nhds hz₀re
  have hev : starComp (completedLFunction χ) =ᶠ[𝓝 z₀] (completedLFunction χ⁻¹) := by
    filter_upwards [hset] with z hz
    have hz' : 1 < ((starRingEnd ℂ) z).re := by simpa [Complex.conj_re] using hz
    have hγ : gammaFactor χ ((starRingEnd ℂ) z) ≠ 0 := gammaFactor_ne_zero_of_one_lt_re χ hz'
    have hγ' : gammaFactor χ⁻¹ z ≠ 0 := gammaFactor_ne_zero_of_one_lt_re χ⁻¹ hz
    have hval := completedLFunction_eq_gammaFactor_mul χ hN hγ
    have hval' := completedLFunction_eq_gammaFactor_mul (χ⁻¹) hN hγ'
    have hconjL : (starRingEnd ℂ) (LFunction χ ((starRingEnd ℂ) z)) = LFunction χ⁻¹ z := by
      have := LFunction_conj χ hχ ((starRingEnd ℂ) z)
      simpa using this
    unfold starComp
    rw [hval, map_mul, hconjL, conj_gammaFactor χ, ← hval']
  have hEqOn := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (U := (Set.univ : Set ℂ)) hF hG
    isPreconnected_univ (Set.mem_univ z₀) hev
  funext z
  exact hEqOn (Set.mem_univ z)

/-- Pointwise form of the conjugation identity for the completed L-function. -/
theorem completedLFunction_conj_apply {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) :
    (starRingEnd ℂ) (completedLFunction χ ((starRingEnd ℂ) s)) = completedLFunction χ⁻¹ s := by
  have hf := starComp_completedLFunction χ hχ
  have h := congrFun hf s
  simpa [starComp] using h

/-- Conjugation symmetry of the logarithmic derivative of the completed L-function:
`Λ(star s, χ⁻¹) = star (Λ(s, χ))`, hence the same for the logarithmic derivatives. -/
theorem logDeriv_completedLFunction_conj {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) :
    logDeriv (DirichletCharacter.completedLFunction χ⁻¹) (star s) =
      star (logDeriv (DirichletCharacter.completedLFunction χ) s) := by
  have hfun := starComp_completedLFunction χ hχ
  have hderiv_aux : ∀ u : ℂ, deriv (completedLFunction χ⁻¹) u =
      (starRingEnd ℂ) (deriv (completedLFunction χ) ((starRingEnd ℂ) u)) := by
    intro u
    have hd : HasDerivAt (starComp (completedLFunction χ))
        ((starRingEnd ℂ) (deriv (completedLFunction χ) ((starRingEnd ℂ) u))) u :=
      hasDerivAt_star_comp
        ((differentiable_completedLFunction hχ) ((starRingEnd ℂ) u)).hasDerivAt
    rw [hfun] at hd
    exact hd.deriv
  have hss : (starRingEnd ℂ) (star s) = s := by
    rw [starRingEnd_apply, star_star]
  have hderiv : deriv (completedLFunction χ⁻¹) (star s) =
      star (deriv (completedLFunction χ) s) := by
    rw [hderiv_aux (star s), hss, starRingEnd_apply]
  have hval : completedLFunction χ⁻¹ (star s) = star (completedLFunction χ s) := by
    rw [← hfun]
    simp only [starComp, starRingEnd_apply, star_star]
  rw [logDeriv_apply, logDeriv_apply, hderiv, hval]
  exact (map_div₀ (starRingEnd ℂ) (deriv (completedLFunction χ) s) (completedLFunction χ s)).symm

end Commons.NumberTheory.DirichletCharacter
