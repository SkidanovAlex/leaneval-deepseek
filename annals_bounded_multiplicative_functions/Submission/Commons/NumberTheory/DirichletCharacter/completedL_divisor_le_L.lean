import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.NumberTheory.LSeries.DirichletContinuation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex DirichletCharacter
open scoped Real Topology
set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable section

namespace Commons.NumberTheory.DirichletCharacter

/-!
# The divisor of the completed L-function is no larger than that of the L-function

For a *non-trivial* Dirichlet character `χ` and a point `u` with `0 < Re u`, the
archimedean Gamma factor `gammaFactor χ` is analytic and non-vanishing on a
neighbourhood of `u` (its only singularities lie in the closed left half-plane
`Re s ≤ 0`).  Since the completed L-function satisfies

`completedLFunction χ s = LFunction χ s * gammaFactor χ s`   for `0 < Re s`,

the divisor of `completedLFunction χ` equals the divisor of `LFunction χ` at `u`.
-/

/-- On the right half-plane `{s | 0 < s.re}` the completed L-function factors as
`LFunction χ s * gammaFactor χ s`. -/
private lemma completedLFunction_eq_mul_gammaFactor_of_re_pos {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.completedLFunction χ s =
      DirichletCharacter.LFunction χ s * gammaFactor χ s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst h
    norm_num at hs
  have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (.inl hs0)
  rcases χ.even_or_odd with hE | hO
  · have hG : gammaFactor χ s ≠ 0 := by
      rw [Even.gammaFactor_def hE]
      exact Complex.Gammaℝ_ne_zero_of_re_pos hs
    calc
      completedLFunction χ s = (completedLFunction χ s / gammaFactor χ s) * gammaFactor χ s := by
        rw [div_mul_cancel₀ _ hG]
      _ = LFunction χ s * gammaFactor χ s := by rw [h]
  · have hG : gammaFactor χ s ≠ 0 := by
      rw [Odd.gammaFactor_def hO]
      exact Complex.Gammaℝ_ne_zero_of_re_pos (by
        rw [Complex.add_re, Complex.one_re]
        linarith)
    calc
      completedLFunction χ s = (completedLFunction χ s / gammaFactor χ s) * gammaFactor χ s := by
        rw [div_mul_cancel₀ _ hG]
      _ = LFunction χ s * gammaFactor χ s := by rw [h]

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

/-- The archimedean Gamma factor of a character is analytic on the open right half-plane. -/
private lemma gammaFactor_analyticAt_of_re_pos {N : ℕ} (χ : DirichletCharacter ℂ N) {z : ℂ}
    (hz : 0 < z.re) : AnalyticAt ℂ (gammaFactor χ) z := by
  rcases χ.even_or_odd with hE | hO
  · have hγ : gammaFactor χ = Complex.Gammaℝ := by
      funext s
      exact Even.gammaFactor_def hE s
    rw [hγ]
    exact Gammaℝ_analyticAt_of_re_pos hz
  · have hγ : gammaFactor χ = (fun s : ℂ => Complex.Gammaℝ (s + 1)) := by
      funext s
      exact Odd.gammaFactor_def hO s
    rw [hγ]
    change AnalyticAt ℂ (fun s : ℂ => Complex.Gammaℝ (s + 1)) z
    refine AnalyticAt.comp (g := Complex.Gammaℝ) (f := fun s : ℂ => s + 1) (x := z) ?_ ?_
    · have hz1 : 0 < (z + 1).re := by simp; linarith
      exact Gammaℝ_analyticAt_of_re_pos hz1
    · fun_prop

/-- The archimedean Gamma factor of a character does not vanish on the open right half-plane. -/
private lemma gammaFactor_ne_zero_of_re_pos {N : ℕ} (χ : DirichletCharacter ℂ N) {z : ℂ}
    (hz : 0 < z.re) : gammaFactor χ z ≠ 0 := by
  rcases χ.even_or_odd with hE | hO
  · rw [Even.gammaFactor_def hE]
    exact Complex.Gammaℝ_ne_zero_of_re_pos hz
  · rw [Odd.gammaFactor_def hO]
    have hz1 : 0 < (z + 1).re := by simp; linarith
    exact Complex.Gammaℝ_ne_zero_of_re_pos hz1

/-- **Divisor comparison at points of the right half-plane.**
For a non-trivial Dirichlet character `χ`, the divisor of the completed L-function at a point
`u` with `0 < Re u` is at most the divisor of the (ordinary) L-function there: the Gamma factor
multiplying `LFunction χ` into `completedLFunction χ` is analytic and zero-free on the right
half-plane, so it contributes nothing to the divisor. -/
theorem completedL_divisor_le_L {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (U : Set ℂ) {u : ℂ} (huU : u ∈ U) (hre : 0 < u.re) :
    MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) U u ≤
      MeromorphicOn.divisor (DirichletCharacter.LFunction χ) U u := by
  classical
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  let L : ℂ → ℂ := DirichletCharacter.LFunction χ
  have hΛan : AnalyticOnNhd ℂ Λ U := by
    intro z hz
    exact (differentiable_completedLFunction hχ).analyticAt z
  have hLan : AnalyticOnNhd ℂ L U := by
    intro z hz
    exact (differentiable_LFunction hχ).analyticAt z
  by_cases h0 : Λ u = 0
  · have hγan : AnalyticAt ℂ (gammaFactor χ) u := gammaFactor_analyticAt_of_re_pos χ hre
    have hγ0 : gammaFactor χ u ≠ 0 := gammaFactor_ne_zero_of_re_pos χ hre
    have hev' : {z : ℂ | 0 < z.re} ∈ 𝓝[≠] u := by
      simpa [nhdsWithin] using
        (Filter.mem_inf_of_left ((isOpen_lt continuous_const continuous_re).mem_nhds hre))
    have hfun : (fun z : ℂ => Λ z) =ᶠ[𝓝[≠] u] fun z : ℂ => gammaFactor χ z * L z := by
      filter_upwards [hev'] with z hz
      · dsimp [Λ, L]
        rw [completedLFunction_eq_mul_gammaFactor_of_re_pos χ hz]
        ring
    have hordL : meromorphicOrderAt (fun z : ℂ => gammaFactor χ z * L z) u =
        meromorphicOrderAt L u :=
      meromorphicOrderAt_mul_of_ne_zero hγan hγ0
    have hord : meromorphicOrderAt Λ u = meromorphicOrderAt L u := by
      dsimp [Λ]
      calc
        meromorphicOrderAt (fun z : ℂ => DirichletCharacter.completedLFunction χ z) u
            = meromorphicOrderAt (fun z : ℂ => gammaFactor χ z * L z) u :=
              meromorphicOrderAt_congr hfun
        _ = meromorphicOrderAt L u := hordL
    have hdΛ : MeromorphicOn.divisor Λ U u = MeromorphicOn.divisor L U u := by
      rw [MeromorphicOn.divisor_apply hΛan.meromorphicOn huU,
        MeromorphicOn.divisor_apply hLan.meromorphicOn huU]
      exact congrArg (WithTop.untop₀ (α := ℤ)) hord
    rw [hdΛ]
  · have hd : MeromorphicOn.divisor Λ U u = 0 := by
      rw [MeromorphicOn.divisor_apply hΛan.meromorphicOn huU]
      have hAn : AnalyticAt ℂ Λ u := hΛan u huU
      have hord : meromorphicOrderAt Λ u = 0 := by
        rw [hAn.meromorphicOrderAt_eq]
        have h0 : analyticOrderAt Λ u = 0 := analyticOrderAt_eq_zero.mpr (Or.inr h0)
        simp [h0]
      simp [hord]
    have hnn : 0 ≤ MeromorphicOn.divisor L U u := by
      rw [MeromorphicOn.divisor_apply hLan.meromorphicOn huU]
      have hAn : AnalyticAt ℂ L u := hLan u huU
      have hNF := hAn.meromorphicNFAt
      have hord : (0 : WithTop ℤ) ≤ meromorphicOrderAt L u :=
        (MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt hNF).2 hAn
      exact (WithTop.untop₀_nonneg (α := ℤ) (a := meromorphicOrderAt L u)).mpr hord
    rw [hd]
    exact hnn

end Commons.NumberTheory.DirichletCharacter