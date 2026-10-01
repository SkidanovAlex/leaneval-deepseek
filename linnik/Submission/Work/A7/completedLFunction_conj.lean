import Mathlib
import Submission.Work.A7.CommonsDeps

/-!
# Conjugation symmetry of the completed Dirichlet L-function

For a non-trivial Dirichlet character `χ` and every `s : ℂ`,

`Λ(χ⁻¹, conj s) = conj (Λ(χ, s))`,

where `Λ` is Mathlib's `DirichletCharacter.completedLFunction`.

The proof is the classical one via the identity theorem. Both
`s ↦ conj (Λ(χ, conj s))` and `Λ(χ⁻¹, ·)` are entire (the characters are
non-trivial, so the completed L-functions are differentiable everywhere, and
conjugation-composition of a holomorphic function is holomorphic). On the open
half-plane `1 < re s` the completed L-function factors as
`Λ(χ, s) = L(χ, s) * gammaFactor χ s`; the L-function is compatible with
conjugation (`LFunction_conj`) and the archimedean Gamma factor is too, because
`Gammaℝ` is built from `π ^ (-s / 2)` and `Gamma (s / 2)`, both of which satisfy
Schwarz reflection, and inverse characters have the same parity. Hence the two
entire functions agree on a non-empty open set and therefore everywhere.
-/

namespace Work.A7

open Complex DirichletCharacter Filter
open scoped Topology

/-- Complex conjugation commutes with Deligne's archimedean Gamma factor. -/
lemma GammaR_conj (z : ℂ) :
    (starRingEnd ℂ) (Complex.Gammaℝ z) = Complex.Gammaℝ ((starRingEnd ℂ) z) := by
  rw [Complex.Gammaℝ_def, map_mul, ← Complex.Gamma_conj (z / 2), Complex.Gammaℝ_def]
  have harg : ((Real.pi : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (le_of_lt Real.pi_pos)]
    exact Real.pi_ne_zero.symm
  have h := Complex.cpow_conj (Real.pi : ℂ) (-z / 2) harg
  rw [Complex.conj_ofReal] at h
  rw [← h]
  congr 2 <;> simp [map_ofNat]

/-- The archimedean Gamma factor of `χ⁻¹` is the conjugate of that of `χ` at the conjugate
point. -/
lemma gammaFactor_conj_star {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (z : ℂ) :
    DirichletCharacter.gammaFactor χ⁻¹ z
      = (starRingEnd ℂ) (DirichletCharacter.gammaFactor χ ((starRingEnd ℂ) z)) := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def, (Commons.NumberTheory.DirichletCharacter.Even_inv h).gammaFactor_def]
    simpa using (GammaR_conj ((starRingEnd ℂ) z)).symm
  · rw [h.gammaFactor_def, (Commons.NumberTheory.DirichletCharacter.Odd_inv h).gammaFactor_def]
    simpa [map_add] using (GammaR_conj ((starRingEnd ℂ) z + 1)).symm

/-- The archimedean Gamma factor does not vanish to the right of the critical line. -/
lemma gammaFactor_ne_zero_of_re_pos' {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z : ℂ} (hz : 0 < z.re) : DirichletCharacter.gammaFactor χ z ≠ 0 := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def]; exact Complex.Gammaℝ_ne_zero_of_re_pos hz
  · rw [h.gammaFactor_def]
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    rw [Complex.add_re, Complex.one_re]; linarith

/-- The completed L-function factors as `L χ s * gammaFactor χ s` where the Gamma factor does
not vanish (in particular on `0 < re s`). -/
lemma completedLFunction_eq_mul_gammaFactor' {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z : ℂ} (hz : 0 < z.re) :
    DirichletCharacter.completedLFunction χ z
      = DirichletCharacter.LFunction χ z * DirichletCharacter.gammaFactor χ z := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z (Or.inl hz0)
  rw [h, div_mul_cancel₀ _ (gammaFactor_ne_zero_of_re_pos' χ hz)]

theorem completedLFunction_conj {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (s : ℂ) :
    DirichletCharacter.completedLFunction χ⁻¹ ((starRingEnd ℂ) s)
      = (starRingEnd ℂ) (DirichletCharacter.completedLFunction χ s) := by
  have hχinv : χ⁻¹ ≠ 1 := by
    intro h
    exact hχ (by simpa using congrArg (fun ψ : DirichletCharacter ℂ N => ψ⁻¹) h)
  have hF : AnalyticOnNhd ℂ
      (Commons.NumberTheory.DirichletCharacter.starComp (DirichletCharacter.completedLFunction χ))
      (Set.univ : Set ℂ) := fun z _ =>
    Differentiable.analyticAt (Commons.NumberTheory.DirichletCharacter.differentiable_starComp
      (DirichletCharacter.differentiable_completedLFunction hχ)) z
  have hG : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ⁻¹) (Set.univ : Set ℂ) :=
    fun z _ =>
      Differentiable.analyticAt (DirichletCharacter.differentiable_completedLFunction hχinv) z
  let z₀ : ℂ := 2
  have hz₀re : (1 : ℝ) < z₀.re := by dsimp [z₀]; norm_num
  have hset : {x : ℂ | 1 < x.re} ∈ 𝓝 z₀ :=
    (isOpen_lt continuous_const continuous_re).mem_nhds hz₀re
  have hev : Commons.NumberTheory.DirichletCharacter.starComp
        (DirichletCharacter.completedLFunction χ)
      =ᶠ[𝓝 z₀] DirichletCharacter.completedLFunction χ⁻¹ := by
    filter_upwards [hset] with z hz
    have hz' : 1 < ((starRingEnd ℂ) z).re := by simpa [Complex.conj_re] using hz
    have hγ : 0 < ((starRingEnd ℂ) z).re := lt_trans zero_lt_one hz'
    have hval := completedLFunction_eq_mul_gammaFactor' χ hγ
    have hval' := completedLFunction_eq_mul_gammaFactor' (χ⁻¹) (lt_trans zero_lt_one hz)
    have hconjL : (starRingEnd ℂ) (DirichletCharacter.LFunction χ ((starRingEnd ℂ) z))
        = DirichletCharacter.LFunction χ⁻¹ z := by
      have := Commons.NumberTheory.DirichletCharacter.LFunction_conj χ hχ ((starRingEnd ℂ) z)
      simpa using this
    unfold Commons.NumberTheory.DirichletCharacter.starComp
    rw [hval, map_mul, hconjL, ← gammaFactor_conj_star χ z, ← hval']
  have hEqOn := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (U := (Set.univ : Set ℂ))
    hF hG isPreconnected_univ (Set.mem_univ z₀) hev
  have h := hEqOn (Set.mem_univ ((starRingEnd ℂ) s))
  unfold Commons.NumberTheory.DirichletCharacter.starComp at h
  simpa using h.symm

end Work.A7
