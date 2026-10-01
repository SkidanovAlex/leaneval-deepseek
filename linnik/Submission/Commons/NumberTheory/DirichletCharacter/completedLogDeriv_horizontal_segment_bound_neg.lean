import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_horizontal_segment_bound
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_conj
import Submission.Commons.NumberTheory.DirichletCharacter.isPrimitive_inv
import Submission.Commons.NumberTheory.DirichletCharacter.Even_inv
import Submission.Commons.NumberTheory.DirichletCharacter.Odd_inv

open Complex DirichletCharacter
open scoped Real Topology
open MeasureTheory intervalIntegral

set_option maxHeartbeats 1000000

namespace Commons.NumberTheory.DirichletCharacter

/-- The inverse of a non-trivial Dirichlet character is non-trivial. -/
private lemma inv_ne_one_of_char_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) : χ⁻¹ ≠ 1 := by
  intro h
  apply hχ
  calc χ = (χ⁻¹)⁻¹ := by rw [inv_inv]
    _ = (1 : DirichletCharacter ℂ N)⁻¹ := by rw [h]
    _ = 1 := by simp

/-- Conjugation commutes with the archimedean gamma factor `Γℝ`. -/
private lemma GammaR_star (z : ℂ) :
    (starRingEnd ℂ) (Complex.Gammaℝ z) = Complex.Gammaℝ ((starRingEnd ℂ) z) := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def]
  have hpow : (starRingEnd ℂ) ((Real.pi : ℂ) ^ (-z / 2)) =
      (Real.pi : ℂ) ^ (-(starRingEnd ℂ) z / 2) := by
    rw [conj_cpow_ofReal_pos Real.pi Real.pi_pos]
    congr 1
    rw [map_div₀, map_neg]
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
  have hG : (starRingEnd ℂ) (Complex.Gamma (z / 2)) =
      Complex.Gamma ((starRingEnd ℂ) z / 2) := by
    rw [← Complex.Gamma_conj (z / 2)]
    congr 1
    rw [map_div₀]
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
  rw [map_mul, hpow, hG]

/-- The archimedean gamma factor is non-zero for arguments of positive real part. -/
private lemma gammaFactor_ne_zero_of_re_pos {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 0 < s.re) : χ.gammaFactor s ≠ 0 := by
  rcases χ.even_or_odd with hχ | hχ
  · rw [hχ.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · rw [hχ.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by rw [Complex.add_re, one_re]; linarith)

/-- Conjugation of the archimedean gamma factor. -/
private lemma gammaFactor_conj {N : ℕ} (χ : DirichletCharacter ℂ N) (z : ℂ) :
    (starRingEnd ℂ) (χ.gammaFactor z) = χ.gammaFactor ((starRingEnd ℂ) z) := by
  rcases χ.even_or_odd with hE | hO
  · rw [hE.gammaFactor_def, hE.gammaFactor_def]
    exact GammaR_star z
  · rw [hO.gammaFactor_def, hO.gammaFactor_def]
    have h1 : (starRingEnd ℂ) (z + 1) = (starRingEnd ℂ) z + 1 := by
      rw [map_add]
      norm_num
    rw [GammaR_star (z + 1), h1]

/-- The gamma factor of `χ⁻¹` agrees with that of `χ`. -/
private lemma gammaFactor_inv {N : ℕ} (χ : DirichletCharacter ℂ N) (z : ℂ) :
    (χ⁻¹).gammaFactor z = χ.gammaFactor z := by
  rcases χ.even_or_odd with hE | hO
  · rw [(Even_inv hE).gammaFactor_def, hE.gammaFactor_def]
  · rw [(Odd_inv hO).gammaFactor_def, hO.gammaFactor_def]

/-- Pointwise conjugation identity for the completed L-function on the half-plane
`Re w > 0`. -/
private lemma completedLFunction_conj_of_re_pos {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {w : ℂ} (hw : 0 < w.re) :
    (starRingEnd ℂ) (DirichletCharacter.completedLFunction χ w) =
      DirichletCharacter.completedLFunction (χ⁻¹) ((starRingEnd ℂ) w) := by
  have hw0 : w ≠ 0 := by
    intro h
    have : (0 : ℝ) < w.re := hw
    rw [h] at this
    norm_num at this
  have hsw : 0 < ((starRingEnd ℂ) w).re := by simpa using hw
  have hγw : χ.gammaFactor w ≠ 0 := gammaFactor_ne_zero_of_re_pos χ hw
  have hγsw : (χ⁻¹).gammaFactor ((starRingEnd ℂ) w) ≠ 0 := by
    rw [gammaFactor_inv]
    exact gammaFactor_ne_zero_of_re_pos χ hsw
  have hL1 := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ w (Or.inl hw0)
  have hL1' : DirichletCharacter.completedLFunction χ w =
      DirichletCharacter.LFunction χ w * χ.gammaFactor w := by
    rw [hL1]
    exact (div_mul_cancel₀ (a := DirichletCharacter.completedLFunction χ w)
      (b := χ.gammaFactor w) hγw).symm
  have hsw0 : ((starRingEnd ℂ) w) ≠ 0 := by
    intro h
    have : ((starRingEnd ℂ) w).re = 0 := by rw [h]; simp
    linarith
  have hL2 := DirichletCharacter.LFunction_eq_completed_div_gammaFactor (χ⁻¹) ((starRingEnd ℂ) w)
    (Or.inl hsw0)
  have hL2' : DirichletCharacter.completedLFunction (χ⁻¹) ((starRingEnd ℂ) w) =
      DirichletCharacter.LFunction (χ⁻¹) ((starRingEnd ℂ) w) *
        (χ⁻¹).gammaFactor ((starRingEnd ℂ) w) := by
    rw [hL2]
    exact (div_mul_cancel₀ (a := DirichletCharacter.completedLFunction (χ⁻¹) ((starRingEnd ℂ) w))
      (b := (χ⁻¹).gammaFactor ((starRingEnd ℂ) w)) hγsw).symm
  calc
    (starRingEnd ℂ) (DirichletCharacter.completedLFunction χ w)
        = (starRingEnd ℂ) (DirichletCharacter.LFunction χ w * χ.gammaFactor w) := by rw [hL1']
    _ = (starRingEnd ℂ) (DirichletCharacter.LFunction χ w) * (starRingEnd ℂ) (χ.gammaFactor w) := by
          rw [map_mul]
    _ = DirichletCharacter.LFunction (χ⁻¹) ((starRingEnd ℂ) w) *
          χ.gammaFactor ((starRingEnd ℂ) w) := by
          rw [LFunction_conj χ hχ w, gammaFactor_conj χ w]
    _ = DirichletCharacter.LFunction (χ⁻¹) ((starRingEnd ℂ) w) *
          (χ⁻¹).gammaFactor ((starRingEnd ℂ) w) := by rw [gammaFactor_inv]
    _ = DirichletCharacter.completedLFunction (χ⁻¹) ((starRingEnd ℂ) w) := by rw [hL2']

/-- The completed L-function is conjugate-symmetric: `Λ(χ)(conj s) = conj (Λ(χ⁻¹)(s))`. -/
private theorem completedLFunction_conj {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) :
    DirichletCharacter.completedLFunction χ ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (DirichletCharacter.completedLFunction (χ⁻¹) s) := by
  classical
  have hχinv : χ⁻¹ ≠ 1 := inv_ne_one_of_char_ne_one χ hχ
  let A : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  let B : ℂ → ℂ := DirichletCharacter.completedLFunction (χ⁻¹)
  have hdA : Differentiable ℂ A := by
    simpa [A] using (DirichletCharacter.differentiable_completedLFunction (χ := χ) hχ)
  have hdB : Differentiable ℂ B := by
    simpa [B] using (DirichletCharacter.differentiable_completedLFunction (χ := χ⁻¹) hχinv)
  have hAan : AnalyticOnNhd ℂ (starComp A) Set.univ :=
    fun z _ => (differentiable_starComp hdA).analyticAt z
  have hBan : AnalyticOnNhd ℂ B Set.univ := fun z _ => hdB.analyticAt z
  have hev : starComp A =ᶠ[𝓝 (2 : ℂ)] B := by
    have hmem : {z : ℂ | 0 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
    filter_upwards [hmem] with z hz
    dsimp [A, B, starComp]
    have hzre : 0 < ((starRingEnd ℂ) z).re := by simpa using hz
    have hc := completedLFunction_conj_of_re_pos χ hχ (w := (starRingEnd ℂ) z) hzre
    simpa [Complex.conj_conj] using hc
  have hEqOn := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (U := (Set.univ : Set ℂ))
    hAan hBan isPreconnected_univ (Set.mem_univ (2 : ℂ)) hev
  have hfun : starComp A = B := funext fun z => hEqOn (Set.mem_univ z)
  have hs := congrFun hfun s
  dsimp [A, B, starComp] at hs
  have := congrArg (starRingEnd ℂ) hs
  simpa [Complex.conj_conj] using this

/-- Conjugation of the logarithmic derivative of the completed L-function. -/
private lemma logDeriv_completedLFunction_conj {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ) :
    logDeriv (DirichletCharacter.completedLFunction (χ⁻¹)) s =
      (starRingEnd ℂ)
        (logDeriv (DirichletCharacter.completedLFunction χ) ((starRingEnd ℂ) s)) := by
  classical
  let A : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  let B : ℂ → ℂ := DirichletCharacter.completedLFunction (χ⁻¹)
  have hdA : Differentiable ℂ A := by
    simpa [A] using (DirichletCharacter.differentiable_completedLFunction (χ := χ) hχ)
  have hfun : starComp A = B := by
    funext z
    dsimp [A, B, starComp]
    have hc := congrArg (starRingEnd ℂ) (completedLFunction_conj χ hχ z)
    simpa [Complex.conj_conj] using hc
  have hderiv : deriv B s = (starRingEnd ℂ) (deriv A ((starRingEnd ℂ) s)) := by
    rw [← hfun]
    exact (hasDerivAt_star_comp (f := A) (c := deriv A ((starRingEnd ℂ) s)) (z := s)
      (hdA ((starRingEnd ℂ) s)).hasDerivAt).deriv
  have hval : B s = (starRingEnd ℂ) (A ((starRingEnd ℂ) s)) := by
    rw [← hfun]; rfl
  calc
    logDeriv B s = deriv B s / B s := rfl
    _ = (starRingEnd ℂ) (deriv A ((starRingEnd ℂ) s)) /
          (starRingEnd ℂ) (A ((starRingEnd ℂ) s)) := by rw [hderiv, hval]
    _ = (starRingEnd ℂ) (deriv A ((starRingEnd ℂ) s) / A ((starRingEnd ℂ) s)) := by
          rw [map_div₀]
    _ = (starRingEnd ℂ) (logDeriv A ((starRingEnd ℂ) s)) := rfl

theorem completedLogDeriv_horizontal_segment_bound_neg {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ C : ℝ, 0 < C ∧ ∀ T' : ℝ, 2 ≤ T' → ∀ δ : ℝ, 0 < δ →
      (∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → δ ≤ |ρ.im + T'|) →
      (∫ x : ℝ in (-1/2)..2, ‖logDeriv (DirichletCharacter.completedLFunction χ)
           ((x : ℂ) - (T' : ℂ) * Complex.I)‖) ≤
        C * Real.log (N * (T' + 3)) *
          (Real.log (N * (T' + 3)) + max 0 (Real.log (1 / δ))) := by
  classical
  have hχinv : χ⁻¹ ≠ 1 := inv_ne_one_of_char_ne_one χ hχ
  have hχinvprim : (χ⁻¹).IsPrimitive := isPrimitive_inv hχprim
  rcases completedLogDeriv_horizontal_segment_bound (χ⁻¹) hχinv hχinvprim with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro T' hT' δ hδ hzero
  have hzeroinv : ∀ ρ : ℂ, DirichletCharacter.completedLFunction (χ⁻¹) ρ = 0 →
      δ ≤ |ρ.im - T'| := by
    intro ρ hρ
    have hc := completedLFunction_conj χ hχ ρ
    have h0 : DirichletCharacter.completedLFunction χ ((starRingEnd ℂ) ρ) = 0 := by
      rw [hc, hρ, map_zero]
    have h1 := hzero ((starRingEnd ℂ) ρ) h0
    rw [Complex.conj_im] at h1
    rw [show (-ρ.im + T') = -(ρ.im - T') by ring, abs_neg] at h1
    exact h1
  have hpoint : ∀ x : ℝ,
      ‖logDeriv (DirichletCharacter.completedLFunction χ)
          ((x : ℂ) - (T' : ℂ) * Complex.I)‖ =
      ‖logDeriv (DirichletCharacter.completedLFunction (χ⁻¹))
          ((x : ℂ) + (T' : ℂ) * Complex.I)‖ := by
    intro x
    have h := logDeriv_completedLFunction_conj χ hχ ((x : ℂ) + (T' : ℂ) * Complex.I)
    have hcs : (starRingEnd ℂ) ((x : ℂ) + (T' : ℂ) * Complex.I) =
        (x : ℂ) - (T' : ℂ) * Complex.I := by
      rw [map_add, map_mul]
      simp [Complex.conj_ofReal, Complex.conj_I]
      ring
    have hnorm := congrArg (fun z : ℂ => ‖z‖) h.symm
    rw [Complex.norm_conj] at hnorm
    rw [hcs] at hnorm
    exact hnorm
  have hinteq : (∫ x : ℝ in (-1/2)..2, ‖logDeriv (DirichletCharacter.completedLFunction χ)
        ((x : ℂ) - (T' : ℂ) * Complex.I)‖) =
      (∫ x : ℝ in (-1/2)..2, ‖logDeriv (DirichletCharacter.completedLFunction (χ⁻¹))
        ((x : ℂ) + (T' : ℂ) * Complex.I)‖) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact hpoint x
  rw [hinteq]
  exact hC T' hT' δ hδ hzeroinv

end Commons.NumberTheory.DirichletCharacter
