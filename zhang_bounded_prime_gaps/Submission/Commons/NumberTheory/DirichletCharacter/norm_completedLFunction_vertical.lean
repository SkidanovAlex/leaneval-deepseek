import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Submission.Commons.NumberTheory.BombieriVinogradov.bilinear_char_perron_bound

open Complex DirichletCharacter
set_option autoImplicit false

namespace Commons.NumberTheory.DirichletCharacter

open Complex Filter MeasureTheory Set
open scoped Real


/-- Pointwise norm identity for the integrand of Euler's integral. -/
lemma norm_integrand (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖(Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1)‖ = Real.exp (-x) * x ^ (s.re - 1) := by
  rw [norm_mul, Complex.norm_of_nonneg (le_of_lt (Real.exp_pos (-x))),
      norm_cpow_eq_rpow_re_of_pos hx]
  rw [Complex.sub_re, Complex.one_re]

/-- The Euler integral for the gamma function is non-negative for real exponents. -/
lemma integral_nonneg_Ioi {σ : ℝ} :
    (0 : ℝ) ≤ ∫ x : ℝ in Ioi (0 : ℝ), Real.exp (-x) * x ^ (σ - 1) := by
  refine integral_nonneg_of_ae ?_
  refine (ae_restrict_iff' (p := fun x : ℝ => 0 ≤ Real.exp (-x) * x ^ (σ - 1))
    measurableSet_Ioi).mpr ?_
  filter_upwards with x hx
  exact mul_nonneg (le_of_lt (Real.exp_pos (-x)))
    (Real.rpow_nonneg (le_of_lt (mem_Ioi.mp hx)) (σ - 1))

/--
**Vertical bound for the Gamma function.**  For `0 < Re s`, the modulus of `Γ(s)` is at
most the value of `Γ` at the real point `Re s`:

`‖Γ(s)‖ ≤ ‖Γ(Re s)‖`.
-/
theorem norm_Gamma_le_norm_Gamma_re (s : ℂ) (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ ‖Complex.Gamma (s.re : ℂ)‖ := by
  have hsσ : 0 < (s.re : ℂ).re := by simpa using hs
  rw [Complex.Gamma_eq_integral hs, Complex.Gamma_eq_integral hsσ]
  let R : ℝ := ∫ x : ℝ in Ioi (0 : ℝ), Real.exp (-x) * x ^ (s.re - 1)
  have h1 : ‖Complex.GammaIntegral s‖ ≤ R := by
    calc
    ‖Complex.GammaIntegral s‖
        = ‖∫ x : ℝ in Ioi (0 : ℝ), (Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1)‖ := by
          simp [Complex.GammaIntegral]
    _ ≤ ∫ x : ℝ in Ioi (0 : ℝ), ‖(Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1)‖ := by
        exact norm_integral_le_integral_norm _
    _ = R := by
        dsimp [R]
        refine setIntegral_congr_fun measurableSet_Ioi ?_
        intro x hx
        exact norm_integrand s (mem_Ioi.mp hx)
  have h2 : ‖Complex.GammaIntegral (s.re : ℂ)‖ = R := by
    rw [Complex.GammaIntegral_ofReal]
    dsimp [R]
    rw [Complex.norm_of_nonneg (integral_nonneg_Ioi)]
  calc
    ‖Complex.GammaIntegral s‖ ≤ R := h1
    _ = ‖Complex.GammaIntegral (s.re : ℂ)‖ := h2.symm

/--
**Vertical bound for the Gamma function at half-shifted arguments.**  For a shift `a`
(so that the argument is `(z + a + I·t) / 2`, the shape that occurs in the archimedean
gamma factor of a Dirichlet L-function) and `0 < Re z`, `‖Γ((z + a + I t)/2)‖` is
bounded uniformly in `t : ℝ` by the value of `Γ` at the real midpoint
`(Re z + Re a) / 2`.
-/
theorem norm_Gamma_vertical_shifted_le (z a : ℂ) (t : ℝ) (hz : 0 < z.re) (ha : 0 ≤ a.re) :
    ‖Complex.Gamma ((z + a + I * t) / 2)‖
      ≤ ‖Complex.Gamma (((z.re + a.re) / 2 : ℝ) : ℂ)‖ := by
  have hdiv : ((z + a + I * t) / 2).re = (z.re + a.re) / 2 := by
    rw [Complex.div_re]
    simp
    ring_nf
  have hre : 0 < ((z + a + I * t) / 2).re := by
    rw [hdiv]
    exact div_pos (by linarith) (by norm_num)
  have h := norm_Gamma_le_norm_Gamma_re ((z + a + I * t) / 2) hre
  rwa [hdiv] at h

/-- Real part of a half: `(s / 2).re = s.re / 2`. -/
lemma re_of_half (s : ℂ) : (s / 2).re = s.re / 2 := by
  rw [Complex.div_re]
  norm_num
  ring

/--
**Vertical bound for Deligne's real gamma factor.**  For `0 < Re s`,
`‖Gammaℝ s‖ ≤ ‖Gammaℝ (Re s)‖` where `Gammaℝ s = π^(-s/2) · Γ(s/2)`.
-/
theorem norm_Gammaℝ_le_norm_Gammaℝ_re (s : ℂ) (hs : 0 < s.re) :
    ‖Complex.Gammaℝ s‖ ≤ ‖Complex.Gammaℝ (s.re : ℂ)‖ := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def]
  rw [norm_mul, norm_mul]
  rw [norm_cpow_eq_rpow_re_of_pos Real.pi_pos, norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have h1 : (-s / 2).re = -s.re / 2 := by
    rw [Complex.div_re, Complex.neg_re]
    norm_num
    ring
  have h2 : (-(s.re : ℂ) / 2).re = -s.re / 2 := by
    rw [Complex.div_re, Complex.neg_re]
    norm_num
    ring
  rw [h1, h2]
  have hpos : 0 < (s / 2).re := by
    rw [re_of_half]
    exact div_pos hs (by norm_num)
  have h := norm_Gamma_le_norm_Gamma_re (s / 2) hpos
  have hArg : ((s / 2).re : ℂ) = (s.re : ℂ) / 2 := by
    rw [re_of_half]
    rw [Complex.ofReal_div]
    rw [show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num]
  have hΓ : ‖Complex.Gamma (s / 2)‖ ≤ ‖Complex.Gamma ((s.re : ℂ) / 2)‖ := by
    simpa [hArg] using h
  exact mul_le_mul_of_nonneg_left hΓ (Real.rpow_nonneg (le_of_lt Real.pi_pos) _)

/-- On `Re s > 1` the completed L-function equals `LFunction * gammaFactor`. -/
lemma completedLFunction_eq_mul_gammaFactor {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    completedLFunction χ s = LFunction χ s * gammaFactor χ s := by
  have hs0 : s ≠ 0 := ne_zero_of_one_lt_re hs
  have h := LFunction_eq_completed_div_gammaFactor χ s (.inl hs0)
  rcases χ.even_or_odd with hE | hO
  · have hG : gammaFactor χ s ≠ 0 := by
      rw [Even.gammaFactor_def hE]
      exact Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
    calc
      completedLFunction χ s = (completedLFunction χ s / gammaFactor χ s) * gammaFactor χ s := by
        rw [div_mul_cancel₀ _ hG]
      _ = LFunction χ s * gammaFactor χ s := by rw [h]
  · have hG : gammaFactor χ s ≠ 0 := by
      rw [Odd.gammaFactor_def hO]
      exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
    calc
      completedLFunction χ s = (completedLFunction χ s / gammaFactor χ s) * gammaFactor χ s := by
        rw [div_mul_cancel₀ _ hG]
      _ = LFunction χ s * gammaFactor χ s := by rw [h]

/-- For `Re s > 1` the gamma factor at `s` is bounded by its value at the real point `Re s`. -/
lemma gammaFactor_norm_le_re {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    ‖gammaFactor χ s‖ ≤ ‖gammaFactor χ (s.re : ℂ)‖ := by
  rcases χ.even_or_odd with hE | hO
  · rw [Even.gammaFactor_def hE, Even.gammaFactor_def hE]
    exact norm_Gammaℝ_le_norm_Gammaℝ_re s (by linarith)
  · rw [Odd.gammaFactor_def hO, Odd.gammaFactor_def hO]
    have h := norm_Gammaℝ_le_norm_Gammaℝ_re (s + 1) (by
      rw [Complex.add_re, Complex.one_re]
      linarith)
    simpa [Complex.add_re, Complex.ofReal_add] using h

/-- A uniform (in the imaginary direction) bound for the L-function on `Re s > 1`. -/
lemma LFunction_norm_le_tsum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    ‖LFunction χ s‖ ≤ ∑' n : ℕ, ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) s n‖ := by
  have hsum : Summable fun n : ℕ => ‖LSeries.term (fun n : ℕ => χ (n : ZMod N)) s n‖ := by
    exact (LSeriesSummable_of_one_lt_re χ hs).norm
  have hsum1 : Summable fun n : ℕ => ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) s n‖ := by
    have hLSS : LSeriesSummable (fun _ : ℕ => (1 : ℂ)) s :=
      LSeriesSummable_of_bounded_of_one_lt_re (f := fun _ : ℕ => (1 : ℂ)) (m := 1)
        (by intro n hn; simp) hs
    exact hLSS.norm
  calc
    ‖LFunction χ s‖ = ‖LSeries (fun n : ℕ => χ (n : ZMod N)) s‖ := by
      rw [LFunction_eq_LSeries χ hs]
    _ ≤ ∑' n : ℕ, ‖LSeries.term (fun n : ℕ => χ (n : ZMod N)) s n‖ := by
      exact norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' n : ℕ, ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) s n‖ := by
      exact hsum.tsum_le_tsum
        (fun n => LSeries.norm_term_le s (by simpa using χ.norm_le_one (n : ZMod N))) hsum1

/-- `|Λ(σ + I t, χ)|` (completed L-function) is bounded uniformly in `t` for `1 < σ`. -/
theorem norm_completedLFunction_vertical {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {σ : ℝ} (hσ : 1 < σ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, ‖completedLFunction χ (σ + Complex.I * (t : ℂ))‖ ≤ B := by
  let oneF : ℕ → ℂ := fun _ => (1 : ℂ)
  let C1 : ℝ := ∑' n : ℕ, ‖LSeries.term oneF (σ : ℂ) n‖
  let C2 : ℝ := ‖gammaFactor χ (σ : ℂ)‖
  have hC1 : 0 ≤ C1 := by
    dsimp [C1]
    exact tsum_nonneg (fun n => norm_nonneg _)
  have hC2 : 0 ≤ C2 := by
    dsimp [C2]
    exact norm_nonneg _
  refine ⟨C1 * C2, mul_nonneg hC1 hC2, ?_⟩
  intro t
  let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  have hs_re : s.re = σ := by
    dsimp [s]
    simp
  have hsσs : 1 < s.re := by
    rwa [hs_re]
  have hprod : completedLFunction χ s = LFunction χ s * gammaFactor χ s :=
    completedLFunction_eq_mul_gammaFactor χ hsσs
  have hG : ‖gammaFactor χ s‖ ≤ C2 := by
    dsimp [C2]
    calc
      ‖gammaFactor χ s‖ ≤ ‖gammaFactor χ (s.re : ℂ)‖ := gammaFactor_norm_le_re χ hsσs
      _ = ‖gammaFactor χ (σ : ℂ)‖ := by rw [hs_re]
  have hsum_s : (∑' n : ℕ, ‖LSeries.term oneF s n‖) = C1 := by
    dsimp [C1]
    apply tsum_congr
    intro n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    rw [hs_re]
    simp [oneF]
  have hL : ‖LFunction χ s‖ ≤ C1 := by
    calc
      ‖LFunction χ s‖ ≤ ∑' n : ℕ, ‖LSeries.term oneF s n‖ := LFunction_norm_le_tsum χ hsσs
      _ = C1 := hsum_s
  calc
    ‖completedLFunction χ s‖ = ‖LFunction χ s * gammaFactor χ s‖ := by rw [hprod]
    _ = ‖LFunction χ s‖ * ‖gammaFactor χ s‖ := by rw [norm_mul]
    _ ≤ ‖LFunction χ s‖ * C2 := mul_le_mul_of_nonneg_left hG (norm_nonneg _)
    _ ≤ C1 * C2 := mul_le_mul_of_nonneg_right hL hC2

end Commons.NumberTheory.DirichletCharacter