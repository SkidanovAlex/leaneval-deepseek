import Mathlib
import Submission.Work.LinnikAreas.Density4.SsmSetup
import Submission.Work.LinnikAreas.Density4.norm_lcmF_le
import Submission.Work.LinnikAreas.Density4.norm_lcmF_le_gen
import Submission.Work.LinnikAreas.Density4.integrable_one_add_abs_rpow_exp
import Submission.Work.LinnikAreas.Density4.integrable_gamma_line_mul
import Submission.Work.LinnikAreas.Density4.SsmPhiAux

open DirichletCharacter Complex MeasureTheory
open scoped Classical BigOperators

noncomputable section

namespace Work.LinnikAreas.Density4

/-- The numerical bound for the shifted contour integral of `Phi`: on the vertical line
`Re s = c1 = 1 - ρ.re - 1/k` the regularised integrand is dominated by
`Cb · log q · (2+|t|) · ‖Γ(s+1)‖ · X^{c1} · ((VW)^{1/k}(1+log(VW))³)`. -/
theorem Phi_shifted_bound {q : ℕ} [NeZero q] (hq : 2 ≤ q) {U V W X : ℝ} (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (ρ : ℂ)
    {k : ℕ} (hk : 1 ≤ k) {Cb CΓ c1 : ℝ} (hCbpos : 0 < Cb) (hCΓpos : 0 < CΓ)
    (hU : 0 < U) (hUV : U ≤ V) (hV : 1 ≤ V) (hW : 1 ≤ W) (hX : 1 ≤ X)
    (hL0 : DirichletCharacter.LFunction χ ρ = 0) (hc1 : c1 = 1 - ρ.re - (k:ℝ)⁻¹)
    (hdist : 1 / Real.log q ≤ |c1|)
    (hLbd : ∀ t : ℝ, ‖DirichletCharacter.LFunction χ (ρ + ((c1 : ℂ) + (t : ℂ) * Complex.I))‖ ≤ Cb * (2 + |t|))
    (hΓ : ∫ t : ℝ, ‖Complex.Gamma (((c1 : ℂ) + (t : ℂ) * Complex.I) + 1)‖ * (2 + |t|) ≤ CΓ) :
    ∫ t : ℝ, ‖Phi q U V W X χ ρ ((c1 : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ Cb * CΓ * Real.log q * X ^ c1 * ((V * W) ^ (1 / (k:ℝ)) * (1 + Real.log (V * W)) ^ 3) := by
  classical
  have hq1 : 1 < q := by omega
  have hlogpos : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq1)
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hkinv1 : (k:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hk)
  have hXpos : 0 < X := lt_of_lt_of_le one_pos hX
  have hVWpos : (0:ℝ) < V * W := by nlinarith
  -- Step 1: `ρ` lies strictly to the left of the pole of the (possibly principal) L-function
  have hρlt : ρ.re < 1 := by
    by_contra hcon
    push_neg at hcon
    exact absurd hL0 (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hcon)
  -- Step 2: `c1 + 1 > 0`, so that the Gamma factor is finite on the shifted line
  have ha : 0 < c1 + 1 := by rw [hc1]; linarith
  -- Step 3: integrability of the majorant
  set g : ℝ → ℝ := fun t => ‖Complex.Gamma (((c1 : ℂ) + (t : ℂ) * Complex.I) + 1)‖ * (2 + |t|) with hgdef
  have hgint : Integrable g := by
    rw [hgdef]
    have h := integrable_gamma_line_mul (c1 + 1) ha
    have heq : (fun t : ℝ => ‖Complex.Gamma (((c1 : ℂ) + (t : ℂ) * Complex.I) + 1)‖ * (2 + |t|))
        = fun t : ℝ => ‖Complex.Gamma (((c1 + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|) := by
      funext t
      rw [show ((c1 : ℂ) + (t : ℂ) * Complex.I) + 1
            = ((c1 + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I by push_cast; ring]
    rw [heq]
    exact h
  set K : ℝ := Cb * Real.log q * X ^ c1 * ((V * W) ^ (1 / (k:ℝ)) * (1 + Real.log (V * W)) ^ 3)
    with hKdef
  have hKnn : 0 ≤ K := by
    have h1 : (0:ℝ) ≤ X ^ c1 := Real.rpow_nonneg hXpos.le c1
    have h2 : (0:ℝ) ≤ (V * W) ^ (1 / (k:ℝ)) := Real.rpow_nonneg hVWpos.le _
    have hVW1 : (1:ℝ) ≤ V * W := by nlinarith
    have h3 : (0:ℝ) ≤ (1 + Real.log (V * W)) ^ 3 :=
      pow_nonneg (by linarith [Real.log_nonneg hVW1]) 3
    have h4 : 0 ≤ Cb * Real.log q * X ^ c1 := by positivity
    rw [hKdef]
    exact mul_nonneg h4 (mul_nonneg h2 h3)
  -- Step 4: pointwise bound
  have hpoint : ∀ t : ℝ, ‖Phi q U V W X χ ρ ((c1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ K * g t := by
    intro t
    set s : ℂ := (c1 : ℂ) + (t : ℂ) * Complex.I with hsdef
    have hs_re : s.re = c1 := by simp [hsdef]
    have hs_ge : 1 / Real.log q ≤ ‖s‖ := by
      calc 1 / Real.log q ≤ |c1| := hdist
        _ = |s.re| := by rw [hs_re]
        _ ≤ ‖s‖ := Complex.abs_re_le_norm s
    have hs_ne : s ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hs_ge
      have : (0:ℝ) < 1 / Real.log q := by positivity
      linarith
    have hs_inv : ‖s⁻¹‖ ≤ Real.log q := by
      rw [norm_inv, inv_le_comm₀ (norm_pos_iff.mpr hs_ne) hlogpos]
      simpa [one_div] using hs_ge
    have hdslope : dslope (fun u : ℂ => DirichletCharacter.LFunction χ (ρ + u)) 0 s
        = s⁻¹ * DirichletCharacter.LFunction χ (ρ + s) := by
      rw [dslope_of_ne _ hs_ne, slope]
      simp [hL0, smul_eq_mul]
    have hLn : ‖DirichletCharacter.LFunction χ (ρ + s)‖ ≤ Cb * (2 + |t|) := by
      have h := hLbd t
      rw [show ρ + ((c1 : ℂ) + (t : ℂ) * Complex.I) = ρ + s by rw [hsdef]] at h
      exact h
    have hXnorm : ‖(X : ℂ) ^ s‖ = X ^ c1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hXpos, hs_re]
    have hre : 1 - (k : ℝ)⁻¹ ≤ (ρ + s).re := by
      have heq : (ρ + s).re = 1 - (k : ℝ)⁻¹ := by
        rw [Complex.add_re, hs_re, hc1]; ring
      rw [heq]
    have hFnorm : ‖lcmF q U V W χ (ρ + s)‖
        ≤ (V * W) ^ (1 / (k:ℝ)) * (1 + Real.log (V * W)) ^ 3 :=
      norm_lcmF_le_gen q hU hUV hV hW χ hk hre
    have hΓeq : ‖Complex.Gamma (s + 1)‖
        = ‖Complex.Gamma (((c1 : ℂ) + (t : ℂ) * Complex.I) + 1)‖ := by rw [hsdef]
    rw [hKdef, hgdef]
    calc ‖Phi q U V W X χ ρ s‖
        = ‖Complex.Gamma (s + 1)‖ * ‖s⁻¹‖ * ‖DirichletCharacter.LFunction χ (ρ + s)‖
            * ‖(X : ℂ) ^ s‖ * ‖lcmF q U V W χ (ρ + s)‖ := by
          rw [Phi, hdslope]
          simp only [norm_mul]
          ring
      _ ≤ ‖Complex.Gamma (((c1 : ℂ) + (t : ℂ) * Complex.I) + 1)‖ * Real.log q
            * (Cb * (2 + |t|)) * X ^ c1
            * ((V * W) ^ (1 / (k:ℝ)) * (1 + Real.log (V * W)) ^ 3) := by
          rw [hΓeq, hXnorm]
          gcongr
      _ = (Cb * Real.log q * X ^ c1 * ((V * W) ^ (1 / (k:ℝ)) * (1 + Real.log (V * W)) ^ 3))
            * (‖Complex.Gamma (((c1 : ℂ) + (t : ℂ) * Complex.I) + 1)‖ * (2 + |t|)) := by
          ring
  -- Step 5: integrate
  calc ∫ t : ℝ, ‖Phi q U V W X χ ρ ((c1 : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ ∫ t : ℝ, K * g t := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
          (hgint.const_mul K) (Filter.Eventually.of_forall hpoint)
    _ = K * ∫ t : ℝ, g t := by rw [integral_const_mul]
    _ ≤ K * CΓ := by
        refine mul_le_mul_of_nonneg_left ?_ hKnn
        rw [hgdef]
        exact hΓ
    _ = Cb * CΓ * Real.log q * X ^ c1 * ((V * W) ^ (1 / (k:ℝ)) * (1 + Real.log (V * W)) ^ 3) := by
        rw [hKdef]; ring

end Work.LinnikAreas.Density4
