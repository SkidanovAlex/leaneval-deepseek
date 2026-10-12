import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Fourier.Notation
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Submission.Work.BoseFixB3.Scaling.chiU_sq_indicator
import Submission.Work.BoseFixB3.Scaling.kinFT_scaled_phi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1000000
/-!
# `Submission/Work/BoseFixB3/Scaling/chiSq_mult_bound`

FS `final_v2.tex` ll. 1531–1535: the Fourier multiplier bound

  `|(ℓ⁻² − Δ)^M χ_Λ²| ≤ C ℓ^{-2M}`,

formalised here as a uniform bound on the corpus's `p`-convention multiplier
`Work.BoseFixB3.multOn` with symbol `F(r) = ((ℓ⁻¹)² + r²)^M` applied to the localisation
window `χ_Λ² = (chiU ℓ 0)²`.

## Strategy

`multOn F ℓ ψ x = Re ∫_p e^{i⟪p,x⟫} F(‖p‖) \hatψ(p) dp`, so

  `|multOn F ℓ ψ x| ≤ ∫_p F(‖p‖) ‖\hatψ(p)‖ dp`.

With `ψ = φ(ℓ⁻¹•·)`, `φ = χ²` (a fixed smooth compactly supported profile), the scaling of
the `p`-convention Fourier transform gives `\hatψ(p) = ℓ³ \hatφ(ℓ•p)`, and the change of
variables `p ↦ ℓ⁻¹•p` yields

  `∫_p F(‖p‖) ‖\hatψ(p)‖ dp = ℓ^{-2M} ∫_q (1+‖q‖²)^M ‖\hatφ(q)‖ dq`

because `F(ℓ⁻¹‖q‖) = ℓ^{-2M}(1+‖q‖²)^M`.  The remaining integral is a constant, so the
bound holds with `C = (2π)⁻³ ∫_q (1+‖q‖²)^M ‖\hatφ(q)‖ dq` — no integrability input is
needed, since every identity used is the unconditional Haar-measure substitution (the
"non-integrable function has integral zero" convention keeps both sides consistent).
-/

noncomputable section

open MeasureTheory Filter Metric
open scoped Real Topology BigOperators FourierTransform SchwartzMap

namespace Work.BoseFixB3.Scaling

local notation "ℝ3" => EuclideanSpace ℝ (Fin 3)

/-! ### Elementary helper: `kinFT` depends only on the pointwise values -/

private lemma kinFT_congr (f g : ℝ3 → ℂ) (h : ∀ z, f z = g z) (p : ℝ3) :
    Submission.BoseGases.kinFT f p = Submission.BoseGases.kinFT g p := by
  simp only [Submission.BoseGases.kinFT]
  apply integral_congr_ae
  filter_upwards with z
  rw [h z]

/-! ### Arithmetic: `((ℓ⁻¹)²)^M = ℓ^{-2M}` -/

private lemma inv_sq_pow (ℓ : ℝ) (M : ℕ) :
    ((ℓ⁻¹ : ℝ) ^ 2) ^ M = ℓ ^ (-(2 * (M : ℤ))) := by
  have h1 : ((ℓ⁻¹ : ℝ) ^ 2) ^ M = (ℓ ^ (2 * M))⁻¹ := by
    rw [inv_pow, inv_pow, pow_mul]
  rw [h1, ← zpow_natCast (ℓ : ℝ) (2 * M), ← zpow_neg]
  congr 1

/-! ### The main multiplier bound -/

private lemma multOn_bound_aux (M : ℕ) (ℓ : ℝ) (hℓ : 0 < ℓ) (x : ℝ3) :
    |Work.BoseFixB3.multOn (fun r => ((ℓ⁻¹) ^ 2 + r ^ 2) ^ M) ℓ
        (fun z : ℝ3 => Submission.BoseGases.chiU ℓ 0 z ^ 2) x|
      ≤ ((2 * π) ^ 3)⁻¹ * ((ℓ⁻¹) ^ 2) ^ M *
          ∫ q : ℝ3, (1 + ‖q‖ ^ 2) ^ M * ‖Submission.BoseGases.kinFT phiC q‖ := by
  have hc : (0 : ℝ) ≤ ((2 * π) ^ 3)⁻¹ := by positivity
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  let u : ℝ3 → ℂ := fun z =>
    (((Submission.BoseGases.acube ℓ).indicator
      (fun z : ℝ3 => Submission.BoseGases.chiU ℓ 0 z ^ 2) z : ℝ) : ℂ)
  let w : ℝ3 → ℂ := fun p => Submission.BoseGases.kinFT phiC (ℓ • p)
  let Gp : ℝ3 → ℂ := fun p => Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
    ((((ℓ⁻¹) ^ 2 + ‖p‖ ^ 2) ^ M : ℝ) : ℂ) * Submission.BoseGases.kinFT u p
  let H : ℝ3 → ℂ := fun p => Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
    ((((ℓ⁻¹) ^ 2 + ‖p‖ ^ 2) ^ M : ℝ) : ℂ) * ((ℓ ^ 3 : ℝ) • w p)
  let K : ℝ3 → ℝ := fun q =>
    (((ℓ⁻¹) ^ 2 + (ℓ⁻¹ * ‖q‖) ^ 2) ^ M) * ‖Submission.BoseGases.kinFT phiC q‖
  -- unfolding `multOn` into a Bochner integral whose integrand is `Gp`
  have hmult : |Work.BoseFixB3.multOn (fun r => ((ℓ⁻¹) ^ 2 + r ^ 2) ^ M) ℓ
      (fun z : ℝ3 => Submission.BoseGases.chiU ℓ 0 z ^ 2) x|
      = |(((((2 * π) ^ 3)⁻¹ : ℝ)) * (∫ p : ℝ3, Gp p)).re| := by
    rw [Work.BoseFixB3.multOn]
  -- pointwise identification of the `kinFT` factor
  have hGH : ∀ p : ℝ3, Gp p = H p := by
    intro p
    simp only [Gp, H]
    rw [kinFT_congr u (fun z : ℝ3 => (phi (ℓ⁻¹ • z) : ℂ))
      (fun z => by simp only [u]; rw [chiU_sq_indicator ℓ hℓ z]) p,
      kinFT_scaled_phi ℓ hℓ p]
  -- pointwise norm of the scaled integrand
  have hnorm : ∀ p : ℝ3, ‖H p‖ = ℓ ^ 3 * ((((ℓ⁻¹) ^ 2 + ‖p‖ ^ 2) ^ M) *
      ‖Submission.BoseGases.kinFT phiC (ℓ • p)‖) := by
    intro p
    have hcast : ‖((((ℓ⁻¹) ^ 2 + ‖p‖ ^ 2) ^ M : ℝ) : ℂ)‖ = ((ℓ⁻¹) ^ 2 + ‖p‖ ^ 2) ^ M :=
      Complex.norm_of_nonneg (by positivity)
    have hsl : ‖(ℓ ^ 3 : ℝ) • Submission.BoseGases.kinFT phiC (ℓ • p)‖
        = ℓ ^ 3 * ‖Submission.BoseGases.kinFT phiC (ℓ • p)‖ := by
      rw [norm_smul, Real.norm_of_nonneg (pow_nonneg hℓ.le 3)]
    simp only [H, w]
    rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul, hcast, hsl]
    ring
  -- the substitution `p ↦ ℓ⁻¹•p` at the level of the `q`-integral
  have hfold : ∀ p : ℝ3, (((ℓ⁻¹) ^ 2 + ‖p‖ ^ 2) ^ M) *
        ‖Submission.BoseGases.kinFT phiC (ℓ • p)‖ = K (ℓ • p) := by
    intro p
    have hℓp : ‖ℓ • p‖ = ℓ * ‖p‖ := by
      rw [norm_smul, Real.norm_of_nonneg hℓ.le]
    have h2 : ℓ⁻¹ * (ℓ * ‖p‖) = ‖p‖ := by field_simp
    simp only [K]
    rw [hℓp, h2]
  have hK : ∀ q : ℝ3, K q = ((ℓ⁻¹) ^ 2) ^ M *
      ((1 + ‖q‖ ^ 2) ^ M * ‖Submission.BoseGases.kinFT phiC q‖) := by
    intro q
    have hbase : (ℓ⁻¹) ^ 2 + (ℓ⁻¹ * ‖q‖) ^ 2 = (ℓ⁻¹) ^ 2 * (1 + ‖q‖ ^ 2) := by ring
    simp only [K]
    rw [hbase, mul_pow]
    ring
  -- the integral computation
  have hInt : (∫ p : ℝ3, ‖Gp p‖)
      = ((ℓ⁻¹) ^ 2) ^ M *
          ∫ q : ℝ3, (1 + ‖q‖ ^ 2) ^ M * ‖Submission.BoseGases.kinFT phiC q‖ := by
    have step1 : (∫ p : ℝ3, ‖Gp p‖) = ∫ p : ℝ3, ‖H p‖ := by
      apply integral_congr_ae
      filter_upwards with p
      rw [hGH p]
    have step2 : (∫ p : ℝ3, ‖H p‖)
        = ℓ ^ 3 * ∫ p : ℝ3, ((((ℓ⁻¹) ^ 2 + ‖p‖ ^ 2) ^ M) *
            ‖Submission.BoseGases.kinFT phiC (ℓ • p)‖) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with p
      rw [hnorm p]
    have step3 : (∫ p : ℝ3, ((((ℓ⁻¹) ^ 2 + ‖p‖ ^ 2) ^ M) *
            ‖Submission.BoseGases.kinFT phiC (ℓ • p)‖))
        = (ℓ ^ 3)⁻¹ * ∫ q : ℝ3, K q := by
      have hsub := MeasureTheory.Measure.integral_comp_smul_of_nonneg
        (hR := hℓ.le) volume K ℓ
      rw [show Module.finrank ℝ ℝ3 = 3 from by simp [EuclideanSpace]] at hsub
      rw [smul_eq_mul] at hsub
      rw [← hsub]
      apply integral_congr_ae
      filter_upwards with p
      rw [hfold p]
    have step4 : (∫ q : ℝ3, K q) = ((ℓ⁻¹) ^ 2) ^ M *
        ∫ q : ℝ3, (1 + ‖q‖ ^ 2) ^ M * ‖Submission.BoseGases.kinFT phiC q‖ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with q
      rw [hK q]
    calc (∫ p : ℝ3, ‖Gp p‖) = ∫ p : ℝ3, ‖H p‖ := step1
      _ = ℓ ^ 3 * ∫ p : ℝ3, ((((ℓ⁻¹) ^ 2 + ‖p‖ ^ 2) ^ M) *
            ‖Submission.BoseGases.kinFT phiC (ℓ • p)‖) := step2
      _ = ℓ ^ 3 * ((ℓ ^ 3)⁻¹ * ∫ q : ℝ3, K q) := by rw [step3]
      _ = ∫ q : ℝ3, K q := by
            rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 3 hℓne), one_mul]
      _ = ((ℓ⁻¹) ^ 2) ^ M *
            ∫ q : ℝ3, (1 + ‖q‖ ^ 2) ^ M * ‖Submission.BoseGases.kinFT phiC q‖ := step4
  calc |Work.BoseFixB3.multOn (fun r => ((ℓ⁻¹) ^ 2 + r ^ 2) ^ M) ℓ
        (fun z : ℝ3 => Submission.BoseGases.chiU ℓ 0 z ^ 2) x|
      = |(((((2 * π) ^ 3)⁻¹ : ℝ)) * (∫ p : ℝ3, Gp p)).re| := hmult
    _ ≤ ‖((((2 * π) ^ 3)⁻¹ : ℝ)) * (∫ p : ℝ3, Gp p)‖ := Complex.abs_re_le_norm _
    _ = ((2 * π) ^ 3)⁻¹ * ‖∫ p : ℝ3, Gp p‖ := by
        rw [Complex.norm_mul, Complex.norm_of_nonneg hc]
    _ ≤ ((2 * π) ^ 3)⁻¹ * ∫ p : ℝ3, ‖Gp p‖ :=
        mul_le_mul_of_nonneg_left (MeasureTheory.norm_integral_le_integral_norm Gp) hc
    _ = ((2 * π) ^ 3)⁻¹ * (((ℓ⁻¹) ^ 2) ^ M *
          ∫ q : ℝ3, (1 + ‖q‖ ^ 2) ^ M * ‖Submission.BoseGases.kinFT phiC q‖) := by
        rw [hInt]
    _ = ((2 * π) ^ 3)⁻¹ * ((ℓ⁻¹) ^ 2) ^ M *
          ∫ q : ℝ3, (1 + ‖q‖ ^ 2) ^ M * ‖Submission.BoseGases.kinFT phiC q‖ := by ring

/-- **FS ll. 1531–1535** (the estimate `|(ℓ⁻² − Δ)^M χ_Λ²| ≤ C ℓ^{-2M}`), in the corpus's
`p`-convention Fourier-multiplier form `multOn`: the multiplier with symbol
`r ↦ ((ℓ⁻¹)² + r²)^M` applied to the localisation window `χ_Λ² = (chiU ℓ 0)²` is bounded
by `C ℓ^{-2M}` uniformly in `ℓ > 0` and in the evaluation point. -/
theorem chiSq_mult_bound (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ℓ : ℝ), 0 < ℓ → ∀ x : EuclideanSpace ℝ (Fin 3),
      |Work.BoseFixB3.multOn (fun r => ((ℓ⁻¹) ^ 2 + r ^ 2) ^ M) ℓ
          (fun z => Submission.BoseGases.chiU ℓ 0 z ^ 2) x|
        ≤ C * ℓ ^ (-(2 * (M : ℤ))) := by
  set J : ℝ := ∫ q : EuclideanSpace ℝ (Fin 3),
      (1 + ‖q‖ ^ 2) ^ M * ‖Submission.BoseGases.kinFT phiC q‖ with hJ
  refine ⟨((2 * π) ^ 3)⁻¹ * max J 0, mul_nonneg (by positivity) (le_max_right _ _), ?_⟩
  intro ℓ hℓ x
  have h1 := multOn_bound_aux M ℓ hℓ x
  rw [← hJ, inv_sq_pow ℓ M] at h1
  have h2 : ((2 * π) ^ 3)⁻¹ * ℓ ^ (-(2 * (M : ℤ))) * J
      ≤ ((2 * π) ^ 3)⁻¹ * max J 0 * ℓ ^ (-(2 * (M : ℤ))) := by
    have hJJ : J ≤ max J 0 := le_max_left _ _
    have hnn : (0 : ℝ) ≤ ((2 * π) ^ 3)⁻¹ * ℓ ^ (-(2 * (M : ℤ))) :=
      mul_nonneg (by positivity) (zpow_nonneg hℓ.le _)
    calc ((2 * π) ^ 3)⁻¹ * ℓ ^ (-(2 * (M : ℤ))) * J
        ≤ ((2 * π) ^ 3)⁻¹ * ℓ ^ (-(2 * (M : ℤ))) * max J 0 :=
          mul_le_mul_of_nonneg_left hJJ hnn
      _ = ((2 * π) ^ 3)⁻¹ * max J 0 * ℓ ^ (-(2 * (M : ℤ))) := by ring
  linarith

end Work.BoseFixB3.Scaling
