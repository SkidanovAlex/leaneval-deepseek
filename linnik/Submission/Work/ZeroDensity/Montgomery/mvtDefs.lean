import Mathlib
import Submission.Work.LinnikAreas.LargeSieve

/-!
# The spreading kernel for the family mean-value theorem `mvtFamilyT`

This file sets up the analytic device used to prove `Work.ZeroDensity.Montgomery.mvtFamilyT`,

`∑_{χ mod q} ∫_{-T}^{T} ‖∑_{n ≤ N} b n · χ(n) · n^{-(σ+it)}‖² dt ≤ C (qT + N) ∑_{n ≤ N} ‖b n‖² n^{-2σ}`,

namely the classical **spreading** (Fourier/Gallagher) argument.  Fix a smooth, even, compactly
supported bump `ρ ≥ 0` on `ℝ` with `∫ ρ = A > 0` (`mvtBump`, `mvtRho`).  Its Fourier transform
`ψ = 𝓕 ρ` (`mvtPsi`) satisfies `‖ψ 0‖ = A`, hence `‖ψ‖ ≥ C = A/2` on a symmetric neighbourhood
`[-E,E]` of the origin (`mvtC`, `mvtE`).  For `δ > 0` set `ρ_δ(y) = δ⁻¹ ρ(y/δ)` (`mvtRhoDeltaC`)
and `Θ_δ = ρ_δ ⋆ \overline{ρ_δ(-·)}` (`mvtTheta`).  Then `𝓕 Θ_δ(s) = ‖ψ (δ s)‖²`, so `Θ_δ` acts as a
*nonnegative* cutoff `≥ C²` on `|s| ≤ 1/δ`, while (unlike the sharp cutoff) it is **compactly
supported**, of width `2 δ · rOut` — and this is the source of the `N` in the final bound.
-/

open scoped FourierTransform
open MeasureTheory Filter
open scoped Topology

namespace Work.ZeroDensity.Montgomery

noncomputable section

/-- The fixed smooth bump on `ℝ` used as the spreading kernel: the default `ContDiffBump` centred
at `0` (smooth, equal to `1` on `[-1,1]`, supported in `[-2,2]`, values in `[0,1]`). -/
def mvtBump : ContDiffBump (0 : ℝ) := default

/-- The bump as a plain function `ℝ → ℝ`. -/
abbrev mvtRho : ℝ → ℝ := ⇑mvtBump

/-- The bump viewed as a complex-valued function. -/
abbrev mvtRhoC : ℝ → ℂ := fun x => (mvtRho x : ℂ)

lemma mvtRho_nonneg (x : ℝ) : 0 ≤ mvtRho x := mvtBump.nonneg
lemma mvtRho_le_one (x : ℝ) : mvtRho x ≤ 1 := mvtBump.le_one
lemma mvtRho_neg (x : ℝ) : mvtRho (-x) = mvtRho x := mvtBump.neg x
lemma mvtRho_continuous : Continuous mvtRho := mvtBump.continuous
lemma mvtRho_contDiff (n : ℕ∞) : ContDiff ℝ (↑n) mvtRho := mvtBump.contDiff (n := n)
lemma mvtRho_hasCompactSupport : HasCompactSupport mvtRho := mvtBump.hasCompactSupport
lemma mvtRho_integrable : Integrable mvtRho := mvtBump.integrable
lemma mvtRhoC_continuous : Continuous mvtRhoC := Complex.continuous_ofReal.comp mvtRho_continuous
lemma mvtRhoC_integrable : Integrable mvtRhoC := mvtRho_integrable.ofReal
lemma mvtRho_zero : mvtRho 0 = 1 := by
  simpa using mvtBump.one_of_mem_closedBall (c := 0) (x := 0)
    (by simpa [Metric.mem_closedBall] using mvtBump.rIn_pos.le)

lemma mvtRho_support_subset (x : ℝ) (hx : mvtRho x ≠ 0) : |x| ≤ mvtBump.rOut := by
  have h1 : x ∈ Function.support mvtBump := hx
  rw [ContDiffBump.support_eq, Metric.mem_ball, dist_zero_right] at h1
  exact le_of_lt h1

/-- `A = ∫ ρ > 0`. -/
def mvtA : ℝ := ∫ x, mvtRho x

lemma mvtA_pos : 0 < mvtA := mvtBump.integral_pos

/-- `C = A/2 > 0`, the lower bound for `‖𝓕ρ‖` near the origin. -/
def mvtC : ℝ := mvtA / 2

lemma mvtC_pos : 0 < mvtC := by
  rw [mvtC]; linarith [mvtA_pos]

/-- `ψ = 𝓕 ρ`. -/
def mvtPsi : ℝ → ℂ := 𝓕 mvtRhoC

lemma mvtPsi_continuous : Continuous mvtPsi := by
  have h := VectorFourier.fourierIntegral_continuous (E := ℂ) (e := Real.fourierChar)
      (μ := volume) (L := innerₗ ℝ) Real.continuous_fourierChar
      (by fun_prop) mvtRhoC_integrable
  simpa [mvtPsi, FourierTransform.fourier, VectorFourier.fourierIntegral] using h

lemma mvtPsi_zero : mvtPsi 0 = (mvtA : ℂ) := by
  have h : mvtPsi 0 = ∫ v, mvtRhoC v := by
    rw [mvtPsi, Real.fourier_eq]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    simp
  rw [h, show (∫ v, mvtRhoC v) = ((∫ v, mvtRho v : ℝ) : ℂ) from integral_ofReal, mvtA]

/-- There is `E ∈ (0,1]` with `‖ψ u‖ ≥ C` for `|u| ≤ E`. -/
lemma mvt_exists_E : ∃ E : ℝ, 0 < E ∧ E ≤ 1 ∧ ∀ u : ℝ, |u| ≤ E → mvtC ≤ ‖mvtPsi u‖ := by
  have hcont : Continuous fun u : ℝ => ‖mvtPsi u‖ := mvtPsi_continuous.norm
  have h0 : mvtC < ‖mvtPsi 0‖ := by
    rw [mvtPsi_zero]
    have : ‖(mvtA : ℂ)‖ = mvtA := by simp [abs_of_pos mvtA_pos]
    rw [this, mvtC]; linarith [mvtA_pos]
  have h2 : ∀ᶠ u in 𝓝 (0:ℝ), mvtC < ‖mvtPsi u‖ :=
    hcont.continuousAt.eventually (isOpen_Ioi.mem_nhds h0)
  rw [Metric.eventually_nhds_iff] at h2
  obtain ⟨ε, hε, hε'⟩ := h2
  refine ⟨min ε 1 / 2, by positivity, ?_, ?_⟩
  · have : min ε 1 ≤ 1 := min_le_right _ _
    linarith
  · intro u hu
    have hdist : dist u 0 < ε := by
      rw [Real.dist_eq, sub_zero]
      have h1 : min ε 1 / 2 < ε := by
        have := min_le_left ε 1
        linarith
      linarith
    exact le_of_lt (hε' hdist)

/-- The neighbourhood size `E` from `mvt_exists_E`. -/
def mvtE : ℝ := Classical.choose mvt_exists_E

lemma mvtE_pos : 0 < mvtE := (Classical.choose_spec mvt_exists_E).1

lemma mvtE_le_one : mvtE ≤ 1 := (Classical.choose_spec mvt_exists_E).2.1

lemma mvtE_bound (u : ℝ) (hu : |u| ≤ mvtE) : mvtC ≤ ‖mvtPsi u‖ :=
  (Classical.choose_spec mvt_exists_E).2.2 u hu

/-- `δ = E/S`. -/
def mvtDelta (S : ℝ) : ℝ := mvtE / S

lemma mvtDelta_pos {S : ℝ} (hS : 0 < S) : 0 < mvtDelta S := by
  rw [mvtDelta]; exact div_pos mvtE_pos hS

lemma mvtDelta_le_one {S : ℝ} (hS : 1 ≤ S) : mvtDelta S ≤ 1 := by
  rw [mvtDelta, div_le_one (by linarith)]
  linarith [mvtE_le_one]

/-- The rescaled bump `ρ_δ`, as a complex-valued function. -/
def mvtRhoDeltaC (S : ℝ) : ℝ → ℂ := fun y => ((mvtDelta S)⁻¹ : ℝ) * mvtRhoC (y / mvtDelta S)

lemma mvtRhoDeltaC_support (S : ℝ) (hS : 0 < S) {y : ℝ} (hy : mvtRhoDeltaC S y ≠ 0) :
    |y| ≤ mvtBump.rOut * mvtDelta S := by
  have hy'' : mvtRho (y / mvtDelta S) ≠ 0 := by
    have := hy
    simp only [mvtRhoDeltaC, mvtRhoC] at this
    intro h
    simp [h] at this
  have := mvtRho_support_subset (y / mvtDelta S) hy''
  rw [abs_div, abs_of_pos (mvtDelta_pos hS)] at this
  rwa [div_le_iff₀ (mvtDelta_pos hS)] at this

lemma mvtRhoDeltaC_continuous (S : ℝ) : Continuous (mvtRhoDeltaC S) :=
  continuous_const.mul (mvtRhoC_continuous.comp (continuous_id.div_const _))

lemma mvtRhoDeltaC_hasCompactSupport (S : ℝ) (hS : 0 < S) :
    HasCompactSupport (mvtRhoDeltaC S) := by
  rw [HasCompactSupport, tsupport]
  have hsub : Function.support (mvtRhoDeltaC S) ⊆
      Set.Icc (-(mvtBump.rOut * mvtDelta S)) (mvtBump.rOut * mvtDelta S) := by
    intro y hy
    have := mvtRhoDeltaC_support S hS hy
    rw [abs_le] at this
    exact this
  exact IsCompact.of_isClosed_subset isCompact_Icc isClosed_closure
    (closure_minimal hsub isClosed_Icc)

lemma mvtRhoDeltaC_integrable (S : ℝ) (hS : 0 < S) : Integrable (mvtRhoDeltaC S) :=
  (mvtRhoDeltaC_continuous S).integrable_of_hasCompactSupport (mvtRhoDeltaC_hasCompactSupport S hS)

/-- The spreading kernel `Θ_δ = ρ_δ ⋆ \overline{ρ_δ(-·)}`. -/
def mvtTheta (S : ℝ) : ℝ → ℂ :=
  convolution (mvtRhoDeltaC S) (fun y => star (mvtRhoDeltaC S (-y)))
    (ContinuousLinearMap.mul ℂ ℂ) volume

lemma mvtTheta_apply (S : ℝ) (x : ℝ) :
    mvtTheta S x = ∫ t, mvtRhoDeltaC S t * star (mvtRhoDeltaC S (-(x - t))) := by
  rw [mvtTheta, convolution_def]
  simp


lemma mvtRhoC_norm_le (t : ℝ) : ‖mvtRhoC t‖ ≤ 1 := by
  rw [mvtRhoC]
  have : ‖((mvtRho t : ℝ) : ℂ)‖ = |mvtRho t| := by simp
  rw [this, abs_of_nonneg (mvtRho_nonneg t)]
  exact mvtRho_le_one t

lemma mvtRhoDeltaC_norm_le (S : ℝ) (hS : 0 < S) (t : ℝ) :
    ‖mvtRhoDeltaC S t‖ ≤ (mvtDelta S)⁻¹ := by
  rw [mvtRhoDeltaC, norm_mul]
  have hc : ‖(((mvtDelta S)⁻¹ : ℝ) : ℂ)‖ = (mvtDelta S)⁻¹ := by
    have h1 : ‖(((mvtDelta S)⁻¹ : ℝ) : ℂ)‖ = |(mvtDelta S)⁻¹| := by simp
    rw [h1, abs_of_pos (inv_pos.mpr (mvtDelta_pos hS))]
  rw [hc]
  exact mul_le_of_le_one_right (le_of_lt (inv_pos.mpr (mvtDelta_pos hS))) (mvtRhoC_norm_le _)

lemma mvtRhoDeltaC_norm_eq (S : ℝ) (hS : 0 < S) (t : ℝ) :
    ‖mvtRhoDeltaC S t‖ = (mvtDelta S)⁻¹ * ‖mvtRhoC (t / mvtDelta S)‖ := by
  rw [mvtRhoDeltaC, norm_mul]
  have hc : ‖(((mvtDelta S)⁻¹ : ℝ) : ℂ)‖ = (mvtDelta S)⁻¹ := by
    have h1 : ‖(((mvtDelta S)⁻¹ : ℝ) : ℂ)‖ = |(mvtDelta S)⁻¹| := by simp
    rw [h1, abs_of_pos (inv_pos.mpr (mvtDelta_pos hS))]
  rw [hc]

lemma mvtRhoC_norm_eq (t : ℝ) : ‖mvtRhoC t‖ = mvtRho t := by
  rw [mvtRhoC]
  have : ‖((mvtRho t : ℝ) : ℂ)‖ = |mvtRho t| := by simp
  rw [this, abs_of_nonneg (mvtRho_nonneg t)]

lemma integral_norm_mvtRhoDeltaC (S : ℝ) (hS : 0 < S) :
    ∫ y, ‖mvtRhoDeltaC S y‖ = mvtA := by
  have hnorm : ∀ y : ℝ, ‖mvtRhoDeltaC S y‖
      = (mvtDelta S)⁻¹ * ‖mvtRhoC (y / mvtDelta S)‖ := fun y =>
    mvtRhoDeltaC_norm_eq S hS y
  simp only [hnorm]
  have hsc : ∫ a : ℝ, ‖mvtRhoC (a / mvtDelta S)‖ = mvtDelta S * mvtA := by
    rw [Measure.integral_comp_div (fun y => ‖mvtRhoC y‖) (mvtDelta S),
      abs_of_pos (mvtDelta_pos hS), smul_eq_mul]
    have : (∫ y, ‖mvtRhoC y‖) = mvtA := by
      simp_rw [mvtRhoC_norm_eq]
      rfl
    rw [this]
  rw [integral_const_mul, hsc]
  field_simp [(mvtDelta_pos hS).ne']

/-- `Θ_δ` is supported in `[-2 δ rOut, 2 δ rOut]`. -/
lemma mvtTheta_support (S : ℝ) (hS : 0 < S) {x : ℝ}
    (hx : 2 * mvtBump.rOut * mvtDelta S < |x|) : mvtTheta S x = 0 := by
  rw [mvtTheta_apply]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [Pi.zero_apply]
  rcases eq_or_ne (mvtRhoDeltaC S t) 0 with h | h
  · rw [h, zero_mul]
  rcases eq_or_ne (mvtRhoDeltaC S (-(x - t))) 0 with h' | h'
  · rw [star_eq_zero.mpr h', mul_zero]
  exfalso
  have h1 := mvtRhoDeltaC_support S hS h
  have h2 := mvtRhoDeltaC_support S hS h'
  rw [abs_neg] at h2
  have h3 : |x| ≤ |x - t| + |t| := by
    have := dist_triangle x t 0
    rwa [Real.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero] at this
  have h4 : |x| ≤ 2 * (mvtBump.rOut * mvtDelta S) := by
    calc |x| ≤ |x - t| + |t| := h3
      _ ≤ mvtBump.rOut * mvtDelta S + mvtBump.rOut * mvtDelta S := add_le_add h2 h1
      _ = 2 * (mvtBump.rOut * mvtDelta S) := by ring
  linarith [hx]

/-- `‖Θ_δ x‖ ≤ A · S / E` for all `x`. -/
lemma mvtTheta_bound (S : ℝ) (hS : 0 < S) (x : ℝ) :
    ‖mvtTheta S x‖ ≤ mvtA * S / mvtE := by
  rw [mvtTheta_apply]
  have hint : Integrable fun t => (mvtDelta S)⁻¹ * ‖mvtRhoDeltaC S (t - x)‖ :=
    ((mvtRhoDeltaC_integrable S hS).comp_sub_right x).norm.const_mul _
  calc ‖∫ t, mvtRhoDeltaC S t * star (mvtRhoDeltaC S (-(x - t)))‖
      ≤ ∫ t, ‖mvtRhoDeltaC S t * star (mvtRhoDeltaC S (-(x - t)))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t, (mvtDelta S)⁻¹ * ‖mvtRhoDeltaC S (t - x)‖ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _) hint
          (Filter.Eventually.of_forall fun t => ?_)
        have hsub : -(x - t) = t - x := by ring
        change ‖mvtRhoDeltaC S t * star (mvtRhoDeltaC S (-(x - t)))‖
          ≤ (mvtDelta S)⁻¹ * ‖mvtRhoDeltaC S (t - x)‖
        rw [norm_mul, norm_star, hsub]
        exact mul_le_mul_of_nonneg_right (mvtRhoDeltaC_norm_le S hS t) (norm_nonneg _)
    _ = (mvtDelta S)⁻¹ * ∫ t, ‖mvtRhoDeltaC S (t - x)‖ := integral_const_mul _ _
    _ = (mvtDelta S)⁻¹ * ∫ t, ‖mvtRhoDeltaC S t‖ := by
        rw [integral_sub_right_eq_self (fun y => ‖mvtRhoDeltaC S y‖) x]
    _ = (mvtDelta S)⁻¹ * mvtA := by rw [integral_norm_mvtRhoDeltaC S hS]
    _ = mvtA * S / mvtE := by rw [mvtDelta]; field_simp


/-- `K` for the counting: `Real.exp D - Real.exp (-D) ≤ mvtK δ` when `D = 2 rOut δ` and `0 ≤ δ ≤ 1`. -/
def mvtK : ℝ := 4 * mvtBump.rOut * Real.exp (2 * mvtBump.rOut)

/-- The constant of `mvtFamilyT`. -/
def mvtCTOT : ℝ :=
  max (8 * Real.pi)
    (2 * Real.pi * (mvtC ^ 2)⁻¹ * max (mvtA / mvtE) (2 * Real.pi * mvtA * mvtK))

/-- The weighted coefficient `c n = b n * n^{-σ}`. -/
def mvtWeight (b : ℕ → ℂ) (σ : ℝ) (n : ℕ) : ℂ := b n * (n : ℂ) ^ (-(σ : ℂ))

lemma mvtNorm_sq_cpow (n : ℕ) (hn : 1 ≤ n) (σ : ℝ) :
    ‖(n : ℂ) ^ (-(σ : ℂ))‖ ^ 2 = (n : ℝ) ^ (-(2 * σ)) := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < n)]
  simp only [Complex.neg_re, Complex.ofReal_re]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ n)]
  congr 1
  ring

lemma mvtWeight_norm_sq (b : ℕ → ℂ) (σ : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ‖mvtWeight b σ n‖ ^ 2 = ‖b n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ)) := by
  rw [mvtWeight, norm_mul, mul_pow, mvtNorm_sq_cpow n hn σ]

/-- The Dirichlet polynomial `∑_{n ≤ N} c n · χ(n) · e^{-2π i s log n}`. -/
def mvtPoly (q : ℕ) (c : ℕ → ℂ) (N : ℕ) (χ : DirichletCharacter ℂ q) (s : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, c n * χ (n : ZMod q)
    * Complex.exp (-(2 * Real.pi * Complex.I * (s : ℂ) * (Real.log (n : ℝ) : ℂ)))

end

end Work.ZeroDensity.Montgomery
