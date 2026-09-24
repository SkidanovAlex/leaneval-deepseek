import Mathlib
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.region_II_defs
import Submission.Work.GM.Affine.WinMass_basic
import Submission.Work.GM.Affine.sample_sum_bound

/-!
# GM §9: the sampling bound for the window mass `WinMass`

`WinMass f M₂ M₃ = Σ'_ℓ ∫_{|τ|≤2} ‖H_ℓ(τ)‖² dτ`, where
`H_ℓ(τ) = Hfun f M₂ M₃ ℓ τ = Σ_{m₂ ∈ R2 M₂} m₂ f̂(m₂(ℓ + τ/M₃)) = Bsum f M₂ (ℓ + τ/M₃)`
is the `m₂`-sum of dilates of `f̂`.

This file proves that the window mass is bounded by a constant multiple of `(1 + M₂)` times the
`L²`-mass of the profile `Hprof f M₂ u = Σ_{m₂ ∈ R2 M₂} f (u/m₂)`, *uniformly in `M₃`*:

`WinMass f M₂ M₃ ≤ (16 C₀ + 8) (1 + M₂) ∫ (Hprof f M₂)²`.

The point of the bound is the classical **sampling** (periodisation) inequality: the profile
`H = Hprof f M₂` is supported in the *fixed* interval `[-2C₀M₂, 2C₀M₂]`, independently of `M₃`,
so the values `Fhat H (k + α)` of its Fourier transform on any shifted lattice `ℤ + α` carry only
`O(1 + M₂) ∫ H²` of mass (GM §9, proved as `sample_sum_bound`):

`Σ_{k ∈ s} ‖Fhat H (k+α)‖² ≤ (4C₀M₂ + 2) ∫ H²`.

Indeed `H_ℓ(τ) = Fhat H (ℓ + τ/M₃)`, so for every fixed `τ` the sum over `ℓ` of `‖H_ℓ(τ)‖²` is a
sampled Fourier mass, while `WinMass` integrates these over `|τ| ≤ 2`.  Summing the integrals by
`Real.tsum_le_of_sum_le` gives `WinMass ≤ 4 (4C₀M₂ + 2) ∫ H²`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- The profile `Hprof f M₂` vanishes off `[-2C₀M₂, 2C₀M₂]` when `f` is supported in
`[1/C₀, C₀]` (and `C₀ ≥ 1`, `M₂ ≥ 0`): each `m₂ ∈ R2 M₂` satisfies `0 < m₂ ≤ 2M₂`, so
`|u| ≤ C₀ m₂ ≤ 2C₀M₂` on the support of the summand `u ↦ f (u/m₂)`. -/
lemma Hprof_support_bound {C₀ M₂ : ℝ} (_hC₀ : 1 ≤ C₀) (_hM₂ : 0 ≤ M₂) {f : ℝ → ℝ}
    (hsup : SuppHyp C₀ f) : ∀ y : ℝ, 2 * C₀ * M₂ < |y| → Hprof f M₂ y = 0 := by
  intro y hy
  by_contra hne
  rw [Hprof] at hne
  obtain ⟨m₂, hm₂, hfm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hm₂pos : (0 : ℝ) < (m₂ : ℝ) := R2_pos' hm₂
  have hm₂le : (m₂ : ℝ) ≤ 2 * M₂ := R2_le' hm₂
  have hmem : y / (m₂ : ℝ) ∈ Set.Icc (1 / C₀) C₀ := hsup _ hfm
  rw [Set.mem_Icc] at hmem
  have hypos : 0 < y := by
    have h : (0 : ℝ) < y / (m₂ : ℝ) := lt_of_lt_of_le (by positivity) hmem.1
    have := mul_pos h hm₂pos
    rwa [div_mul_cancel₀ y (ne_of_gt hm₂pos)] at this
  have h2 : y = (y / (m₂ : ℝ)) * (m₂ : ℝ) := (div_mul_cancel₀ y (ne_of_gt hm₂pos)).symm
  have h3 : y ≤ C₀ * (2 * M₂) := by
    rw [h2]
    calc (y / (m₂ : ℝ)) * (m₂ : ℝ) ≤ C₀ * (m₂ : ℝ) :=
          mul_le_mul_of_nonneg_right hmem.2 hm₂pos.le
      _ ≤ C₀ * (2 * M₂) := mul_le_mul_of_nonneg_left hm₂le (by linarith)
  rw [abs_of_pos hypos] at hy
  nlinarith [h3, hy]

/-- `Hfun f M₂ M₃ ℓ τ` is the Fourier transform of the profile `Hprof f M₂` at the frequency
`ℓ + τ/M₃`; this is the identification that turns the `ℓ`-sum of window masses into a sampled
Fourier mass. -/
lemma Hfun_eq_integral {C₀ : ℝ} (hC₀ : 1 ≤ C₀) {M₂ M₃ : ℝ} (hM₂ : 0 < M₂) {f : ℝ → ℝ}
    (hf : Continuous f) (hsup : SuppHyp C₀ f) (ℓ : ℤ) (τ : ℝ) :
    Hfun f M₂ M₃ ℓ τ
      = ∫ u : ℝ, efun (-(u * ((ℓ : ℝ) + τ / M₃))) * ((Hprof f M₂ u : ℝ) : ℂ) := by
  rw [Hfun_eq_Bsum, Bsum_eq_Fhat_Hprof hf hsup hC₀ hM₂, Fhat_eq_integral']
  exact integral_congr_ae (Filter.Eventually.of_forall (fun u => mul_comm _ _))

/-- **Sampling bound for the window mass.** For `f` continuous, compactly supported in
`[1/C₀, C₀]` (`C₀ ≥ 1`) and any `M₂, M₃ > 0`,

`WinMass f M₂ M₃ ≤ (16C₀ + 8) (1 + M₂) ∫ (Hprof f M₂)²`,

with a constant independent of `M₃`. -/
theorem winmass_sampling {C₀ : ℝ} (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ M₂ M₃ : ℝ, 0 < M₂ → 0 < M₃ → ∀ f : ℝ → ℝ, Continuous f →
      HasCompactSupport f → SuppHyp C₀ f →
      WinMass f M₂ M₃ ≤ C * (1 + M₂) * ∫ u, (∑ m₂ ∈ R2 M₂, f (u / (m₂ : ℝ))) ^ 2 := by
  refine ⟨16 * C₀ + 8, by linarith, ?_⟩
  intro M₂ M₃ hM₂ hM₃ f hf hcs hsup
  -- The sampled Fourier mass of the profile bounds every finite `ℓ`-sum of window masses.
  have hbound : ∀ (s : Finset ℤ) (τ : ℝ), ∑ ℓ ∈ s, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2
      ≤ (2 * (2 * C₀ * M₂) + 2) * ∫ u : ℝ, ‖((Hprof f M₂ u : ℝ) : ℂ)‖ ^ 2 := by
    intro s τ
    have hHcont : Continuous (fun u : ℝ => ((Hprof f M₂ u : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (Hprof_continuous hf M₂)
    have hR0 : 0 ≤ 2 * C₀ * M₂ := by positivity
    have hHsupp : ∀ y : ℝ, 2 * C₀ * M₂ < |y| → ((Hprof f M₂ y : ℝ) : ℂ) = 0 := by
      intro y hy
      rw [Hprof_support_bound hC₀ hM₂.le hsup y hy, Complex.ofReal_zero]
    have key : (∑ ℓ ∈ s, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2)
        = ∑ ℓ ∈ s,
            ‖∫ u : ℝ, efun (-(u * ((ℓ : ℝ) + τ / M₃))) * ((Hprof f M₂ u : ℝ) : ℂ)‖ ^ 2 :=
      Finset.sum_congr rfl (fun ℓ _ => by rw [Hfun_eq_integral hC₀ hM₂ hf hsup ℓ τ])
    rw [key]
    exact sample_sum_bound hHcont hR0 hHsupp (τ / M₃) s
  -- `Fhat f` is continuous, so each window integrand is continuous and hence integrable.
  have hFc : Continuous (Fhat f) := by
    unfold Fhat
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (hf.integrable_of_hasCompactSupport hcs).ofReal
  have hcont : ∀ ℓ : ℤ, Continuous (fun τ : ℝ => ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2) := by
    intro ℓ
    unfold Hfun
    refine Continuous.norm ?_ |>.pow 2
    refine continuous_finsetSum _ (fun m₂ _ => ?_)
    refine Continuous.mul continuous_const ?_
    exact hFc.comp (continuous_const.mul (continuous_const.add (continuous_id.div_const _)))
  have hint : ∀ ℓ : ℤ, Integrable (fun τ : ℝ => ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2)
      (volume.restrict (Set.Icc (-2 : ℝ) 2)) := fun ℓ =>
    ((hcont ℓ).continuousOn).integrableOn_compact isCompact_Icc
  have hconst : Integrable
      (fun _ : ℝ => (2 * (2 * C₀ * M₂) + 2) * ∫ u : ℝ, ‖((Hprof f M₂ u : ℝ) : ℂ)‖ ^ 2)
      (volume.restrict (Set.Icc (-2 : ℝ) 2)) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hconstval : ∫ τ in Set.Icc (-2 : ℝ) 2,
        ((2 * (2 * C₀ * M₂) + 2) * ∫ u : ℝ, ‖((Hprof f M₂ u : ℝ) : ℂ)‖ ^ 2)
      = ((2 * (2 * C₀ * M₂) + 2) * ∫ u : ℝ, ‖((Hprof f M₂ u : ℝ) : ℂ)‖ ^ 2) * 4 := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Icc]
    norm_num
    ring
  -- Sum the `ℓ`-terms under the integral and compare with the constant bound.
  have hstep : ∀ s : Finset ℤ,
      (∑ ℓ ∈ s, ∫ τ in Set.Icc (-2 : ℝ) 2, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2)
        ≤ ((2 * (2 * C₀ * M₂) + 2) * ∫ u : ℝ, ‖((Hprof f M₂ u : ℝ) : ℂ)‖ ^ 2) * 4 := by
    intro s
    have hlin : (∑ ℓ ∈ s, ∫ τ in Set.Icc (-2 : ℝ) 2, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2)
        = ∫ τ in Set.Icc (-2 : ℝ) 2, ∑ ℓ ∈ s, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 :=
      (MeasureTheory.integral_finsetSum s (fun i _ => hint i)).symm
    rw [hlin]
    calc ∫ τ in Set.Icc (-2 : ℝ) 2, ∑ ℓ ∈ s, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2
        ≤ ∫ τ in Set.Icc (-2 : ℝ) 2,
            ((2 * (2 * C₀ * M₂) + 2) * ∫ u : ℝ, ‖((Hprof f M₂ u : ℝ) : ℂ)‖ ^ 2) := by
          refine MeasureTheory.integral_mono_of_nonneg ?_ hconst ?_
          · filter_upwards with x
            exact Finset.sum_nonneg (fun i _ => by positivity)
          · filter_upwards with x
            exact hbound s x
      _ = ((2 * (2 * C₀ * M₂) + 2) * ∫ u : ℝ, ‖((Hprof f M₂ u : ℝ) : ℂ)‖ ^ 2) * 4 :=
          hconstval
  have hnn : ∀ ℓ : ℤ, 0 ≤ ∫ τ in Set.Icc (-2 : ℝ) 2, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 := by
    intro ℓ
    exact integral_nonneg (fun τ => by positivity)
  have hW := Real.tsum_le_of_sum_le hnn hstep
  -- Turn the norm into the square of the (real) profile, and absorb the constants.
  have hint_eq : (∫ u : ℝ, ‖((Hprof f M₂ u : ℝ) : ℂ)‖ ^ 2) = ∫ u : ℝ, (Hprof f M₂ u) ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall (fun u => norm_ofReal_sq _))
  have hA : 0 ≤ ∫ u : ℝ, (Hprof f M₂ u) ^ 2 := integral_nonneg (fun u => sq_nonneg _)
  have hfin : ((2 * (2 * C₀ * M₂) + 2) * (∫ u : ℝ, (Hprof f M₂ u) ^ 2)) * 4
      ≤ (16 * C₀ + 8) * (1 + M₂) * ∫ u : ℝ, (Hprof f M₂ u) ^ 2 := by
    have h1 : ((2 * (2 * C₀ * M₂) + 2) * (∫ u : ℝ, (Hprof f M₂ u) ^ 2)) * 4
        = (16 * C₀ * M₂ + 8) * (∫ u : ℝ, (Hprof f M₂ u) ^ 2) := by ring
    rw [h1]
    have h2 : (16 * C₀ * M₂ + 8) ≤ (16 * C₀ + 8) * (1 + M₂) := by nlinarith [hM₂]
    calc (16 * C₀ * M₂ + 8) * (∫ u : ℝ, (Hprof f M₂ u) ^ 2)
        ≤ ((16 * C₀ + 8) * (1 + M₂)) * (∫ u : ℝ, (Hprof f M₂ u) ^ 2) :=
          mul_le_mul_of_nonneg_right h2 hA
      _ = (16 * C₀ + 8) * (1 + M₂) * ∫ u : ℝ, (Hprof f M₂ u) ^ 2 := by ring
  calc WinMass f M₂ M₃
      ≤ ((2 * (2 * C₀ * M₂) + 2) * ∫ u : ℝ, ‖((Hprof f M₂ u : ℝ) : ℂ)‖ ^ 2) * 4 := hW
    _ = ((2 * (2 * C₀ * M₂) + 2) * (∫ u : ℝ, (Hprof f M₂ u) ^ 2)) * 4 := by rw [hint_eq]
    _ ≤ (16 * C₀ + 8) * (1 + M₂) * ∫ u : ℝ, (Hprof f M₂ u) ^ 2 := hfin
    _ = (16 * C₀ + 8) * (1 + M₂) * ∫ u, (∑ m₂ ∈ R2 M₂, f (u / (m₂ : ℝ))) ^ 2 := rfl

end

end Work.GM.Affine
