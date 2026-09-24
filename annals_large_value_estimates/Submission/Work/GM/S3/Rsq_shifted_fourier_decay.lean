import Mathlib
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.hhat_defs
import Submission.Work.GM.S3.fourier_decay_explicit
import Submission.Work.GM.S3.term_contDiff_hasCompactSupport
import Submission.Work.GM.S3.Rsq_eq_sum_phi
import Submission.Work.GM.S3.term_fourierTransform_decay

/-!
# Fourier decay at rate `T` of a bump times `‖R‖²`, with the bump shifted

GM's observation that `‖R(u)‖² = Σ_{t,t'∈W} u^{i(t-t')}` is a sum of `|W|²` oscillatory
exponentials, whose frequencies `t - t'` are bounded by `2T` when `W ⊆ [-T,T]`.  Integrating by
parts `j` times against a fixed smooth bump therefore costs `(1+T)^j`, *not* the smoothing scale
of the bump.

The proof is assembled from the single-term estimates proved in the sibling files:

* `Work.GM.S3.term_fourierTransform_decay` -- Fourier decay of one term
  `u ↦ ψ₁(u+w) ψ₂(u) u^{iτ}` at rate `(1+|τ|)^j`;
* `Work.GM.S3.term_contDiff_hasCompactSupport` -- that term is `C^∞` with compact support;
* `Work.GM.S3.Rsq_eq_sum_phi` -- the pointwise expansion `‖R(u)‖² = Σ_{t,t'} u^{i(t-t')}` for
  `u > 0`;

together with the additivity of the Fourier transform over finite sums
(`rsq_fourier_finset_sum`, from `MeasureTheory.integral_finsetSum`) and the observation that the
expanded function vanishes identically for `u ≤ 0` (where `ψ₂` does).
-/



namespace Work.GM.S3

open Complex Finset MeasureTheory
open scoped BigOperators FourierTransform

theorem rsq_integrable_finset_sum_fun {ι : Type*} (s : Finset ι) (g : ι → ℝ → ℂ)
    (hg : ∀ i ∈ s, Integrable (g i)) :
    Integrable (fun u : ℝ => ∑ i ∈ s, g i u) := by
  have h : Integrable (∑ i ∈ s, g i) volume :=
    Finset.sum_induction g (p := fun (G : ℝ → ℂ) => Integrable G volume)
      (fun a b ha hb => ha.add hb) (by simp) hg
  rwa [show (fun u : ℝ => ∑ i ∈ s, g i u) = (∑ i ∈ s, g i) by
    funext u; rw [Finset.sum_apply]]

theorem rsq_integrable_phase_mul (ξ : ℝ) {g : ℝ → ℂ} (hg : Integrable g volume) :
    Integrable (fun v : ℝ => cexp (↑(-2 * Real.pi * inner ℝ v ξ) * I) * g v) volume := by
  refine Integrable.bdd_mul (f := fun v : ℝ => cexp (↑(-2 * Real.pi * inner ℝ v ξ) * I))
    (g := g) (c := 1) hg ?_ ?_
  · exact (by fun_prop : Continuous fun v : ℝ => cexp (↑(-2 * Real.pi * inner ℝ v ξ) * I)).aestronglyMeasurable
  · filter_upwards with v
    have hz : ((((-2 * Real.pi * inner ℝ v ξ : ℝ)) : ℂ) * Complex.I).re = 0 := by
      rw [Complex.mul_I_re]; simp
    rw [Complex.norm_exp, hz, Real.exp_zero]

theorem rsq_fourier_finset_sum {ι : Type*} (s : Finset ι) (g : ι → ℝ → ℂ)
    (hg : ∀ i ∈ s, Integrable (g i) volume) :
    𝓕 (fun u : ℝ => ∑ i ∈ s, g i u) = ∑ i ∈ s, 𝓕 (g i) := by
  funext ξ
  rw [Finset.sum_apply, Real.fourier_eq']
  have hpt : ∀ v : ℝ, cexp (↑(-2 * Real.pi * inner ℝ v ξ) * I) • (∑ i ∈ s, g i v)
      = ∑ i ∈ s, cexp (↑(-2 * Real.pi * inner ℝ v ξ) * I) * g i v := by
    intro v
    rw [smul_eq_mul, Finset.mul_sum]
  simp_rw [hpt]
  have hsum := MeasureTheory.integral_finsetSum (μ := volume) (G := ℂ) (s := s)
      (f := fun i v => cexp (↑(-2 * Real.pi * inner ℝ v ξ) * I) * g i v)
      (fun i hi => rsq_integrable_phase_mul ξ (hg i hi))
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Real.fourier_eq']
  simp only [smul_eq_mul]

theorem Rsq_shifted_fourier_decay (ψ₁ ψ₂ : ℝ → ℝ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀)
    (h₁ : Work.GM.S3.IsBumpAtOne ψ₁ C₀) (h₂ : Work.GM.S3.IsBumpAtOne ψ₂ C₀) :
    ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
      ∀ (W : Finset ℝ) (T w : ℝ), 1 ≤ T → (∀ t ∈ W, |t| ≤ T) → ∀ (j : ℕ) (ξ : ℝ), T < |ξ| →
        ‖FourierTransform.fourier
            (fun u : ℝ => ((ψ₁ (u + w) * ψ₂ u * ‖Submission.GM.Rfun W u‖ ^ 2 : ℝ) : ℂ)) ξ‖
          ≤ K j * (W.card : ℝ) ^ 2 * (1 + T) ^ j / |ξ| ^ j := by
  obtain ⟨K, hK0, hK⟩ := term_fourierTransform_decay ψ₁ ψ₂ C₀ hC₀ h₁ h₂
  refine ⟨fun j => 2 ^ j * K j, fun j => by have h := hK0 j; positivity, ?_⟩
  intro W T w hT hWt j ξ hξ
  have hξpos : 0 < |ξ| := by linarith [abs_nonneg ξ]
  have hξ0 : ξ ≠ 0 := abs_pos.mp hξpos
  -- ψ₂ vanishes off its support
  have hψ₂zero : ∀ u : ℝ, u ∉ Set.Icc (1 / C₀) C₀ → ψ₂ u = 0 := by
    intro u hu
    by_contra h
    exact hu (h₂.2.2.1 u h)
  have hC₀pos : 0 < C₀ := by linarith
  -- each term is integrable
  have hterm_int : ∀ τ : ℝ,
      Integrable (fun u : ℝ => ((ψ₁ (u + w) * ψ₂ u : ℝ) : ℂ) * phi τ u) volume := fun τ =>
    ((term_contDiff_hasCompactSupport ψ₁ ψ₂ C₀ hC₀ h₁ h₂ w τ).1.continuous).integrable_of_hasCompactSupport
      (term_contDiff_hasCompactSupport ψ₁ ψ₂ C₀ hC₀ h₁ h₂ w τ).2
  -- pointwise expansion of the target function
  have hφ : (fun u : ℝ => ((ψ₁ (u + w) * ψ₂ u * ‖Submission.GM.Rfun W u‖ ^ 2 : ℝ) : ℂ))
      = fun u : ℝ => ∑ t ∈ W, ∑ t' ∈ W, ((ψ₁ (u + w) * ψ₂ u : ℝ) : ℂ) * phi (t - t') u := by
    funext u
    by_cases hu : 0 < u
    · have h1 : ((ψ₁ (u + w) * ψ₂ u * ‖Submission.GM.Rfun W u‖ ^ 2 : ℝ) : ℂ)
          = ((ψ₁ (u + w) * ψ₂ u : ℝ) : ℂ) * ((‖Submission.GM.Rfun W u‖ ^ 2 : ℝ) : ℂ) := by
        push_cast; ring
      rw [h1, Rsq_eq_sum_phi W hu, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [Finset.mul_sum]
    · have hsupp : u ∉ Set.Icc (1 / C₀) C₀ := by
        intro hmem
        have : (0:ℝ) < 1 / C₀ := one_div_pos.mpr hC₀pos
        linarith [hmem.1]
      have h0 : ψ₂ u = 0 := hψ₂zero u hsupp
      simp [h0]
  -- Fourier transform of the finite sum
  have hF := rsq_fourier_finset_sum W
      (fun t => fun u => ∑ t' ∈ W, ((ψ₁ (u + w) * ψ₂ u : ℝ) : ℂ) * phi (t - t') u)
      (fun t ht => rsq_integrable_finset_sum_fun W
        (fun t' => fun u => ((ψ₁ (u + w) * ψ₂ u : ℝ) : ℂ) * phi (t - t') u)
        (fun t' ht' => hterm_int _))
  have hF2 : ∀ t : ℝ, FourierTransform.fourier
      (fun u : ℝ => ∑ t' ∈ W, ((ψ₁ (u + w) * ψ₂ u : ℝ) : ℂ) * phi (t - t') u)
      = ∑ t' ∈ W, FourierTransform.fourier
          (fun u : ℝ => ((ψ₁ (u + w) * ψ₂ u : ℝ) : ℂ) * phi (t - t') u) := fun t =>
    rsq_fourier_finset_sum W (fun t' => fun u => ((ψ₁ (u + w) * ψ₂ u : ℝ) : ℂ) * phi (t - t') u)
      (fun t' ht' => hterm_int _)
  rw [hφ, hF]
  simp only [hF2, Finset.sum_apply]
  calc ‖∑ t ∈ W, ∑ t' ∈ W, FourierTransform.fourier
            (fun u : ℝ => ((ψ₁ (u + w) * ψ₂ u : ℝ) : ℂ) * phi (t - t') u) ξ‖
      ≤ ∑ t ∈ W, ∑ t' ∈ W, ‖FourierTransform.fourier
            (fun u : ℝ => ((ψ₁ (u + w) * ψ₂ u : ℝ) : ℂ) * phi (t - t') u) ξ‖ := by
        refine (norm_sum_le _ _).trans ?_
        exact Finset.sum_le_sum fun t ht => norm_sum_le _ _
    _ ≤ ∑ t ∈ W, ∑ t' ∈ W, K j * (2 * (1 + T)) ^ j / |ξ| ^ j := by
        refine Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun t' ht' => ?_
        refine (hK w (t - t') ξ j hξ0).trans ?_
        have h4 : (1 + |t - t'|) ^ j ≤ (2 * (1 + T)) ^ j := by
          have habs : |t - t'| ≤ 2 * T := by
            have h3 : |t - t'| ≤ |t| + |t'| := by
              simpa [sub_eq_add_neg] using abs_add_le t (-t')
            linarith [hWt t ht, hWt t' ht']
          exact pow_le_pow_left₀ (by positivity) (by linarith) j
        have hden : 0 < |ξ| ^ j := pow_pos hξpos j
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h4 (hK0 j)) hden.le
    _ = (W.card : ℝ) * (W.card : ℝ) * (K j * (2 * (1 + T)) ^ j / |ξ| ^ j) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
    _ = 2 ^ j * K j * (W.card : ℝ) ^ 2 * (1 + T) ^ j / |ξ| ^ j := by
        rw [mul_pow]
        ring

end Work.GM.S3
