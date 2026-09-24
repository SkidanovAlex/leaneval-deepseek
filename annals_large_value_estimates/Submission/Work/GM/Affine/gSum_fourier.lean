import Mathlib
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.cauchy_base
import Submission.Work.GM.Affine.plancherel_continuous
import Submission.Work.GM.Affine.fourier_piece

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.GM.Affine

noncomputable section


/-- Finite sums of compactly supported functions are compactly supported. -/
lemma hasCompactSupport_finset_sum_fun {ι : Type*} (s : Finset ι) (g : ι → ℝ → ℂ)
    (h : ∀ i ∈ s, HasCompactSupport (g i)) :
    HasCompactSupport (fun u : ℝ => ∑ i ∈ s, g i u) := by
  have hfun : (fun u : ℝ => ∑ i ∈ s, g i u) = ∑ i ∈ s, g i := by
    funext u
    simp only [Finset.sum_apply]
  rw [hfun]
  exact HasCompactSupport.finset_sum h

/-- Finite sums of integrable functions are integrable. -/
lemma integrable_finset_sum_fun {ι : Type*} (s : Finset ι) (g : ι → ℝ → ℂ)
    (h : ∀ i ∈ s, Integrable (g i)) :
    Integrable (fun u : ℝ => ∑ i ∈ s, g i u) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using integrable_zero (μ := volume) (f := fun _ : ℝ => (0 : ℂ))
  | insert a s ha ih =>
      have hfun : (fun u : ℝ => ∑ i ∈ insert a s, g i u) = fun u => g a u + ∑ i ∈ s, g i u := by
        funext u; rw [Finset.sum_insert ha]
      rw [hfun]
      exact Integrable.add (h a (Finset.mem_insert_self a s))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Pulling a constant out of the Fourier transform. -/
lemma fourier_const_mul (c : ℂ) (G : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun u => c * G u) ξ = c * 𝓕 G ξ := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  rw [mul_smul_comm]

/-- Linearity of the Fourier transform over a finite sum. -/
lemma fourier_finset_sum {ι : Type*} (s : Finset ι) (g : ι → ℝ → ℂ)
    (h : ∀ i ∈ s, Integrable (g i)) (ξ : ℝ) :
    𝓕 (fun u : ℝ => ∑ i ∈ s, g i u) ξ = ∑ i ∈ s, 𝓕 (g i) ξ := by
  rw [Real.fourier_real_eq]
  simp only [Finset.smul_sum]
  rw [integral_finsetSum s (fun i hi =>
    (by simpa only [Real.inner_apply] using
      (Real.fourierIntegral_convergent_iff (f := g i) ξ).2 (h i hi)))]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Real.fourier_real_eq]

/-- The complexification of GM's majorant `gSum` as a triple finite sum. -/
lemma gSum_complex_eq (K M₁ M₂ M₃ : ℝ) (f : ℝ → ℝ) :
    (fun u : ℝ => ((gSum K M₁ M₂ M₃ f u : ℝ) : ℂ))
      = fun u : ℝ => ∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3ext K M₃,
          ((psi1 K ((m₃ : ℝ) / M₃) * f (((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ)) : ℝ) : ℂ) := by
  funext u
  simp only [gSum]
  push_cast
  ring

/-- `gSum` (complexified) is continuous when `f` is. -/
lemma continuous_gSum_complex (K M₁ M₂ M₃ : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (fun u : ℝ => ((gSum K M₁ M₂ M₃ f u : ℝ) : ℂ)) := by
  rw [gSum_complex_eq]
  apply continuous_finsetSum
  intro m₁ _
  apply continuous_finsetSum
  intro m₂ _
  apply continuous_finsetSum
  intro m₃ _
  exact Complex.continuous_ofReal.comp (continuous_const.mul (hf.comp (by fun_prop)))

/-- `gSum` (complexified) has compact support when `f` does. -/
lemma hasCompactSupport_gSum_complex (K M₁ M₂ M₃ : ℝ) (hM₁ : 0 < M₁) {f : ℝ → ℝ}
    (hcs : HasCompactSupport f) :
    HasCompactSupport (fun u : ℝ => ((gSum K M₁ M₂ M₃ f u : ℝ) : ℂ)) := by
  have hsum : HasCompactSupport (fun u : ℝ => ∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂,
      ∑ m₃ ∈ R3ext K M₃,
        ((psi1 K ((m₃ : ℝ) / M₃) * f (((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ)) : ℝ) : ℂ)) := by
    apply hasCompactSupport_finset_sum_fun
    intro m₁ hm₁
    apply hasCompactSupport_finset_sum_fun
    intro m₂ hm₂
    apply hasCompactSupport_finset_sum_fun
    intro m₃ hm₃
    have h1 : (m₁ : ℝ) ≠ 0 := by
      have h : M₁ < |(m₁ : ℝ)| := (Finset.mem_filter.mp hm₁).2
      intro h0; rw [h0] at h; simp only [abs_zero] at h; linarith
    have h2 : (m₂ : ℝ) ≠ 0 := by
      have h : (1 : ℤ) ≤ m₂ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm₂).1).1
      have h2' : (1 : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast h
      intro h0; rw [h0] at h2'; linarith
    exact HasCompactSupport.comp_left
      (HasCompactSupport.mul_left (hasCompactSupport_affine hcs h1 h2))
      (g := fun x : ℝ => ((x : ℝ) : ℂ)) (by simp)
  convert hsum using 1
  funext u
  simp only [gSum]
  push_cast
  ring

/-- Fourier transform of a single `ψ₁`-weighted affine piece. -/
lemma fourier_gSum_piece (K M₃ : ℝ) {f : ℝ → ℝ} (m₁ m₂ m₃ : ℤ) (ξ : ℝ)
    (hm₁ : (m₁ : ℝ) ≠ 0) (hm₂ : 0 < (m₂ : ℝ)) :
    𝓕 (fun u : ℝ => ((psi1 K ((m₃ : ℝ) / M₃) *
        f (((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ)) : ℝ) : ℂ)) ξ
      = ((psi1 K ((m₃ : ℝ) / M₃) : ℝ) : ℂ) *
          ((((m₂ : ℝ) / |(m₁ : ℝ)| : ℝ) : ℂ) * Fhat f (ξ * (m₂ : ℝ) / (m₁ : ℝ)) *
            efun (ξ * (m₃ : ℝ) / (m₁ : ℝ))) := by
  have hsplit : (fun u : ℝ => ((psi1 K ((m₃ : ℝ) / M₃) *
        f (((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ)) : ℝ) : ℂ))
      = fun u : ℝ => ((psi1 K ((m₃ : ℝ) / M₃) : ℝ) : ℂ) *
          ((f (((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ)) : ℝ) : ℂ) := by
    funext u
    push_cast
    ring
  rw [hsplit, fourier_const_mul]
  rw [fourier_piece (c := (m₁ : ℝ)) (d := (m₃ : ℝ)) (e := (m₂ : ℝ)) hm₁ (ne_of_gt hm₂)]
  rw [abs_div, abs_of_pos hm₂]

/-- The pointwise computation of `ĝ` (equations (9.2)–(9.3) of GM §9). -/
lemma ghat_eq (K M₁ M₂ M₃ : ℝ) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) {f : ℝ → ℝ}
    (hf : Continuous f) (hcs : HasCompactSupport f) (ξ : ℝ) :
    ghat K M₁ M₂ M₃ f ξ =
      ∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂,
        ((((m₂ : ℝ) / |(m₁ : ℝ)| : ℝ) : ℂ) * Fhat f (ξ * (m₂ : ℝ) / (m₁ : ℝ)) *
          ∑ m₃ ∈ R3ext K M₃,
            ((psi1 K ((m₃ : ℝ) / M₃) : ℝ) : ℂ) * efun (ξ * (m₃ : ℝ) / (m₁ : ℝ))) := by
  have hm₁ne : ∀ m₁ ∈ R1 M₁, (m₁ : ℝ) ≠ 0 := by
    intro m₁ hm₁ h
    have h' : M₁ < |(m₁ : ℝ)| := (Finset.mem_filter.mp hm₁).2
    rw [h] at h'
    simp at h'
    linarith
  have hm₂pos : ∀ m₂ ∈ R2 M₂, 0 < (m₂ : ℝ) := by
    intro m₂ hm₂
    have h : (1 : ℤ) ≤ m₂ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm₂).1).1
    exact_mod_cast h
  have hipiece : ∀ m₁ ∈ R1 M₁, ∀ m₂ ∈ R2 M₂, ∀ m₃ ∈ R3ext K M₃,
      Integrable (fun u : ℝ => ((psi1 K ((m₃ : ℝ) / M₃) *
        f (((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ)) : ℝ) : ℂ)) := by
    intro m₁ hm₁ m₂ hm₂ m₃ hm₃
    have hcont : Continuous (fun u : ℝ => psi1 K ((m₃ : ℝ) / M₃) *
        f (((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ))) :=
      continuous_const.mul (hf.comp (by fun_prop))
    have hcs' : HasCompactSupport (fun u : ℝ => psi1 K ((m₃ : ℝ) / M₃) *
        f (((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ))) :=
      HasCompactSupport.mul_left
        (hasCompactSupport_affine hcs (hm₁ne m₁ hm₁) (ne_of_gt (hm₂pos m₂ hm₂)))
    exact (hcont.integrable_of_hasCompactSupport hcs').ofReal
  simp only [ghat]
  rw [gSum_complex_eq]
  rw [fourier_finset_sum (s := R1 M₁)
        (g := fun m₁ u => ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3ext K M₃,
          ((psi1 K ((m₃ : ℝ) / M₃) * f (((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ)) : ℝ) : ℂ))
        (fun m₁ hm₁ => integrable_finset_sum_fun _ _
          (fun m₂ hm₂ => integrable_finset_sum_fun _ _
            (fun m₃ hm₃ => hipiece m₁ hm₁ m₂ hm₂ m₃ hm₃))) ξ]
  refine Finset.sum_congr rfl (fun m₁ hm₁ => ?_)
  rw [fourier_finset_sum (s := R2 M₂)
        (g := fun m₂ u => ∑ m₃ ∈ R3ext K M₃,
          ((psi1 K ((m₃ : ℝ) / M₃) * f (((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ)) : ℝ) : ℂ))
        (fun m₂ hm₂ => integrable_finset_sum_fun _ _
          (fun m₃ hm₃ => hipiece m₁ hm₁ m₂ hm₂ m₃ hm₃)) ξ]
  refine Finset.sum_congr rfl (fun m₂ hm₂ => ?_)
  rw [fourier_finset_sum (s := R3ext K M₃)
        (g := fun m₃ u => ((psi1 K ((m₃ : ℝ) / M₃) *
          f (((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ)) : ℝ) : ℂ))
        (fun m₃ hm₃ => hipiece m₁ hm₁ m₂ hm₂ m₃ hm₃) ξ]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m₃ hm₃ => ?_)
  rw [fourier_gSum_piece K M₃ m₁ m₂ m₃ ξ (hm₁ne m₁ hm₁) (hm₂pos m₂ hm₂)]
  ring

/-- Plancherel for GM's majorant `g` together with the explicit formula for `ĝ` (the
Fourier-analytic core of GM Lemma 9.2). -/
theorem gSum_fourier {K M₁ M₂ M₃ : ℝ} (hK : 0 < K) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hM₃ : 0 < M₃) {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    (∫ u, (gSum K M₁ M₂ M₃ f u) ^ 2 = ∫ ξ, ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2) ∧
    (∀ ξ : ℝ, ghat K M₁ M₂ M₃ f ξ =
      ∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂,
        ((((m₂ : ℝ) / |(m₁ : ℝ)| : ℝ) : ℂ) * Fhat f (ξ * (m₂ : ℝ) / (m₁ : ℝ)) *
          ∑ m₃ ∈ R3ext K M₃, ((psi1 K ((m₃ : ℝ) / M₃) : ℝ) : ℂ) * efun (ξ * (m₃ : ℝ) / (m₁ : ℝ)))) := by
  have hcont := continuous_gSum_complex K M₁ M₂ M₃ hf
  have hcs' := hasCompactSupport_gSum_complex K M₁ M₂ M₃ hM₁ hcs
  refine ⟨?_, fun ξ => ghat_eq K M₁ M₂ M₃ hM₁ hM₂ hf hcs ξ⟩
  have hcongr : ∫ u, (gSum K M₁ M₂ M₃ f u) ^ 2
      = ∫ u, ‖((gSum K M₁ M₂ M₃ f u : ℝ) : ℂ)‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards with u
    rw [Complex.sq_norm, Complex.normSq_ofReal]
    ring
  rw [hcongr]
  exact plancherel_continuous (fun u : ℝ => ((gSum K M₁ M₂ M₃ f u : ℝ) : ℂ)) hcont hcs'

end

end Work.GM.Affine
