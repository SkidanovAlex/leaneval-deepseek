/-
# The density of the complex Gaussians in the radial Schwartz space

Given `y > 0`, the functions `x ↦ exp (π i τ ‖x‖²)` with `Im τ = y` span a dense
subspace of the radial Schwartz functions on `R^n`.  Consequently a continuous linear
functional on the Schwartz space which vanishes on all these Gaussians vanishes on every
radial Schwartz function.

The proof follows the plan of Lemma 3.3 in the CKMRV paper:

* a functional vanishing on the Gaussians vanishes on `x ↦ exp (-π y ‖x‖²) h (‖x‖²)` for
  every compactly supported smooth `h` (Fourier inversion plus Riemann sums);
* a radial Schwartz function `f` equals `x ↦ exp (-π y ‖x‖²) Ξ (‖x‖²)` where
  `Ξ = exp (π y ·) ∘ profile f` is smooth on `[0,∞)` with a weighted rapid decay;
* such a `Ξ` is approximated, in the weighted seminorms that control the composite
  `x ↦ Ψ (‖x‖²)`, by a compactly supported smooth function.
-/
import Mathlib
import Submission.Work.Core.Basic
import Submission.Work.Radial.Basic
import Submission.Work.Radial.seminorm_bound
import Submission.Work.Radial.exp_approx_smooth
import Submission.Work.Radial.kills_profile_smooth
import Submission.Work.Radial.deGaussed_profile
import Submission.Work.Radial.gaussian_profile_schwartz
import Submission.Work.FunctionalEquations.DensityAux.composite_seminorm_smooth

open Filter
open LeanEval.Analysis.CKMRVInterpolation
open scoped SchwartzMap ContDiff

namespace Work.Radial

variable {n : ℕ} [NeZero n]

theorem gaussians_dense (n : ℕ) [NeZero n] {y : ℝ} (hy : 0 < y)
    (Λ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] ℂ)
    (h : ∀ (τ : ℂ), τ.im = y → ∀ F : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (∀ x, F x = Work.Core.gaussianFun n τ x) → Λ F = 0) :
    ∀ f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), Radial f → Λ f = 0 := by
  obtain ⟨s, C₀, hC₀, hΛbnd⟩ := exists_seminorm_bound n Λ
  have hcomp : ∀ i : ℕ × ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (Ψ : ℝ → ℂ) (L : ℝ),
      ContDiffOn ℝ ∞ Ψ (Set.Ici 0) →
      (∀ j : ℕ, j ≤ i.2 → ∀ t : ℝ, 0 ≤ t →
        (1 + t) ^ (i.1 + 2 * i.2) * ‖iteratedDerivWithin j Ψ (Set.Ici 0) t‖ ≤ L) →
      ∀ x : EuclideanSpace ℝ (Fin n),
        ‖x‖ ^ i.1 * ‖iteratedFDeriv ℝ i.2 (fun x : EuclideanSpace ℝ (Fin n) => Ψ (‖x‖ ^ 2)) x‖
          ≤ C * L :=
    fun i => Work.FunctionalEquations.DensityAux.composite_seminorm_smooth n i.1 i.2
  choose Ci hCin hCib using hcomp
  have hsup : ∀ G : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (s.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin n)) ℂ)) G ≤
        ∑ i ∈ s, SchwartzMap.seminorm ℝ i.1 i.2 G :=
    fun G => finset_sup_apply_le_sum (n := n) s
      (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin n)) ℂ) G
  set J : ℕ := s.sup (fun i : ℕ × ℕ => i.2) with hJ
  set K : ℕ := s.sup (fun i : ℕ × ℕ => i.1 + 2 * i.2) with hK
  intro f hf
  obtain ⟨hsm, hdec, hprof⟩ := deGaussed_profile n y f hf
  set Ξ : ℝ → ℂ := fun t => Real.exp (Real.pi * y * t) *
      profile (f : EuclideanSpace ℝ (Fin n) → ℂ) t with hΞ
  have hΞsm : ContDiffOn ℝ ∞ Ξ (Set.Ici 0) := hsm
  have hΞdec : ∀ j K' : ℕ, ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      (1 + t) ^ K' * Real.exp (-(Real.pi * y * t)) *
        ‖iteratedDerivWithin j Ξ (Set.Ici 0) t‖ ≤ ε := hdec
  have key : ∀ ε : ℝ, 0 < ε → ‖Λ f‖ ≤ C₀ * (∑ i ∈ s, Ci i) * ε := by
    intro ε hε
    obtain ⟨g, hgsm, hgsupp, hgb⟩ := exp_approx_smooth y hy Ξ hΞsm hΞdec J K hε
    obtain ⟨F, hF⟩ := gaussian_profile_schwartz n y hgsm hgsupp
    have hΛF : Λ F = 0 := kills_profile_smooth n hy Λ h hgsm hgsupp hF
    set Ψ : ℝ → ℂ := fun t => Real.exp (-(Real.pi * y * t)) * (Ξ t - g t) with hΨ
    have hΨsm : ContDiffOn ℝ ∞ Ψ (Set.Ici 0) := by
      rw [hΨ]
      have h1 : ContDiffOn ℝ ∞ (fun t : ℝ => -(Real.pi * y * t)) (Set.Ici 0) :=
        (contDiffOn_const.mul contDiffOn_id).neg
      have h2 : ContDiffOn ℝ ∞ (fun t : ℝ => Real.exp (-(Real.pi * y * t))) (Set.Ici 0) :=
        Real.contDiff_exp.comp_contDiffOn h1
      have h3 := Complex.ofRealCLM.contDiff.comp_contDiffOn h2
      exact h3.mul (hΞsm.sub hgsm.contDiffOn)
    have hΞval : ∀ t : ℝ, Ξ t = Real.exp (Real.pi * y * t) *
        profile (f : EuclideanSpace ℝ (Fin n) → ℂ) t := by
      intro t; rw [hΞ]
    have hfun : ((f - F : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) : EuclideanSpace ℝ (Fin n) → ℂ) =
        fun x => Ψ (‖x‖ ^ 2) := by
      funext x
      have h1 : profile (f : EuclideanSpace ℝ (Fin n) → ℂ) (‖x‖ ^ 2) =
          Real.exp (-(Real.pi * y * ‖x‖ ^ 2)) * Ξ (‖x‖ ^ 2) := by
        rw [hΞval (‖x‖ ^ 2), ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add,
          show -(Real.pi * y * ‖x‖ ^ 2) + Real.pi * y * ‖x‖ ^ 2 = 0 by ring,
          Real.exp_zero, Complex.ofReal_one, one_mul]
      have h3 : F x = Real.exp (-(Real.pi * y * ‖x‖ ^ 2)) * g (‖x‖ ^ 2) := by
        rw [hF x, gaussianTimesProfile, gaussianWeight]
        push_cast
        ring_nf
      simp only [sub_apply, hprof x, h3, h1, hΨ]
      ring_nf
    have hsemi : ∀ i ∈ s, SchwartzMap.seminorm ℝ i.1 i.2 (f - F) ≤ Ci i * ε := by
      intro i hi
      have hleJ : i.2 ≤ J := Finset.le_sup (f := fun i : ℕ × ℕ => i.2) hi
      have hleK : i.1 + 2 * i.2 ≤ K := Finset.le_sup (f := fun i : ℕ × ℕ => i.1 + 2 * i.2) hi
      have hL : ∀ j : ℕ, j ≤ i.2 → ∀ t : ℝ, 0 ≤ t →
          (1 + t) ^ (i.1 + 2 * i.2) * ‖iteratedDerivWithin j Ψ (Set.Ici 0) t‖ ≤ ε := by
        intro j hj t ht
        have hjJ : j ≤ J := le_trans hj hleJ
        have hw : (1 + t) ^ (i.1 + 2 * i.2) ≤ (1 + t) ^ K :=
          pow_le_pow_right₀ (by linarith) hleK
        calc (1 + t) ^ (i.1 + 2 * i.2) * ‖iteratedDerivWithin j Ψ (Set.Ici 0) t‖
            ≤ (1 + t) ^ K * ‖iteratedDerivWithin j Ψ (Set.Ici 0) t‖ :=
              mul_le_mul_of_nonneg_right hw (norm_nonneg _)
          _ ≤ ε := hgb j hjJ t ht
      refine SchwartzMap.seminorm_le_bound ℝ i.1 i.2 (f - F) (mul_nonneg (hCin i) hε.le) ?_
      intro x
      rw [hfun]
      exact hCib i Ψ ε hΨsm hL x
    have hsum : ∑ i ∈ s, SchwartzMap.seminorm ℝ i.1 i.2 (f - F) ≤ ∑ i ∈ s, Ci i * ε :=
      Finset.sum_le_sum hsemi
    have hsum' : ∑ i ∈ s, SchwartzMap.seminorm ℝ i.1 i.2 (f - F) ≤ (∑ i ∈ s, Ci i) * ε := by
      have hsum_mul : ∑ i ∈ s, Ci i * ε = (∑ i ∈ s, Ci i) * ε := (Finset.sum_mul ..).symm
      rw [← hsum_mul]
      exact hsum
    have hΛdiff : Λ (f - F) = Λ f := by rw [map_sub, hΛF, sub_zero]
    calc ‖Λ f‖ = ‖Λ (f - F)‖ := by rw [hΛdiff]
      _ ≤ C₀ * (s.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin n)) ℂ)) (f - F) :=
            hΛbnd (f - F)
      _ ≤ C₀ * ∑ i ∈ s, SchwartzMap.seminorm ℝ i.1 i.2 (f - F) :=
            mul_le_mul_of_nonneg_left (hsup (f - F)) hC₀
      _ ≤ C₀ * ((∑ i ∈ s, Ci i) * ε) := mul_le_mul_of_nonneg_left hsum' hC₀
      _ = C₀ * (∑ i ∈ s, Ci i) * ε := by rw [← mul_assoc]
  have hfin : ‖Λ f‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖Λ f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    set S : ℝ := ∑ i ∈ s, Ci i with hS
    have hSnn : 0 ≤ S := Finset.sum_nonneg fun i _ => (hCin i)
    have hden : 0 < 2 * (C₀ * S + 1) := by positivity
    have hεpos : 0 < ‖Λ f‖ / (2 * (C₀ * S + 1)) := by positivity
    have hb := key _ hεpos
    have hratio : C₀ * S / (2 * (C₀ * S + 1)) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith [mul_nonneg hC₀ hSnn]
    have h2 : C₀ * (∑ i ∈ s, Ci i) * (‖Λ f‖ / (2 * (C₀ * S + 1))) ≤ ‖Λ f‖ / 2 := by
      rw [← hS]
      have : C₀ * S * (‖Λ f‖ / (2 * (C₀ * S + 1))) = (C₀ * S / (2 * (C₀ * S + 1))) * ‖Λ f‖ := by
        ring
      rw [this]
      calc (C₀ * S / (2 * (C₀ * S + 1))) * ‖Λ f‖ ≤ (1 / 2) * ‖Λ f‖ :=
            mul_le_mul_of_nonneg_right hratio (norm_nonneg _)
        _ = ‖Λ f‖ / 2 := by ring
    linarith
  exact norm_eq_zero.mp hfin

end Work.Radial
