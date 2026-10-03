/-
# The Calderón–Zygmund seed of the lacunary bump `lacψ`

This module proves `Work.KMTAreas.A7.lacBumpSeed`: the mean-zero bump
`lacψ = η - η(2·)` of `lacBumpDefs` is the Fourier transform of a *real* seed `Ψ` whose
inverse Fourier transform it is, and which satisfies the shifted-Calderón–Zygmund seed
bounds `IsCZSeed Ψ Ψ' B` of `Work.Analysis.CzShift`.

The proof has three ingredients:

* `lacψ` is even, real-valued (as a complex-valued function) and compactly supported, so
  `𝓕 lacψ` is real (this is where the seed is real-valued);
* `lacψ` is `C^∞` with compact support, hence a Schwartz function, so Fourier inversion
  (`𝓕 (𝓕⁻ lacψ) = lacψ`) holds with no integrability work;
* the seed bounds `IsCZSeed` come from `Work.Analysis.CzShift.exists_isCZSeed_of_fourierInv`,
  the derivative bounds it needs being supplied by the Schwartz seminorms of `lacψ`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.lacBumpDefs

namespace Work.KMTAreas.A7

open MeasureTheory Filter
open scoped FourierTransform

noncomputable section

/-! ## Elementary properties of the bump `lacψ` -/

/-- `lacψ` vanishes off `[-1,1]`. -/
lemma lacψ_zero_of_one_lt_abs {ξ : ℝ} (h : 1 < |ξ|) : lacψ ξ = 0 := by
  have h2 : (1 : ℝ) ≤ |2 * ξ| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    linarith
  simp only [lacψ]
  rw [Work.KMTContract.kmtEta_zero (le_of_lt h), Work.KMTContract.kmtEta_zero h2, sub_zero]

/-- `lacψ` is smooth. -/
lemma lacψ_contDiff : ContDiff ℝ (↑(⊤ : ℕ∞)) lacψ := by
  have h1 : ContDiff ℝ ↑(⊤ : ℕ∞) (Work.KMTContract.kmtEta) :=
    (ContinuousLinearMap.contDiff (n := (↑(⊤ : ℕ∞))) (Complex.ofRealCLM : ℝ →L[ℝ] ℂ)).comp
      (ContDiffBump.contDiff Work.KMTContract.kmtBump (n := ⊤))
  unfold lacψ
  exact h1.sub (h1.comp (by fun_prop))

/-- `lacψ` is even. -/
lemma lacψ_even (ξ : ℝ) : lacψ (-ξ) = lacψ ξ := by
  simp only [lacψ]
  rw [Work.KMTContract.kmtEta_neg, show 2 * -ξ = -(2 * ξ) by ring, Work.KMTContract.kmtEta_neg]

/-- `lacψ` is real-valued. -/
lemma lacψ_star (ξ : ℝ) : (starRingEnd ℂ) (lacψ ξ) = lacψ ξ := by
  simp only [lacψ, Work.KMTContract.kmtEta]
  rw [map_sub, Complex.conj_ofReal, Complex.conj_ofReal]

/-- `lacψ` has compact support. -/
lemma lacψ_hasCompactSupport : HasCompactSupport lacψ :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:ℝ) 1) (by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    by_contra h
    exact hx (lacψ_zero_of_one_lt_abs (not_le.mp h)))

/-- `lacψ` is integrable. -/
lemma lacψ_integrable : Integrable lacψ :=
  lacψ_contDiff.continuous.integrable_of_hasCompactSupport lacψ_hasCompactSupport

/-! ## Conjugation commutes with integration and with the Fourier transform -/

/-- Conjugation commutes with the Bochner integral. -/
private lemma integral_star_eq (g : ℝ → ℂ) (hg : Integrable g) :
    ∫ x, (starRingEnd ℂ) (g x) = (starRingEnd ℂ) (∫ x, g x) := by
  have h := ContinuousLinearMap.integral_comp_comm (Complex.conjCLE : ℂ →L[ℝ] ℂ) hg
  have h1 : (fun x => (starRingEnd ℂ) (g x)) = fun x => (Complex.conjCLE : ℂ → ℂ) (g x) := by
    funext x; rw [Complex.conjCLE_apply]
  have h2 : (starRingEnd ℂ) (∫ x, g x) = (Complex.conjCLE : ℂ → ℂ) (∫ x, g x) := by
    rw [Complex.conjCLE_apply]
  rw [h1, h2]
  exact h

/-- `𝓕 (conj ∘ f) (-w) = conj (𝓕 f w)` for integrable `f`. -/
private lemma conj_fourier (f : ℝ → ℂ) (hf : Integrable f) (w : ℝ) :
    (starRingEnd ℂ) (𝓕 f w) = 𝓕 (fun x => (starRingEnd ℂ) (f x)) (-w) := by
  have hint : Integrable (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * v * w) * Complex.I) • f v) := by
    have h : Integrable (fun v : ℝ => 𝐞 (-(v * w)) • f v) := by
      simpa [mul_comm] using (Real.fourierIntegral_convergent_iff (μ := volume) (f := f) w).2 hf
    refine h.congr (Eventually.of_forall fun v => ?_)
    show 𝐞 (-(v * w)) • f v = Complex.exp (↑(-2 * Real.pi * v * w) * Complex.I) • f v
    rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, smul_eq_mul]
    congr 1
    push_cast
    ring_nf
  rw [Real.fourier_real_eq_integral_exp_smul]
  rw [← integral_star_eq _ hint]
  rw [Real.fourier_real_eq_integral_exp_smul]
  congr 1 with v
  rw [smul_eq_mul, smul_eq_mul, map_mul, ← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring_nf

/-! ## The Fourier transform of `lacψ` is real -/

/-- `𝓕 lacψ` is even (because `lacψ` is). -/
lemma fourier_lacψ_even (ξ : ℝ) : 𝓕 lacψ (-ξ) = 𝓕 lacψ ξ := by
  have h2 : (fun x : ℝ => lacψ (-x)) = lacψ := funext lacψ_even
  have h3 : 𝓕⁻ lacψ = 𝓕 lacψ := by rw [Real.fourierInv_eq_fourier_comp_neg, h2]
  rw [← Real.fourierInv_eq_fourier_neg lacψ ξ, h3]

/-- `𝓕 lacψ` is real-valued. -/
lemma star_fourier_lacψ (ξ : ℝ) : (starRingEnd ℂ) (𝓕 lacψ ξ) = 𝓕 lacψ ξ := by
  rw [conj_fourier lacψ lacψ_integrable ξ]
  rw [show (fun x => (starRingEnd ℂ) (lacψ x)) = lacψ from funext lacψ_star]
  exact fourier_lacψ_even ξ

/-- The (real) seed attached to `lacψ`: the real part of `𝓕⁻ lacψ`. -/
noncomputable def lacΨ : ℝ → ℝ := fun u => (FourierTransformInv.fourierInv lacψ u).re

/-- `lacΨ` indeed complexifies to `𝓕⁻ lacψ`. -/
lemma lacΨ_spec (u : ℝ) : (lacΨ u : ℂ) = FourierTransformInv.fourierInv lacψ u := by
  unfold lacΨ
  rw [Real.fourierInv_eq_fourier_neg]
  exact Complex.conj_eq_iff_re.mp (star_fourier_lacψ (-u))

/-! ## `lacψ` as a Schwartz function, and the inverse Fourier transform -/

/-- `lacψ` bundled as a Schwartz function. -/
noncomputable def lacψS : SchwartzMap ℝ ℂ :=
  lacψ_hasCompactSupport.toSchwartzMap lacψ_contDiff

lemma lacψS_coe : ⇑lacψS = lacψ :=
  funext fun x => HasCompactSupport.toSchwartzMap_toFun _ _ x

/-- The Schwartz seminorms of `lacψ` bound every iterated derivative. -/
lemma norm_iteratedDeriv_lacψ_le (j : ℕ) (ξ : ℝ) :
    ‖iteratedDeriv j lacψ ξ‖ ≤ SchwartzMap.seminorm ℝ 0 j lacψS := by
  rw [← lacψS_coe, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ lacψS j ξ

/-- The inverse Fourier transform of `lacψ` as a Schwartz function. -/
noncomputable def lacK : SchwartzMap ℝ ℂ := FourierTransformInv.fourierInv lacψS

lemma lacK_coe : (⇑lacK : ℝ → ℂ) = FourierTransformInv.fourierInv lacψ := by
  rw [show ⇑lacK = FourierTransformInv.fourierInv (⇑lacψS) from
    SchwartzMap.fourierInv_coe lacψS]
  exact congrArg FourierTransformInv.fourierInv lacψS_coe

/-- Fourier inversion: the Fourier transform of `lacΨ` (complexified) is `lacψ`. -/
lemma lacΨ_fourier (ξ : ℝ) : 𝓕 (fun u : ℝ => (lacΨ u : ℂ)) ξ = lacψ ξ := by
  have hfun : (fun u : ℝ => (lacΨ u : ℂ)) = ⇑lacK := by
    rw [lacK_coe]
    exact funext lacΨ_spec
  rw [hfun, ← SchwartzMap.fourier_coe lacK]
  rw [show 𝓕 lacK = lacψS from FourierInvPair.fourier_fourierInv_eq lacψS]
  exact congrFun lacψS_coe ξ

/-! ## The constant `lacC` and the seed bounds -/

/-- A single constant dominating all the Schwartz seminorms of `lacψ` that are needed. -/
noncomputable def lacC : ℝ := max 1 (max (SchwartzMap.seminorm ℝ 0 0 lacψS)
  (max (SchwartzMap.seminorm ℝ 0 1 lacψS) (SchwartzMap.seminorm ℝ 0 2 lacψS)))

lemma lacC_one_le : 1 ≤ lacC := by unfold lacC; exact le_max_left _ _
lemma lacC_pos : 0 < lacC := lt_of_lt_of_le zero_lt_one lacC_one_le

lemma sem_le_lacC : SchwartzMap.seminorm ℝ 0 0 lacψS ≤ lacC ∧
    SchwartzMap.seminorm ℝ 0 1 lacψS ≤ lacC ∧ SchwartzMap.seminorm ℝ 0 2 lacψS ≤ lacC := by
  unfold lacC
  refine ⟨le_trans (le_max_left _ _) (le_max_right _ _), ?_, ?_⟩
  · exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  · exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)

/-- Every iterated derivative of `lacψ` is smooth. -/
lemma iteratedDeriv_lacψ_contDiff (j : ℕ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (iteratedDeriv j lacψ) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv j lacψ_contDiff

/-! ## The seed -/

theorem lacBumpSeed :
    ∃ (Ψ Ψ' : ℝ → ℝ) (B : ℝ), 1 ≤ B ∧
      Work.Analysis.CzShift.IsCZSeed Ψ Ψ' B ∧
      (∀ u : ℝ, (Ψ u : ℂ) = FourierTransformInv.fourierInv Work.KMTAreas.A7.lacψ u) ∧
      (∀ ξ : ℝ, FourierTransform.fourier (fun u : ℝ => (Ψ u : ℂ)) ξ = Work.KMTAreas.A7.lacψ ξ) := by
  obtain ⟨hS0, hS1, hS2⟩ := sem_le_lacC
  have hbd : ∀ ξ : ℝ, ‖lacψ ξ‖ ≤ lacC := by
    intro ξ
    have h := norm_iteratedDeriv_lacψ_le 0 ξ
    rw [iteratedDeriv_zero] at h
    exact le_trans h hS0
  have hbd' : ∀ ξ : ℝ, ‖iteratedDeriv 1 lacψ ξ‖ ≤ lacC := fun ξ =>
    le_trans (norm_iteratedDeriv_lacψ_le 1 ξ) hS1
  have hbd'' : ∀ ξ : ℝ, ‖iteratedDeriv 2 lacψ ξ‖ ≤ lacC := fun ξ =>
    le_trans (norm_iteratedDeriv_lacψ_le 2 ξ) hS2
  have hd : ∀ ξ : ℝ, HasDerivAt lacψ (iteratedDeriv 1 lacψ ξ) ξ := by
    intro ξ
    have h : DifferentiableAt ℝ lacψ ξ := (lacψ_contDiff.differentiable (by simp)).differentiableAt
    rw [iteratedDeriv_one]
    exact h.hasDerivAt
  have hd2 : ∀ ξ : ℝ, HasDerivAt (iteratedDeriv 1 lacψ) (iteratedDeriv 2 lacψ ξ) ξ := by
    intro ξ
    have h : DifferentiableAt ℝ (iteratedDeriv 1 lacψ) ξ :=
      ((iteratedDeriv_lacψ_contDiff 1).differentiable (by simp)).differentiableAt
    have h2 : iteratedDeriv 2 lacψ ξ = deriv (iteratedDeriv 1 lacψ) ξ := by
      rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ]
    rw [h2]
    exact h.hasDerivAt
  have hsupp : ∀ ξ : ℝ, lacC < |ξ| → lacψ ξ = 0 := fun ξ h =>
    lacψ_zero_of_one_lt_abs (lt_of_le_of_lt lacC_one_le h)
  obtain ⟨B, hB, Ψ', hseed⟩ := Work.Analysis.CzShift.exists_isCZSeed_of_fourierInv
    lacψ (iteratedDeriv 1 lacψ) (iteratedDeriv 2 lacψ) lacΨ lacC
    lacC_pos lacΨ_spec hsupp hbd hd hbd' hd2 hbd''
  exact ⟨lacΨ, Ψ', B, hB, hseed, lacΨ_spec, lacΨ_fourier⟩

end

end Work.KMTAreas.A7
