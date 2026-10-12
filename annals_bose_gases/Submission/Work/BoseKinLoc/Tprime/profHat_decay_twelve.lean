import Mathlib.Tactic.Have
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.OneBodyKin.ProfHatDecay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Tprime.profHat_decay_twelve`

The bump profile of `Submission.BoseGases.chi` decays faster than `(1 + ‖p‖)^{-12}`:

    `∃ K ≥ 0, ∀ p, |profHat p| ≤ K / (1 + ‖p‖) ^ 12`.

This is the exponent-`12` instance of the Schwartz-decay statement
`Work.OneBodyKin.ProfHatDecay` (which records exponent `6`), proved by the same four-step
argument with the Schwartz index raised from `6` to `12`:

1. `χ` is `C^∞` with compact support, hence a Schwartz map `chiSchwartz : 𝓢(ℝ³, ℂ)`;
2. `|profHat p| = ‖𝓕 chiSchwartz ((2π)⁻¹ • p)‖` (`kinFT_chi_eq` + `kinFT_eq_fourier`);
3. Schwartz decay of `𝓕 chiSchwartz` at index `12` gives `‖p‖^12 |profHat p| ≤ K'`
   for `‖p‖ ≥ 1`;
4. the elementary bound `|profHat p| ≤ ∫|χ|` covers `‖p‖ ≤ 1`, where `(1+‖p‖)^12 ≤ 4096`.

The two regimes are combined into the single bound with the constant `4096 · max M K'`.
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff

namespace Work.BoseKinLoc.Tprime

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## 1. The bump `χ`, viewed as a Schwartz function -/

/-- The bump `χ` as a complex-valued function. -/
private noncomputable def chiComplex : ℝ³ → ℂ := fun z => (chi z : ℂ)

private lemma chiComplex_contDiff : ContDiff ℝ ∞ chiComplex := by
  unfold chiComplex
  exact Complex.ofRealCLM.contDiff.comp chi_contDiff

private lemma chiComplex_hasCompactSupport : HasCompactSupport chiComplex := by
  refine HasCompactSupport.mono chi_hasCompactSupport ?_
  intro x hx
  simpa [chiComplex] using hx

/-- The bump `χ` as a Schwartz map (smooth + compactly supported). -/
private noncomputable def chiSchwartz : 𝓢(ℝ³, ℂ) :=
  chiComplex_hasCompactSupport.toSchwartzMap chiComplex_contDiff

private lemma chiSchwartz_coe : ⇑chiSchwartz = fun z => (chi z : ℂ) := by
  funext x
  rw [chiSchwartz, HasCompactSupport.toSchwartzMap_toFun]
  rfl

/-! ## 2. `profHat` is the Fourier transform of `χ` at the frequency `(2π)⁻¹ • p` -/

/-- The bridge between the real cosine profile and Mathlib's Schwartz Fourier transform:

    `|profHat p| = ‖𝓕 chiSchwartz ((2π)⁻¹ • p)‖`. -/
private lemma profHat_eq_fourier_norm (p : ℝ³) :
    |Work.OneBodyKin.profHat p| = ‖(𝓕 chiSchwartz) ((2 * Real.pi)⁻¹ • p)‖ := by
  have key : (Work.OneBodyKin.profHat p : ℂ) = (𝓕 chiSchwartz) ((2 * Real.pi)⁻¹ • p) := by
    rw [← Work.OneBodyKin.kinFT_chi_eq p]
    rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
    rw [SchwartzMap.fourier_coe chiSchwartz, chiSchwartz_coe]
  rw [← key]
  exact (RCLike.norm_ofReal (K := ℂ) _).symm

/-! ## 3. The uniform (`L¹ → L^∞`) bound -/

/-- **The bump profile is bounded by the total mass of the bump**: `|profHat p| ≤ ∫_z |χ z| dz`.
This is the elementary bound for the cosine transform of a compactly supported bump
(`|cos| ≤ 1`); no decay is needed. -/
private lemma profHat_abs_le_integral (p : ℝ³) : |Work.OneBodyKin.profHat p| ≤ ∫ z : ℝ³, |chi z| := by
  have hint2 : Integrable (fun z : ℝ³ => |chi z|) volume := by
    refine (chi_continuous.abs).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.mono chi_hasCompactSupport ?_
    intro z hz
    simp only [Function.mem_support] at hz ⊢
    intro h
    exact hz (by simp [h])
  have hint1 : Integrable (fun z : ℝ³ => |chi z * Real.cos (inner ℝ p z)|) volume := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (chi_continuous.mul
        (Real.continuous_cos.comp (continuous_const.inner continuous_id))).abs
    · refine HasCompactSupport.mono chi_hasCompactSupport ?_
      intro z hz
      simp only [Function.mem_support] at hz ⊢
      intro h
      exact hz (by simp [h])
  rw [Work.OneBodyKin.profHat]
  refine (abs_integral_le_integral_abs).trans ?_
  exact integral_mono_ae hint1 hint2 (Filter.Eventually.of_forall (fun z => by
    change |chi z * Real.cos (inner ℝ p z)| ≤ |chi z|
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)))

/-! ## 4. The decay bound at exponent `12` -/

theorem profHat_decay_twelve : ∃ K : ℝ, 0 ≤ K ∧ ∀ p : EuclideanSpace ℝ (Fin 3),
    |Work.OneBodyKin.profHat p| ≤ K / (1 + ‖p‖) ^ 12 := by
  -- Schwartz decay of `𝓕 χ` at index `12`: `‖x‖^12 ‖𝓕χ x‖ ≤ K`
  obtain ⟨K, _hKpos, hK⟩ := (𝓕 chiSchwartz).decay 12 0
  have hKdec : ∀ x : ℝ³, ‖x‖ ^ 12 * ‖(𝓕 chiSchwartz) x‖ ≤ K := fun x => by
    have h := hK x
    rwa [norm_iteratedFDeriv_zero] at h
  set M : ℝ := ∫ z : ℝ³, |chi z| with hMdef
  set K' : ℝ := K * (2 * Real.pi) ^ 12 with hK'def
  have hMnn : 0 ≤ M := by rw [hMdef]; exact integral_nonneg (fun z => abs_nonneg _)
  have hK'nn : 0 ≤ K' := by rw [hK'def]; positivity
  have hMunif : ∀ p : ℝ³, |Work.OneBodyKin.profHat p| ≤ M := fun p => by
    rw [hMdef]; exact profHat_abs_le_integral p
  refine ⟨4096 * max M K', by positivity, fun p => ?_⟩
  by_cases hp : ‖p‖ ≤ 1
  · -- small momenta: the uniform bound and `(1 + ‖p‖)^12 ≤ 4096`
    have h2 : (1 + ‖p‖) ^ 12 ≤ 4096 := by
      have h1 : 1 + ‖p‖ ≤ 2 := by linarith [norm_nonneg p]
      calc (1 + ‖p‖) ^ 12 ≤ 2 ^ 12 := pow_le_pow_left₀ (by positivity) h1 12
        _ = 4096 := by norm_num
    have hpos : (0 : ℝ) < (1 + ‖p‖) ^ 12 := by positivity
    rw [le_div_iff₀ hpos]
    have ha : |Work.OneBodyKin.profHat p| * (1 + ‖p‖) ^ 12 ≤ M * 4096 :=
      mul_le_mul (hMunif p) h2 (by positivity) hMnn
    have hb : M * 4096 ≤ 4096 * max M K' := by linarith [le_max_left M K']
    linarith
  · -- large momenta: Schwartz decay and `(1 + ‖p‖)^12 ≤ 4096 ‖p‖^12`
    simp only [not_le] at hp
    have hp1 : 1 ≤ ‖p‖ := le_of_lt hp
    have hpnn : (0 : ℝ) < ‖p‖ := lt_of_lt_of_le one_pos hp1
    have hπ12 : (0 : ℝ) < (2 * Real.pi) ^ 12 := by positivity
    have hdec : ‖p‖ ^ 12 * |Work.OneBodyKin.profHat p| ≤ K' := by
      have hw : ‖(2 * Real.pi)⁻¹ • p‖ = ‖p‖ / (2 * Real.pi) := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (2 * Real.pi)⁻¹)]
        ring
      have h := hKdec ((2 * Real.pi)⁻¹ • p)
      rw [hw, ← profHat_eq_fourier_norm p] at h
      have hdiv : (‖p‖ / (2 * Real.pi)) ^ 12 * |Work.OneBodyKin.profHat p|
          = ‖p‖ ^ 12 * |Work.OneBodyKin.profHat p| / (2 * Real.pi) ^ 12 := by
        rw [div_pow]; ring
      rw [hdiv, div_le_iff₀ hπ12] at h
      rw [hK'def]
      exact h
    have hb : |Work.OneBodyKin.profHat p| ≤ K' / ‖p‖ ^ 12 := by
      rw [le_div_iff₀ (pow_pos hpnn 12)]
      nlinarith [hdec]
    have hb2 : K' / ‖p‖ ^ 12 ≤ 4096 * max M K' / (1 + ‖p‖) ^ 12 := by
      rw [div_le_div_iff₀ (pow_pos hpnn 12) (by positivity)]
      have h12 : (1 + ‖p‖) ^ 12 ≤ 4096 * ‖p‖ ^ 12 := by
        have h1 : 1 + ‖p‖ ≤ 2 * ‖p‖ := by linarith
        calc (1 + ‖p‖) ^ 12 ≤ (2 * ‖p‖) ^ 12 := pow_le_pow_left₀ (by positivity) h1 12
          _ = 2 ^ 12 * ‖p‖ ^ 12 := by rw [mul_pow]
          _ = 4096 * ‖p‖ ^ 12 := by norm_num
      calc K' * (1 + ‖p‖) ^ 12 ≤ K' * (4096 * ‖p‖ ^ 12) :=
            mul_le_mul_of_nonneg_left h12 hK'nn
        _ = 4096 * K' * ‖p‖ ^ 12 := by ring
        _ ≤ 4096 * max M K' * ‖p‖ ^ 12 := by
            apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg p) 12)
            linarith [le_max_right M K']
    linarith

end Work.BoseKinLoc.Tprime
