import Mathlib.Tactic.Have
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.OneBodyKin.kinFT_chi_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.ProfHatDecay` — polynomial decay of the bump profile

The Fourier profile of the corpus bump `χ` decays faster than any polynomial:

    `∃ C ≥ 0, ∀ p, |profHat p| ≤ C / (1 + ‖p‖)^6`.

This is the Schwartz-class statement `χ ∈ C_c^∞(ℝ³) ⟹ 𝓕χ ∈ 𝓢(ℝ³)` made quantitative, and it is
what any argument needing summability of `profHat` against polynomial weights (the `SymBound`
roadmap of this chapter, the `SymD`/`symA` estimates, the `p`-space bounds in `KernFT/`) has to
invoke.

## The proof, in four steps

1. **The bump is Schwartz.** `chiComplex z = (χ z : ℂ)` is `C^∞` with compact support
   (`chi_contDiff`, `chi_hasCompactSupport`), hence a Schwartz map `chiSchwartz` via
   `HasCompactSupport.toSchwartzMap`.
2. **`profHat` is the Fourier trace.** `kinFT_chi_eq` identifies `kinFT χ` with `profHat`;
   `kinFT_eq_fourier` (the corpus identification of the `p`-convention transform with Mathlib's
   `𝓕`) turns this into

       `|profHat p| = ‖𝓕 chiSchwartz ((2π)⁻¹ • p)‖`.

3. **Decay at infinity.** The Fourier transform of a Schwartz map is a Schwartz map, so by
   `SchwartzMap.decay 6 0` there is `K > 0` with `‖x‖^6 ‖𝓕 chiSchwartz x‖ ≤ K` for all `x`;
   substituting `x = (2π)⁻¹ • p` gives `‖p‖^6 |profHat p| ≤ (2π)^6 K =: K'`.
4. **Uniform bound.** `|profHat p| ≤ ∫_z |χ z| =: M`, since `|cos| ≤ 1`.

Combining `min (M, K'/‖p‖^6)` with the split at `‖p‖ ≤ 1` (`(1+‖p‖)^6 ≤ 64`) versus
`1 ≤ ‖p‖` (`(1+‖p‖)^6 ≤ 64 ‖p‖^6`) yields the single bound `|profHat p| ≤ 64·max M K'/(1+‖p‖)^6`.
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff

namespace Work.OneBodyKin

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 800000

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The bump `χ`, viewed as a Schwartz function -/

/-- The bump `χ` as a complex-valued function.  (The Fourier transform is complex-valued, even
though `χ` is real and its transform is real.) -/
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
    |profHat p| = ‖(𝓕 chiSchwartz) ((2 * Real.pi)⁻¹ • p)‖ := by
  have key : (profHat p : ℂ) = (𝓕 chiSchwartz) ((2 * Real.pi)⁻¹ • p) := by
    rw [← kinFT_chi_eq p]
    rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
    rw [SchwartzMap.fourier_coe chiSchwartz, chiSchwartz_coe]
  rw [← key]
  exact (RCLike.norm_ofReal (K := ℂ) _).symm

/-! ## 3. The uniform (`L¹ → L^∞`) bound -/

/-- **The bump profile is bounded by the total mass of the bump**: `|profHat p| ≤ ∫_z |χ z| dz`.
This is the elementary bound for the cosine transform of a compactly supported bump
(`|cos| ≤ 1`); no decay is needed. -/
private lemma profHat_abs_le_integral (p : ℝ³) : |profHat p| ≤ ∫ z : ℝ³, |chi z| := by
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
  rw [profHat]
  refine (abs_integral_le_integral_abs).trans ?_
  exact integral_mono_ae hint1 hint2 (Filter.Eventually.of_forall (fun z => by
    change |chi z * Real.cos (inner ℝ p z)| ≤ |chi z|
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)))

/-! ## 4. The decay bound -/

/-- **Polynomial decay of the bump profile.**  There is a constant `C ≥ 0` with
`|profHat p| ≤ C/(1 + ‖p‖)^6` for every momentum `p`. -/
theorem ProfHatDecay :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : EuclideanSpace ℝ (Fin 3),
      |Work.OneBodyKin.profHat p| ≤ C / (1 + ‖p‖) ^ 6 := by
  -- Schwartz decay of `𝓕 χ`: `‖x‖^6 ‖𝓕χ x‖ ≤ K`
  obtain ⟨K, hKpos, hK⟩ := (𝓕 chiSchwartz).decay 6 0
  have hKdec : ∀ x : ℝ³, ‖x‖ ^ 6 * ‖(𝓕 chiSchwartz) x‖ ≤ K := fun x => by
    have h := hK x
    rwa [norm_iteratedFDeriv_zero] at h
  set M : ℝ := ∫ z : ℝ³, |chi z| with hMdef
  set K' : ℝ := K * (2 * Real.pi) ^ 6 with hK'def
  have hMnn : 0 ≤ M := by rw [hMdef]; exact integral_nonneg (fun z => abs_nonneg _)
  have hK'nn : 0 ≤ K' := by rw [hK'def]; positivity
  have hMunif : ∀ p : ℝ³, |profHat p| ≤ M := fun p => by
    rw [hMdef]; exact profHat_abs_le_integral p
  refine ⟨64 * max M K', by positivity, fun p => ?_⟩
  by_cases hp : ‖p‖ ≤ 1
  · -- small momenta: use the uniform bound and `(1 + ‖p‖)^6 ≤ 64`
    have h2 : (1 + ‖p‖) ^ 6 ≤ 64 := by
      have h1 : 1 + ‖p‖ ≤ 2 := by linarith [norm_nonneg p]
      calc (1 + ‖p‖) ^ 6 ≤ 2 ^ 6 := pow_le_pow_left₀ (by positivity) h1 6
        _ = 64 := by norm_num
    have hpos : (0 : ℝ) < (1 + ‖p‖) ^ 6 := by positivity
    rw [le_div_iff₀ hpos]
    have ha : |profHat p| * (1 + ‖p‖) ^ 6 ≤ M * 64 :=
      mul_le_mul (hMunif p) h2 (by positivity) hMnn
    have hb : M * 64 ≤ 64 * max M K' := by linarith [le_max_left M K']
    linarith
  · -- large momenta: use the Schwartz decay and `(1 + ‖p‖)^6 ≤ 64 ‖p‖^6`
    simp only [not_le] at hp
    have hp1 : 1 ≤ ‖p‖ := le_of_lt hp
    have hpnn : (0 : ℝ) < ‖p‖ := lt_of_lt_of_le one_pos hp1
    have hπ6 : (0 : ℝ) < (2 * Real.pi) ^ 6 := by positivity
    have hdec : ‖p‖ ^ 6 * |profHat p| ≤ K' := by
      have hw : ‖(2 * Real.pi)⁻¹ • p‖ = ‖p‖ / (2 * Real.pi) := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (2 * Real.pi)⁻¹)]
        ring
      have h := hKdec ((2 * Real.pi)⁻¹ • p)
      rw [hw, ← profHat_eq_fourier_norm p] at h
      have hdiv : (‖p‖ / (2 * Real.pi)) ^ 6 * |profHat p|
          = ‖p‖ ^ 6 * |profHat p| / (2 * Real.pi) ^ 6 := by
        rw [div_pow]; ring
      rw [hdiv, div_le_iff₀ hπ6] at h
      rw [hK'def]
      exact h
    have hb : |profHat p| ≤ K' / ‖p‖ ^ 6 := by
      rw [le_div_iff₀ (pow_pos hpnn 6)]
      nlinarith [hdec]
    have hb2 : K' / ‖p‖ ^ 6 ≤ 64 * max M K' / (1 + ‖p‖) ^ 6 := by
      rw [div_le_div_iff₀ (pow_pos hpnn 6) (by positivity)]
      have h6 : (1 + ‖p‖) ^ 6 ≤ 64 * ‖p‖ ^ 6 := by
        have h1 : 1 + ‖p‖ ≤ 2 * ‖p‖ := by linarith
        calc (1 + ‖p‖) ^ 6 ≤ (2 * ‖p‖) ^ 6 := pow_le_pow_left₀ (by positivity) h1 6
          _ = 2 ^ 6 * ‖p‖ ^ 6 := by rw [mul_pow]
          _ = 64 * ‖p‖ ^ 6 := by norm_num
      calc K' * (1 + ‖p‖) ^ 6 ≤ K' * (64 * ‖p‖ ^ 6) := mul_le_mul_of_nonneg_left h6 hK'nn
        _ = 64 * K' * ‖p‖ ^ 6 := by ring
        _ ≤ 64 * max M K' * ‖p‖ ^ 6 := by
            apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg p) 6)
            linarith [le_max_right M K']
    linarith

end Work.OneBodyKin
