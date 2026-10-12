import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.BoseK15.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseK15.ChiReg_corpus` — FS `lem:DecaychiHat` for the corpus χ

The chapter `Submission/Work/BoseK15/` records FS §10's kernel obligations K1–K5
(`Defs.lean`).  Its K2 regularity row is the predicate

  `ChiReg B s C`  ⟺  `|B.hatChi p| (1+‖p‖²)^s ≤ C`  and  `|B.hatChiSq p| (1+‖p‖²)^s ≤ C`,

FS's `lem:DecaychiHat`.  The `BoxData` axioms of `Submission/Work/BoseB4/BoxChi.lean`
(continuity + compact support of `χ`) do **not** imply it; what is needed is the smoothness
of `χ`.  This file proves it for the *concrete* corpus χ (`Submission.BoseGases.chi`,
the `C^∞` cubic bump, `Submission/CubicChi.lean`):

  `ChiReg corpusBox s C` for **every** decay order `s`,

`corpusBox` being the corpus χ presented as FS's `BoxData`.  Since `χ` is `C^∞` with
compact support, both `χ` and `χ²` are Schwartz functions, so their cosine transforms
decay faster than any polynomial — this is `lem:DecaychiHat` with the decay order free,
which is exactly what the `hatChi_small` (order `26`) and `tail_hatChiSq` (order `25.5`)
thresholds of `Defs.lean` consume.

## The argument

1. `decay_cos_integral_smooth`: for *any* `g : ℝ³ → ℝ` that is `C^∞` with compact support,
   and every `m`, there is `C ≥ 0` with
   `|∫ x, g x · cos⟪p,x⟫| ≤ C/(1+‖p‖)^m` for all `p`.
   The proof is the standard one: complexify `g` and package it as a Schwartz map `G`
   (`HasCompactSupport.toSchwartzMap`), so that `𝓕 G` is a Schwartz map
   (`SchwartzMap.decay`); identify the cosine integral with the real part of `𝓕 G` at the
   frequency `(2π)⁻¹ • p` (`SchwartzMap.fourier_coe` + `Real.fourier_eq'`); bound the
   modulus by the modulus of the Fourier transform (`Complex.abs_re_le_norm`); and combine
   with the elementary uniform bound `|∫ g·cos| ≤ ∫|g|` by splitting at `‖p‖ ≤ 1`.
2. `mul_pow_le_of_decay`: a `C/(1+‖p‖)^{2s}` bound upgrades to the `ChiReg` shape
   `|a p| (1+‖p‖²)^s ≤ C`, since `1+‖p‖² ≤ (1+‖p‖)²`.
3. `ChiReg_corpus`: apply (1) with `m = 2s` to `g = χ` (for `hatChi`) and to `g = χ²`
   (which is `hatChiSq`, the transform of the *square* of `χ`), then take the max of the
   two constants, using that `χ²` is again `C^∞` with compact support.
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff

namespace Work.BoseK15

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000

/-- **Rapid decay of the cosine transform of a smooth compactly supported function.**
For `g : ℝ³ → ℝ` of class `C^∞` with compact support, and every decay order `m`, there is
`C ≥ 0` with `|∫ x, g x · cos⟪p,x⟫| ≤ C/(1+‖p‖)^m` for all momenta `p`.

This is the quantitative Schwartz-class statement "`g ∈ C_c^∞ ⟹ 𝔉g ∈ 𝓢`" in the real
(cosine) convention used throughout the B4/K15 corpus. -/
theorem decay_cos_integral_smooth (g : ℝ³ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgs : HasCompactSupport g) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ³,
      |∫ x : ℝ³, g x * Real.cos (inner ℝ p x)| ≤ C / (1 + ‖p‖) ^ m := by
  -- (1) complexify and package as a Schwartz map
  have hcs : HasCompactSupport (fun x : ℝ³ => (g x : ℂ)) :=
    hgs.comp_left (show ((0 : ℝ) : ℂ) = 0 by simp)
  have hdiff : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ³ => (g x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hg
  set G : 𝓢(ℝ³, ℂ) := hcs.toSchwartzMap hdiff with hG
  have hG_coe : ⇑G = fun x : ℝ³ => (g x : ℂ) :=
    funext (HasCompactSupport.toSchwartzMap_toFun hcs hdiff)
  -- (2) the pointwise bound by the Schwartz Fourier transform
  have hpoint : ∀ p : ℝ³,
      |∫ x : ℝ³, g x * Real.cos (inner ℝ p x)| ≤ ‖(𝓕 G) ((2 * Real.pi)⁻¹ • p)‖ := by
    intro p
    set φ : ℝ³ → ℂ := fun y => Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) * (g y : ℂ)
      with hφ
    have hcont : Continuous φ := by
      rw [hφ]
      refine Continuous.mul ?_ ?_
      · refine Complex.continuous_exp.comp (Continuous.neg ?_)
        exact continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_const.inner continuous_id))
      · exact Complex.continuous_ofReal.comp hg.continuous
    have hcsφ : HasCompactSupport φ := by
      rw [hφ]
      refine hgs.mono ?_
      intro y hy
      simp only [Function.mem_support] at hy ⊢
      intro h
      exact hy (by simp [h])
    have hφint : Integrable φ := hcont.integrable_of_hasCompactSupport hcsφ
    -- the real part passes through the integral
    have hre : (∫ y : ℝ³, φ y).re = ∫ y : ℝ³, (φ y).re :=
      (ContinuousLinearMap.integral_comp_comm Complex.reCLM hφint).symm
    -- the pointwise real part
    have hexp1 : ∀ y : ℝ³, Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
        = ((Real.cos (inner ℝ p y) : ℝ) : ℂ) - ((Real.sin (inner ℝ p y) : ℝ) : ℂ) * Complex.I := by
      intro y
      rw [show -(Complex.I * ((inner ℝ p y : ℝ) : ℂ))
            = ((-(inner ℝ p y) : ℝ) : ℂ) * Complex.I from by push_cast; ring]
      rw [Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
      push_cast
      ring
    have hpt : ∀ y : ℝ³, Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) * (g y : ℂ)
        = ((g y * Real.cos (inner ℝ p y) : ℝ) : ℂ)
          + ((-(g y * Real.sin (inner ℝ p y)) : ℝ) : ℂ) * Complex.I := by
      intro y
      rw [hexp1 y]
      push_cast
      ring
    have hre_pt : ∀ y : ℝ³, (φ y).re = g y * Real.cos (inner ℝ p y) := by
      intro y
      simp only [hφ]
      rw [hpt y]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    have hre_int : (∫ y : ℝ³, (φ y).re) = ∫ y : ℝ³, g y * Real.cos (inner ℝ p y) :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => hre_pt y)
    -- the Fourier identification
    have hfour : (∫ y : ℝ³, φ y) = (𝓕 G) ((2 * Real.pi)⁻¹ • p) := by
      simp only [hφ]
      rw [SchwartzMap.fourier_coe G, hG_coe]
      rw [Real.fourier_eq']
      apply integral_congr_ae
      filter_upwards with v
      have harg : (-2 * Real.pi * inner ℝ v ((2 * Real.pi)⁻¹ • p) : ℝ) = -(inner ℝ v p) := by
        have h2π : (2 * Real.pi : ℝ) ≠ 0 := by positivity
        rw [real_inner_smul_right]
        calc -2 * Real.pi * ((2 * Real.pi)⁻¹ * inner ℝ v p)
            = ((-2 * Real.pi) * (2 * Real.pi)⁻¹) * inner ℝ v p := by ring
          _ = -(inner ℝ v p) := by
              rw [show (-2 * Real.pi : ℝ) = -(2 * Real.pi) by ring, neg_mul,
                mul_inv_cancel₀ h2π]
              ring
      have hexp : Complex.exp (((-2 * Real.pi * inner ℝ v ((2 * Real.pi)⁻¹ • p) : ℝ) : ℂ)
            * Complex.I)
          = Complex.exp (-(Complex.I * ((inner ℝ p v : ℝ) : ℂ))) := by
        rw [harg, real_inner_comm p v]
        congr 1
        push_cast
        ring
      rw [hexp, smul_eq_mul]
    have h1 : |∫ x : ℝ³, g x * Real.cos (inner ℝ p x)| = |(∫ y : ℝ³, φ y).re| := by
      rw [← hre_int, ← hre]
    have h2 : |(∫ y : ℝ³, φ y).re| ≤ ‖(𝓕 G) ((2 * Real.pi)⁻¹ • p)‖ := by
      simpa [hfour] using Complex.abs_re_le_norm (∫ y : ℝ³, φ y)
    rw [h1]
    exact h2
  -- (3) the uniform bound
  have hunif : ∀ p : ℝ³,
      |∫ x : ℝ³, g x * Real.cos (inner ℝ p x)| ≤ ∫ x : ℝ³, |g x| := by
    intro p
    have hcs2 : HasCompactSupport (fun x : ℝ³ => |g x|) := by
      refine hgs.mono ?_
      intro x hx
      simp only [Function.mem_support] at hx ⊢
      intro h
      exact hx (by simp [h])
    have hint2 : Integrable (fun x : ℝ³ => |g x|) :=
      hg.continuous.abs.integrable_of_hasCompactSupport hcs2
    have hcs1 : HasCompactSupport (fun x : ℝ³ => |g x * Real.cos (inner ℝ p x)|) := by
      refine hgs.mono ?_
      intro x hx
      simp only [Function.mem_support] at hx ⊢
      intro h
      exact hx (by simp [h])
    have hint1 : Integrable (fun x : ℝ³ => |g x * Real.cos (inner ℝ p x)|) := by
      refine Continuous.integrable_of_hasCompactSupport ?_ hcs1
      exact (hg.continuous.mul
        (Real.continuous_cos.comp (continuous_const.inner continuous_id))).abs
    calc |∫ x : ℝ³, g x * Real.cos (inner ℝ p x)|
        ≤ ∫ x : ℝ³, |g x * Real.cos (inner ℝ p x)| := abs_integral_le_integral_abs
      _ ≤ ∫ x : ℝ³, |g x| := integral_mono_ae hint1 hint2
            (Filter.Eventually.of_forall fun x => by
              change |g x * Real.cos (inner ℝ p x)| ≤ |g x|
              rw [abs_mul]
              exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
  -- (4) combine the Schwartz decay with the uniform bound
  obtain ⟨K, hKpos, hKdec⟩ := (𝓕 G).decay m 0
  have hKnn : 0 ≤ K := le_of_lt hKpos
  have hKdec' : ∀ x : ℝ³, ‖x‖ ^ m * ‖(𝓕 G) x‖ ≤ K := fun x => by
    have h := hKdec x
    rwa [norm_iteratedFDeriv_zero] at h
  set M : ℝ := ∫ x : ℝ³, |g x| with hMdef
  have hMnn : 0 ≤ M := by rw [hMdef]; exact integral_nonneg (fun x => abs_nonneg _)
  set K' : ℝ := K * (2 * Real.pi) ^ m with hK'def
  have hK'nn : 0 ≤ K' := by rw [hK'def]; positivity
  refine ⟨2 ^ m * max M K', by positivity, fun p => ?_⟩
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (1 + ‖p‖) ^ m)]
  by_cases hp : ‖p‖ ≤ 1
  · have h2 : (1 + ‖p‖) ^ m ≤ 2 ^ m :=
      pow_le_pow_left₀ (by positivity) (by linarith [norm_nonneg p]) m
    have hle1 : |∫ x : ℝ³, g x * Real.cos (inner ℝ p x)| ≤ M := by
      rw [hMdef]
      exact hunif p
    calc |∫ x : ℝ³, g x * Real.cos (inner ℝ p x)| * (1 + ‖p‖) ^ m
        ≤ M * 2 ^ m := mul_le_mul hle1 h2 (by positivity) hMnn
      _ ≤ 2 ^ m * max M K' := by
          have h := mul_le_mul_of_nonneg_right (le_max_left M K')
            (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) m)
          linarith
  · simp only [not_le] at hp
    have hpnn : 0 < ‖p‖ := lt_of_lt_of_le one_pos (le_of_lt hp)
    have hπm : (0 : ℝ) < (2 * Real.pi) ^ m := by positivity
    have hdec : ‖p‖ ^ m * ‖(𝓕 G) ((2 * Real.pi)⁻¹ • p)‖ ≤ K' := by
      have hw : ‖(2 * Real.pi)⁻¹ • p‖ = ‖p‖ / (2 * Real.pi) := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (2 * Real.pi)⁻¹)]
        ring
      have h := hKdec' ((2 * Real.pi)⁻¹ • p)
      rw [hw] at h
      have hdiv : (‖p‖ / (2 * Real.pi)) ^ m * ‖(𝓕 G) ((2 * Real.pi)⁻¹ • p)‖
          = ‖p‖ ^ m * ‖(𝓕 G) ((2 * Real.pi)⁻¹ • p)‖ / (2 * Real.pi) ^ m := by
        rw [div_pow]; ring
      rw [hdiv, div_le_iff₀ hπm] at h
      rw [hK'def]
      exact h
    have hle : |∫ x : ℝ³, g x * Real.cos (inner ℝ p x)| ≤ K' / ‖p‖ ^ m := by
      rw [le_div_iff₀ (pow_pos hpnn m)]
      calc |∫ x : ℝ³, g x * Real.cos (inner ℝ p x)| * ‖p‖ ^ m
          = ‖p‖ ^ m * |∫ x : ℝ³, g x * Real.cos (inner ℝ p x)| := by ring
        _ ≤ ‖p‖ ^ m * ‖(𝓕 G) ((2 * Real.pi)⁻¹ • p)‖ :=
            mul_le_mul_of_nonneg_left (hpoint p) (pow_nonneg (le_of_lt hpnn) m)
        _ ≤ K' := hdec
    have hb2 : K' / ‖p‖ ^ m ≤ 2 ^ m * max M K' / (1 + ‖p‖) ^ m := by
      rw [div_le_div_iff₀ (pow_pos hpnn m) (by positivity : (0 : ℝ) < (1 + ‖p‖) ^ m)]
      have h2m : (1 + ‖p‖) ^ m ≤ 2 ^ m * ‖p‖ ^ m := by
        have h1 : 1 + ‖p‖ ≤ 2 * ‖p‖ := by linarith
        calc (1 + ‖p‖) ^ m ≤ (2 * ‖p‖) ^ m := pow_le_pow_left₀ (by positivity) h1 m
          _ = 2 ^ m * ‖p‖ ^ m := by rw [mul_pow]
      calc K' * (1 + ‖p‖) ^ m ≤ K' * (2 ^ m * ‖p‖ ^ m) :=
            mul_le_mul_of_nonneg_left h2m hK'nn
        _ = 2 ^ m * K' * ‖p‖ ^ m := by ring
        _ ≤ 2 ^ m * max M K' * ‖p‖ ^ m :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_right M K')
              (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) m)) (pow_nonneg (norm_nonneg p) m)
    calc |∫ x : ℝ³, g x * Real.cos (inner ℝ p x)| * (1 + ‖p‖) ^ m
        ≤ (K' / ‖p‖ ^ m) * (1 + ‖p‖) ^ m :=
          mul_le_mul_of_nonneg_right hle (by positivity)
      _ ≤ (2 ^ m * max M K' / (1 + ‖p‖) ^ m) * (1 + ‖p‖) ^ m :=
          mul_le_mul_of_nonneg_right hb2 (by positivity)
      _ = 2 ^ m * max M K' :=
          div_mul_cancel₀ _ (ne_of_gt (by positivity : (0 : ℝ) < (1 + ‖p‖) ^ m))

/-- A `C/(1+‖p‖)^{2s}` decay bound for `|a p|` gives the `ChiReg`-shaped bound
`|a p| (1 + ‖p‖²)^s ≤ C`. -/
theorem mul_pow_le_of_decay (a : ℝ³ → ℝ) (C : ℝ) (hC : 0 ≤ C) (s : ℕ)
    (h : ∀ p : ℝ³, |a p| ≤ C / (1 + ‖p‖) ^ (2 * s)) :
    ∀ p : ℝ³, |a p| * (1 + ‖p‖ ^ 2) ^ s ≤ C := by
  intro p
  have hpos : (0 : ℝ) < (1 + ‖p‖) ^ (2 * s) := by positivity
  have hle : (1 + ‖p‖ ^ 2) ^ s ≤ (1 + ‖p‖) ^ (2 * s) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith [norm_nonneg p]) s
  calc |a p| * (1 + ‖p‖ ^ 2) ^ s
      ≤ (C / (1 + ‖p‖) ^ (2 * s)) * (1 + ‖p‖ ^ 2) ^ s :=
        mul_le_mul_of_nonneg_right (h p) (by positivity)
    _ ≤ (C / (1 + ‖p‖) ^ (2 * s)) * (1 + ‖p‖) ^ (2 * s) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ ≤ C := le_of_eq (div_mul_cancel₀ _ (ne_of_gt hpos))

/-! ## `lem:DecaychiHat` for the corpus bump -/

/-- **FS `lem:DecaychiHat` for the corpus χ, at every decay order.**  The corpus bump `χ`
(`Submission.BoseGases.chi`) is `C^∞` with compact support, so both `χ` and `χ²` are
Schwartz functions and their cosine transforms decay faster than any polynomial:
`ChiReg corpusBox s C` holds for every `s`, with `C` obtained by applying
`decay_cos_integral_smooth` at order `2s` to `χ` (this is `hatChi`) and to `χ²` (this is
`hatChiSq`, the transform of the *square* of `χ`) and taking the maximum. -/
theorem ChiReg_corpus (s : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ChiReg corpusBox s C := by
  obtain ⟨C₁, hC₁nn, hC₁⟩ := decay_cos_integral_smooth (fun x : ℝ³ => Submission.BoseGases.chi x)
    Submission.BoseGases.chi_contDiff Submission.BoseGases.chi_hasCompactSupport (2 * s)
  have hsq_diff : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ³ => (Submission.BoseGases.chi x) ^ 2) :=
    Submission.BoseGases.chi_contDiff.pow 2
  have hsq_cs : HasCompactSupport (fun x : ℝ³ => (Submission.BoseGases.chi x) ^ 2) := by
    refine Submission.BoseGases.chi_hasCompactSupport.mono ?_
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h
    exact hx (by simp [h])
  obtain ⟨C₂, hC₂nn, hC₂⟩ := decay_cos_integral_smooth
    (fun x : ℝ³ => (Submission.BoseGases.chi x) ^ 2) hsq_diff hsq_cs (2 * s)
  refine ⟨max C₁ C₂, le_trans hC₁nn (le_max_left C₁ C₂), ?_, ?_⟩
  · intro p
    have hb : ∀ q : ℝ³, |corpusBox.hatChi q| * (1 + ‖q‖ ^ 2) ^ s ≤ C₁ :=
      mul_pow_le_of_decay (fun q : ℝ³ => corpusBox.hatChi q) C₁ hC₁nn s (fun q => by
        simpa only [Work.BoseB4.BoxData.hatChi, corpusBox_chi] using hC₁ q)
    exact le_trans (hb p) (le_max_left C₁ C₂)
  · intro p
    have hb : ∀ q : ℝ³, |corpusBox.hatChiSq q| * (1 + ‖q‖ ^ 2) ^ s ≤ C₂ :=
      mul_pow_le_of_decay (fun q : ℝ³ => corpusBox.hatChiSq q) C₂ hC₂nn s (fun q => by
        simpa only [Work.BoseB4.BoxData.hatChiSq, corpusBox_chi] using hC₂ q)
    exact le_trans (hb p) (le_max_right C₁ C₂)

end Work.BoseK15
