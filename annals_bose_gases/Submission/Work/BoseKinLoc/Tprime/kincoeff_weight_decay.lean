import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.OneBodyKin.integrable_fsKinCoeff_mul_abs_profHat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Tprime.kincoeff_weight_decay`

The cut-off-weighted bump profile decays cubically in the cut-off:

    `∃ K ≥ 0, ∀ C ≥ 1, ∫_p [‖p‖ − C]₊² |profHat p| dp ≤ K / C³`.

This is the `C⁻³` tail estimate for the FS cut-off `fsKinCoeff C r = [r − C]₊²` against the
bump profile `profHat`, needed for the boundary term `symD_value_bound` of the two-regime
symbol bound (`Tprime/symD_value_bound.lean`).

## Why `C⁻³` and not `C⁻¹`

The naive domination `[‖p‖ − C]₊² ≤ ‖p‖²` only gives the *constant* `∫_p ‖p‖²|profHat p|`.
The decay in `C` comes from the fact that the cut-off concentrates the integrand on the
region `‖p‖ ≳ C`: writing `fsKinCoeff C ‖p‖ = (max (‖p‖ − C) 0)²` and using

    `(max (r − C) 0)² ≤ r⁵ / C³`   for `r ≥ 0`, `C > 0`

(the substitution `r = tC`, `t ≥ 1`, reduces this to `(t−1)² ≤ t³`, i.e. `t² − 3t + 1 ≥ 0`
on `t ≥ 1` — see `fsKinCoeff_le_norm_pow_div`), the whole integral is dominated by

    `C⁻³ ∫_p ‖p‖⁵ |profHat p| dp`,

which is the `C⁻³` statement with `K = ∫_p ‖p‖⁵ |profHat p| dp`, provided that weight is
integrable.  For that we need more than the power-`6` decay of `ProfHatDecay`: `|profHat|`
must decay faster than `‖p‖⁻⁸`.  Since `χ` is smooth and compactly supported, `profHat` is a
Schwartz function, so *any* polynomial order is available; `profHat_decay_gen` below makes
this quantitative (the exponent `n + 4` for the weight `‖p‖ⁿ`).
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology Real FourierTransform SchwartzMap ContDiff

namespace Work.BoseKinLoc.Tprime

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases Work.OneBodyKin

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## 1. The bump profile is Schwartz: decay of arbitrary polynomial order

The proof is that of `Work.OneBodyKin.ProfHatDecay` (which stops at order `6`), with the
Schwartz decay of `𝓕 χ` invoked at the order `n` demanded. -/

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

/-- `|profHat p|` is the modulus of the Schwartz Fourier transform of `χ` at `(2π)⁻¹ • p`. -/
private lemma profHat_eq_fourier_norm (p : ℝ³) :
    |profHat p| = ‖(𝓕 chiSchwartz) ((2 * Real.pi)⁻¹ • p)‖ := by
  have key : (profHat p : ℂ) = (𝓕 chiSchwartz) ((2 * Real.pi)⁻¹ • p) := by
    rw [← kinFT_chi_eq p]
    rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
    rw [SchwartzMap.fourier_coe chiSchwartz, chiSchwartz_coe]
  rw [← key]
  exact (RCLike.norm_ofReal (K := ℂ) _).symm

/-- The elementary `L¹ → L^∞` bound `|profHat p| ≤ ∫_z |χ z| dz`. -/
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

/-- **Decay of the bump profile to arbitrary polynomial order.**  For every `n` there is
`K ≥ 0` with `|profHat p| ≤ K/(1 + ‖p‖)^n`. -/
private lemma profHat_decay_gen (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : ℝ³, |profHat p| ≤ K / (1 + ‖p‖) ^ n := by
  obtain ⟨K, _hKpos, hK⟩ := (𝓕 chiSchwartz).decay n 0
  have hKdec : ∀ x : ℝ³, ‖x‖ ^ n * ‖(𝓕 chiSchwartz) x‖ ≤ K := fun x => by
    have h := hK x
    rwa [norm_iteratedFDeriv_zero] at h
  set M : ℝ := ∫ z : ℝ³, |chi z| with hMdef
  set K' : ℝ := K * (2 * Real.pi) ^ n with hK'def
  have hMnn : 0 ≤ M := by rw [hMdef]; exact integral_nonneg (fun z => abs_nonneg _)
  have hK'nn : 0 ≤ K' := by rw [hK'def]; positivity
  have hMunif : ∀ p : ℝ³, |profHat p| ≤ M := fun p => by
    rw [hMdef]; exact profHat_abs_le_integral p
  refine ⟨2 ^ n * max M K', by positivity, fun p => ?_⟩
  have hpos : (0 : ℝ) < (1 + ‖p‖) ^ n := by positivity
  rw [le_div_iff₀ hpos]
  by_cases hp : ‖p‖ ≤ 1
  · -- small momenta: the uniform bound and `(1 + ‖p‖)^n ≤ 2^n`
    have h2 : (1 + ‖p‖) ^ n ≤ 2 ^ n := by
      have h1 : 1 + ‖p‖ ≤ 2 := by linarith [norm_nonneg p]
      exact pow_le_pow_left₀ (by positivity) h1 n
    have ha : |profHat p| * (1 + ‖p‖) ^ n ≤ M * 2 ^ n :=
      mul_le_mul (hMunif p) h2 hpos.le hMnn
    have hb : M * 2 ^ n ≤ 2 ^ n * max M K' := by
      have h1 : M * 2 ^ n ≤ max M K' * 2 ^ n :=
        mul_le_mul_of_nonneg_right (le_max_left M K') (pow_nonneg (by norm_num) n)
      linarith
    linarith
  · -- large momenta: the Schwartz decay of `𝓕 χ` and `(1 + ‖p‖)^n ≤ 2^n ‖p‖^n`
    simp only [not_le] at hp
    have hp1 : 1 ≤ ‖p‖ := le_of_lt hp
    have hpnn : (0 : ℝ) < ‖p‖ := lt_of_lt_of_le one_pos hp1
    have hπn : (0 : ℝ) < (2 * Real.pi) ^ n := by positivity
    have hdec : ‖p‖ ^ n * |profHat p| ≤ K' := by
      have hw : ‖(2 * Real.pi)⁻¹ • p‖ = ‖p‖ / (2 * Real.pi) := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (2 * Real.pi)⁻¹)]
        ring
      have h := hKdec ((2 * Real.pi)⁻¹ • p)
      rw [hw, ← profHat_eq_fourier_norm p] at h
      have hdiv : (‖p‖ / (2 * Real.pi)) ^ n * |profHat p|
          = ‖p‖ ^ n * |profHat p| / (2 * Real.pi) ^ n := by
        rw [div_pow]; ring
      rw [hdiv, div_le_iff₀ hπn] at h
      rw [hK'def]
      exact h
    have hb : |profHat p| ≤ K' / ‖p‖ ^ n := by
      rw [le_div_iff₀ (pow_pos hpnn n)]
      nlinarith [hdec]
    have hb2 : K' / ‖p‖ ^ n ≤ 2 ^ n * max M K' / (1 + ‖p‖) ^ n := by
      rw [div_le_div_iff₀ (pow_pos hpnn n) hpos]
      have h2n : (1 + ‖p‖) ^ n ≤ 2 ^ n * ‖p‖ ^ n := by
        have h1 : 1 + ‖p‖ ≤ 2 * ‖p‖ := by linarith
        calc (1 + ‖p‖) ^ n ≤ (2 * ‖p‖) ^ n := pow_le_pow_left₀ (by positivity) h1 n
          _ = 2 ^ n * ‖p‖ ^ n := by rw [mul_pow]
      calc K' * (1 + ‖p‖) ^ n ≤ K' * (2 ^ n * ‖p‖ ^ n) :=
            mul_le_mul_of_nonneg_left h2n hK'nn
        _ = 2 ^ n * K' * ‖p‖ ^ n := by ring
        _ ≤ 2 ^ n * max M K' * ‖p‖ ^ n := by
            refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg p) n)
            nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n, le_max_right M K', hK'nn]
    have h3 : |profHat p| ≤ 2 ^ n * max M K' / (1 + ‖p‖) ^ n := le_trans hb hb2
    calc |profHat p| * (1 + ‖p‖) ^ n
        ≤ (2 ^ n * max M K' / (1 + ‖p‖) ^ n) * (1 + ‖p‖) ^ n :=
          mul_le_mul_of_nonneg_right h3 hpos.le
      _ = 2 ^ n * max M K' := by
          rw [div_mul_cancel₀ _ (ne_of_gt hpos)]

/-! ## 2. Integrability of the polynomial weight against `|profHat|` -/

private lemma integrable_one_add_norm_inv_four :
    Integrable (fun p : ℝ³ => ((1 + ‖p‖ : ℝ) ^ 4)⁻¹) := by
  have h := integrable_one_add_norm (E := ℝ³) (μ := volume) (r := 4) (by
    rw [finrank_euclideanSpace_fin]; norm_num)
  refine h.congr (Filter.Eventually.of_forall (fun p => ?_))
  show (1 + ‖p‖) ^ (-(4 : ℝ)) = ((1 + ‖p‖ : ℝ) ^ 4)⁻¹
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖p‖)]
  congr 1
  exact Real.rpow_natCast (1 + ‖p‖) 4

/-- **`p ↦ ‖p‖ⁿ |profHat p|` is integrable.**  With the decay of order `n + 4`
(`profHat_decay_gen`) the weight is dominated by `K (1 + ‖p‖)⁻⁴`, integrable in dimension
`3` because `4 > 3`. -/
private lemma integrable_abs_profHat_mul_norm_pow_aux (n : ℕ) :
    Integrable (fun p : ℝ³ => ‖p‖ ^ n * |profHat p|) := by
  obtain ⟨K, _hK0, hK⟩ := profHat_decay_gen (n + 4)
  have hdom : Integrable (fun p : ℝ³ => K * ((1 + ‖p‖ : ℝ) ^ 4)⁻¹) :=
    integrable_one_add_norm_inv_four.const_mul K
  refine hdom.mono'
    (((continuous_norm.pow n).mul continuous_profHat.abs).aestronglyMeasurable) ?_
  filter_upwards with p
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg p) n) (abs_nonneg _))]
  have h1 : ‖p‖ ^ n ≤ (1 + ‖p‖) ^ n :=
    pow_le_pow_left₀ (norm_nonneg p) (by linarith [norm_nonneg p]) n
  calc ‖p‖ ^ n * |profHat p|
      ≤ (1 + ‖p‖) ^ n * (K / (1 + ‖p‖) ^ (n + 4)) :=
        mul_le_mul h1 (hK p) (abs_nonneg _) (pow_nonneg (by linarith [norm_nonneg p]) n)
    _ = K * ((1 + ‖p‖ : ℝ) ^ 4)⁻¹ := by
        have hne : (1 + ‖p‖ : ℝ) ^ n ≠ 0 := by positivity
        rw [pow_add, ← mul_div_assoc, mul_div_mul_left _ _ hne, div_eq_mul_inv]

/-! ## 3. The pointwise cut-off inequality -/

/-- **The elementary pointwise bound**: for `C > 0` and every `r ≥ 0`,

    `(max (r − C) 0)² ≤ r⁵ / C³`.

After `r = tC` (`t ≥ 1`) this is `(t − 1)² ≤ t³`, i.e. `t² − 3t + 1 ≥ 0` on `t ≥ 1` — which
holds with room to spare (`t² ≤ t³` alone already gives `(t−1)² = t² − 2t + 1 ≤ t³`). -/
private lemma fsKinCoeff_le_norm_pow_div {C : ℝ} (hC : 0 < C) (p : ℝ³) :
    fsKinCoeff C ‖p‖ ≤ ‖p‖ ^ 5 / C ^ 3 := by
  by_cases h : ‖p‖ ≤ C
  · -- the cut-off vanishes
    rw [fsKinCoeff, max_eq_right (by linarith : ‖p‖ - C ≤ 0),
      zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    positivity
  · -- `‖p‖ > C`: use `‖p‖ - C ≤ ‖p‖` and `C ≤ ‖p‖`
    simp only [not_le] at h
    rw [fsKinCoeff, max_eq_left (by linarith [h.le] : (0 : ℝ) ≤ ‖p‖ - C),
      le_div_iff₀ (by positivity : (0 : ℝ) < C ^ 3)]
    have h1 : C ^ 3 ≤ ‖p‖ ^ 3 := pow_le_pow_left₀ hC.le h.le 3
    have h2 : (‖p‖ - C) ^ 2 ≤ ‖p‖ ^ 2 := by
      nlinarith [norm_nonneg p, h.le]
    calc (‖p‖ - C) ^ 2 * C ^ 3 ≤ ‖p‖ ^ 2 * ‖p‖ ^ 3 :=
          mul_le_mul h2 h1 (by positivity) (by positivity)
      _ = ‖p‖ ^ 5 := by ring

/-! ## 4. The cut-off decay theorem -/

theorem kincoeff_weight_decay : ∃ K : ℝ, 0 ≤ K ∧ ∀ C : ℝ, 1 ≤ C →
    (∫ p : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.fsKinCoeff C ‖p‖ * |Work.OneBodyKin.profHat p|) ≤ K / C ^ 3 := by
  refine ⟨∫ p : ℝ³, ‖p‖ ^ 5 * |profHat p|, ?_, ?_⟩
  · exact integral_nonneg (fun p => mul_nonneg (pow_nonneg (norm_nonneg p) 5) (abs_nonneg _))
  · intro C hC
    have hCpos : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC
    have hfint : Integrable (fun p : ℝ³ => fsKinCoeff C ‖p‖ * |profHat p|) :=
      integrable_fsKinCoeff_mul_abs_profHat C
    have hwint : Integrable (fun p : ℝ³ => ‖p‖ ^ 5 * |profHat p|) :=
      integrable_abs_profHat_mul_norm_pow_aux 5
    have hmidint : Integrable (fun p : ℝ³ => (‖p‖ ^ 5 / C ^ 3) * |profHat p|) := by
      have h : Integrable (fun p : ℝ³ => (‖p‖ ^ 5 * |profHat p|) * (C ^ 3)⁻¹) :=
        hwint.mul_const _
      refine h.congr (Filter.Eventually.of_forall (fun p => ?_))
      ring
    have hpoint : ∀ p : ℝ³,
        fsKinCoeff C ‖p‖ * |profHat p| ≤ (‖p‖ ^ 5 / C ^ 3) * |profHat p| := fun p =>
      mul_le_mul_of_nonneg_right (fsKinCoeff_le_norm_pow_div hCpos p) (abs_nonneg _)
    calc (∫ p : ℝ³, fsKinCoeff C ‖p‖ * |profHat p|)
        ≤ ∫ p : ℝ³, (‖p‖ ^ 5 / C ^ 3) * |profHat p| :=
          integral_mono_ae hfint hmidint (Filter.Eventually.of_forall hpoint)
      _ = (∫ p : ℝ³, (‖p‖ ^ 5 * |profHat p|) * (C ^ 3)⁻¹) := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
          ring
      _ = (∫ p : ℝ³, ‖p‖ ^ 5 * |profHat p|) * (C ^ 3)⁻¹ := integral_mul_const _ _
      _ = (∫ p : ℝ³, ‖p‖ ^ 5 * |profHat p|) / C ^ 3 := by rw [div_eq_mul_inv]

end Work.BoseKinLoc.Tprime
