import Submission.FUP.LocalizeSum
import Submission.FUP.LocalizeKappa
import Submission.Commons.Analysis.Fourier.truncation_low_le
import Submission.Commons.Analysis.Fourier.fourier_convFun_ae
import Submission.Commons.Analysis.Fourier.integral_eta_shift_ge

open MeasureTheory FourierTransform Metric Filter Set
open scoped ENNReal BigOperators Topology

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Auxiliaries for Han–Schlag's single-scale estimate (Lemma 4.3)

**Status (Session 55).**  The lemmas in this file are correct and are exactly the *surrounding
bookkeeping* of Han–Schlag's Lemma 4.3 (`weight_shift_le` = the uniformity of the modulation
average, `convFun_indicator_eq` = the localised convolution identity, `norm_convFun_le_hsq` =
`‖f*φ‖_{L²} ≤ ‖f‖_{H^{-d}}` for a damping kernel, `subLp*` = the indicator bookkeeping).  They are
**not** sufficient on their own: the missing input is the band-limit-free localisation with a
*fixed* exponent `prop:locddim` (see `Submission/FUP/ROADMAP.md`, Session 55).
`Submission/FUP/LocalizeKappa.lean` — despite its name — does **not** supply it.

Ingredients of the single-scale estimate (`Submission/FUP/LocalizeScale.lean`):

* the modulation with a *continuous* parameter `η` and the Fourier shift
  `𝓕(f·e^{2πi⟨·,η⟩})(ξ) = 𝓕f(ξ-η)` (`phaseEta`, `modEta`, `fourier_modEta`);
* the comparison of the `H^{-d}` weight under a shift by `η ∈ [-2,2]^d`
  (`weight_shift_le`), which is what makes the `η`-average uniform;
* the localised convolution identity `1_{S'}(f*φ) = 1_{S'}((1_S f)*φ)` for the localisation
  geometry of `Submission/FUP/LocalizeGeom.lean` (`convFun_indicator_eq`);
* the indicator of an `L²` class as an `L²` class (`subLp`) and its elementary properties;
* the explicit constants of the estimate (`Theta`, `qOf`, `scaleBeta`, `scaleGamma`).
-/

namespace Submission.FUP

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-! ## The modulation with a continuous parameter -/

/-- The modulation phase `x ↦ e^{2πi⟨x,η⟩}`. -/
noncomputable def phaseEta (η x : ℝᵈ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ x η : ℝ) : ℂ))

lemma norm_phaseEta (η x : ℝᵈ) : ‖phaseEta η x‖ = 1 := by
  rw [phaseEta, Complex.norm_exp]
  have hre : (2 * (Real.pi : ℂ) * Complex.I * ((inner ℝ x η : ℝ) : ℂ)).re = 0 := by
    rw [show (2 * (Real.pi : ℂ) * Complex.I * ((inner ℝ x η : ℝ) : ℂ))
        = ((2 * Real.pi * (inner ℝ x η : ℝ) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    simp
  rw [hre, Real.exp_zero]

lemma measurable_phaseEta (η : ℝᵈ) : Measurable (phaseEta η) := by
  rw [show phaseEta η = fun x : ℝᵈ =>
      Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ x η : ℝ) : ℂ)) from rfl]
  fun_prop

/-- The modulation `f ↦ (x ↦ e^{2πi⟨x,η⟩} f x)`. -/
noncomputable def modEta (η : ℝᵈ) (f : ℝᵈ → ℂ) : ℝᵈ → ℂ := fun x => phaseEta η x * f x

lemma memLp_modEta {η : ℝᵈ} {f : ℝᵈ → ℂ} (hf : MemLp f 2 (volume : Measure ℝᵈ)) :
    MemLp (modEta η f) 2 (volume : Measure ℝᵈ) := by
  refine hf.of_le (((measurable_phaseEta η).aestronglyMeasurable).mul hf.1) ?_
  filter_upwards with x
  rw [modEta, norm_mul, norm_phaseEta, one_mul]

/-- **The Fourier transform of a modulation** (continuous parameter). -/
lemma fourier_modEta {η : ℝᵈ} {f : ℝᵈ → ℂ} (hf : MemLp f 2 (volume : Measure ℝᵈ)) :
    ((𝓕 ((memLp_modEta (η := η) hf).toLp (modEta η f)) : Lp ℂ 2 (volume : Measure ℝᵈ)) :
        ℝᵈ → ℂ) =ᵐ[volume]
      (fun ξ => ((𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) (ξ - η)) := by
  have h := Commons.Analysis.Fourier.fourier_modulation_ae d η f hf
  obtain ⟨hf', heq⟩ := h
  have hcoe : (memLp_modEta (η := η) hf).toLp (modEta η f) = hf'.toLp _ := by
    congr 1
  rw [hcoe]
  exact heq

/-! ## Comparison of the `H^{-d}` weight under a shift -/

/-- **The `H^{-d}` weight is shift-invariant up to the constant `(1+16d)^d`.**  For `|ηᵢ| ≤ 2`
one has `⟨ξ - η⟩^{-2d} ≤ (1+16d)^d ⟨ξ⟩^{-2d}`, hence the corresponding weighted integrals
compare. -/
lemma weight_shift_le {η : ℝᵈ} (hη : ∀ i : Fin d, |η i| ≤ 2) {F : ℝᵈ → ℂ}
    (hF : MemLp F 2 (volume : Measure ℝᵈ)) :
    (∫ ξ, (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) * ‖F (ξ - η)‖ ^ 2)
      ≤ (40 * ((d : ℝ) + 1)) ^ d * ∫ ξ, (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) * ‖F ξ‖ ^ 2 := by
  set Cd : ℝ := 40 * ((d : ℝ) + 1) with hCd
  have hCd1 : (1 : ℝ) ≤ Cd := by rw [hCd]; nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hCdpos : (0 : ℝ) < Cd := lt_of_lt_of_le zero_lt_one hCd1
  have hηn : ‖η‖ ^ 2 ≤ 4 * (d : ℝ) := by
    have h1 : ∀ i : Fin d, ‖η i‖ ^ 2 ≤ 4 := by
      intro i
      have h2 := abs_le.mp (hη i)
      rw [Real.norm_eq_abs, sq_abs]
      nlinarith [h2.1, h2.2]
    calc ‖η‖ ^ 2 = ∑ i : Fin d, ‖η i‖ ^ 2 := by
          rw [EuclideanSpace.real_norm_sq_eq]
          exact Finset.sum_congr rfl (fun i _ => by rw [Real.norm_eq_abs, sq_abs])
      _ ≤ ∑ _i : Fin d, (4 : ℝ) := Finset.sum_le_sum (fun i _ => h1 i)
      _ = 4 * (d : ℝ) := by simp [Finset.sum_const, Finset.card_univ]; ring
  have hkey : ∀ ξ : ℝᵈ, (1 : ℝ) + ‖ξ‖ ^ 2 ≤ Cd * (1 + ‖ξ + η‖ ^ 2) := by
    intro ξ
    rcases lt_or_ge (2 * ‖η‖) ‖ξ‖ with h | h
    · have h1 : ‖ξ‖ / 2 ≤ ‖ξ + η‖ := by
        have hn := norm_sub_le (ξ + η) η
        simp only [add_sub_cancel_right] at hn
        linarith [norm_nonneg (ξ + η), norm_nonneg η]
      have h2 : ‖ξ‖ ^ 2 ≤ 4 * ‖ξ + η‖ ^ 2 := by nlinarith [norm_nonneg ξ, norm_nonneg (ξ + η)]
      have h3 : (1 : ℝ) + ‖ξ‖ ^ 2 ≤ 4 * (1 + ‖ξ + η‖ ^ 2) := by nlinarith [sq_nonneg ‖ξ + η‖]
      have h4 : (4 : ℝ) ≤ Cd := by rw [hCd]; nlinarith [Nat.cast_nonneg (α := ℝ) d]
      nlinarith [h3, h4, sq_nonneg ‖ξ + η‖]
    · have h3 : (1 : ℝ) + ‖ξ‖ ^ 2 ≤ 1 + (2 * ‖η‖) ^ 2 := by
        nlinarith [h, norm_nonneg ξ, norm_nonneg η]
      have h4 : (1 : ℝ) + (2 * ‖η‖) ^ 2 ≤ Cd := by
        rw [hCd]; nlinarith [hηn, Nat.cast_nonneg (α := ℝ) d]
      nlinarith [h3, h4, sq_nonneg ‖ξ + η‖, hCd1]
  have hpt : ∀ ξ : ℝᵈ, (1 + ‖ξ + η‖ ^ 2) ^ (-(d : ℝ))
      ≤ Cd ^ d * (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) := by
    intro ξ
    have h1 : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
    have h2 : (0 : ℝ) < 1 + ‖ξ + η‖ ^ 2 := by positivity
    have h3 : (1 + ‖ξ‖ ^ 2) / Cd ≤ 1 + ‖ξ + η‖ ^ 2 := by
      rw [div_le_iff₀ hCdpos]
      linarith [hkey ξ]
    calc (1 + ‖ξ + η‖ ^ 2) ^ (-(d : ℝ))
        ≤ ((1 + ‖ξ‖ ^ 2) / Cd) ^ (-(d : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (div_pos h1 hCdpos) h3
            (by linarith [Nat.cast_nonneg (α := ℝ) d])
      _ = (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) * Cd ^ (d : ℝ) := by
          rw [Real.div_rpow (le_of_lt h1) (le_of_lt hCdpos), Real.rpow_neg (le_of_lt hCdpos)]
          field_simp
      _ = (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) * Cd ^ d := by rw [Real.rpow_natCast]
      _ = Cd ^ d * (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) := by ring
  have hsub : (∫ ξ, (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) * ‖F (ξ - η)‖ ^ 2)
      = ∫ ξ, (1 + ‖ξ + η‖ ^ 2) ^ (-(d : ℝ)) * ‖F ξ‖ ^ 2 := by
    have hmp : MeasurePreserving (fun ξ : ℝᵈ => ξ + η) (volume : Measure ℝᵈ) (volume : Measure ℝᵈ) :=
      measurePreserving_add_right (volume : Measure ℝᵈ) η
    have hemb : MeasurableEmbedding (fun ξ : ℝᵈ => ξ + η) :=
      (Homeomorph.addRight η).measurableEmbedding
    have h := hmp.integral_comp hemb
      (fun ζ : ℝᵈ => (1 + ‖ζ‖ ^ 2) ^ (-(d : ℝ)) * ‖F (ζ - η)‖ ^ 2)
    simpa [Function.comp, add_sub_cancel_right] using h.symm
  rw [hsub]
  have hIntF : Integrable (fun ξ : ℝᵈ => ‖F ξ‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have hmem : Integrable (fun ξ : ℝᵈ => (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) * ‖F ξ‖ ^ 2) volume := by
    refine Integrable.mono' hIntF ?_ ?_
    · exact ((measurable_hweight (d := d)).aestronglyMeasurable).mul
        (hF.aestronglyMeasurable.norm.pow 2)
    · filter_upwards with ξ
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hweight_nonneg ξ) (sq_nonneg _))]
      exact mul_le_of_le_one_left (sq_nonneg _) (hweight_le_one ξ)
  calc (∫ ξ, (1 + ‖ξ + η‖ ^ 2) ^ (-(d : ℝ)) * ‖F ξ‖ ^ 2)
      ≤ ∫ ξ, Cd ^ d * ((1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) * ‖F ξ‖ ^ 2) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ξ =>
          mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))
          (hmem.const_mul _) (Filter.Eventually.of_forall fun ξ => ?_)
        calc (1 + ‖ξ + η‖ ^ 2) ^ (-(d : ℝ)) * ‖F ξ‖ ^ 2
            ≤ (Cd ^ d * (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ))) * ‖F ξ‖ ^ 2 :=
              mul_le_mul_of_nonneg_right (hpt ξ) (sq_nonneg _)
          _ = Cd ^ d * ((1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) * ‖F ξ‖ ^ 2) := by ring
    _ = Cd ^ d * ∫ ξ, (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) * ‖F ξ‖ ^ 2 := by
        rw [MeasureTheory.integral_const_mul]

/-! ## The localised convolution identity -/

/-- **The localisation identity.**  If `φ` is supported (a.e.) in the cube of radius `c₁/2` and
`x` lies in the concentric sub-cube `locCubesSmall c₁ a` of the localisation cube `locCubes c₁ a`,
then the convolution of `k` with `φ` at `x` only sees the values of `k` on `locCubes c₁ a`. -/
theorem convFun_indicator_eq {c₁ : ℝ} (hc₁ : 0 < c₁) (φ : ℝᵈ → ℂ)
    (hφsupp : ∀ᵐ z ∂(volume : Measure ℝᵈ),
      (∃ i : Fin d, c₁ / 2 < |z i|) → φ z = 0)
    (a : (Fin d → ℤ) → Fin d → ℝ) (k : ℝᵈ → ℂ) :
    ∀ x ∈ locCubesSmall c₁ a,
      Commons.Analysis.Fourier.convFun k φ x
        = Commons.Analysis.Fourier.convFun ((locCubes c₁ a).indicator k) φ x := by
  intro x hx
  rw [Commons.Analysis.Fourier.convFun, Commons.Analysis.Fourier.convFun]
  refine integral_congr_ae ?_
  have hbase : ∀ᵐ y ∂(volume : Measure ℝᵈ),
      (∃ i : Fin d, c₁ / 2 < |(x - y) i|) → φ (x - y) = 0 :=
    (Measure.measurePreserving_sub_left (volume : Measure ℝᵈ) x).quasiMeasurePreserving.ae hφsupp
  filter_upwards [hbase] with y hy
  by_cases hyS : y ∈ locCubes c₁ a
  · rw [Set.indicator_of_mem hyS]
  · have hsep := separation_locCubes hc₁ a x hx y hyS
    obtain ⟨i, hi⟩ := hsep
    have hz : φ (x - y) = 0 := hy ⟨i, by simpa only [PiLp.sub_apply] using hi⟩
    rw [Set.indicator_of_notMem hyS, hz, zero_mul, mul_zero]

/-! ## The indicator of an `L²` class -/

/-- The `L²` class of `S.indicator g` for `g : Lp ℂ 2` and a measurable `S`. -/
noncomputable def subLp (S : Set ℝᵈ) (g : Lp ℂ 2 (volume : Measure ℝᵈ))
    (hS : MeasurableSet S) : Lp ℂ 2 (volume : Measure ℝᵈ) :=
  ((Lp.memLp g).indicator hS).toLp (S.indicator (g : ℝᵈ → ℂ))

lemma subLp_coe (S : Set ℝᵈ) (g : Lp ℂ 2 (volume : Measure ℝᵈ)) (hS : MeasurableSet S) :
    (subLp S g hS : ℝᵈ → ℂ) =ᵐ[volume] S.indicator (g : ℝᵈ → ℂ) := by
  rw [subLp]
  exact MemLp.coeFn_toLp _

lemma norm_subLp_le (S : Set ℝᵈ) (g : Lp ℂ 2 (volume : Measure ℝᵈ)) (hS : MeasurableSet S) :
    ‖subLp S g hS‖ ≤ ‖g‖ := by
  rw [MeasureTheory.Lp.norm_def, MeasureTheory.Lp.norm_def]
  refine ENNReal.toReal_mono (ne_of_lt (Lp.memLp g).2) ?_
  refine eLpNorm_mono_ae ?_
  filter_upwards [subLp_coe S g hS] with x h1
  rw [h1]
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, norm_zero]
    exact norm_nonneg _

/-- `MemLp f 1` implies integrability (without any finiteness assumption on the measure). -/
lemma integrable_of_memLp_one {f : ℝᵈ → ℂ} (hf : MemLp f 1 (volume : Measure ℝᵈ)) :
    Integrable f (volume : Measure ℝᵈ) := by
  refine ⟨hf.1, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm, ← eLpNorm_one_eq_lintegral_enorm]
  exact hf.2

/-- `subLp` is additive (the indicator of a sum is the sum of the indicators). -/
lemma subLp_sub (S : Set ℝᵈ) (g g' : Lp ℂ 2 (volume : Measure ℝᵈ)) (hS : MeasurableSet S) :
    subLp S (g - g') hS = subLp S g hS - subLp S g' hS := by
  classical
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_sub (subLp S g hS) (subLp S g' hS), subLp_coe S (g - g') hS,
    subLp_coe S g hS, subLp_coe S g' hS, Lp.coeFn_sub g g'] with x e5 e3 e1 e2 e4
  rw [e5, Pi.sub_apply, e3, e1, e2, Set.indicator_apply, Set.indicator_apply,
    Set.indicator_apply, e4]
  by_cases hx : x ∈ S
  · simp only [hx, if_true, Pi.sub_apply]
  · simp only [hx, if_false]; ring

/-- **The `L²` bound for a convolution with a damping kernel.**  If the Fourier transform of `φ`
is bounded (a.e.) by the `H^{-d}` weight `⟨ξ⟩^{-d}` — the situation produced by a damping function
— then `‖f * φ‖_{L²} ≤ ‖f‖_{H^{-d}}`.  This is the a.e.-form of the convolution bound needed in
the localised convolution step. -/
lemma norm_convFun_le_hsq {A : ℝ} (h : Lp ℂ 2 (volume : Measure ℝᵈ)) (φf : ℝᵈ → ℂ)
    (hφ1 : MemLp φf 1 (volume : Measure ℝᵈ)) (hφ2 : MemLp φf 2 (volume : Measure ℝᵈ))
    (hφb : ∀ ξ : ℝᵈ, ‖𝓕 φf ξ‖ ≤ A)
    (hφw : ∀ᵐ ξ ∂(volume : Measure ℝᵈ),
      ‖𝓕 φf ξ‖ ≤ (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ) / 2)) :
    ‖(Commons.Analysis.Fourier.memLp_convFun_two (Lp.memLp h)
        (integrable_of_memLp_one hφ1)).toLp
        (Commons.Analysis.Fourier.convFun (h : ℝᵈ → ℂ) φf)‖ ^ 2 ≤ hsq h := by
  set kLp : Lp ℂ 2 (volume : Measure ℝᵈ) := (Commons.Analysis.Fourier.memLp_convFun_two
    (Lp.memLp h) (integrable_of_memLp_one hφ1)).toLp
    (Commons.Analysis.Fourier.convFun (h : ℝᵈ → ℂ) φf) with hkLp
  have hconv := Commons.Analysis.Fourier.fourier_convFun_ae d (f := (h : ℝᵈ → ℂ)) (φ := φf) (A := A)
    (Lp.memLp h) (integrable_of_memLp_one hφ1) hφ2 hφb
  have hconv' : ((𝓕 kLp : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) =ᵐ[volume]
      fun ξ => ((𝓕 h : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ * 𝓕 φf ξ := by
    filter_upwards [hconv] with ξ e1
    rw [e1, Lp.toLp_coeFn h (Lp.memLp h)]
  have hInt1 : Integrable
      (fun ξ : ℝᵈ => ‖((𝓕 kLp : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp (𝓕 kLp)).aestronglyMeasurable).mp
      (Lp.memLp (𝓕 kLp))
  have hInt2 : Integrable (fun ξ : ℝᵈ => (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) *
      ‖((𝓕 h : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ‖ ^ 2) volume := by
    refine Integrable.mono'
      ((memLp_two_iff_integrable_sq_norm (Lp.memLp (𝓕 h)).aestronglyMeasurable).mp
        (Lp.memLp (𝓕 h))) ?_ ?_
    · exact (measurable_hweight (d := d)).aestronglyMeasurable.mul
        ((Lp.memLp (𝓕 h)).aestronglyMeasurable.norm.pow 2)
    · filter_upwards with ξ
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hweight_nonneg ξ) (sq_nonneg _))]
      exact mul_le_of_le_one_left (sq_nonneg _) (hweight_le_one ξ)
  have hmain : ∫ ξ, ‖((𝓕 kLp : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ‖ ^ 2
      ≤ ∫ ξ, (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) *
          ‖((𝓕 h : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ‖ ^ 2 := by
    refine integral_mono_ae hInt1 hInt2 ?_
    filter_upwards [hconv', hφw] with ξ e1 e2
    rw [e1, norm_mul, mul_pow]
    have h3 : ‖𝓕 φf ξ‖ ^ 2 ≤ (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) := by
      calc ‖𝓕 φf ξ‖ ^ 2 ≤ ((1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ) / 2)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) e2 2
        _ = (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) := by
            rw [← Real.rpow_natCast ((1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ) / 2)) 2,
              ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2)]
            norm_num
    calc ‖((𝓕 h : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ‖ ^ 2 * ‖𝓕 φf ξ‖ ^ 2
        ≤ ‖((𝓕 h : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ‖ ^ 2 * (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) :=
          mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
      _ = (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) *
            ‖((𝓕 h : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ‖ ^ 2 := by ring
  have hnorm : ‖kLp‖ ^ 2 = ∫ ξ, ‖((𝓕 kLp : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ‖ ^ 2 := by
    rw [← MeasureTheory.Lp.norm_fourier_eq kLp,
      Commons.Analysis.Fourier.lp_integral_norm_sq (𝓕 kLp)]
  rw [hnorm]
  exact hmain

/-- Modulating and then restricting to `S` is the same as restricting and then modulating. -/
lemma subLp_modEta (S : Set ℝᵈ) (hS : MeasurableSet S) (h : Lp ℂ 2 (volume : Measure ℝᵈ))
    (η : ℝᵈ) :
    subLp S ((memLp_modEta (Lp.memLp h)).toLp (modEta η (h : ℝᵈ → ℂ))) hS
      = (memLp_modEta ((Lp.memLp h).indicator hS)).toLp
          (modEta η (S.indicator (h : ℝᵈ → ℂ))) := by
  have hL : (subLp S ((memLp_modEta (Lp.memLp h)).toLp (modEta η (h : ℝᵈ → ℂ))) hS : ℝᵈ → ℂ)
      =ᵐ[volume] S.indicator (modEta η (h : ℝᵈ → ℂ)) := by
    refine (subLp_coe _ _ hS).trans ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_modEta (Lp.memLp h))] with x e
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, e]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  have hR : ((memLp_modEta ((Lp.memLp h).indicator hS)).toLp
      (modEta η (S.indicator (h : ℝᵈ → ℂ))) : ℝᵈ → ℂ)
      =ᵐ[volume] modEta η (S.indicator (h : ℝᵈ → ℂ)) :=
    MemLp.coeFn_toLp (memLp_modEta ((Lp.memLp h).indicator hS))
  have hpt : ∀ x : ℝᵈ, S.indicator (modEta η (h : ℝᵈ → ℂ)) x
      = modEta η (S.indicator (h : ℝᵈ → ℂ)) x := by
    intro x
    by_cases hx : x ∈ S
    · simp only [Set.indicator_of_mem hx, modEta]
    · simp only [Set.indicator_of_notMem hx, modEta, mul_zero]
  refine Lp.ext ?_
  filter_upwards [hL, hR] with x e1 e2
  rw [e1, e2, hpt x]

/-- **The `H^{-d}` norm of a modulation is comparable to that of the function itself**, with the
constant `(40(1+d))^d` for shifts in `[-2,2]^d`. -/
lemma hsq_modEta_le {η : ℝᵈ} (hη : ∀ i : Fin d, |η i| ≤ 2) (h : Lp ℂ 2 (volume : Measure ℝᵈ)) :
    hsq ((memLp_modEta (Lp.memLp h)).toLp (modEta η (h : ℝᵈ → ℂ)))
      ≤ (40 * ((d : ℝ) + 1)) ^ d * hsq h := by
  have hFmem : MemLp ((𝓕 h : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) 2 volume := Lp.memLp _
  have h1 : (∫ ξ, (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) * ‖((𝓕 ((memLp_modEta (Lp.memLp h)).toLp
        (modEta η (h : ℝᵈ → ℂ))) : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ‖ ^ 2)
      = ∫ ξ, (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) *
          ‖((𝓕 h : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) (ξ - η)‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [fourier_modEta (η := η) (Lp.memLp h)] with ξ e
    rw [e, Lp.toLp_coeFn h (Lp.memLp h)]
  rw [hsq, hsq, h1]
  exact weight_shift_le hη hFmem

/-! ## The explicit constants of the single-scale estimate -/

/-- `Θ(r) = (log (2+r))^{-α}` (Han–Schlag–Cohen). -/
noncomputable def Theta (α r : ℝ) : ℝ := (Real.log (2 + r)) ^ (-α)

/-- The frequency weight parameter `q = c₃Θ(R)/(2π)` (so that `4πq = 2c₃Θ(R)`). -/
noncomputable def qOf (c₃ α R : ℝ) : ℝ := c₃ * Theta α R / (2 * Real.pi)

/-- The constant multiplying the localisation term in the single-scale estimate. -/
noncomputable def scaleBeta (d : ℕ) (c₃ α R κ C : ℝ) : ℝ :=
  2 * Real.exp (C / qOf c₃ α R) * (2 : ℝ) ^ κ * (40 * ((d : ℝ) + 1)) ^ d * (1 + R ^ 2) ^ d

/-- The constant multiplying the `hsq h` term (the "bad" term) of the single-scale estimate. -/
noncomputable def scaleGamma (d : ℕ) (c₃ α R κ C : ℝ) : ℝ :=
  2 * Real.exp (C / qOf c₃ α R) * (2 : ℝ) ^ κ * (40 * ((d : ℝ) + 1)) ^ d * (1 + R ^ 2) ^ (2 * d)
      * Real.exp (-(2 * κ * c₃ * Theta α R * R))
    + 2 * (40 * ((d : ℝ) + 1)) ^ d * (1 + R ^ 2) ^ d * Real.exp (-(2 * c₃ * Theta α R * R))

end Submission.FUP
