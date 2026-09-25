import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.Lacunary.defs
import Submission.Work.BourgainPlan.Oscillation.lacunary_truncated_maximal_l2
import Submission.Work.BourgainPlan.Oscillation.oscZ_lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.Lacunary.cesaro_defs
import Submission.Work.BourgainPlan.Oscillation.Lacunary.cesaro_props
import Submission.Work.BourgainPlan.Oscillation.Lacunary.cesaro_second_half

/-!
# Assembly of the Cesàro (`P = X`) lacunary oscillation inequality

The Cesàro multiplier `m_N(θ) = N⁻¹(e^{2πiNθ}-1)/(e^{2πiθ}-1)` factors as `h(Nθ)·r(θ)` with the
*profile* `h = cesH` and the *weight* `r = cesR`.  The weight has a pole at `θ = 1`, so the circle
is split at `1/2`:

* on the first half `(0,1/2]` the truncated weight `cesRT = 1_{(0,1/2]}·r` is bounded by `π/2`, and
  the Cesàro family *is* the weighted dilation family `cesRT·cesH(⌊ρ^i⌋·)`;
* on the second half the half-circle symmetry `m_N(1-ε) = conj (m_N ε)` converts the family into
  the *conjugate* of the same weighted dilation family taken with the complex-conjugated data.

Both halves are therefore bounded by the dilation-profile input `DilProfile`; the weighted cut
inputs (`WgtCut` for a fixed shift, `TScale` for the physical radii `t/⌊ρ^i⌋`) provide the profile
decomposition, and `ProfileData` supplies the Cesàro profile facts.
-/

namespace Work.BourgainPlan.Oscillation.Lacunary

open Finset MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-! ## Elementary helpers -/

lemma enorm_conj (z : ℂ) : ‖(starRingEnd ℂ) z‖ₑ = ‖z‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, Complex.norm_conj]

/-- Conjugating the values of a family does not change its block oscillation. -/
lemma oscZ_conj (A : ℕ → ℤ → ℂ) (J : ℕ) (k : ℕ → ℕ) :
    Work.BourgainPlan.Oscillation.oscZ (fun i x => (starRingEnd ℂ) (A i x)) J k
      = Work.BourgainPlan.Oscillation.oscZ A J k := by
  unfold Work.BourgainPlan.Oscillation.oscZ
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine lintegral_congr (fun x => ?_)
  refine congrArg (fun z : ℝ≥0∞ => z ^ (2:ℝ)) ?_
  refine iSup_congr (fun i => ?_)
  refine iSup_congr (fun _ => ?_)
  rw [← map_sub]
  exact enorm_conj _

/-- Interval integrability from a bound on `(a,b]`. -/
lemma intervalIntegrable_of_Ioc_bound {a b : ℝ} (hab : a ≤ b) {h : ℝ → ℂ} (hh : Measurable h)
    {C : ℝ} (hC : ∀ θ ∈ Set.Ioc a b, ‖h θ‖ ≤ C) : IntervalIntegrable h volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact Integrable.of_bound hh.aestronglyMeasurable.restrict C
    (ae_restrict_of_forall_mem measurableSet_Ioc hC)

/-- On the first half circle the Cesàro multiplier is the profile multiplier. -/
lemma cesM_eq_profile_of_mem (N : ℕ) (hN : 1 ≤ N) {θ : ℝ} (hθ : θ ∈ Set.Ioc (0:ℝ) (1/2)) :
    cesM N θ = cesH ((N:ℝ) * θ) * cesRT θ := by
  have h1 : θ ∈ Set.Ioc (0:ℝ) 1 := ⟨hθ.1, by linarith [hθ.2]⟩
  rw [cesM_eq_cesH_cesR N hN h1, cesRT, if_pos ⟨hθ.1, hθ.2⟩]

lemma cesRT_eq_zero_of_lt (θ : ℝ) (h : 1/2 < θ) : cesRT θ = 0 := by
  rw [cesRT, if_neg]; rintro ⟨-, h2⟩; linarith

/-! ## The first-half reduction -/

/-- **The first-half reduction.**  On `(0,1/2]` the Cesàro multiplier *is* the profile multiplier
`cesRT·cesH(⌊ρ^i⌋·)`, and the profile multiplier vanishes on `(1/2,1]`; hence the Cesàro integral
over the first half circle equals the *full circle* profile integral. -/
lemma cesaro_first_half (N : ℕ) (hN : 1 ≤ N) (f : ℤ → ℂ) (s : Finset ℤ)
    (hs : ∀ n, n ∉ s → f n = 0) (x : ℤ) :
    (∫ θ in (0:ℝ)..((1:ℝ)/2),
        cesM N θ * (∑ j ∈ s, f j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
          Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ))))
      = ∫ θ in (0:ℝ)..1,
          (cesRT θ * cesH ((N:ℝ) * θ)) *
            (∑ j ∈ s, f j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
            Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ))) := by
  set P : ℝ → ℂ := fun θ =>
    ∑ j ∈ s, f j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ))) with hP
  have hPbd : ∀ θ, ‖P θ‖ ≤ ∑ j ∈ s, ‖f j‖ := by
    intro θ
    rw [hP]
    refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [norm_mul, show 2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ))
          = ((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hPmeas : Measurable P := by
    rw [hP]; fun_prop
  have hEchar_norm : ∀ θ : ℝ,
      ‖Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))‖ = 1 := by
    intro θ
    rw [Complex.norm_exp]
    have : (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ))).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [this, Real.exp_zero]
  have hEchar_meas : Measurable (fun θ : ℝ =>
      Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))) :=
    Complex.measurable_exp.comp (by fun_prop)
  have hcesMmeas : Measurable (cesM N) := by
    unfold cesM
    exact (measurable_const.mul
      (((Complex.measurable_exp.comp (by fun_prop)).sub measurable_const).div
        ((Complex.measurable_exp.comp (by fun_prop)).sub measurable_const)))
  have hmeasc : Measurable (fun θ : ℝ => cesM N θ * P θ *
      Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))) :=
    Measurable.mul (Measurable.mul hcesMmeas hPmeas) hEchar_meas
  have hbd1 : ∀ θ ∈ Set.Ioc (0:ℝ) ((1:ℝ)/2),
      ‖cesM N θ * P θ * Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))‖
        ≤ ∑ j ∈ s, ‖f j‖ := by
    intro θ hθ
    rw [norm_mul, norm_mul, hEchar_norm θ, mul_one]
    exact le_trans (mul_le_mul (cesM_norm_le_one N hN ⟨hθ.1, by linarith [hθ.2]⟩) (hPbd θ)
      (norm_nonneg _) (by norm_num)) (le_of_eq (one_mul _))
  have hmeasp : Measurable (fun θ : ℝ => (cesRT θ * cesH ((N:ℝ) * θ)) * P θ *
      Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))) :=
    Measurable.mul (Measurable.mul (Measurable.mul measurable_cesRT
      (measurable_cesH.comp (by fun_prop))) hPmeas) hEchar_meas
  have hbd2 : ∀ θ ∈ Set.Ioc (0:ℝ) 1,
      ‖(cesRT θ * cesH ((N:ℝ) * θ)) * P θ *
        Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))‖
        ≤ Real.pi / 2 * (∑ j ∈ s, ‖f j‖) := by
    intro θ _
    rw [norm_mul, norm_mul, norm_mul, hEchar_norm θ, mul_one]
    calc ‖cesRT θ‖ * ‖cesH ((N:ℝ) * θ)‖ * ‖P θ‖
        ≤ (Real.pi / 2 * 1) * (∑ j ∈ s, ‖f j‖) := by
          refine mul_le_mul (mul_le_mul (cesRT_norm_le θ) (cesH_norm_le_one _)
            (norm_nonneg _) (by positivity)) (hPbd θ) (norm_nonneg _) (by positivity)
      _ = Real.pi / 2 * (∑ j ∈ s, ‖f j‖) := by ring
  have hcongr : (∫ θ in (0:ℝ)..((1:ℝ)/2), cesM N θ * P θ *
        Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ))))
      = ∫ θ in (0:ℝ)..((1:ℝ)/2), (cesRT θ * cesH ((N:ℝ) * θ)) * P θ *
          Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ))) := by
    refine intervalIntegral.integral_congr (fun θ hθ => ?_)
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ (1:ℝ)/2)] at hθ
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      simp [cesM, cesH, cesRT]
    · rw [cesM_eq_profile_of_mem N hN ⟨h0, hθ.2⟩]
      ring
  have hzero : (∫ θ in ((1:ℝ)/2)..1, (cesRT θ * cesH ((N:ℝ) * θ)) * P θ *
      Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))) = 0 := by
    rw [show (0 : ℂ) = ∫ θ in ((1:ℝ)/2)..1, (0:ℂ) from by simp]
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun θ hθ => ?_))
    rw [Set.uIoc_of_le (by norm_num : (1:ℝ)/2 ≤ 1)] at hθ
    rw [cesRT_eq_zero_of_lt θ hθ.1]; ring
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (intervalIntegrable_of_Ioc_bound (C := Real.pi / 2 * (∑ j ∈ s, ‖f j‖))
      (by norm_num : (0:ℝ) ≤ (1:ℝ)/2) hmeasp (fun θ hθ => hbd2 θ ⟨hθ.1, by linarith [hθ.2]⟩))
    (intervalIntegrable_of_Ioc_bound (C := Real.pi / 2 * (∑ j ∈ s, ‖f j‖))
      (by norm_num : (1:ℝ)/2 ≤ 1) hmeasp (fun θ hθ => hbd2 θ ⟨by linarith [hθ.1], hθ.2⟩))
  rw [← hsplit, hcongr, hzero, add_zero]

/-! ## The half-circle splitting -/

/-- **The half-circle splitting of the Cesàro integral.** -/
lemma cesaro_half_identity (N : ℕ) (hN : 1 ≤ N) (f : ℤ → ℂ) (s : Finset ℤ)
    (hs : ∀ n, n ∉ s → f n = 0) (x : ℤ) :
    (∫ θ in (0:ℝ)..1,
        cesM N θ * (∑ j ∈ s, f j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
        Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ))))
      = (∫ θ in (0:ℝ)..1,
          (cesRT θ * cesH ((N:ℝ) * θ)) *
          (∑ j ∈ s, f j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
          Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ))))
        + (∫ θ in ((1:ℝ)/2)..1,
          cesM N θ * (∑ j ∈ s, f j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
          Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))) := by
  set P : ℝ → ℂ := fun θ =>
    ∑ j ∈ s, f j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ))) with hP
  have hPbd : ∀ θ, ‖P θ‖ ≤ ∑ j ∈ s, ‖f j‖ := by
    intro θ
    rw [hP]
    refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [norm_mul, show 2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ))
          = ((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hPmeas : Measurable P := by
    rw [hP]; fun_prop
  have hEchar_norm : ∀ θ : ℝ,
      ‖Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))‖ = 1 := by
    intro θ
    rw [Complex.norm_exp]
    have : (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ))).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [this, Real.exp_zero]
  have hEchar_meas : Measurable (fun θ : ℝ =>
      Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))) :=
    Complex.measurable_exp.comp (by fun_prop)
  have hcesMmeas : Measurable (cesM N) := by
    unfold cesM
    exact (measurable_const.mul
      (((Complex.measurable_exp.comp (by fun_prop)).sub measurable_const).div
        ((Complex.measurable_exp.comp (by fun_prop)).sub measurable_const)))
  have hAi : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ 1 →
      IntervalIntegrable (fun θ : ℝ => cesM N θ * P θ *
        Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))) volume a b := by
    intro a b ha hab hb
    refine intervalIntegrable_of_Ioc_bound (C := ∑ j ∈ s, ‖f j‖) hab
      (Measurable.mul (Measurable.mul hcesMmeas hPmeas) hEchar_meas) (fun θ hθ => ?_)
    rw [norm_mul, norm_mul, hEchar_norm θ, mul_one]
    exact le_trans (mul_le_mul (cesM_norm_le_one N hN ⟨by linarith [ha, hθ.1],
      by linarith [hθ.2, hb]⟩) (hPbd θ) (norm_nonneg _) (by norm_num))
      (le_of_eq (one_mul _))
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hAi (a := 0) (b := (1:ℝ)/2) (by norm_num) (by norm_num) (by norm_num))
    (hAi (a := (1:ℝ)/2) (b := 1) (by norm_num) (by norm_num) (by norm_num))
  rw [← hsplit, cesaro_first_half N hN f s hs x]

/-! ## The assembly -/

theorem cesaro_mult_oscZ_of_parts (ρ : ℝ) (hρ : 1 < ρ)
    (hw : WgtCutExists ρ) (ht : ∀ C₁, 0 < C₁ → WgtCut ρ C₁ → TScaleExists ρ)
    (hd : ∀ C₂, 0 < C₂ → TScale ρ C₂ → DilProfileExists ρ) (hp : ProfileData ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : ℕ) (k : ℕ → ℕ), StrictMono k →
      ∀ (f : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → f n = 0) →
        Work.BourgainPlan.Oscillation.oscZ (fun i x =>
            ∫ θ in (0:ℝ)..1,
              (((Work.BourgainPlan.Oscillation.lacScale ρ i : ℂ))⁻¹ *
                ((Complex.exp (2 * Real.pi * Complex.I *
                    ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) * θ)) - 1) /
                 (Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ)) - 1))) *
              (∑ j ∈ s, f j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
              Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))) J k
          ≤ ENNReal.ofReal (C^2) *
              ∫⁻ x : ℤ, ‖f x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
  obtain ⟨Cw, hCw, hw'⟩ := hw
  obtain ⟨C₂, hC₂, ht'⟩ := ht Cw hCw hw'
  obtain ⟨C₃, hC₃, hd'⟩ := hd C₂ hC₂ ht'
  obtain ⟨A, M, hA, hM, hst, hMbd, htail⟩ := hp
  set K : ℝ := C₃ * (Real.pi / 2) * (M + A) with hK
  refine ⟨Real.sqrt (8 * K^2 + 1), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro J k hk f s hs
  set f' : ℤ → ℂ := fun j => (starRingEnd ℂ) (f j) with hf'
  have hs' : ∀ n, n ∉ s → f' n = 0 := by
    intro n hn
    rw [hf']
    simp [hs n hn]
  set B1 : ℕ → ℤ → ℂ := fun i x =>
      ∫ θ in (0:ℝ)..1,
        (cesRT θ * cesH ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) * θ)) *
        (∑ j ∈ s, f j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
        Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ))) with hB1
  set B2 : ℕ → ℤ → ℂ := fun i x =>
      ∫ θ in (0:ℝ)..1,
        (cesRT θ * cesH ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) * θ)) *
        (∑ j ∈ s, f' j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
        Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ))) with hB2
  have hb : ∀ (g : ℤ → ℂ), (∀ n, n ∉ s → g n = 0) →
      Work.BourgainPlan.Oscillation.oscZ (fun i x =>
          ∫ θ in (0:ℝ)..1,
            (cesRT θ * cesH ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) * θ)) *
            (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
            Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))) J k
        ≤ ENNReal.ofReal (K^2) * ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
    intro g hg
    have h := hd' cesH cesH1 cesH2 cesHd measurable_cesH measurable_cesH1 measurable_cesH2
      measurable_cesHd A M hA.le hM.le cesH_split hst hMbd htail cesRT measurable_cesRT
      (Real.pi / 2) (by positivity) cesRT_norm_le J k hk g s hg
    simpa only [mul_assoc, hK] using h
  have hB1bd := hb f hs
  have hB2bd := hb f' hs'
  have hfl : (∫⁻ x : ℤ, ‖f' x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count)
      = ∫⁻ x : ℤ, ‖f x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
    rw [hf']
    refine lintegral_congr (fun x => ?_)
    rw [enorm_conj]
  have hdec : ∀ i x,
      (∫ θ in (0:ℝ)..1,
          cesM (Work.BourgainPlan.Oscillation.lacScale ρ i) θ *
          (∑ j ∈ s, f j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
          Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ))))
        = B1 i x + (starRingEnd ℂ) (B2 i x) := by
    intro i x
    have hN : 1 ≤ Work.BourgainPlan.Oscillation.lacScale ρ i :=
      one_le_lacScale ρ hρ.le i
    rw [cesaro_half_identity (Work.BourgainPlan.Oscillation.lacScale ρ i) hN f s hs x,
      cesaro_second_half (Work.BourgainPlan.Oscillation.lacScale ρ i) hN x f s hs]
  have hfam : (fun i x => ∫ θ in (0:ℝ)..1,
        (((Work.BourgainPlan.Oscillation.lacScale ρ i : ℂ))⁻¹ *
          ((Complex.exp (2 * Real.pi * Complex.I *
              ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) * θ)) - 1) /
           (Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ)) - 1))) *
        (∑ j ∈ s, f j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
        Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ))))
      = fun i x => B1 i x + (starRingEnd ℂ) (B2 i x) := by
    funext i x
    simpa only [cesM] using hdec i x
  have hstep1 : Work.BourgainPlan.Oscillation.oscZ
        (fun i x => B1 i x + (starRingEnd ℂ) (B2 i x)) J k
      ≤ 4 * Work.BourgainPlan.Oscillation.oscZ B1 J k
        + 4 * Work.BourgainPlan.Oscillation.oscZ
            (fun i x => (starRingEnd ℂ) (B2 i x)) J k :=
    oscZ_add_le (fun i x => B1 i x + (starRingEnd ℂ) (B2 i x)) B1
      (fun i x => (starRingEnd ℂ) (B2 i x)) (fun i x => by ring) J k
  have hstep2 : Work.BourgainPlan.Oscillation.oscZ
        (fun i x => (starRingEnd ℂ) (B2 i x)) J k
      = Work.BourgainPlan.Oscillation.oscZ B2 J k := oscZ_conj B2 J k
  have hB1bd' : Work.BourgainPlan.Oscillation.oscZ B1 J k
      ≤ ENNReal.ofReal (K^2) * ∫⁻ x : ℤ, ‖f x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := hB1bd
  have hB2bd' : Work.BourgainPlan.Oscillation.oscZ B2 J k
      ≤ ENNReal.ofReal (K^2) * ∫⁻ x : ℤ, ‖f x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
    simpa only [hfl] using hB2bd
  calc Work.BourgainPlan.Oscillation.oscZ (fun i x => ∫ θ in (0:ℝ)..1,
        (((Work.BourgainPlan.Oscillation.lacScale ρ i : ℂ))⁻¹ *
          ((Complex.exp (2 * Real.pi * Complex.I *
              ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) * θ)) - 1) /
           (Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ)) - 1))) *
        (∑ j ∈ s, f j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
        Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))) J k
      = Work.BourgainPlan.Oscillation.oscZ
          (fun i x => B1 i x + (starRingEnd ℂ) (B2 i x)) J k := by rw [hfam]
    _ ≤ 4 * Work.BourgainPlan.Oscillation.oscZ B1 J k
          + 4 * Work.BourgainPlan.Oscillation.oscZ
              (fun i x => (starRingEnd ℂ) (B2 i x)) J k := hstep1
    _ = 4 * Work.BourgainPlan.Oscillation.oscZ B1 J k
          + 4 * Work.BourgainPlan.Oscillation.oscZ B2 J k := by rw [hstep2]
    _ ≤ 4 * (ENNReal.ofReal (K^2) *
            ∫⁻ x : ℤ, ‖f x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count)
          + 4 * (ENNReal.ofReal (K^2) *
            ∫⁻ x : ℤ, ‖f x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) :=
        add_le_add (mul_le_mul_of_nonneg_left hB1bd' (by norm_num))
          (mul_le_mul_of_nonneg_left hB2bd' (by norm_num))
    _ = ENNReal.ofReal (8 * K^2) *
          ∫⁻ x : ℤ, ‖f x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
        have h8 : (8 : ℝ≥0∞) * ENNReal.ofReal (K^2) = ENNReal.ofReal (8 * K^2) := by
          rw [show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by norm_num,
            ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 8)]
        rw [← add_mul, show (4 : ℝ≥0∞) + 4 = (8 : ℝ≥0∞) by norm_num, ← mul_assoc, h8]
    _ ≤ ENNReal.ofReal (8 * K^2 + 1) *
          ∫⁻ x : ℤ, ‖f x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count :=
        mul_le_mul_of_nonneg_right
          (ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg K])) bot_le
    _ = ENNReal.ofReal ((Real.sqrt (8 * K^2 + 1)) ^ 2) *
          ∫⁻ x : ℤ, ‖f x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
        rw [Real.sq_sqrt (by positivity)]

end

end Work.BourgainPlan.Oscillation.Lacunary
