import Mathlib
import Submission.Work.FatouL1.cauchyLineBound
import Submission.Work.FatouL1.hcLineMass
import Submission.Work.FatouL1.hcSliceFubini
import Submission.Work.FatouL1.hcExistsSigma
import Submission.Work.FatouL1.hcKernelDecay
import Submission.Work.FatouL1.hcLineIntBound
import Submission.Work.FatouL1.hcLineIntKernel

namespace Work.FatouL1

open MeasureTheory Filter intervalIntegral
open scoped Topology ENNReal

noncomputable section

/-- The two-line Cauchy representation of a holomorphic function of bounded line mass on a strip. -/
theorem hcStripRep {a b m : ℝ} {h : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ h {z : ℂ | a < z.re ∧ z.re < b})
    (hint : ∀ x ∈ Set.Ioo a b, MeasureTheory.Integrable (fun y : ℝ => h ((x : ℂ) + y * Complex.I)))
    (hmass : ∀ x ∈ Set.Ioo a b, ∫⁻ y : ℝ, ENNReal.ofReal ‖h ((x : ℂ) + y * Complex.I)‖ ≤ ENNReal.ofReal m)
    {x₁ x₂ : ℝ} (h₁ : x₁ ∈ Set.Ioo a b) (h₂ : x₂ ∈ Set.Ioo a b) (h12 : x₁ < x₂)
    {z : ℂ} (hz₁ : x₁ < z.re) (hz₂ : z.re < x₂) :
    h z = (1 / (2 * Real.pi)) *
      ((∫ y : ℝ, h ((x₂ : ℂ) + y * Complex.I) / (((x₂ : ℂ) + y * Complex.I) - z))
       - (∫ y : ℝ, h ((x₁ : ℂ) + y * Complex.I) / (((x₁ : ℂ) + y * Complex.I) - z))) := by
  obtain ⟨hGc, hGb⟩ := hcSliceFubini hhol hint hmass h₁ h₂ h12
  set G : ℝ → ℝ := fun Y => ∫ x : ℝ in x₁..x₂, ‖h ((x : ℂ) + Y * Complex.I)‖ with hGdef
  have hGnn : ∀ Y : ℝ, 0 ≤ G Y := by
    intro Y; rw [hGdef]
    exact intervalIntegral.integral_nonneg_of_forall h12.le (fun x => norm_nonneg _)
  set K : ℝ := (x₂ - x₁) * max m 0 with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]; exact mul_nonneg (by linarith) (le_max_right _ _)
  have hGb' : ∀ Y₁ Y₂ : ℝ, Y₁ ≤ Y₂ → ∫ Y : ℝ in Y₁..Y₂, G Y ≤ K := by
    intro Y₁ Y₂ h; rw [hGdef, hKdef]; exact hGb Y₁ Y₂ h
  have hmem : ∀ x ∈ Set.uIcc x₁ x₂, a < x ∧ x < b := by
    intro x hx
    rw [Set.uIcc_of_le h12.le] at hx
    exact ⟨lt_of_lt_of_le h₁.1 hx.1, lt_of_le_of_lt hx.2 h₂.2⟩
  have hholR : ∀ Y : ℝ, ContinuousOn (fun x : ℝ => h ((x : ℂ) + Y * Complex.I)) (Set.uIcc x₁ x₂) := by
    intro Y
    refine hhol.continuousOn.comp ?_ ?_
    · fun_prop
    · intro x hx
      have hx' := hmem x hx
      rw [Set.mem_ofPred_eq]
      have hre : ((x : ℂ) + Y * Complex.I).re = x := by simp
      rw [hre]; exact hx'
  -- the sequence sigma
  have hσ : ∀ n : ℕ, ∃ σ : ℝ, (|z.im| + (n:ℝ) + 1) ≤ σ ∧ σ ≤ 2 * (|z.im| + (n:ℝ) + 1) ∧
      G (σ) + G (-σ) ≤ 2 * K / (|z.im| + (n:ℝ) + 1) := by
    intro n
    have hN : 0 < |z.im| + (n : ℝ) + 1 := by positivity
    have h := hcExistsSigma (y₀ := 0) (N := |z.im| + (n : ℝ) + 1) hKnn hGc hGnn hGb' hN
    simpa using h
  choose σ hσ using hσ
  have hσlo : ∀ n : ℕ, (|z.im| + (n:ℝ) + 1) ≤ σ n := fun n => (hσ n).1
  have hσhi : ∀ n : ℕ, σ n ≤ 2 * (|z.im| + (n:ℝ) + 1) := fun n => (hσ n).2.1
  have hσsmall : ∀ n : ℕ, G (σ n) + G (-(σ n)) ≤ 2 * K / (|z.im| + (n:ℝ) + 1) := fun n => (hσ n).2.2
  have hσgt : ∀ n : ℕ, |z.im| < σ n := by
    intro n
    have h1 := hσlo n
    have h2 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have h3 : (0:ℝ) ≤ |z.im| := abs_nonneg _
    linarith
  have hσpos : ∀ n : ℕ, 0 < σ n := fun n => lt_of_le_of_lt (abs_nonneg z.im) (hσgt n)
  have hσtop : Tendsto σ atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    have h1 := hσlo n
    have h3 : (0:ℝ) ≤ |z.im| := abs_nonneg _
    linarith
  have hσneg : Tendsto (fun n : ℕ => -(σ n)) atTop atBot := tendsto_neg_atTop_atBot.comp hσtop
  have hbdd0 : Tendsto (fun n : ℕ => 2 * K / (|z.im| + (n:ℝ) + 1)) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => (|z.im| + (n:ℝ) + 1)) atTop atTop := by
      refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
      have h3 : (0:ℝ) ≤ |z.im| := abs_nonneg _
      linarith
    have h := (tendsto_const_nhds (x := (2*K))).div_atTop h1
    simpa using h
  have hGsum : Tendsto (fun n : ℕ => G (σ n) + G (-(σ n))) atTop (nhds 0) :=
    squeeze_zero (fun n => by have a := hGnn (σ n); have b := hGnn (-(σ n)); linarith)
      (fun n => hσsmall n) hbdd0
  have hden1 : ∀ n : ℕ, 1 ≤ σ n - |z.im| := by
    intro n
    have h1 := hσlo n
    have h2 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have h3 : (0:ℝ) ≤ |z.im| := abs_nonneg _
    linarith
  -- horizontal estimate
  have hhoriz : ∀ Y : ℝ, |z.im| < |Y| →
      ‖∫ x : ℝ in x₁..x₂, h ((x : ℂ) + Y * Complex.I) / (((x : ℂ) + Y * Complex.I) - z)‖
        ≤ G Y / (|Y| - |z.im|) := by
    intro Y hY
    have hpos : 0 < |Y| - |z.im| := sub_pos.mpr hY
    have hle : x₁ ≤ x₂ := h12.le
    have hIb : IntervalIntegrable (fun x : ℝ => ‖h ((x : ℂ) + Y * Complex.I)‖ * (|Y| - |z.im|)⁻¹) volume x₁ x₂ :=
      ((hholR Y).norm.intervalIntegrable).mul_const _
    have hpoint : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.Ioc x₁ x₂ →
        ‖h ((x : ℂ) + Y * Complex.I) / (((x : ℂ) + Y * Complex.I) - z)‖
          ≤ ‖h ((x : ℂ) + Y * Complex.I)‖ * (|Y| - |z.im|)⁻¹ := by
      refine Eventually.of_forall (fun x hx => ?_)
      have hden : |Y| - |z.im| ≤ ‖((x : ℂ) + Y * Complex.I) - z‖ := by
        have h1 := Complex.abs_im_le_norm (((x : ℂ) + Y * Complex.I) - z)
        have him : (((x : ℂ) + Y * Complex.I) - z).im = Y - z.im := by simp
        rw [him] at h1
        have htri : |Y| ≤ |z.im| + |Y - z.im| := by
          have h := abs_add_le z.im (Y - z.im)
          rwa [show z.im + (Y - z.im) = Y from by ring] at h
        linarith
      rw [norm_div]
      exact le_trans (div_le_div_of_nonneg_left (norm_nonneg _) hpos hden)
        (le_of_eq (div_eq_mul_inv _ _))
    have hstep := intervalIntegral.norm_integral_le_of_norm_le hle hpoint hIb
    calc ‖∫ x : ℝ in x₁..x₂, h ((x : ℂ) + Y * Complex.I) / (((x : ℂ) + Y * Complex.I) - z)‖
        ≤ ∫ x : ℝ in x₁..x₂, ‖h ((x : ℂ) + Y * Complex.I)‖ * (|Y| - |z.im|)⁻¹ := hstep
      _ = (∫ x : ℝ in x₁..x₂, ‖h ((x : ℂ) + Y * Complex.I)‖) * (|Y| - |z.im|)⁻¹ :=
          intervalIntegral.integral_mul_const _ _
      _ = G Y / (|Y| - |z.im|) := by rw [hGdef, div_eq_mul_inv]
  have hAbot : ∀ n : ℕ,
      ‖∫ x : ℝ in x₁..x₂, h ((x : ℂ) + (-(σ n)) * Complex.I) / (((x : ℂ) + (-(σ n)) * Complex.I) - z)‖
        ≤ G (-(σ n)) / (σ n - |z.im|) := by
    intro n
    have h := hhoriz (-(σ n)) (by rw [abs_neg, abs_of_pos (hσpos n)]; exact hσgt n)
    simpa [abs_neg, abs_of_pos (hσpos n)] using h
  have hAtop : ∀ n : ℕ,
      ‖∫ x : ℝ in x₁..x₂, h ((x : ℂ) + (σ n) * Complex.I) / (((x : ℂ) + (σ n) * Complex.I) - z)‖
        ≤ G (σ n) / (σ n - |z.im|) := by
    intro n
    have h := hhoriz (σ n) (by rw [abs_of_pos (hσpos n)]; exact hσgt n)
    simpa [abs_of_pos (hσpos n)] using h
  have hAB : Tendsto (fun n : ℕ =>
      (∫ x : ℝ in x₁..x₂, h ((x : ℂ) + (-(σ n)) * Complex.I) / (((x : ℂ) + (-(σ n)) * Complex.I) - z))
      - (∫ x : ℝ in x₁..x₂, h ((x : ℂ) + (σ n) * Complex.I) / (((x : ℂ) + (σ n) * Complex.I) - z)))
      atTop (nhds 0) := by
    refine squeeze_zero_norm (fun n => ?_) hGsum
    have hA := hAbot n
    have hB := hAtop n
    have hns := norm_sub_le
      (∫ x : ℝ in x₁..x₂, h ((x : ℂ) + (-(σ n)) * Complex.I) / (((x : ℂ) + (-(σ n)) * Complex.I) - z))
      (∫ x : ℝ in x₁..x₂, h ((x : ℂ) + (σ n) * Complex.I) / (((x : ℂ) + (σ n) * Complex.I) - z))
    have hpos : 0 < σ n - |z.im| := lt_of_lt_of_le zero_lt_one (hden1 n)
    have hX : 0 ≤ G (σ n) + G (-(σ n)) := by
      have a := hGnn (σ n); have b := hGnn (-(σ n)); linarith
    calc ‖(∫ x : ℝ in x₁..x₂, h ((x : ℂ) + (-(σ n)) * Complex.I) / (((x : ℂ) + (-(σ n)) * Complex.I) - z))
          - (∫ x : ℝ in x₁..x₂, h ((x : ℂ) + (σ n) * Complex.I) / (((x : ℂ) + (σ n) * Complex.I) - z))‖
        ≤ ‖∫ x : ℝ in x₁..x₂, h ((x : ℂ) + (-(σ n)) * Complex.I) / (((x : ℂ) + (-(σ n)) * Complex.I) - z)‖
          + ‖∫ x : ℝ in x₁..x₂, h ((x : ℂ) + (σ n) * Complex.I) / (((x : ℂ) + (σ n) * Complex.I) - z)‖ := hns
      _ ≤ G (-(σ n)) / (σ n - |z.im|) + G (σ n) / (σ n - |z.im|) := add_le_add hA hB
      _ = (G (σ n) + G (-(σ n))) / (σ n - |z.im|) := by rw [add_div]; ring
      _ ≤ G (σ n) + G (-(σ n)) := by
          rw [div_le_iff₀ hpos]
          calc G (σ n) + G (-(σ n)) = (G (σ n) + G (-(σ n))) * 1 := (mul_one _).symm
            _ ≤ (G (σ n) + G (-(σ n))) * (σ n - |z.im|) :=
                mul_le_mul_of_nonneg_left (hden1 n) hX
  -- vertical integrability
  have hvInt : ∀ L : ℝ, L ∈ Set.Ioo a b → L ≠ z.re →
      Integrable (fun y : ℝ => h ((L : ℂ) + y * Complex.I) / (((L : ℂ) + y * Complex.I) - z)) := by
    intro L hL hLz
    have h0 : Integrable (fun y : ℝ => h ((L : ℂ) + y * Complex.I)) := hint L hL
    have hden : 0 < |L - z.re| := abs_pos.mpr (sub_ne_zero.mpr hLz)
    have hg : Integrable (fun y : ℝ => ‖h ((L : ℂ) + y * Complex.I)‖ * |L - z.re|⁻¹) :=
      Integrable.mul_const (Integrable.norm h0) _
    refine Integrable.mono' hg ?_ ?_
    · have hcont : Continuous (fun y : ℝ => h ((L : ℂ) + y * Complex.I)) :=
        hhol.continuousOn.comp_continuous
          (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
          (fun y => by constructor <;> simp <;> linarith [hL.1, hL.2])
      have hcontd : Continuous (fun y : ℝ => ((L : ℂ) + y * Complex.I) - z) :=
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).sub continuous_const
      have hne : ∀ y : ℝ, ((L : ℂ) + y * Complex.I) - z ≠ 0 := by
        intro y hcon
        have h2 : L - z.re = 0 := by
          have := congrArg Complex.re hcon
          simpa using this
        exact hLz (sub_eq_zero.mp h2)
      have hcontq : Continuous (fun y : ℝ =>
          h ((L : ℂ) + y * Complex.I) / (((L : ℂ) + y * Complex.I) - z)) :=
        hcont.div hcontd hne
      exact Continuous.aestronglyMeasurable hcontq
    · refine Eventually.of_forall (fun y => ?_)
      have hwz : |L - z.re| ≤ ‖((L : ℂ) + y * Complex.I) - z‖ := by
        have h1 := Complex.abs_re_le_norm (((L : ℂ) + y * Complex.I) - z)
        have hre : (((L : ℂ) + y * Complex.I) - z).re = L - z.re := by simp
        rw [hre] at h1
        exact h1
      rw [norm_div]
      calc ‖h ((L : ℂ) + y * Complex.I)‖ / ‖((L : ℂ) + y * Complex.I) - z‖
          ≤ ‖h ((L : ℂ) + y * Complex.I)‖ / |L - z.re| :=
            div_le_div_of_nonneg_left (norm_nonneg _) hden hwz
        _ = ‖h ((L : ℂ) + y * Complex.I)‖ * |L - z.re|⁻¹ := div_eq_mul_inv _ _
  have hI2 : Integrable (fun y : ℝ => h ((x₂ : ℂ) + y * Complex.I) / (((x₂ : ℂ) + y * Complex.I) - z)) :=
    hvInt x₂ h₂ (ne_of_gt (by linarith : z.re < x₂))
  have hI1 : Integrable (fun y : ℝ => h ((x₁ : ℂ) + y * Complex.I) / (((x₁ : ℂ) + y * Complex.I) - z)) :=
    hvInt x₁ h₁ (ne_of_lt (by linarith : x₁ < z.re))
  have hlimBR : Tendsto (fun n : ℕ => ∫ y : ℝ in (-(σ n))..(σ n),
      h ((x₂ : ℂ) + y * Complex.I) / (((x₂ : ℂ) + y * Complex.I) - z)) atTop
      (nhds (∫ y : ℝ, h ((x₂ : ℂ) + y * Complex.I) / (((x₂ : ℂ) + y * Complex.I) - z))) :=
    intervalIntegral_tendsto_integral hI2 hσneg hσtop
  have hlimBL : Tendsto (fun n : ℕ => ∫ y : ℝ in (-(σ n))..(σ n),
      h ((x₁ : ℂ) + y * Complex.I) / (((x₁ : ℂ) + y * Complex.I) - z)) atTop
      (nhds (∫ y : ℝ, h ((x₁ : ℂ) + y * Complex.I) / (((x₁ : ℂ) + y * Complex.I) - z))) :=
    intervalIntegral_tendsto_integral hI1 hσneg hσtop
  have hrect : ∀ n : ℕ, 2 * Real.pi * Complex.I * h z =
      rectB x₁ x₂ (σ n) (fun ζ => h ζ / (ζ - z)) := by
    intro n
    have hYl : -(σ n) < z.im := (abs_lt.mp (hσgt n)).1
    have hYr : z.im < σ n := (abs_lt.mp (hσgt n)).2
    refine (rectCauchy hz₁ hz₂ hYl hYr ?_).symm
    refine hhol.mono ?_
    intro w hw
    rw [Complex.mem_reProdIm] at hw
    rw [Set.uIcc_of_le h12.le] at hw
    exact ⟨lt_of_lt_of_le h₁.1 hw.1.1, lt_of_le_of_lt hw.1.2 h₂.2⟩
  have hlimAll : Tendsto (fun n : ℕ =>
      (∫ x : ℝ in x₁..x₂, h ((x : ℂ) + (-(σ n)) * Complex.I) / (((x : ℂ) + (-(σ n)) * Complex.I) - z))
      - (∫ x : ℝ in x₁..x₂, h ((x : ℂ) + (σ n) * Complex.I) / (((x : ℂ) + (σ n) * Complex.I) - z))
      + (Complex.I * (∫ y : ℝ in (-(σ n))..(σ n), h ((x₂ : ℂ) + y * Complex.I) / (((x₂ : ℂ) + y * Complex.I) - z))
        - Complex.I * (∫ y : ℝ in (-(σ n))..(σ n), h ((x₁ : ℂ) + y * Complex.I) / (((x₁ : ℂ) + y * Complex.I) - z))))
      atTop (nhds (0 + (Complex.I * (∫ y : ℝ, h ((x₂ : ℂ) + y * Complex.I) / (((x₂ : ℂ) + y * Complex.I) - z))
        - Complex.I * (∫ y : ℝ, h ((x₁ : ℂ) + y * Complex.I) / (((x₁ : ℂ) + y * Complex.I) - z))))) :=
    hAB.add ((hlimBR.const_mul Complex.I).sub (hlimBL.const_mul Complex.I))
  have hlimConst : Tendsto (fun n : ℕ =>
      (∫ x : ℝ in x₁..x₂, h ((x : ℂ) + (-(σ n)) * Complex.I) / (((x : ℂ) + (-(σ n)) * Complex.I) - z))
      - (∫ x : ℝ in x₁..x₂, h ((x : ℂ) + (σ n) * Complex.I) / (((x : ℂ) + (σ n) * Complex.I) - z))
      + (Complex.I * (∫ y : ℝ in (-(σ n))..(σ n), h ((x₂ : ℂ) + y * Complex.I) / (((x₂ : ℂ) + y * Complex.I) - z))
        - Complex.I * (∫ y : ℝ in (-(σ n))..(σ n), h ((x₁ : ℂ) + y * Complex.I) / (((x₁ : ℂ) + y * Complex.I) - z))))
      atTop (nhds (2 * Real.pi * Complex.I * h z)) := by
    refine Tendsto.congr' (Eventually.of_forall (fun n => ?_)) tendsto_const_nhds
    rw [hrect n]
    simp only [rectB]
    ring
  have hkey := tendsto_nhds_unique hlimConst hlimAll
  have hkey2 : 2 * Real.pi * Complex.I * h z = Complex.I *
      ((∫ y : ℝ, h ((x₂ : ℂ) + y * Complex.I) / (((x₂ : ℂ) + y * Complex.I) - z))
       - (∫ y : ℝ, h ((x₁ : ℂ) + y * Complex.I) / (((x₁ : ℂ) + y * Complex.I) - z))) := by
    rw [hkey]; ring
  have h2π : (2 * (Real.pi : ℂ)) ≠ 0 := by
    apply mul_ne_zero (by norm_num)
    exact_mod_cast Real.pi_ne_zero
  have hcancel : 2 * (Real.pi : ℂ) * h z =
      (∫ y : ℝ, h ((x₂ : ℂ) + y * Complex.I) / (((x₂ : ℂ) + y * Complex.I) - z))
       - (∫ y : ℝ, h ((x₁ : ℂ) + y * Complex.I) / (((x₁ : ℂ) + y * Complex.I) - z)) := by
    have h1 : Complex.I * (2 * (Real.pi : ℂ) * h z) = Complex.I *
        ((∫ y : ℝ, h ((x₂ : ℂ) + y * Complex.I) / (((x₂ : ℂ) + y * Complex.I) - z))
         - (∫ y : ℝ, h ((x₁ : ℂ) + y * Complex.I) / (((x₁ : ℂ) + y * Complex.I) - z))) := by
      rw [← hkey2]; ring
    exact mul_left_cancel₀ Complex.I_ne_zero h1
  rw [← hcancel]
  have hstep : (1 / (2 * Real.pi)) * (2 * Real.pi * h z) = h z := by
    rw [one_div]
    exact inv_mul_cancel_left₀ h2π (h z)
  rw [hstep]

theorem hcBoundaryDecay {a b m : ℝ} (hab : a < b) {h : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ h {z : ℂ | a < z.re ∧ z.re < b})
    (hint : ∀ x ∈ Set.Ioo a b, MeasureTheory.Integrable (fun y : ℝ => h ((x : ℂ) + y * Complex.I)))
    (hmass : ∀ x ∈ Set.Ioo a b, ∫⁻ y : ℝ, ENNReal.ofReal ‖h ((x : ℂ) + y * Complex.I)‖ ≤ ENNReal.ofReal m)
    {c d : ℝ} (hac : a < c) (hcd : c ≤ d) (hdb : d < b) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Icc c d, ∀ y : ℝ, ‖h ((x : ℂ) + y * Complex.I)‖ ≤ C) ∧
    Filter.Tendsto (fun Y : ℝ => ∫ x : ℝ in c..d, h ((x : ℂ) + Y * Complex.I)) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun Y : ℝ => ∫ x : ℝ in c..d, h ((x : ℂ) + (-Y) * Complex.I)) Filter.atTop (nhds 0) := by
  set x₁ : ℝ := (a + c) / 2 with hx₁def
  set x₂ : ℝ := (b + d) / 2 with hx₂def
  have hx₁mem : x₁ ∈ Set.Ioo a b := by
    rw [hx₁def]; constructor <;> linarith
  have hx₂mem : x₂ ∈ Set.Ioo a b := by
    rw [hx₂def]; constructor <;> linarith
  have hx₁c : x₁ < c := by rw [hx₁def]; linarith
  have hdx₂ : d < x₂ := by rw [hx₂def]; linarith
  have h12 : x₁ < x₂ := by linarith
  have hδ₁pos : 0 < c - x₁ := by linarith
  have hδ₂pos : 0 < x₂ - d := by linarith
  have hm'nn : 0 ≤ max m 0 := le_max_right _ _
  have hline₁ : ∫ y : ℝ, ‖h ((x₁ : ℂ) + y * Complex.I)‖ ≤ max m 0 := hcLineMass hint hmass hx₁mem
  have hline₂ : ∫ y : ℝ, ‖h ((x₂ : ℂ) + y * Complex.I)‖ ≤ max m 0 := hcLineMass hint hmass hx₂mem
  -- the two-line representation for z = x + Y i with x in [c,d]
  have hrepOf : ∀ x ∈ Set.Icc c d, ∀ Y : ℝ,
      h ((x : ℂ) + Y * Complex.I) = (1 / (2 * Real.pi)) *
        ((∫ y : ℝ, h ((x₂ : ℂ) + y * Complex.I) / (((x₂ : ℂ) + y * Complex.I) - ((x : ℂ) + Y * Complex.I)))
         - (∫ y : ℝ, h ((x₁ : ℂ) + y * Complex.I) / (((x₁ : ℂ) + y * Complex.I) - ((x : ℂ) + Y * Complex.I)))) := by
    intro x hx Y
    have hre : ((x : ℂ) + Y * Complex.I).re = x := by simp
    exact hcStripRep hhol hint hmass hx₁mem hx₂mem h12
      (by rw [hre]; exact lt_of_lt_of_le hx₁c hx.1)
      (by rw [hre]; exact lt_of_le_of_lt hx.2 hdx₂)
  -- part 1 : uniform bound
  have hpart1 : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Icc c d, ∀ y : ℝ, ‖h ((x : ℂ) + y * Complex.I)‖ ≤ C := by
    refine ⟨max m 0 / (2 * Real.pi) * (1 / (c - x₁) + 1 / (x₂ - d)), ?_, ?_⟩
    · positivity
    · intro x hx Y
      have hre : ((x : ℂ) + Y * Complex.I).re = x := by simp
      have hxx₁ : x₁ < x := lt_of_lt_of_le hx₁c hx.1
      have hxx₂ : x < x₂ := lt_of_le_of_lt hx.2 hdx₂
      have hV₂ : ‖∫ y : ℝ, h ((x₂ : ℂ) + y * Complex.I) /
            (((x₂ : ℂ) + y * Complex.I) - ((x : ℂ) + Y * Complex.I))‖ ≤ max m 0 / (x₂ - d) := by
        have h := hcLineIntBound (hint x₂ hx₂mem) hline₂ hm'nn (L := x₂) (z := ((x : ℂ) + Y * Complex.I))
          (by rw [hre]; exact ne_of_gt hxx₂)
        refine le_trans h ?_
        rw [hre]
        exact div_le_div_of_nonneg_left hm'nn hδ₂pos (by rw [abs_of_pos (by linarith : 0 < x₂ - x)]; linarith [hx.2])
      have hV₁ : ‖∫ y : ℝ, h ((x₁ : ℂ) + y * Complex.I) /
            (((x₁ : ℂ) + y * Complex.I) - ((x : ℂ) + Y * Complex.I))‖ ≤ max m 0 / (c - x₁) := by
        have h := hcLineIntBound (hint x₁ hx₁mem) hline₁ hm'nn (L := x₁) (z := ((x : ℂ) + Y * Complex.I))
          (by rw [hre]; exact ne_of_lt hxx₁)
        refine le_trans h ?_
        rw [hre]
        exact div_le_div_of_nonneg_left hm'nn hδ₁pos (by rw [abs_of_neg (by linarith : x₁ - x < 0)]; linarith [hx.1])
      rw [hrepOf x hx Y]
      have hπ : 0 ≤ (1 / (2 * Real.pi) : ℝ) := by positivity
      calc ‖(1 / (2 * Real.pi)) *
            ((∫ y : ℝ, h ((x₂ : ℂ) + y * Complex.I) / (((x₂ : ℂ) + y * Complex.I) - ((x : ℂ) + Y * Complex.I)))
             - (∫ y : ℝ, h ((x₁ : ℂ) + y * Complex.I) / (((x₁ : ℂ) + y * Complex.I) - ((x : ℂ) + Y * Complex.I))))‖
          = (1 / (2 * Real.pi)) * ‖(∫ y : ℝ, h ((x₂ : ℂ) + y * Complex.I) / (((x₂ : ℂ) + y * Complex.I) - ((x : ℂ) + Y * Complex.I)))
             - (∫ y : ℝ, h ((x₁ : ℂ) + y * Complex.I) / (((x₁ : ℂ) + y * Complex.I) - ((x : ℂ) + Y * Complex.I)))‖ := by
              rw [norm_mul]
              congr 1
              simp
        _ ≤ (1 / (2 * Real.pi)) * (max m 0 / (x₂ - d) + max m 0 / (c - x₁)) := by
              refine mul_le_mul_of_nonneg_left ?_ hπ
              exact le_trans (norm_sub_le _ _) (add_le_add hV₂ hV₁)
        _ = max m 0 / (2 * Real.pi) * (1 / (c - x₁) + 1 / (x₂ - d)) := by ring
  -- the decay bound function psi
  set F₁ : ℝ → ℝ := fun y => ‖h ((x₁ : ℂ) + y * Complex.I)‖ with hF₁def
  set F₂ : ℝ → ℝ := fun y => ‖h ((x₂ : ℂ) + y * Complex.I)‖ with hF₂def
  set K₁ : ℝ → ℝ := fun Y => ∫ y : ℝ, F₁ y / Real.sqrt ((c - x₁) ^ 2 + (y - Y) ^ 2) with hK₁def
  set K₂ : ℝ → ℝ := fun Y => ∫ y : ℝ, F₂ y / Real.sqrt ((x₂ - d) ^ 2 + (y - Y) ^ 2) with hK₂def
  set ψ : ℝ → ℝ := fun Y => (1 / (2 * Real.pi)) * (K₁ Y + K₂ Y) with hψdef
  have hF₁int : MeasureTheory.Integrable F₁ := by rw [hF₁def]; exact (hint x₁ hx₁mem).norm
  have hF₂int : MeasureTheory.Integrable F₂ := by rw [hF₂def]; exact (hint x₂ hx₂mem).norm
  have hF₁nn : ∀ y : ℝ, 0 ≤ F₁ y := fun y => by rw [hF₁def]; exact norm_nonneg _
  have hF₂nn : ∀ y : ℝ, 0 ≤ F₂ y := fun y => by rw [hF₂def]; exact norm_nonneg _
  have hK₁t : Filter.Tendsto K₁ Filter.atTop (nhds 0) := by
    have h := (hcKernelDecay hF₁nn hF₁int hδ₁pos).1
    simpa only [hK₁def] using h
  have hK₁b : Filter.Tendsto K₁ Filter.atBot (nhds 0) := by
    have h := (hcKernelDecay hF₁nn hF₁int hδ₁pos).2
    simpa only [hK₁def] using h
  have hK₂t : Filter.Tendsto K₂ Filter.atTop (nhds 0) := by
    have h := (hcKernelDecay hF₂nn hF₂int hδ₂pos).1
    simpa only [hK₂def] using h
  have hK₂b : Filter.Tendsto K₂ Filter.atBot (nhds 0) := by
    have h := (hcKernelDecay hF₂nn hF₂int hδ₂pos).2
    simpa only [hK₂def] using h
  have hψt : Filter.Tendsto ψ Filter.atTop (nhds 0) := by
    rw [hψdef]
    have h := (hK₁t.add hK₂t).const_mul (1 / (2 * Real.pi))
    simpa using h
  have hψb : Filter.Tendsto ψ Filter.atBot (nhds 0) := by
    rw [hψdef]
    have h := (hK₁b.add hK₂b).const_mul (1 / (2 * Real.pi))
    simpa using h
  -- pointwise domination by psi
  have hdom : ∀ x ∈ Set.Icc c d, ∀ Y : ℝ, ‖h ((x : ℂ) + Y * Complex.I)‖ ≤ ψ Y := by
    intro x hx Y
    have hre : ((x : ℂ) + Y * Complex.I).re = x := by simp
    have him : ((x : ℂ) + Y * Complex.I).im = Y := by simp
    have hxx₁ : x₁ < x := lt_of_lt_of_le hx₁c hx.1
    have hxx₂ : x < x₂ := lt_of_le_of_lt hx.2 hdx₂
    have hV₂ : ‖∫ y : ℝ, h ((x₂ : ℂ) + y * Complex.I) /
          (((x₂ : ℂ) + y * Complex.I) - ((x : ℂ) + Y * Complex.I))‖ ≤ K₂ Y := by
      have h := hcLineIntKernel (hint x₂ hx₂mem) (L := x₂) (z := ((x : ℂ) + Y * Complex.I))
        (by rw [hre]; exact ne_of_gt hxx₂) hδ₂pos
        (by rw [hre]; exact (by rw [abs_of_pos (by linarith : 0 < x₂ - x)]; linarith [hx.2]))
      rw [him] at h
      simpa only [hK₂def, hF₂def] using h
    have hV₁ : ‖∫ y : ℝ, h ((x₁ : ℂ) + y * Complex.I) /
          (((x₁ : ℂ) + y * Complex.I) - ((x : ℂ) + Y * Complex.I))‖ ≤ K₁ Y := by
      have h := hcLineIntKernel (hint x₁ hx₁mem) (L := x₁) (z := ((x : ℂ) + Y * Complex.I))
        (by rw [hre]; exact ne_of_lt hxx₁) hδ₁pos
        (by rw [hre]; exact (by rw [abs_of_neg (by linarith : x₁ - x < 0)]; linarith [hx.1]))
      rw [him] at h
      simpa only [hK₁def, hF₁def] using h
    rw [hrepOf x hx Y, hψdef]
    have hπ : 0 ≤ (1 / (2 * Real.pi) : ℝ) := by positivity
    calc ‖(1 / (2 * Real.pi)) *
          ((∫ y : ℝ, h ((x₂ : ℂ) + y * Complex.I) / (((x₂ : ℂ) + y * Complex.I) - ((x : ℂ) + Y * Complex.I)))
           - (∫ y : ℝ, h ((x₁ : ℂ) + y * Complex.I) / (((x₁ : ℂ) + y * Complex.I) - ((x : ℂ) + Y * Complex.I))))‖
        = (1 / (2 * Real.pi)) * ‖(∫ y : ℝ, h ((x₂ : ℂ) + y * Complex.I) / (((x₂ : ℂ) + y * Complex.I) - ((x : ℂ) + Y * Complex.I)))
           - (∫ y : ℝ, h ((x₁ : ℂ) + y * Complex.I) / (((x₁ : ℂ) + y * Complex.I) - ((x : ℂ) + Y * Complex.I)))‖ := by
            rw [norm_mul]
            congr 1
            simp
      _ ≤ (1 / (2 * Real.pi)) * (K₂ Y + K₁ Y) := by
            refine mul_le_mul_of_nonneg_left ?_ hπ
            exact le_trans (norm_sub_le _ _) (add_le_add hV₂ hV₁)
      _ = (1 / (2 * Real.pi)) * (K₁ Y + K₂ Y) := by ring
  -- conclusion 2
  have hnorm2 : ∀ Y : ℝ, ‖∫ x : ℝ in c..d, h ((x : ℂ) + Y * Complex.I)‖ ≤ ψ Y * |d - c| :=
    fun Y => intervalIntegral.norm_integral_le_of_norm_le_const
      (fun x hx => hdom x (by have h := Set.uIoc_subset_uIcc hx; rwa [Set.uIcc_of_le hcd] at h) Y)
  have hlim2 : Filter.Tendsto (fun Y : ℝ => ∫ x : ℝ in c..d, h ((x : ℂ) + Y * Complex.I)) Filter.atTop (nhds 0) := by
    have hsq : Filter.Tendsto (fun Y : ℝ => ψ Y * |d - c|) Filter.atTop (nhds 0) := by
      have h : Filter.Tendsto (fun Y : ℝ => ψ Y * |d - c|) Filter.atTop (nhds (0 * |d - c|)) :=
        hψt.mul tendsto_const_nhds
      simpa using h
    exact squeeze_zero_norm (fun Y => hnorm2 Y) hsq
  -- conclusion 3
  have hnorm3 : ∀ Y : ℝ, ‖∫ x : ℝ in c..d, h ((x : ℂ) + (-Y) * Complex.I)‖ ≤ ψ (-Y) * |d - c| :=
    fun Y => intervalIntegral.norm_integral_le_of_norm_le_const
      (fun x hx => by
        have h := hdom x (by have h2 := Set.uIoc_subset_uIcc hx; rwa [Set.uIcc_of_le hcd] at h2) (-Y)
        simpa using h)
  have hlim3 : Filter.Tendsto (fun Y : ℝ => ∫ x : ℝ in c..d, h ((x : ℂ) + (-Y) * Complex.I)) Filter.atTop (nhds 0) := by
    have hsq : Filter.Tendsto (fun Y : ℝ => ψ (-Y) * |d - c|) Filter.atTop (nhds 0) := by
      have h : Filter.Tendsto (fun Y : ℝ => ψ (-Y) * |d - c|) Filter.atTop (nhds (0 * |d - c|)) :=
        (hψb.comp tendsto_neg_atTop_atBot).mul tendsto_const_nhds
      simpa using h
    exact squeeze_zero_norm (fun Y => hnorm3 Y) hsq
  exact ⟨hpart1, hlim2, hlim3⟩

end

end Work.FatouL1
