import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_complete
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts
import Submission.Work.FTS.PhiStar.Honesty.radGreen_near_limits_of_le_rpow
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS_EllLimOK.PkgJets.cosTailB
import Submission.Work.FTS_EllLimOK.PkgJets.cosWeightTail_le
import Submission.Work.FTS_RegExport.RXR1.HJ.AKBounds
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.EllipticEst.ModalSolution.eFam_pythagoras_alt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter

namespace Work.EllipticEst.ModalSolution

local notation "Iθ" => Work.Spaces.Iθ

/-! ## Elementary facts -/

private lemma cos_nonneg_of_mem_Iθ_alt {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Real.cos θ :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩

private lemma volume_Iθ_lt_top_alt : MeasureTheory.volume Iθ < ⊤ := by
  rw [Work.Spaces.Iθ, Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

/-- A continuous function on `Iθ` is integrable there. -/
private lemma integrableOn_of_continuousOn_alt {g : ℝ → ℝ} (hg : ContinuousOn g Iθ) :
    MeasureTheory.IntegrableOn g Iθ := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  refine MeasureTheory.IntegrableOn.of_bound volume_Iθ_lt_top_alt
    (hg.aestronglyMeasurable measurableSet_Icc) C ?_
  filter_upwards [MeasureTheory.ae_restrict_mem (s := Iθ) measurableSet_Icc] with θ hθ
  exact hC θ hθ

/-- The set integral over `Iθ = [0, π/2]` is the interval integral over `0..π/2`. -/
private lemma setIntegral_Iθ_eq_interval_alt (g : ℝ → ℝ) :
    (∫ θ in Iθ, g θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]

/-- `eFam m` is continuous. -/
private lemma continuous_eFam_alt (m : ℕ) :
    Continuous (fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
  simp only [Work.FTS.PhiStar.Gegenbauer.eFam]
  exact Real.continuous_cos.mul
    (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).comp
      Real.continuous_sin)

/-- The truncated mode sum `∑_{m ≤ N} cmode m F z · eFam m θ`. -/
private def sumEFamAlt (F : ℝ → ℝ → ℝ) (z : ℝ) (N : ℕ) : ℝ → ℝ :=
  fun θ => ∑ m ∈ Finset.range (N + 1),
    Work.FTS.PhiStar.Series.cmode m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ

private lemma continuous_sumEFamAlt (F : ℝ → ℝ → ℝ) (z : ℝ) (N : ℕ) :
    Continuous (sumEFamAlt F z N) :=
  continuous_finsetSum _ fun m _ =>
    continuous_const.mul (continuous_eFam_alt m)

/-! ## The coefficient identity, linearity, and the collapse of the square -/

/-- `cmode m F z` times the norm of `eFam m` is the `e_m`-moment of the slice `F z ·`. -/
private lemma cmode_mul_norm_alt (F : ℝ → ℝ → ℝ) (z : ℝ) (m : ℕ) :
    Work.FTS.PhiStar.Series.cmode m F z *
        (∫ θ in Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
      = ∫ θ in Iθ, F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ := by
  have hnum := setIntegral_Iθ_eq_interval_alt
    (fun θ => F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
  have hden := setIntegral_Iθ_eq_interval_alt
    (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
  have hne : (∫ θ in Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ) ≠ 0 := by
    rw [Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts m]
    positivity
  simp only [Work.FTS.PhiStar.Series.cmode, ← hnum, ← hden]
  exact div_mul_cancel₀ _ hne

/-- The cross term `θ ↦ F z θ · eFam m θ · cos θ` is integrable on `Iθ`. -/
private lemma integrableOn_mul_eFam_cos_alt (F : ℝ → ℝ → ℝ) (z : ℝ) (m : ℕ)
    (hmeas : MeasureTheory.AEStronglyMeasurable (fun θ => F z θ)
      (MeasureTheory.volume.restrict Iθ))
    (hz : MeasureTheory.IntegrableOn (fun θ => F z θ ^ 2 * Real.cos θ) Iθ) :
    MeasureTheory.IntegrableOn
      (fun θ => F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) Iθ := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_eFam_alt m).continuousOn
  have hMabs : ∀ θ ∈ Iθ, |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ M := fun θ hθ => by
    simpa only [Real.norm_eq_abs] using hM θ hθ
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hMabs 0 ⟨le_rfl, by positivity⟩)
  have hcos : MeasureTheory.IntegrableOn (fun θ : ℝ => Real.cos θ) Iθ :=
    integrableOn_of_continuousOn_alt Real.continuous_cos.continuousOn
  have hmaj : MeasureTheory.Integrable
      (fun θ : ℝ => (1 / 2) * (F z θ ^ 2 * Real.cos θ) + (1 / 2) * (M ^ 2 * Real.cos θ))
      (MeasureTheory.volume.restrict Iθ) :=
    (hz.const_mul (1 / 2)).add ((hcos.const_mul (M ^ 2)).const_mul (1 / 2))
  refine MeasureTheory.Integrable.mono' hmaj
    ((hmeas.mul (continuous_eFam_alt m).aestronglyMeasurable).mul
      Real.continuous_cos.aestronglyMeasurable) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem (s := Iθ) measurableSet_Icc] with θ hθ
  have hc : 0 ≤ Real.cos θ := cos_nonneg_of_mem_Iθ_alt hθ
  have he : (Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hMabs θ hθ) 2
  have hAB : |F z θ| * |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
      ≤ (F z θ ^ 2 + M ^ 2) / 2 := by
    nlinarith [sq_nonneg (|F z θ| - |Work.FTS.PhiStar.Gegenbauer.eFam m θ|),
      sq_abs (F z θ), sq_abs (Work.FTS.PhiStar.Gegenbauer.eFam m θ)]
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hc]
  calc |F z θ| * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| * Real.cos θ
      ≤ ((F z θ ^ 2 + M ^ 2) / 2) * Real.cos θ :=
        mul_le_mul_of_nonneg_right hAB hc
    _ = (1 / 2) * (F z θ ^ 2 * Real.cos θ) + (1 / 2) * (M ^ 2 * Real.cos θ) := by ring

/-- Linearity of the integral against a finite linear combination of modes. -/
private lemma integral_mul_finset_sum_alt (F : ℝ → ℝ → ℝ) (z : ℝ) (s : Finset ℕ) (c : ℕ → ℝ)
    (hint : ∀ m ∈ s, MeasureTheory.IntegrableOn
      (fun θ => F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) Iθ) :
    (∫ θ in Iθ, F z θ * (∑ m ∈ s, c m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Real.cos θ)
      = ∑ m ∈ s, c m *
          (∫ θ in Iθ, F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) := by
  have hpt : (fun θ => F z θ * (∑ m ∈ s, c m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        * Real.cos θ)
      = fun θ => ∑ m ∈ s, c m *
          (F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) := by
    funext θ
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hpt, integral_finsetSum s (f := fun m θ =>
      c m * (F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ))
      (fun m hm => (hint m hm).const_mul _)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MeasureTheory.integral_const_mul]

/-- `∫_{Iθ} (∑_m c_m e_m)² cos θ = ∑_m c_m² ∫_{Iθ} e_m² cos θ`. -/
private lemma sum_sq_collapse_alt (s : Finset ℕ) (c : ℕ → ℝ) :
    (∫ θ in Iθ, (∑ m ∈ s, c m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * Real.cos θ)
      = ∑ m ∈ s, c m ^ 2 *
          (∫ θ in Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ) := by
  have hpt : (fun θ => (∑ m ∈ s, c m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2
        * Real.cos θ)
      = fun θ => ∑ m ∈ s, ∑ n ∈ s, c m * c n *
          (Work.FTS.PhiStar.Gegenbauer.eFam m θ
            * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) := by
    funext θ
    rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hcont : ∀ m n : ℕ, Continuous
      (fun θ : ℝ => c m * c n * (Work.FTS.PhiStar.Gegenbauer.eFam m θ
        * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)) := fun m n =>
    ((continuous_const : Continuous fun _ : ℝ => c m * c n)).mul
      (((continuous_eFam_alt m).mul (continuous_eFam_alt n)).mul Real.continuous_cos)
  calc (∫ θ in Iθ, (∑ m ∈ s, c m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * Real.cos θ)
      = (∫ θ in Iθ, ∑ m ∈ s, ∑ n ∈ s, c m * c n *
          (Work.FTS.PhiStar.Gegenbauer.eFam m θ
            * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)) := by
        rw [hpt]
    _ = ∑ m ∈ s, ∫ θ in Iθ, ∑ n ∈ s, c m * c n *
          (Work.FTS.PhiStar.Gegenbauer.eFam m θ
            * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) :=
        integral_finsetSum s
          (f := fun m θ => ∑ n ∈ s, c m * c n *
            (Work.FTS.PhiStar.Gegenbauer.eFam m θ
              * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
          (fun m _ => integrableOn_of_continuousOn_alt
            (continuous_finsetSum s (fun n _ => hcont m n)).continuousOn)
    _ = ∑ m ∈ s, ∑ n ∈ s, ∫ θ in Iθ, c m * c n *
          (Work.FTS.PhiStar.Gegenbauer.eFam m θ
            * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        exact integral_finsetSum s
          (f := fun n θ => c m * c n * (Work.FTS.PhiStar.Gegenbauer.eFam m θ
            * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
          (fun n _ => integrableOn_of_continuousOn_alt (hcont m n).continuousOn)
    _ = ∑ m ∈ s, ∑ n ∈ s, c m * c n *
          (∫ θ in Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ
            * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) := by
        refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
        exact MeasureTheory.integral_const_mul _ _
    _ = ∑ m ∈ s, c m ^ 2 *
          (∫ θ in Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ) := by
        refine Finset.sum_congr rfl fun m hm => ?_
        refine (Finset.sum_eq_single m ?_ ?_).trans ?_
        · intro n _ hn
          rw [eFam_orthogonal_Iθ m n (Ne.symm hn), mul_zero]
        · intro hm'
          exact absurd hm hm'
        · have hInt : (∫ θ in Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ
                * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
              = ∫ θ in Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ :=
            setIntegral_congr_fun (s := Iθ)
              (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc) (fun θ _ => by ring)
          rw [hInt]
          ring

/-! ## The Pythagoras identity -/

theorem eFam_pythagoras_alt (F : ℝ → ℝ → ℝ) (z : ℝ) (N : ℕ)
    (hmeas : MeasureTheory.AEStronglyMeasurable (fun θ => F z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hz : MeasureTheory.IntegrableOn (fun θ => F z θ ^ 2 * Real.cos θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ,
        (F z θ - ∑ m ∈ Finset.range (N + 1),
          Work.FTS.PhiStar.Series.cmode m F z *
            Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * Real.cos θ)
      = (∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ)
        - ∑ m ∈ Finset.range (N + 1), (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ,
              Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ) := by
  change (∫ θ in Iθ, (F z θ - sumEFamAlt F z N θ) ^ 2 * Real.cos θ)
      = (∫ θ in Iθ, F z θ ^ 2 * Real.cos θ)
        - ∑ m ∈ Finset.range (N + 1), (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 *
            (∫ θ in Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
  have hzI : MeasureTheory.Integrable (fun θ => F z θ ^ 2 * Real.cos θ)
      (MeasureTheory.volume.restrict Iθ) := hz
  have hint : ∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun θ => F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) Iθ :=
    fun m => integrableOn_mul_eFam_cos_alt F z m hmeas hz
  have hcontS : Continuous (sumEFamAlt F z N) := continuous_sumEFamAlt F z N
  have hmeasS : MeasureTheory.AEStronglyMeasurable (sumEFamAlt F z N)
      (MeasureTheory.volume.restrict Iθ) := hcontS.aestronglyMeasurable
  have hSSI : MeasureTheory.Integrable (fun θ => sumEFamAlt F z N θ ^ 2 * Real.cos θ)
      (MeasureTheory.volume.restrict Iθ) :=
    integrableOn_of_continuousOn_alt ((hcontS.pow 2).mul Real.continuous_cos).continuousOn
  have hFSI : MeasureTheory.Integrable (fun θ => F z θ * sumEFamAlt F z N θ * Real.cos θ)
      (MeasureTheory.volume.restrict Iθ) := by
    refine MeasureTheory.Integrable.mono'
      ((hzI.const_mul (1 / 2)).add (hSSI.const_mul (1 / 2))) ?_ ?_
    · exact (hmeas.mul hmeasS).mul Real.continuous_cos.aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem (s := Iθ) measurableSet_Icc] with θ hθ
      have hc : 0 ≤ Real.cos θ := cos_nonneg_of_mem_Iθ_alt hθ
      have hAB : |F z θ| * |sumEFamAlt F z N θ|
          ≤ (F z θ ^ 2 + sumEFamAlt F z N θ ^ 2) / 2 := by
        nlinarith [sq_nonneg (|F z θ| - |sumEFamAlt F z N θ|), sq_abs (F z θ),
          sq_abs (sumEFamAlt F z N θ)]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hc]
      calc |F z θ| * |sumEFamAlt F z N θ| * Real.cos θ
          ≤ ((F z θ ^ 2 + sumEFamAlt F z N θ ^ 2) / 2) * Real.cos θ :=
            mul_le_mul_of_nonneg_right hAB hc
        _ = (1 / 2) * (F z θ ^ 2 * Real.cos θ)
              + (1 / 2) * (sumEFamAlt F z N θ ^ 2 * Real.cos θ) := by ring
  -- the cross integral
  have hP : (∫ θ in Iθ, F z θ * sumEFamAlt F z N θ * Real.cos θ)
      = ∑ m ∈ Finset.range (N + 1), (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 *
          (∫ θ in Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ) := by
    refine (integral_mul_finset_sum_alt F z (Finset.range (N + 1))
      (fun m => Work.FTS.PhiStar.Series.cmode m F z) (fun m _ => hint m)).trans ?_
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← cmode_mul_norm_alt F z m]
    ring
  -- the squared-sum integral
  have hQ : (∫ θ in Iθ, sumEFamAlt F z N θ ^ 2 * Real.cos θ)
      = ∑ m ∈ Finset.range (N + 1), (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 *
          (∫ θ in Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ) :=
    sum_sq_collapse_alt (Finset.range (N + 1)) (fun m => Work.FTS.PhiStar.Series.cmode m F z)
  -- the expansion of the square
  have hexp : (∫ θ in Iθ, (F z θ - sumEFamAlt F z N θ) ^ 2 * Real.cos θ)
      = (∫ θ in Iθ, F z θ ^ 2 * Real.cos θ)
        - 2 * (∫ θ in Iθ, F z θ * sumEFamAlt F z N θ * Real.cos θ)
        + (∫ θ in Iθ, sumEFamAlt F z N θ ^ 2 * Real.cos θ) := by
    rw [show (∫ θ in Iθ, (F z θ - sumEFamAlt F z N θ) ^ 2 * Real.cos θ)
        = ∫ θ in Iθ, (F z θ ^ 2 * Real.cos θ
            - 2 * (F z θ * sumEFamAlt F z N θ * Real.cos θ)
            + sumEFamAlt F z N θ ^ 2 * Real.cos θ) from
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring)),
      MeasureTheory.integral_add
        (f := fun θ : ℝ => F z θ ^ 2 * Real.cos θ
          - 2 * (F z θ * sumEFamAlt F z N θ * Real.cos θ))
        (g := fun θ : ℝ => sumEFamAlt F z N θ ^ 2 * Real.cos θ)
        (hzI.sub (hFSI.const_mul 2)) hSSI,
      MeasureTheory.integral_sub hzI (hFSI.const_mul 2),
      MeasureTheory.integral_const_mul]
  rw [hexp, hP, hQ]
  ring

end Work.EllipticEst.ModalSolution
end
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.NRI.LevelDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.DivQ.NRI

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The data functionals at a variable level -/

/-- The honest `η`-data `Denη = ∫_{Iθ}(∂_θh)² sin(2θ)^{-η}`. -/
def nrDenEta (h : ℝ → ℝ) : ℝ := ∫ θ in Work.Spaces.Iθ, PsiEta h θ

/-- The honest `γ`-data at angular order `m`: `Denγ m = ∫_{Iθ}(D_θ^m(∂_θh))² sin(2θ)^{-γ}`. -/
def nrDenGam (α : ℝ) (h : ℝ → ℝ) (m : ℕ) : ℝ := ∫ θ in Work.Spaces.Iθ, PsiGam α h m θ

/-- The right-hand side `Denη + Σ_{1 ≤ m ≤ j} Denγ m` of the inversion at level `j`. -/
def nrSS (α : ℝ) (h : ℝ → ℝ) (j : ℕ) : ℝ :=
  nrDenEta h + ∑ m ∈ Finset.Icc 1 j, nrDenGam α h m

/-- `nrSS` in the raw form in which the region lemmas state their right-hand sides. -/
lemma nrSS_eq (α : ℝ) (h : ℝ → ℝ) (j : ℕ) :
    nrSS α h j
      = (∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        + ∑ m ∈ Finset.Icc 1 j, (∫ θ in Work.Spaces.Iθ,
            (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := rfl

lemma nrDenEta_nonneg {h : ℝ → ℝ} : 0 ≤ nrDenEta h := by
  rw [nrDenEta]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => psiEta_nonneg h θ hθ)

lemma nrDenGam_nonneg {α : ℝ} {h : ℝ → ℝ} (m : ℕ) : 0 ≤ nrDenGam α h m := by
  rw [nrDenGam]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => psiGam_nonneg α h m θ hθ)

lemma nrSS_nonneg (α : ℝ) (h : ℝ → ℝ) (l : ℕ) : 0 ≤ nrSS α h l :=
  add_nonneg nrDenEta_nonneg (Finset.sum_nonneg (fun m _ => nrDenGam_nonneg m))

lemma nrSS_mono (α : ℝ) (h : ℝ → ℝ) {m l : ℕ} (hml : m ≤ l) : nrSS α h m ≤ nrSS α h l := by
  refine add_le_add le_rfl ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    exact ⟨hx.1, le_trans hx.2 hml⟩
  · intro x _ _
    exact nrDenGam_nonneg x

lemma nrDenGam_le_SS (α : ℝ) (h : ℝ → ℝ) {l : ℕ} (hl : 1 ≤ l) :
    nrDenGam α h l ≤ nrSS α h l := by
  have hmem : l ∈ Finset.Icc 1 l := Finset.mem_Icc.mpr ⟨hl, le_rfl⟩
  have h := Finset.single_le_sum (f := fun m => nrDenGam α h m)
    (fun m _ => nrDenGam_nonneg m) hmem
  exact le_trans h (le_add_of_nonneg_left nrDenEta_nonneg)

lemma nrDenEta_le_SS (α : ℝ) (h : ℝ → ℝ) (l : ℕ) : nrDenEta h ≤ nrSS α h l := by
  simp only [nrSS]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun m _ => nrDenGam_nonneg m))

/-! ## The two pullbacks of the honest data -/

/-- The `x`-pullback of the `η`-data is integrable on `(0,x₁)` and its integral is at most
`Denη`. -/
lemma nrSubEta_data {h : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (PsiEta h) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (SubEta h) (Set.Ioo 0 xNear) ∧
      (∫ x in Set.Ioo (0 : ℝ) xNear, SubEta h x) ≤ nrDenEta h := by
  obtain ⟨h1, h2⟩ := thetaOfSubst (Ψ := PsiEta h) hint (psiEta_nonneg h)
  have h1' : MeasureTheory.IntegrableOn
      (fun x : ℝ => PsiEta h (thetaOf x) * (1 / (2 * kappa x))) (Set.Ioo 0 xNear) := by
    rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
    exact h1
  have h2' : (∫ x in Set.Ioo (0 : ℝ) xNear,
        PsiEta h (thetaOf x) * (1 / (2 * kappa x))) ≤ nrDenEta h := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le xNear_pos.le]
    exact h2
  exact ⟨h1'.congr_fun (fun x _ => rfl) measurableSet_Ioo,
    by rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun x _ => rfl)]; exact h2'⟩

/-- The `x`-pullback of the `γ`-data at order `m` is integrable on `(0,x₁)` and its integral is
at most `Denγ m`. -/
lemma nrHonGam_data {α : ℝ} {h : ℝ → ℝ} {m : ℕ}
    (hint : MeasureTheory.IntegrableOn (PsiGam α h m) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (HonGam α h m) (Set.Ioo 0 xNear) ∧
      (∫ x in Set.Ioo (0 : ℝ) xNear, HonGam α h m x) ≤ nrDenGam α h m := by
  obtain ⟨h1, h2⟩ := thetaOfSubst (Ψ := PsiGam α h m) hint (psiGam_nonneg α h m)
  have h1' : MeasureTheory.IntegrableOn
      (fun x : ℝ => PsiGam α h m (thetaOf x) * (1 / (2 * kappa x))) (Set.Ioo 0 xNear) := by
    rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
    exact h1
  have heq : Set.EqOn (HonGam α h m)
      (fun x : ℝ => PsiGam α h m (thetaOf x) * (1 / (2 * kappa x))) (Set.Ioo 0 xNear) := by
    intro x hx
    have hs : Real.sin (2 * thetaOf x) = x := sin_two_thetaOf_Ioo hx
    simp only [HonGam, PsiGam, hs]
  have h2' : (∫ x in Set.Ioo (0 : ℝ) xNear,
        PsiGam α h m (thetaOf x) * (1 / (2 * kappa x))) ≤ nrDenGam α h m := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le xNear_pos.le]
    exact h2
  exact ⟨h1'.congr_fun heq.symm measurableSet_Ioo,
    by rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo heq]; exact h2'⟩

/-! ## Integrability of the dominating functions at a variable level -/

/-- **Integrability of `Dom`/`AccDom` up to level `N`**, from the data at levels `1 ≤ m ≤ N`.
This is `Work.FTS.H2.DivQ.dom_integrable` with the uniform bound `4` replaced by `N` (its
inductive proof consumes `hGam` only at the next level). -/
lemma nrDom_integrable_le {α : ℝ} {h : ℝ → ℝ} {Cm : ℝ} (N : ℕ)
    (hEta : MeasureTheory.IntegrableOn (SubEta h) (Set.Ioo 0 xNear))
    (hGam : ∀ m ∈ Finset.Icc 1 N,
      MeasureTheory.IntegrableOn (HonGam α h m) (Set.Ioo 0 xNear)) :
    (∀ l ≤ N, MeasureTheory.IntegrableOn (Dom α h Cm l) (Set.Ioo 0 xNear)) ∧
      (∀ l ≤ N, MeasureTheory.IntegrableOn (AccDom α h Cm l) (Set.Ioo 0 xNear)) := by
  have key : ∀ l ≤ N,
      MeasureTheory.IntegrableOn (Dom α h Cm l) (Set.Ioo 0 xNear) ∧
      MeasureTheory.IntegrableOn (AccDom α h Cm l) (Set.Ioo 0 xNear) ∧
      MeasureTheory.IntegrableOn (AccDom α h Cm (l + 1)) (Set.Ioo 0 xNear) := by
    intro l
    induction l with
    | zero =>
        intro _
        have h0 : MeasureTheory.IntegrableOn (Dom α h Cm 0) (Set.Ioo 0 xNear) := by
          rw [Dom_zero]; exact hEta
        have h1 : MeasureTheory.IntegrableOn (AccDom α h Cm 0) (Set.Ioo 0 xNear) := by
          rw [AccDom_zero]; exact MeasureTheory.integrableOn_zero
        have h2 : MeasureTheory.IntegrableOn (AccDom α h Cm (0 + 1)) (Set.Ioo 0 xNear) := by
          rw [AccDom_succ]
          exact h1.add h0
        exact ⟨h0, h1, h2⟩
    | succ l ih =>
        intro hl
        obtain ⟨hDl, hAl, hAl1⟩ := ih (by omega)
        have hG : MeasureTheory.IntegrableOn (HonGam α h (l + 1)) (Set.Ioo 0 xNear) :=
          hGam (l + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        have hD : MeasureTheory.IntegrableOn (Dom α h Cm (l + 1)) (Set.Ioo 0 xNear) := by
          rw [Dom_succ]
          exact (hG.const_mul 2).add (hAl1.const_mul (2 * (((l + 1 : ℕ) : ℝ)) * Cm ^ 2))
        have hA : MeasureTheory.IntegrableOn (AccDom α h Cm (l + 1)) (Set.Ioo 0 xNear) := hAl1
        have hA2 : MeasureTheory.IntegrableOn (AccDom α h Cm (l + 2)) (Set.Ioo 0 xNear) := by
          rw [show l + 2 = (l + 1) + 1 from rfl, AccDom_succ]
          exact hA.add hD
        exact ⟨hD, hA, hA2⟩
  exact ⟨fun l hl => (key l hl).1, fun l hl => (key l hl).2.1⟩

/-! ## The per-level integral recursion -/

/-- **The integral step at level `k+1`.**  If the partial sum `AccDom (k+1)` has already been
bounded by `T · nrSS (k+1)`, then the level-`k+1` member `Dom (k+1)` of the recursion is bounded
by `(2 + 2(k+1)Cm²T) · nrSS (k+1)`. -/
lemma nrLevel_bound {α : ℝ} {h : ℝ → ℝ} {Cm T : ℝ} {k : ℕ}
    (hGamInt : MeasureTheory.IntegrableOn (HonGam α h (k + 1)) (Set.Ioo 0 xNear))
    (hAccInt : MeasureTheory.IntegrableOn (AccDom α h Cm (k + 1)) (Set.Ioo 0 xNear))
    (hGamBd : (∫ x in Set.Ioo (0 : ℝ) xNear, HonGam α h (k + 1) x)
        ≤ nrDenGam α h (k + 1))
    (hGamSS : nrDenGam α h (k + 1) ≤ nrSS α h (k + 1))
    (hAccBd : (∫ x in Set.Ioo (0 : ℝ) xNear, AccDom α h Cm (k + 1) x)
        ≤ T * nrSS α h (k + 1)) :
    (∫ x in Set.Ioo (0 : ℝ) xNear, Dom α h Cm (k + 1) x)
      ≤ (2 + 2 * (((k + 1 : ℕ) : ℝ)) * Cm ^ 2 * T) * nrSS α h (k + 1) := by
  have hI1 : MeasureTheory.IntegrableOn (fun x => 2 * HonGam α h (k + 1) x)
      (Set.Ioo 0 xNear) := hGamInt.const_mul 2
  have hI2 : MeasureTheory.IntegrableOn
      (fun x => (2 * (((k + 1 : ℕ) : ℝ)) * Cm ^ 2) * AccDom α h Cm (k + 1) x)
      (Set.Ioo 0 xNear) := hAccInt.const_mul _
  have hEq : (∫ x in Set.Ioo (0 : ℝ) xNear, Dom α h Cm (k + 1) x)
      = 2 * (∫ x in Set.Ioo (0 : ℝ) xNear, HonGam α h (k + 1) x)
        + (2 * (((k + 1 : ℕ) : ℝ)) * Cm ^ 2)
            * (∫ x in Set.Ioo (0 : ℝ) xNear, AccDom α h Cm (k + 1) x) := by
    simp only [Dom_succ_eq]
    rw [MeasureTheory.integral_add hI1 hI2,
      MeasureTheory.integral_const_mul 2 (fun x => HonGam α h (k + 1) x),
      MeasureTheory.integral_const_mul (2 * (((k + 1 : ℕ) : ℝ)) * Cm ^ 2)
        (fun x => AccDom α h Cm (k + 1) x)]
  rw [hEq]
  have hstep := mul_le_mul_of_nonneg_left hAccBd
    (by positivity : (0 : ℝ) ≤ 2 * (((k + 1 : ℕ) : ℝ)) * Cm ^ 2)
  linarith [hGamBd, hGamSS, hstep]

/-! ## The explicit recursion constants

The level-indexed bounds are `∫ AccDom l ≤ nrKT Cm l · nrSS l` and `∫ Dom l ≤ nrKC Cm l · nrSS l`,
where the recurrences are

  `nrKT Cm 1 = 1`,   `nrKT Cm (l+1) = nrKT Cm l + nrKC Cm l`   (`l ≥ 1`),
  `nrKC Cm l = 2 + 2·l·Cm²·nrKT Cm l`   (`l ≥ 1`),

solved explicitly (`nrKT` is the single recursion below). -/

/-- The accumulated constant for `∫ AccDom l`. -/
def nrKT (Cm : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | (n + 2) => nrKT Cm (n + 1) * (1 + 2 * ((n + 1 : ℕ) : ℝ) * Cm ^ 2) + 2

/-- The constant for `∫ Dom l`. -/
def nrKC (Cm : ℝ) (l : ℕ) : ℝ := 2 + 2 * (l : ℝ) * Cm ^ 2 * nrKT Cm l

/-- A universal constant dominating all `nrKC Cm l`, `l ≤ 4`. -/
def nrKCTot (Cm : ℝ) : ℝ := nrKC Cm 1 + nrKC Cm 2 + nrKC Cm 3 + nrKC Cm 4

@[simp] lemma nrKT_zero (Cm : ℝ) : nrKT Cm 0 = 0 := rfl

@[simp] lemma nrKT_one (Cm : ℝ) : nrKT Cm 1 = 1 := rfl

lemma nrKT_succ_succ (Cm : ℝ) (n : ℕ) :
    nrKT Cm (n + 2) = nrKT Cm (n + 1) * (1 + 2 * ((n + 1 : ℕ) : ℝ) * Cm ^ 2) + 2 := rfl

lemma nrKT_nonneg (Cm : ℝ) : ∀ l, 0 ≤ nrKT Cm l := by
  intro l
  induction l with
  | zero => simp
  | succ l ih =>
      rcases l with _ | m
      · simp
      · rw [show m + 1 + 1 = m + 2 from rfl, nrKT_succ_succ]
        have h2 : (0 : ℝ) ≤ 1 + 2 * ((m + 1 : ℕ) : ℝ) * Cm ^ 2 := by positivity
        nlinarith [ih, h2]


lemma nrKC_nonneg (Cm : ℝ) {l : ℕ} (hl : 1 ≤ l) : 0 ≤ nrKC Cm l := by
  have hl' : (0 : ℝ) ≤ (l : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ (l : ℝ) * Cm ^ 2 * nrKT Cm l :=
    mul_nonneg (mul_nonneg hl' (sq_nonneg Cm)) (nrKT_nonneg Cm l)
  simp only [nrKC]
  linarith

lemma nrKC_ge_two (Cm : ℝ) {l : ℕ} (hl : 1 ≤ l) : 2 ≤ nrKC Cm l := by
  have hl' : (0 : ℝ) ≤ (l : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ (l : ℝ) * Cm ^ 2 * nrKT Cm l :=
    mul_nonneg (mul_nonneg hl' (sq_nonneg Cm)) (nrKT_nonneg Cm l)
  simp only [nrKC]
  linarith

/-- The recurrence satisfied by `nrKT`. -/
lemma nrKT_succ_eq (Cm : ℝ) {l : ℕ} (hl : 1 ≤ l) : nrKT Cm (l + 1) = nrKT Cm l + nrKC Cm l := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  simp only [nrKT, nrKC]
  push_cast
  ring

lemma nrKC_le_tot (Cm : ℝ) {l : ℕ} (hl1 : 1 ≤ l) (hl4 : l ≤ 4) : nrKC Cm l ≤ nrKCTot Cm := by
  have h1 := nrKC_nonneg Cm (l := 1) le_rfl
  have h2 := nrKC_nonneg Cm (l := 2) (by norm_num)
  have h3 := nrKC_nonneg Cm (l := 3) (by norm_num)
  have h4 := nrKC_nonneg Cm (l := 4) (by norm_num)
  simp only [nrKCTot]
  interval_cases l <;> linarith

lemma nrKCTot_pos (Cm : ℝ) : 0 < nrKCTot Cm := by
  have h1 := nrKC_ge_two Cm (l := 1) le_rfl
  have h2 := nrKC_ge_two Cm (l := 2) (by norm_num)
  have h3 := nrKC_ge_two Cm (l := 3) (by norm_num)
  have h4 := nrKC_ge_two Cm (l := 4) (by norm_num)
  simp only [nrKCTot]
  linarith

end Work.FTS.H2.DivQ.NRI
end
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.W_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open scoped Real Topology
open MeasureTheory Set Filter


end Work.FTS.H2.DivQ
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.radGreen_sq_w_sq_meas_engine =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.PhiStar.Honesty

open Work.FTS.EllExist

/-- `radGreen` written in terms of the two named indicial branches (`radGreen_eq` followed by the
unfolding of `rgG1`, `rgG2`). -/
private lemma radGreen_eq_rgK_mul (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) :
    Work.FTS.PhiStar.Radial.radGreen α m c z
      = rgK α m * (rgG1 α m c z + rgG2 α m c z) := by
  rw [radGreen_eq]
  simp only [rgG1, rgG2]

/-- The weight identity `(w z)² = (1+z)⁴/z⁴`. -/
private lemma w_sq_eq (z : ℝ) : (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
  rw [Work.Spaces.w, div_pow]
  rw [show ((1 + z) ^ 2) ^ 2 = (1 + z) ^ 4 by ring, show (z ^ 2) ^ 2 = z ^ 4 by ring]

/-- `(1+z)⁴ ≤ 16` for `0 < z ≤ 1`. -/
private lemma one_add_pow_four_le {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1) : (1 + z) ^ 4 ≤ 16 := by
  have h0 : (0 : ℝ) ≤ 1 + z := by linarith
  have h1 : 1 + z ≤ 2 := by linarith
  calc (1 + z) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ h0 h1 4
    _ = 16 := by norm_num

/-- `(1+z)⁴ ≤ 16 z⁴` for `1 ≤ z`. -/
private lemma one_add_pow_four_le_mul {z : ℝ} (hz1 : 1 ≤ z) : (1 + z) ^ 4 ≤ 16 * z ^ 4 := by
  have h0 : (0 : ℝ) ≤ 1 + z := by linarith
  have h1 : 1 + z ≤ 2 * z := by linarith
  calc (1 + z) ^ 4 ≤ (2 * z) ^ 4 := pow_le_pow_left₀ h0 h1 4
    _ = 16 * z ^ 4 := by ring

/-- `(a + b)² ≤ 2a² + 2b²`. -/
private lemma sq_add_le_two (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

theorem radGreen_sq_w_sq_meas_engine {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : AEMeasurable c)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 0) := by
  -- the four weighted square bounds for the two indicial branches
  have hG1n := rgG1_sq_div_z4_Ioo (α := α) (m := m) (c := c) hα hα4 hm hc hnear hfar
  have hG2n := rgG2_sq_div_z4_Ioo (α := α) (m := m) (c := c) hα hα4 hm hc hnear hfar
  have hG1f := rgG1_sq_Ioi (α := α) (m := m) (c := c) hα hα4 hm hc hnear hfar
  have hG2f := rgG2_sq_Ioi (α := α) (m := m) (c := c) hα hα4 hm hc hnear hfar
  -- continuity of the weight square on `(0,∞)`
  have hwcont : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    have h : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by
      funext z
      rw [Work.Spaces.w]
    rw [h]
    exact (((continuous_const.add continuous_id).pow 2).continuousOn.div
      ((continuous_id.pow 2).continuousOn)
      (fun z hz => pow_ne_zero 2 (ne_of_gt hz))).pow 2
  -- a.e. strong measurability of the two branches on `(0,∞)`
  have hG1meas : AEStronglyMeasurable (fun z : ℝ => rgG1 α m c z)
      (volume.restrict (Set.Ioi 0)) :=
    (rgG1_cont_Ioi (α := α) (m := m) (c := c) hα hα4 hm hc hnear hfar).aestronglyMeasurable
      measurableSet_Ioi
  have hG2meas : AEStronglyMeasurable (fun z : ℝ => rgG2 α m c z)
      (volume.restrict (Set.Ioi 0)) := by
    have htail : AEStronglyMeasurable (fun z : ℝ => ∫ t in Set.Ioi z, rgF2 α m c t)
        (volume.restrict (Set.Ioi 0)) :=
      Work.FTS.EllExist.Closers.aesm_tailPrim_Ioi (rgF2 α m c)
    have hpow : AEStronglyMeasurable (fun z : ℝ => z ^ (rgP α m))
        (volume.restrict (Set.Ioi 0)) :=
      (continuousOn_id.rpow_const (fun z hz => Or.inl (ne_of_gt hz))).aestronglyMeasurable
        measurableSet_Ioi
    simpa only [rgG2, rgB] using hpow.fun_mul htail
  have hradMeas : AEStronglyMeasurable (fun z : ℝ => Work.FTS.PhiStar.Radial.radGreen α m c z)
      (volume.restrict (Set.Ioi 0)) := by
    have h : AEStronglyMeasurable
        (fun z : ℝ => rgK α m * (rgG1 α m c z + rgG2 α m c z))
        (volume.restrict (Set.Ioi 0)) := (hG1meas.fun_add hG2meas).const_mul (rgK α m)
    refine h.congr ?_
    filter_upwards with z
    exact (radGreen_eq_rgK_mul α m c z).symm
  have htarget : AEStronglyMeasurable
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (volume.restrict (Set.Ioi 0)) :=
    (hradMeas.pow 2).fun_mul (hwcont.aestronglyMeasurable measurableSet_Ioi)
  -- ## the near piece `(0,1)`
  have hnear_int : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioo 0 1) := by
    have hdom : MeasureTheory.IntegrableOn
        (fun z : ℝ => 16 * (rgK α m) ^ 2 *
          (2 * ((rgG2 α m c z) ^ 2 / z ^ 4) + 2 * ((rgG1 α m c z) ^ 2 / z ^ 4)))
        (Set.Ioo 0 1) :=
      ((hG2n.const_mul 2).add (hG1n.const_mul 2)).const_mul (16 * (rgK α m) ^ 2)
    refine Integrable.mono' hdom ?_ ?_
    · have hw : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
          (volume.restrict (Set.Ioo 0 1)) :=
        (hwcont.mono (fun z hz => hz.1)).aestronglyMeasurable measurableSet_Ioo
      have hrad : AEStronglyMeasurable
          (fun z : ℝ => Work.FTS.PhiStar.Radial.radGreen α m c z)
          (volume.restrict (Set.Ioo 0 1)) :=
        hradMeas.mono_measure (Measure.restrict_mono Set.Ioo_subset_Ioi_self le_rfl)
      exact (hrad.pow 2).fun_mul hw
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
      have hz0 : (0 : ℝ) < z := hz.1
      have hz1 : z ≤ 1 := hz.2.le
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      have hwle : (Work.Spaces.w z) ^ 2 ≤ 16 / z ^ 4 := by
        rw [w_sq_eq z, div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < z ^ 4)]
        exact one_add_pow_four_le hz0 hz1
      have hsq := sq_add_le_two (rgG1 α m c z) (rgG2 α m c z)
      rw [radGreen_eq_rgK_mul α m c z]
      calc (rgK α m * (rgG1 α m c z + rgG2 α m c z)) ^ 2 * (Work.Spaces.w z) ^ 2
          = (rgK α m) ^ 2 * (rgG1 α m c z + rgG2 α m c z) ^ 2
              * (Work.Spaces.w z) ^ 2 := by ring
        _ ≤ (rgK α m) ^ 2 * (2 * (rgG1 α m c z) ^ 2 + 2 * (rgG2 α m c z) ^ 2)
              * (16 / z ^ 4) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hsq (sq_nonneg _)) hwle ?_ ?_
            · positivity
            · positivity
        _ = 16 * (rgK α m) ^ 2 * (2 * ((rgG2 α m c z) ^ 2 / z ^ 4)
              + 2 * ((rgG1 α m c z) ^ 2 / z ^ 4)) := by ring
  -- ## the far piece `(1,∞)`
  have hfar_int : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 1) := by
    have hdom : MeasureTheory.IntegrableOn
        (fun z : ℝ => 16 * (rgK α m) ^ 2 *
          (2 * (rgG2 α m c z) ^ 2 + 2 * (rgG1 α m c z) ^ 2)) (Set.Ioi 1) :=
      ((hG2f.const_mul 2).add (hG1f.const_mul 2)).const_mul (16 * (rgK α m) ^ 2)
    refine Integrable.mono' hdom ?_ ?_
    · have hsub : Set.Ioi (1 : ℝ) ⊆ Set.Ioi (0 : ℝ) := Set.Ioi_subset_Ioi (by norm_num)
      have hw : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
          (volume.restrict (Set.Ioi 1)) :=
        (hwcont.mono hsub).aestronglyMeasurable measurableSet_Ioi
      have hrad : AEStronglyMeasurable
          (fun z : ℝ => Work.FTS.PhiStar.Radial.radGreen α m c z)
          (volume.restrict (Set.Ioi 1)) :=
        hradMeas.mono_measure (Measure.restrict_mono hsub le_rfl)
      exact (hrad.pow 2).fun_mul hw
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      have hz1 : (1 : ℝ) ≤ z := hz.le
      have hz0 : (0 : ℝ) < z := lt_of_lt_of_le one_pos hz1
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      have hwle : (Work.Spaces.w z) ^ 2 ≤ 16 := by
        rw [w_sq_eq z, div_le_iff₀ (by positivity : (0 : ℝ) < z ^ 4)]
        exact one_add_pow_four_le_mul hz1
      have hsq := sq_add_le_two (rgG1 α m c z) (rgG2 α m c z)
      rw [radGreen_eq_rgK_mul α m c z]
      calc (rgK α m * (rgG1 α m c z + rgG2 α m c z)) ^ 2 * (Work.Spaces.w z) ^ 2
          = (rgK α m) ^ 2 * (rgG1 α m c z + rgG2 α m c z) ^ 2
              * (Work.Spaces.w z) ^ 2 := by ring
        _ ≤ (rgK α m) ^ 2 * (2 * (rgG1 α m c z) ^ 2 + 2 * (rgG2 α m c z) ^ 2) * 16 := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hsq (sq_nonneg _)) hwle ?_ ?_
            · positivity
            · positivity
        _ = 16 * (rgK α m) ^ 2 * (2 * (rgG2 α m c z) ^ 2
              + 2 * (rgG1 α m c z) ^ 2) := by ring
  -- ## glue `(0,1)` and `(1,∞)`
  have hA : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Icc (0 : ℝ) 1) :=
    hnear_int.congr_set_ae (MeasureTheory.Ioo_ae_eq_Icc).symm
  have hB : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ici (1 : ℝ)) :=
    hfar_int.congr_set_ae (MeasureTheory.Ioi_ae_eq_Ici).symm
  have hU := hA.union hB
  have hset : Set.Icc (0 : ℝ) 1 ∪ Set.Ici (1 : ℝ) = Set.Ici (0 : ℝ) := by
    ext x
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ici]
    constructor
    · rintro (⟨h1, _⟩ | h3) <;> linarith
    · intro h
      rcases le_or_gt x 1 with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr h'.le
  rw [hset] at hU
  exact hU.mono_set Set.Ioi_subset_Ici_self

end Work.FTS.PhiStar.Honesty
end
end
