/-
# `eFam_pythagoras_alt` — Pythagoras for the truncated angular eigenbasis (`eFam`)

Self-contained alternative proof of the truncated Pythagorean identity for the Dirichlet
eigenbasis `eFam m θ = cos θ · gC (2m+1) (sin θ)` of `Work.Elliptic.Lzero`:

  `∫_{Iθ} (F z θ - ∑_{m ≤ N} c_m e_m θ)² cos θ = ∫_{Iθ} F z θ² cos θ - ∑_{m ≤ N} c_m² ∫_{Iθ} e_m² cos θ`

with `c_m = cmode m F z` the `e_m`-coefficient of the slice `F z ·` (`Series/Defs.lean`).

Everything is done with the weighted pairing `⟨f, g⟩ = ∫_{Iθ} f g cos θ`:

* `cmode_mul_norm_alt` — `c_m · ∫ e_m² cos = ∫ F z · e_m · cos` (the definition of `cmode`,
  with the interval integral `∫_{0}^{π/2}` rewritten as the set integral over `Iθ`);
* `sum_sq_collapse_alt` — `∫ (∑_m c_m e_m)² cos = ∑_m c_m² ∫ e_m² cos` (linearity of the
  integral plus the orthogonality `eFam_orthogonal_Iθ`);
* `integral_mul_finset_sum_alt` — linearity of the integral against a finite sum;
* the pointwise expansion `(F - S)² cos = F² cos - 2 F S cos + S² cos` and linearity of the
  integral.

The only integrability input involving `F` is the AM–GM domination of `F · S · cos` by
`(F² cos + S² cos)/2`; all other integrability side conditions are for continuous functions on
the compact interval `Iθ`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_complete
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts
import Submission.Work.Spaces.Defs
import Submission.Work.EllipticEst.ModalSolution.eFamBasisFts_FALSE

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
