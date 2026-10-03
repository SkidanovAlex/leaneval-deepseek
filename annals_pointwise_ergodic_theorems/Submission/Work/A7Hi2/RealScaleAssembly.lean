import Mathlib
import Submission.Work.A7Hi2.RealScaleDefs
import Submission.Work.KMTAreas.A7.lacunaryBumpDilationVar
import Submission.Port.Aesm

/-!
# The assembly of the real-scale lacunary dilation variational estimate

This module assembles `Work.A7Hi2.dilVarRealScale` from

* the **integer-scale** estimate `Work.KMTAreas.A7Hi.DilVarClean` (the proved JSW/Lépingle
  lacunary variational estimate for integral scales), applied to the integer surrogate
  `intScaleR ∘ σ`;
* the **values square function of the difference family** `A_{σ n} − A_{ρ n}`
  (`n ↦ ∑'_j (bumpKernR K (σ n) j − bumpKernR K (ρ n) j) · f (x − j)`), whose `ℓᵖ`-boundedness is
  the conclusion of `Work.A7Hi2.diffSqSumR_of_inputs`.

The pointwise mechanism is

  `Vʳ(A_{σ n} f) ≤ Vʳ(A_{ρ n} f) + Vʳ(A_{σ n} f − A_{ρ n} f)`
  `             ≤ Vʳ(A_{ρ n} f) + (2·2^{1/r}+1)·(Σ_n |A_{σ n} f − A_{ρ n} f|²)^{1/2}`,

the second step being `Work.KMTAreas.A7.variationalNorm_le_sqSum`, followed by Minkowski for
`eLpNorm` of `ℝ≥0∞`-valued functions (`Work.KMTAreas.A7.eLpNorm_add_le_ennreal`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.A7Hi2

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## Summability of the sampled dilation kernels

For a bounded `f` the convolution sums `∑'_j bumpKernR K σ j · f (x − j)` are absolutely
convergent, which is what makes the splitting `A_σ f = A_ρ f + (A_σ − A_ρ) f` a statement about
`tsum`s.  (For unbounded `f` the convolution sums are the junk value `0`, and the final estimate is
then trivial; this is handled by the case split in the main proof below.) -/

/-- The sampled dilation kernel at scale `σ ≥ 1` is summable.  (Port of
`Work.KMTAreas.A7.bumpKern_summable` to real scales, via
`Work.KMTAreas.A7.one_add_div_rpow_neg_two_le`.) -/
lemma summable_bumpKernR (K : SchwartzMap ℝ ℂ) {σ : ℝ} (hσ : 1 ≤ σ) :
    Summable (fun j : ℤ => bumpKernR K σ j) := by
  obtain ⟨B, hBpos, hB⟩ := Commons.Analysis.Fourier.schwartz_decay_real K 2
  have hσpos : (0 : ℝ) < σ := lt_of_lt_of_le one_pos hσ
  refine Summable.of_norm_bounded (f := fun j : ℤ => bumpKernR K σ j)
    (g := fun j : ℤ => B * σ * (1 + |(j : ℝ)|) ^ (-2 : ℝ)) ?_ ?_
  · exact Work.KMTAreas.A7.summable_int_one_add_abs_neg_two.mul_left _
  · intro j
    have h := hB ((j : ℝ) / σ)
    have hfeq : (1 + |(j : ℝ) / σ|) = (1 + |(j : ℝ)| / σ) := by
      rw [abs_div, abs_of_pos hσpos]
    rw [hfeq] at h
    have hnn : (0 : ℝ) ≤ 1 / σ := by positivity
    calc ‖bumpKernR K σ j‖
        = (1 / σ) * ‖K ((j : ℝ) / σ)‖ := by
          rw [bumpKernR, norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hσpos, one_div]
      _ ≤ (1 / σ) * (B * (1 + |(j : ℝ)| / σ) ^ (-2 : ℝ)) :=
          mul_le_mul_of_nonneg_left h hnn
      _ ≤ (1 / σ) * (B * (σ ^ 2 * (1 + |(j : ℝ)|) ^ (-2 : ℝ))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hBpos.le) hnn
          exact Work.KMTAreas.A7.one_add_div_rpow_neg_two_le σ hσ _
      _ = B * σ * (1 + |(j : ℝ)|) ^ (-2 : ℝ) := by field_simp

/-- Splitting a convolution kernel into the difference of two kernels. -/
lemma tsum_diff_mul_eq (k₁ k₂ : ℤ → ℂ) (f : ℤ → ℂ) (x : ℤ)
    (h₁ : Summable (fun j : ℤ => k₁ j * f (x - j)))
    (h₂ : Summable (fun j : ℤ => k₂ j * f (x - j))) :
    (∑' j : ℤ, (k₁ j - k₂ j) * f (x - j))
      = (∑' j : ℤ, k₁ j * f (x - j)) - (∑' j : ℤ, k₂ j * f (x - j)) := by
  rw [← Summable.tsum_sub h₁ h₂]
  exact tsum_congr fun j => by ring

/-! ## The main assembly -/

/-- **The real-scale lacunary dilation variational estimate from the square function of the
difference family.**  The hypothesis `hSqSum` is the conclusion of
`Work.A7Hi2.diffSqSumR_of_inputs` (with the three analytic inputs instantiated). -/
theorem dilVarRealScale_of_sqSum (p : ℝ) (hp : 1 < p) (r : NNReal) (hr : 2 < r)
    (K : SchwartzMap ℝ ℂ)
    (hSqSum : ∃ C : ℝ, 0 < C ∧ ∀ (σ ρ : ℕ → ℝ), (∀ n, 1 ≤ σ n) → (∀ n, 2 * σ n ≤ σ (n + 1)) →
      (∀ n, 1 ≤ ρ n) → (∀ n, 2 * ρ n ≤ ρ (n + 1)) →
      (∀ n, ρ n ≤ σ n ∧ σ n ≤ 2 * ρ n) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm
          (fun x : ℤ => (∑' n : ℕ, ‖∑' j : ℤ, diffKernR K (σ n) (ρ n) j * f (x - j)‖ₑ
            ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
          (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℕ → ℝ) (hσ1 : ∀ n : ℕ, 1 ≤ σ n)
      (hσ2 : ∀ n : ℕ, 2 * σ n ≤ σ (n + 1)) (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => ∑' j : ℤ, (1 / σ n) * K ((j : ℝ) / (σ n)) * f (x - j)))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            MeasureTheory.Measure.count := by
  obtain ⟨C₂, hC₂pos, hC₂⟩ := hSqSum
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.KMTAreas.A7.lacunaryBumpDilationVar p hp r hr K
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num : (1 : NNReal) ≤ 2) (le_of_lt hr)
  have hr2 : (2 : NNReal) ≤ r := le_of_lt hr
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  set D : ℝ := 2 * (2 : ℝ) ^ (1 / (r : ℝ)) + 1 with hD
  have hDpos : 0 < D := by rw [hD]; positivity
  have hq0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have hqt : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (le_of_lt hp)
  refine ⟨C₁ + D * C₂ + 1, by positivity, ?_⟩
  intro σ hσ1 hσ2 f
  set ρ : ℕ → ℝ := fun n => ((intScaleR (σ n) : ℕ) : ℝ) with hρdef
  have hρ1 : ∀ n : ℕ, 1 ≤ ρ n := fun n => by
    simp only [hρdef]
    exact_mod_cast one_le_intScaleR (σ n)
  have hρ2 : ∀ n : ℕ, 2 * ρ n ≤ ρ (n + 1) := fun n => by
    simp only [hρdef]
    exact_mod_cast intScaleR_lacunary hσ1 hσ2 n
  have hcmp : ∀ n : ℕ, ρ n ≤ σ n ∧ σ n ≤ 2 * ρ n := fun n => by
    simp only [hρdef]
    exact ⟨intScaleR_le (hσ1 n), le_of_lt (lt_two_mul_intScaleR (hσ1 n))⟩
  rcases eq_top_or_lt_top (a := MeasureTheory.eLpNorm f (ENNReal.ofReal p)
    (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)) with htop | hfin
  · -- `f` is not in `ℓᵖ`: the right-hand side is `⊤`
    have hCpos : (0 : ℝ) < C₁ + D * C₂ + 1 := by nlinarith [hC₁pos, hDpos, hC₂pos]
    rw [htop]
    rw [ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hCpos)]
    exact le_top
  · -- main case: `f ∈ ℓᵖ`, hence `f` is bounded
    have hQne : (∫⁻ x : ℤ, ‖f x‖ₑ ^ p
        ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)) ≠ ⊤ := by
      intro hc
      rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hq0 hqt,
        ENNReal.toReal_ofReal hp0.le, hc,
        ENNReal.top_rpow_of_pos (by positivity : (0 : ℝ) < 1 / p)] at hfin
      exact absurd hfin (lt_irrefl _)
    obtain ⟨M, hM⟩ := Work.KMTAreas.A7.norm_le_of_summable_norm_rpow hp0
      (Work.KMTAreas.A7.summable_norm_rpow_of_lintegral_ne_top hp0 hQne)
    -- the pointwise variational inequality
    have hpoint : ∀ x : ℤ,
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => ∑' j : ℤ,
            bumpKernR K (σ n) j * f (x - j))
          ≤ PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => ∑' j : ℤ,
              bumpKernR K (ρ n) j * f (x - j))
            + ENNReal.ofReal D * (∑' n : ℕ, ‖∑' j : ℤ,
                diffKernR K (σ n) (ρ n) j * f (x - j)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
      intro x
      have hsplit : (fun n : ℕ => ∑' j : ℤ, bumpKernR K (σ n) j * f (x - j))
          = (fun n : ℕ => ∑' j : ℤ, bumpKernR K (ρ n) j * f (x - j))
            + (fun n : ℕ => ∑' j : ℤ, diffKernR K (σ n) (ρ n) j * f (x - j)) := by
        funext n
        have h1 : Summable (fun j : ℤ => bumpKernR K (σ n) j * f (x - j)) :=
          Work.KMTAreas.A7.summable_mul_bounded (bumpKernR K (σ n))
            (summable_bumpKernR K (hσ1 n)) f M hM x
        have h2 : Summable (fun j : ℤ => bumpKernR K (ρ n) j * f (x - j)) :=
          Work.KMTAreas.A7.summable_mul_bounded (bumpKernR K (ρ n))
            (summable_bumpKernR K (hρ1 n)) f M hM x
        have h3 := tsum_diff_mul_eq (bumpKernR K (σ n)) (bumpKernR K (ρ n)) f x h1 h2
        simp only [Pi.add_apply, diffKernR]
        rw [h3]; ring
      rw [hsplit]
      refine (Submission.PointwiseErgodicTheorems.variationalNorm_add_le hr1 _ _).trans ?_
      refine add_le_add le_rfl ?_
      rw [hD]
      exact Work.KMTAreas.A7.variationalNorm_le_sqSum hr2 _
    -- the bound for the integer-scale family
    have h1 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => ∑' j : ℤ, bumpKernR K (ρ n) j * f (x - j)))
        (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal C₁ * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
      have hfun : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => ∑' j : ℤ, bumpKernR K (ρ n) j * f (x - j)))
          = fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => ∑' j : ℤ, (1 / ((intScaleR (σ n) : ℕ) : ℝ))
              * K ((j : ℝ) / ((intScaleR (σ n) : ℕ) : ℝ)) * f (x - j)) := by
        funext x
        refine congrArg _ (funext fun n => ?_)
        exact tsum_congr fun j => by simp only [hρdef, bumpKernR]
      rw [hfun]
      exact hC₁ (fun n => intScaleR (σ n)) (fun n => one_le_intScaleR (σ n))
        (fun n => intScaleR_lacunary hσ1 hσ2 n) f
    -- the bound for the difference family
    have h2 : MeasureTheory.eLpNorm (fun x : ℤ => (∑' n : ℕ, ‖∑' j : ℤ,
            diffKernR K (σ n) (ρ n) j * f (x - j)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
        (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal C₂ * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) :=
      hC₂ σ ρ hσ1 hσ2 hρ1 hρ2 hcmp f
    -- assemble
    have key : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => ∑' j : ℤ, bumpKernR K (ρ n) j * f (x - j)))
        (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        + ENNReal.ofReal D * MeasureTheory.eLpNorm (fun x : ℤ => (∑' n : ℕ, ‖∑' j : ℤ,
            diffKernR K (σ n) (ρ n) j * f (x - j)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
        (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal (C₁ + D * C₂ + 1) * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
      refine (add_le_add h1 (mul_le_mul_of_nonneg_left h2 bot_le)).trans ?_
      rw [← mul_assoc, ← ENNReal.ofReal_mul hDpos.le, ← add_mul,
        ← ENNReal.ofReal_add hC₁pos.le (mul_nonneg hDpos.le hC₂pos.le)]
      exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (by linarith)) bot_le
    refine (Work.KMTAreas.A7.eLpNorm_mono_ennreal hpoint hq0 hqt).trans ?_
    refine (Work.KMTAreas.A7.eLpNorm_add_le_ennreal hq1 hqt).trans ?_
    rw [Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal ENNReal.ofReal_ne_top hq0 hqt]
    exact key

end

end Work.A7Hi2
