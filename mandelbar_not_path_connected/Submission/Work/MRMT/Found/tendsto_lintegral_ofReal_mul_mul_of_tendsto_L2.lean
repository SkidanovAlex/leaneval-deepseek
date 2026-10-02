import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.tendsto_lintegral_ofReal_mul_normSq_of_cauchy_L2
import Submission.Work.MRMT.Found.aemeasurable_comp_of_pull

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false

namespace Work.MRMT.Found

open MeasureTheory Filter
open scoped ENNReal Topology

-- i.e. ∫⁻_Ω ofReal (‖ν n z‖ * ‖ρ n (f z)‖ * ‖ρ n z‖) → 0, given:
--   ∫⁻_Ω H (f z) ≤ ofReal Cp * ∫⁻_Φ H for all H ≥ 0;  ν n → 0 a.e. and ‖ν n‖ ≤ B a.e.;
--   (ρ n) Cauchy and bounded in L²(Ω ∪ Φ).
/-- With `a = ‖ρ n (f z)‖`, `b = ‖ρ n z‖`, the elementary bound `a*b ≤ a² + b²` splits the
three-factor integrand into the two pieces handled by
`tendsto_lintegral_ofReal_mul_normSq_of_cauchy_L2` (one with `c = ρ n`, one with `c = ρ n ∘ f`,
the latter made measurable through the pull-back hypothesis `hpull`). -/
theorem tendsto_lintegral_ofReal_mul_mul_of_tendsto_L2 {Ω Φ : Set ℂ}
    (hΩ : MeasurableSet Ω) (hΩfin : (MeasureTheory.volume : MeasureTheory.Measure ℂ) Ω ≠ ⊤)
    (hΦ : MeasurableSet Φ) (hΦfin : (MeasureTheory.volume : MeasureTheory.Measure ℂ) Φ ≠ ⊤)
    {f : ℂ → ℂ} (hf : Continuous f)
    (hpull : ∃ Cp : ℝ, 0 < Cp ∧ ∀ H : ℂ → ENNReal,
      MeasureTheory.lintegral (MeasureTheory.Measure.restrict MeasureTheory.volume Ω) (fun z => H (f z))
        ≤ ENNReal.ofReal Cp * MeasureTheory.lintegral
            (MeasureTheory.Measure.restrict MeasureTheory.volume Φ) H)
    {ν : ℕ → ℂ → ℂ}
    (hνmeas : ∀ n, MeasureTheory.AEStronglyMeasurable (ν n) (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hν0 : Filter.Eventually (fun z => Filter.Tendsto (fun n => ν n z) Filter.atTop (nhds 0))
      (MeasureTheory.ae (MeasureTheory.volume : MeasureTheory.Measure ℂ)))
    (hνb : ∃ B : ℝ, 0 ≤ B ∧ ∀ n, Filter.Eventually (fun z => ‖ν n z‖ ≤ B)
      (MeasureTheory.ae (MeasureTheory.volume : MeasureTheory.Measure ℂ)))
    {ρ : ℕ → ℂ → ℂ}
    (hρmeas : ∀ n, MeasureTheory.AEStronglyMeasurable (ρ n) (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hρcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      MeasureTheory.lintegral (MeasureTheory.Measure.restrict MeasureTheory.volume (Ω ∪ Φ))
        (fun w => ENNReal.ofReal ‖ρ n w - ρ m w‖ ^ 2) ≤ ENNReal.ofReal ε)
    (hρbdd : ∃ D : ℝ, 0 ≤ D ∧ ∀ n,
      MeasureTheory.lintegral (MeasureTheory.Measure.restrict MeasureTheory.volume (Ω ∪ Φ))
        (fun w => ENNReal.ofReal ‖ρ n w‖ ^ 2) ≤ ENNReal.ofReal D) :
    Filter.Tendsto (fun n => MeasureTheory.lintegral
      (MeasureTheory.Measure.restrict MeasureTheory.volume Ω)
      (fun z => ENNReal.ofReal (‖ν n z‖ * ‖ρ n (f z)‖ * ‖ρ n z‖))) Filter.atTop (nhds 0) := by
  obtain ⟨Cp, hCp, hpullH⟩ := hpull
  obtain ⟨B, hB0, hνbB⟩ := hνb
  obtain ⟨D, hD0, hρD0⟩ := hρbdd
  -- rewrite the `L²`-bounds on `Ω ∪ Φ` into the exact integrand shape used by the engine
  have hρD : ∀ n, ∫⁻ w in Ω ∪ Φ, ENNReal.ofReal (‖ρ n w‖ ^ 2) ≤ ENNReal.ofReal D := by
    intro n
    rw [show (∫⁻ w in Ω ∪ Φ, ENNReal.ofReal (‖ρ n w‖ ^ 2))
        = ∫⁻ w in Ω ∪ Φ, ENNReal.ofReal ‖ρ n w‖ ^ 2 from
      lintegral_congr (fun w => by rw [pow_two, pow_two, ENNReal.ofReal_mul (norm_nonneg (ρ n w))])]
    exact hρD0 n
  have hρcau : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ w in Ω ∪ Φ, ENNReal.ofReal (‖ρ n w - ρ m w‖ ^ 2) ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hρcauchy ε hε
    refine ⟨N, fun n m hn hm => ?_⟩
    rw [show (∫⁻ w in Ω ∪ Φ, ENNReal.ofReal (‖ρ n w - ρ m w‖ ^ 2))
        = ∫⁻ w in Ω ∪ Φ, ENNReal.ofReal ‖ρ n w - ρ m w‖ ^ 2 from
      lintegral_congr (fun w => by rw [pow_two, pow_two, ENNReal.ofReal_mul (norm_nonneg _)])]
    exact hN n m hn hm
  -- the engine applied to `c = ρ n`
  have hρmeasΩ : ∀ n, AEMeasurable (ρ n) (MeasureTheory.Measure.restrict MeasureTheory.volume Ω) := fun n =>
    ((hρmeas n).mono_measure MeasureTheory.Measure.restrict_le_self).aemeasurable
  have hcbddρ : ∀ n, ∫⁻ z in Ω, ENNReal.ofReal (‖ρ n z‖ ^ 2) ≤ ENNReal.ofReal D := by
    intro n
    exact le_trans (lintegral_mono_set (Set.subset_union_left)) (hρD n)
  have hcauρ : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ z in Ω, ENNReal.ofReal (‖ρ n z - ρ m z‖ ^ 2) ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hρcau ε hε
    exact ⟨N, fun n m hn hm => le_trans (lintegral_mono_set (Set.subset_union_left)) (hN n m hn hm)⟩
  have hT2 : Filter.Tendsto (fun n => ∫⁻ z in Ω, ENNReal.ofReal (‖ν n z‖ * ‖ρ n z‖ ^ 2))
      Filter.atTop (nhds 0) :=
    tendsto_lintegral_ofReal_mul_normSq_of_cauchy_L2 hνmeas hν0 hB0 hνbB hρmeasΩ hD0 hcbddρ hcauρ
  -- the engine applied to `c = ρ n ∘ f`; measurability of the composition uses `hpull`
  have hcfmeas : ∀ n, AEMeasurable (fun z => ρ n (f z))
      (MeasureTheory.Measure.restrict MeasureTheory.volume Ω) :=
    fun n => aemeasurable_comp_of_pull hf ⟨Cp, hCp, hpullH⟩ (hρmeas n)
  have hcbdd_cf : ∀ n, ∫⁻ z in Ω, ENNReal.ofReal (‖ρ n (f z)‖ ^ 2) ≤ ENNReal.ofReal (Cp * D) := by
    intro n
    have h1 : ∫⁻ z in Ω, ENNReal.ofReal (‖ρ n (f z)‖ ^ 2)
        ≤ ENNReal.ofReal Cp * ∫⁻ z in Φ, ENNReal.ofReal (‖ρ n z‖ ^ 2) :=
      hpullH (fun w => ENNReal.ofReal (‖ρ n w‖ ^ 2))
    have h2 : ∫⁻ z in Φ, ENNReal.ofReal (‖ρ n z‖ ^ 2) ≤ ENNReal.ofReal D :=
      le_trans (lintegral_mono_set Set.subset_union_right) (hρD n)
    calc ∫⁻ z in Ω, ENNReal.ofReal (‖ρ n (f z)‖ ^ 2)
        ≤ ENNReal.ofReal Cp * ENNReal.ofReal D := le_trans h1 (mul_le_mul_right h2 _)
      _ = ENNReal.ofReal (Cp * D) := (ENNReal.ofReal_mul hCp.le).symm
  have hcau_cf : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ z in Ω, ENNReal.ofReal (‖ρ n (f z) - ρ m (f z)‖ ^ 2) ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hρcau (ε / Cp) (div_pos hε hCp)
    refine ⟨N, fun n m hn hm => ?_⟩
    have h1 : ∫⁻ z in Ω, ENNReal.ofReal (‖ρ n (f z) - ρ m (f z)‖ ^ 2)
        ≤ ENNReal.ofReal Cp * ∫⁻ z in Φ, ENNReal.ofReal (‖ρ n z - ρ m z‖ ^ 2) :=
      hpullH (fun w => ENNReal.ofReal (‖ρ n w - ρ m w‖ ^ 2))
    have h2 : ∫⁻ z in Φ, ENNReal.ofReal (‖ρ n z - ρ m z‖ ^ 2) ≤ ENNReal.ofReal (ε / Cp) :=
      le_trans (lintegral_mono_set Set.subset_union_right) (hN n m hn hm)
    calc ∫⁻ z in Ω, ENNReal.ofReal (‖ρ n (f z) - ρ m (f z)‖ ^ 2)
        ≤ ENNReal.ofReal Cp * ENNReal.ofReal (ε / Cp) := le_trans h1 (mul_le_mul_right h2 _)
      _ = ENNReal.ofReal (Cp * (ε / Cp)) := (ENNReal.ofReal_mul hCp.le).symm
      _ = ENNReal.ofReal ε := by rw [mul_div_cancel₀ ε (ne_of_gt hCp)]
  have hT1 : Filter.Tendsto (fun n => ∫⁻ z in Ω, ENNReal.ofReal (‖ν n z‖ * ‖ρ n (f z)‖ ^ 2))
      Filter.atTop (nhds 0) :=
    tendsto_lintegral_ofReal_mul_normSq_of_cauchy_L2 hνmeas hν0 hB0 hνbB hcfmeas
      (mul_nonneg hCp.le hD0) hcbdd_cf hcau_cf
  -- conclude by the pointwise bound `‖ρ n (f z)‖ * ‖ρ n z‖ ≤ ‖ρ n (f z)‖² + ‖ρ n z‖²`
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  filter_upwards [(ENNReal.tendsto_nhds_zero.mp hT1) (ε / 2) (ENNReal.half_pos hε.ne'),
                  (ENNReal.tendsto_nhds_zero.mp hT2) (ε / 2) (ENNReal.half_pos hε.ne')] with n h1 h2
  have hmeas1 : AEMeasurable (fun z => ENNReal.ofReal (‖ν n z‖ * ‖ρ n (f z)‖ ^ 2))
      (MeasureTheory.Measure.restrict MeasureTheory.volume Ω) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((((hνmeas n).mono_measure MeasureTheory.Measure.restrict_le_self).aemeasurable.norm).mul
        ((hcfmeas n).norm.pow_const 2))
  calc ∫⁻ z in Ω, ENNReal.ofReal (‖ν n z‖ * ‖ρ n (f z)‖ * ‖ρ n z‖)
      ≤ ∫⁻ z in Ω, (ENNReal.ofReal (‖ν n z‖ * ‖ρ n (f z)‖ ^ 2)
            + ENNReal.ofReal (‖ν n z‖ * ‖ρ n z‖ ^ 2)) := by
        refine lintegral_mono (fun z => ?_)
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hab : ‖ρ n (f z)‖ * ‖ρ n z‖ ≤ ‖ρ n (f z)‖ ^ 2 + ‖ρ n z‖ ^ 2 := by
          nlinarith [sq_nonneg (‖ρ n (f z)‖ - ‖ρ n z‖), norm_nonneg (ρ n (f z)),
            norm_nonneg (ρ n z)]
        nlinarith [mul_le_mul_of_nonneg_left hab (norm_nonneg (ν n z))]
    _ = (∫⁻ z in Ω, ENNReal.ofReal (‖ν n z‖ * ‖ρ n (f z)‖ ^ 2))
          + ∫⁻ z in Ω, ENNReal.ofReal (‖ν n z‖ * ‖ρ n z‖ ^ 2) := lintegral_add_left' hmeas1 _
    _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
    _ = ε := ENNReal.add_halves ε

end Work.MRMT.Found
