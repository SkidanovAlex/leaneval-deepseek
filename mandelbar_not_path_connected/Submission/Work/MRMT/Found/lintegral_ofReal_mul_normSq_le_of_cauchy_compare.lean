import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory ENNReal

/-- Elementary real inequality: if `0 ≤ u ≤ B`, `0 ≤ r ≤ p + q` and `0 ≤ p, q`, then
`u * r ^ 2 ≤ 2 * B * p ^ 2 + 2 * u * q ^ 2`. -/
lemma real_mul_sq_le_of_le_add (u B r p q : ℝ) (hu : 0 ≤ u) (huB : u ≤ B)
    (hr0 : 0 ≤ r) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : r ≤ p + q) :
    u * r ^ 2 ≤ 2 * B * p ^ 2 + 2 * u * q ^ 2 := by
  have hpq : (0:ℝ) ≤ p + q := by linarith
  have hr2 : r ^ 2 ≤ (p + q) ^ 2 := by
    nlinarith [hr0, hr, hpq, sq_nonneg (p + q - r)]
  have h2 : (p + q) ^ 2 ≤ 2 * (p ^ 2 + q ^ 2) := add_sq_le (a := p) (b := q)
  have h3 : u * r ^ 2 ≤ u * (2 * (p ^ 2 + q ^ 2)) :=
    le_trans (mul_le_mul_of_nonneg_left hr2 hu) (mul_le_mul_of_nonneg_left h2 hu)
  have h5 : 2 * u * p ^ 2 ≤ 2 * B * p ^ 2 := by nlinarith [sq_nonneg p]
  nlinarith [h3, h5]

theorem lintegral_ofReal_mul_normSq_le_of_cauchy_compare {Ω : Set ℂ}
    {ν : ℕ → ℂ → ℂ}
    (hνmeas : ∀ n, MeasureTheory.AEStronglyMeasurable (ν n) (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    {B : ℝ} (hB : 0 ≤ B)
    (hνb : ∀ n, Filter.Eventually (fun z => ‖ν n z‖ ≤ B)
      (MeasureTheory.ae (MeasureTheory.volume : MeasureTheory.Measure ℂ)))
    {c : ℕ → ℂ → ℂ}
    (hcmeas : ∀ n, AEMeasurable (c n) (MeasureTheory.Measure.restrict MeasureTheory.volume Ω))
    (n N : ℕ) :
    ∫⁻ z in Ω, ENNReal.ofReal (‖ν n z‖ * ‖c n z‖ ^ 2)
      ≤ ENNReal.ofReal (2 * B) * (∫⁻ z in Ω, ENNReal.ofReal (‖c n z - c N z‖ ^ 2))
        + ∫⁻ z in Ω, ENNReal.ofReal (2 * ‖ν n z‖ * ‖c N z‖ ^ 2) := by
  have hf : AEMeasurable (fun z => ENNReal.ofReal (‖c n z - c N z‖ ^ 2))
      (MeasureTheory.Measure.restrict MeasureTheory.volume Ω) :=
    (((hcmeas n).sub (hcmeas N)).norm.pow_const 2).ennreal_ofReal
  have hA : AEMeasurable
      (fun z => ENNReal.ofReal (2 * B) * ENNReal.ofReal (‖c n z - c N z‖ ^ 2))
      (MeasureTheory.Measure.restrict MeasureTheory.volume Ω) :=
    hf.const_mul _
  have hpt : Filter.Eventually (fun z => ENNReal.ofReal (‖ν n z‖ * ‖c n z‖ ^ 2) ≤
      ENNReal.ofReal (2 * B) * ENNReal.ofReal (‖c n z - c N z‖ ^ 2)
        + ENNReal.ofReal (2 * ‖ν n z‖ * ‖c N z‖ ^ 2))
      (MeasureTheory.ae (MeasureTheory.Measure.restrict MeasureTheory.volume Ω)) := by
    have hb := ae_mono (Measure.restrict_le_self (s := Ω)) (hνb n)
    filter_upwards [hb] with z hz
    have hu : (0:ℝ) ≤ ‖ν n z‖ := norm_nonneg _
    have hr0 : (0:ℝ) ≤ ‖c n z‖ := norm_nonneg _
    have hp : (0:ℝ) ≤ ‖c n z - c N z‖ := norm_nonneg _
    have hq : (0:ℝ) ≤ ‖c N z‖ := norm_nonneg _
    have hr : ‖c n z‖ ≤ ‖c n z - c N z‖ + ‖c N z‖ := by
      have h : c n z = (c n z - c N z) + c N z := by ring
      calc ‖c n z‖ = ‖(c n z - c N z) + c N z‖ := congrArg (fun w => ‖w‖) h
        _ ≤ ‖c n z - c N z‖ + ‖c N z‖ := norm_add_le _ _
    have hreal := real_mul_sq_le_of_le_add ‖ν n z‖ B ‖c n z‖ ‖c n z - c N z‖ ‖c N z‖
      hu hz hr0 hp hq hr
    have h1 : ENNReal.ofReal (‖ν n z‖ * ‖c n z‖ ^ 2) ≤
        ENNReal.ofReal (2 * B * ‖c n z - c N z‖ ^ 2 + 2 * ‖ν n z‖ * ‖c N z‖ ^ 2) :=
      ENNReal.ofReal_le_ofReal hreal
    have hadd : ENNReal.ofReal (2 * B * ‖c n z - c N z‖ ^ 2 + 2 * ‖ν n z‖ * ‖c N z‖ ^ 2)
        = ENNReal.ofReal (2 * B * ‖c n z - c N z‖ ^ 2)
          + ENNReal.ofReal (2 * ‖ν n z‖ * ‖c N z‖ ^ 2) :=
      ENNReal.ofReal_add (p := 2 * B * ‖c n z - c N z‖ ^ 2)
        (q := 2 * ‖ν n z‖ * ‖c N z‖ ^ 2) (by positivity) (by positivity)
    have hmul : ENNReal.ofReal (2 * B * ‖c n z - c N z‖ ^ 2)
        = ENNReal.ofReal (2 * B) * ENNReal.ofReal (‖c n z - c N z‖ ^ 2) :=
      ENNReal.ofReal_mul (p := 2 * B) (q := ‖c n z - c N z‖ ^ 2) (by linarith)
    rw [hadd, hmul] at h1
    exact h1
  calc ∫⁻ z in Ω, ENNReal.ofReal (‖ν n z‖ * ‖c n z‖ ^ 2)
      ≤ ∫⁻ z, (ENNReal.ofReal (2 * B) * ENNReal.ofReal (‖c n z - c N z‖ ^ 2)
          + ENNReal.ofReal (2 * ‖ν n z‖ * ‖c N z‖ ^ 2))
          ∂(MeasureTheory.Measure.restrict MeasureTheory.volume Ω) :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal (2 * B)
          * (∫⁻ z, ENNReal.ofReal (‖c n z - c N z‖ ^ 2)
              ∂(MeasureTheory.Measure.restrict MeasureTheory.volume Ω))
          + ∫⁻ z, ENNReal.ofReal (2 * ‖ν n z‖ * ‖c N z‖ ^ 2)
              ∂(MeasureTheory.Measure.restrict MeasureTheory.volume Ω) := by
        rw [lintegral_add_left' hA, lintegral_const_mul'' _ hf]

end Work.MRMT.Found
