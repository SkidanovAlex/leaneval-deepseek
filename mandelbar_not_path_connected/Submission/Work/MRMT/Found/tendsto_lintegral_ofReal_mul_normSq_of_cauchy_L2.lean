import Mathlib
import Submission.Work.MRMT.Found.tendsto_lintegral_ofReal_mul_normSq_of_ae_tendsto_zero
import Submission.Work.MRMT.Found.lintegral_ofReal_mul_normSq_le_of_cauchy_compare

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

theorem tendsto_lintegral_ofReal_mul_normSq_of_cauchy_L2 {Ω : Set ℂ}
    {ν : ℕ → ℂ → ℂ} (hνmeas : ∀ n, MeasureTheory.AEStronglyMeasurable (ν n) (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hν0 : Filter.Eventually (fun z => Filter.Tendsto (fun n => ν n z) Filter.atTop (nhds 0))
      (MeasureTheory.ae (MeasureTheory.volume : MeasureTheory.Measure ℂ)))
    {B : ℝ} (hB : 0 ≤ B)
    (hνb : ∀ n, Filter.Eventually (fun z => ‖ν n z‖ ≤ B)
      (MeasureTheory.ae (MeasureTheory.volume : MeasureTheory.Measure ℂ)))
    {c : ℕ → ℂ → ℂ}
    (hcmeas : ∀ n, AEMeasurable (c n) (MeasureTheory.Measure.restrict MeasureTheory.volume Ω))
    {K : ℝ} (hK : 0 ≤ K)
    (hcbdd : ∀ n, ∫⁻ z in Ω, ENNReal.ofReal (‖c n z‖ ^ 2) ≤ ENNReal.ofReal K)
    (hcau : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ z in Ω, ENNReal.ofReal (‖c n z - c m z‖ ^ 2) ≤ ENNReal.ofReal ε) :
    Filter.Tendsto (fun n => ∫⁻ z in Ω, ENNReal.ofReal (‖ν n z‖ * ‖c n z‖ ^ 2))
      Filter.atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hεtop : ε = ⊤
  · rw [hεtop]
    exact Filter.Eventually.of_forall (fun n => le_top)
  set r : ℝ := (ε / 2).toReal with hrdef
  have hε2ne0 : ε / 2 ≠ 0 := ne_of_gt (ENNReal.half_pos (ne_of_gt hε))
  have hε2netop : ε / 2 ≠ ⊤ := ENNReal.div_ne_top hεtop (by norm_num)
  have hrpos : 0 < r := by
    rw [hrdef]; exact ENNReal.toReal_pos hε2ne0 hε2netop
  have h2B1 : (0:ℝ) < 2 * B + 1 := by linarith
  set ε' : ℝ := r / (2 * B + 1) with hepdef
  have hε'pos : 0 < ε' := div_pos hrpos h2B1
  have hkey : ENNReal.ofReal (2 * B) * ENNReal.ofReal ε' ≤ ε / 2 := by
    rw [← ENNReal.ofReal_mul (by linarith : (0:ℝ) ≤ 2 * B)]
    have hle : 2 * B * ε' ≤ r := by
      have hEq : 2 * B * ε' = (2 * B * r) / (2 * B + 1) := by rw [hepdef]; ring
      rw [hEq, div_le_iff₀ h2B1]
      nlinarith [hrpos.le]
    calc ENNReal.ofReal (2 * B * ε') ≤ ENNReal.ofReal r := ENNReal.ofReal_le_ofReal hle
      _ ≤ ε / 2 := ENNReal.ofReal_toReal_le
  obtain ⟨N, hN⟩ := hcau ε' hε'pos
  have hDCT : Filter.Tendsto (fun n => ∫⁻ z in Ω, ENNReal.ofReal (2 * ‖ν n z‖ * ‖c N z‖ ^ 2))
      Filter.atTop (nhds 0) :=
    tendsto_lintegral_ofReal_mul_normSq_of_ae_tendsto_zero hνmeas hν0 hB hνb
      (by norm_num : (0:ℝ) ≤ 2) (hcmeas N) hK (hcbdd N)
  have hevDCT : ∀ᶠ n in Filter.atTop,
      (∫⁻ z in Ω, ENNReal.ofReal (2 * ‖ν n z‖ * ‖c N z‖ ^ 2)) ≤ ε / 2 :=
    (ENNReal.tendsto_nhds_zero.mp hDCT) (ε / 2) (ENNReal.half_pos (ne_of_gt hε))
  filter_upwards [hevDCT, Filter.eventually_ge_atTop N] with n hTn hnN
  calc ∫⁻ z in Ω, ENNReal.ofReal (‖ν n z‖ * ‖c n z‖ ^ 2)
      ≤ ENNReal.ofReal (2 * B) * (∫⁻ z in Ω, ENNReal.ofReal (‖c n z - c N z‖ ^ 2))
        + ∫⁻ z in Ω, ENNReal.ofReal (2 * ‖ν n z‖ * ‖c N z‖ ^ 2) :=
        lintegral_ofReal_mul_normSq_le_of_cauchy_compare hνmeas hB hνb hcmeas n N
    _ ≤ ENNReal.ofReal (2 * B) * ENNReal.ofReal ε' + ε / 2 :=
        add_le_add (mul_le_mul_right (hN n N hnN (le_refl N)) _) hTn
    _ ≤ ε / 2 + ε / 2 := add_le_add hkey le_rfl
    _ = ε := ENNReal.add_halves ε

end Work.MRMT.Found
