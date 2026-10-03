/-
# The `ℓ²` bound for the IW projections at bounded height and bounded level

The Ionescu--Wainger projection `kmtProj ρ l k = Π_{≤l,≤k}` has symbol
`ξ ↦ iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k)) ξ`, i.e. the sum of at most
`#(ℚ/ℤ)_{≤l}` translates of the cutoff `η_{≤k}`.  For `l ≤ L` the height bound of Appendix A
(`Work.Analysis.IonescuWainger.iw_height_card_le`) gives

`#(ℚ/ℤ)_{≤l} ≤ C_ρ · 2^{2^{ρl}} ≤ C_ρ · 2^{2^{ρL}}`,

while for `k ≤ 0` the periodised cutoff is bounded by `2` (`norm_periodize_etaCut_le_two`).  Hence
the symbol is bounded by the constant `B = 2 C_ρ 2^{2^{ρL}}`, *uniformly* in `l ≤ L` and `k ≤ 0`,
and the multiplier is bounded on `ℓ²` by `B` (`eLpNorm_kmtProj_le_of_symbol`).

This is the `ℓ²` input needed by the `MdlLpH` chapter, where the projection height is `l ≤ L` and
the `η`-height `k` runs over the non-positive integers.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.mdlF_two_le
import Submission.Work.KMTAreas.A7.iwArithFreqs_card_le

namespace Work.KMTPlan.A6.MdlLpH

open MeasureTheory
open scoped ENNReal BigOperators
open Work.Analysis.IonescuWainger Work.KMTContract

theorem kmtProj_two_le_of_le (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (L : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (l : ℕ) (k : ℤ), l ≤ L → k ≤ 0 → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (Work.KMTContract.kmtProj ρ l k f) 2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal B * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := iw_height_card_le hρ
  refine ⟨2 * C₀ * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (L : ℝ))), by positivity, ?_⟩
  intro l k hl hk f
  -- the cardinality of `(ℚ/ℤ)_{≤l}` is bounded independently of `l ≤ L`
  have hcard : ((iwArithFreqs ρ l).card : ℝ)
      ≤ C₀ * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (L : ℝ))) := by
    refine le_trans (hC₀ l) (mul_le_mul_of_nonneg_left ?_ hC₀pos.le)
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hl) hρ.le)
  -- hence the symbol of `kmtProj ρ l k` is bounded, uniformly in `k ≤ 0`
  have hsym : ∀ θ : Circle,
      ‖iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k)) θ‖
        ≤ 2 * C₀ * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (L : ℝ))) := by
    intro θ
    refine le_trans (norm_iwSymbolSet_le (iwArithFreqs ρ l)
      (fun ξ => norm_periodize_etaCut_le_two k hk ξ) θ) ?_
    calc ((iwArithFreqs ρ l).card : ℝ) * 2
        ≤ (C₀ * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (L : ℝ)))) * 2 :=
          mul_le_mul_of_nonneg_right hcard (by norm_num)
      _ = 2 * C₀ * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (L : ℝ))) := by ring
  rcases eq_or_ne (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) ⊤ with hf | hf
  · rw [hf, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))]
    exact le_top
  · have hfmem : MemLp f 2 MeasureTheory.Measure.count :=
      MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hf)
    exact eLpNorm_kmtProj_le_of_symbol hsym (by positivity) hfmem

end Work.KMTPlan.A6.MdlLpH
