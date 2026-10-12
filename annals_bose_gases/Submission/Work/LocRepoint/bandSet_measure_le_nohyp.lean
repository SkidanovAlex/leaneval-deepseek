import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.LocRepoint.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocRepoint

open MeasureTheory

/-- **The band-measure bound without the regime hypothesis.**

`Work.SmallBoxSliding.bandSet_measure_le` proves the band bound only in the
regime `0 ≤ ½L(1+d) − 2μ^{-1/3}` (i.e. the band has nonnegative width in the
`w := (Ld)•u`-coordinates).  The bound in fact holds for *all* `L, d, μ > 0`:
in the complementary regime `½L(1+d) < 2μ^{-1/3}` the band condition
`∃ j, ½L(1+d) − 2μ^{-1/3} ≤ |w_j|` is automatic (as `½L(1+d) − 2μ^{-1/3} ≤ 0`),
so `bandSet = {u | ∀ j, |w_j| ≤ ½L(1+d)}` is exactly the `∞`-cube of half-side
`A := ½L(1+d)`; its `u`-volume is `((Ld)³)⁻¹ (2A)³ = ((Ld)³)⁻¹ (L(1+d))³`, and
`L(1+d) < 4μ^{-1/3} ≤ 12μ^{-1/3}` gives the claim. -/
lemma bandSet_measure_le_nohyp {L d μ : ℝ} (hL : 0 < L) (hd : 0 < d) (hμ : 0 < μ) :
    (MeasureTheory.volume (Work.SmallBoxSliding.bandSet L d μ)).toReal
      ≤ ((L * d) ^ 3)⁻¹ * (12 * μ ^ (-1 / 3 : ℝ) * L ^ 2 * (1 + d) ^ 2) := by
  by_cases hAδ : 0 ≤ (1 / 2) * L * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ)
  · exact Work.SmallBoxSliding.bandSet_measure_le (ℓ := L) (d := d) (μ := μ) hL hd hμ hAδ
  · have hAδ' : (1 / 2) * L * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ) < 0 := lt_of_not_ge hAδ
    have hr0 : 0 ≤ μ ^ (-1 / 3 : ℝ) := le_of_lt (Real.rpow_pos_of_pos hμ _)
    have hRHSnn : 0 ≤ ((L * d) ^ 3)⁻¹ * (12 * μ ^ (-1 / 3 : ℝ) * L ^ 2 * (1 + d) ^ 2) := by
      positivity
    refine ENNReal.toReal_le_of_le_ofReal hRHSnn ?_
    let A : ℝ := (1 / 2) * L * (1 + d)
    have hA0 : 0 ≤ A := by dsimp [A]; positivity
    -- in this regime the band is contained in the `∞`-cube of half-side `A`
    have hcube : (MeasureTheory.volume (Work.SmallBoxSliding.bandSet L d μ))
        ≤ ENNReal.ofReal (((L * d) ^ 3)⁻¹ * (2 * A) ^ 3) := by
      have hshell := Submission.BoseGases.band_shell_measure (c := L * d) (A := A) (δ := A)
        (mul_pos hL hd) hA0 hA0 (sub_nonneg.mpr (le_refl A))
      have hsub : Work.SmallBoxSliding.bandSet L d μ ⊆ {u : EuclideanSpace ℝ (Fin 3) |
            (∃ j : Fin 3, A - A ≤ |((L * d) • u).ofLp j|) ∧
            (∀ j : Fin 3, |((L * d) • u).ofLp j| ≤ A)} := by
        intro u hu
        refine ⟨⟨0, ?_⟩, ?_⟩
        · rw [sub_self]; exact abs_nonneg _
        · simpa [A] using hu.2
      refine le_trans (measure_mono hsub) ?_
      simpa using hshell
    have hnum : (2 * A) ^ 3 ≤ 12 * μ ^ (-1 / 3 : ℝ) * L ^ 2 * (1 + d) ^ 2 := by
      have hstep : (1 / 2) * (L * (1 + d)) < 2 * μ ^ (-1 / 3 : ℝ) := by linarith [hAδ']
      have h4 : 4 * μ ^ (-1 / 3 : ℝ) ≤ 12 * μ ^ (-1 / 3 : ℝ) := by linarith [hr0]
      have hlin : L * (1 + d) ≤ 12 * μ ^ (-1 / 3 : ℝ) := by linarith [hstep, h4]
      calc (2 * A) ^ 3 = L ^ 2 * (1 + d) ^ 2 * (L * (1 + d)) := by dsimp [A]; ring
        _ ≤ L ^ 2 * (1 + d) ^ 2 * (12 * μ ^ (-1 / 3 : ℝ)) :=
              mul_le_mul_of_nonneg_left hlin (by positivity)
        _ = 12 * μ ^ (-1 / 3 : ℝ) * L ^ 2 * (1 + d) ^ 2 := by ring
    refine le_trans hcube ?_
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left hnum
      (inv_nonneg.mpr (pow_nonneg (mul_nonneg (le_of_lt hL) (le_of_lt hd)) 3))

end Work.LocRepoint
