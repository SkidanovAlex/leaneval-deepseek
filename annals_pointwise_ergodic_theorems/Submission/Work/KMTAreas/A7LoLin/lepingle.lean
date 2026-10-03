/-
# The bottom-height unmodulated low-pass lacunary variational estimate

The unmodulated family `n ↦ Tle ρ 0 (varphiN ⌊a n⌋ 0)` is, at arithmetic height `0`, the family of
bump dilations `bumpOp K₀ (2^{logN ⌊a n⌋})` (`Work.KMTAreas.A7LoLin.kmtProj_zero_eq_bumpOp`), and
the dyadic levels `n ↦ logN ⌊a n⌋` are monotone.  Hence the estimate follows from Lépingle's
inequality for lacunary bump dilations — here taken in the axiom-clean form
`Work.KMTAreas.A7Hi.DilVar` — by monotone reindexing
(`Work.KMTAreas.A7.variationalNorm_comp_mono_le`), through the auxiliary lemma
`Work.KMTAreas.A7LoLin.lowpass0_of_lepingle`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7LoLin.lowpass0
import Submission.Work.KMTAreas.A7Hi.DilVar

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7LoLin

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTAreas.A7
open Work.Analysis.EndVar

noncomputable section

/-- **The bottom-height unmodulated low-pass lacunary variational estimate.** -/
theorem lowpass0 (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hpt : p < ⊤)
    (r : NNReal) (hr : 2 < r) (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ C : NNReal, ∀ (a : ℕ → NNReal) (ha : Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
      (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Tle ρ 0 (varphiN (Nat.floor (a n)) 0) f x))
          p MeasureTheory.Measure.count
        ≤ (C : ENNReal) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  have hp0 : 1 < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt hpt)).mpr hp
  obtain ⟨C, hC⟩ := lowpass0_of_lepingle ρ hΛ p.toReal hp0 r hr
    (Work.KMTAreas.A7Hi.DilVar p.toReal hp0 r hr K0)
  exact ⟨C, fun a ha ha1 f => by
    rw [show p = ENNReal.ofReal p.toReal from (ENNReal.ofReal_toReal (ne_of_lt hpt)).symm]
    exact hC a ha ha1 f⟩

end

end Work.KMTAreas.A7LoLin
