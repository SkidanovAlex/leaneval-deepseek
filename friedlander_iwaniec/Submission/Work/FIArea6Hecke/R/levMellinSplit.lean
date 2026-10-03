import Mathlib
import Submission.Work.FIArea6Hecke.R.levelHeckeDefs

namespace Work.FIArea6Hecke.R

open MeasureTheory Set
open scoped ComplexConjugate

/-- The point `thetaCutPt B` is null for the restricted measure on `(0,∞)`. -/
private lemma ae_ne_thetaCutPt (B : ℝ) (hB : 0 < B) :
    ∀ᵐ u ∂(volume.restrict (Ioi 0)), u ≠ thetaCutPt B := by
  rw [MeasureTheory.ae_iff]
  have hset : {u : ℝ | ¬ u ≠ thetaCutPt B} = {thetaCutPt B} := by
    ext u; simp only [Set.mem_ofPred_eq, ne_eq, not_not, Set.mem_singleton_iff]
  rw [hset, Measure.restrict_apply (measurableSet_singleton _)]
  have hinter : ({thetaCutPt B} : Set ℝ) ∩ Ioi 0 = {thetaCutPt B} := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_Ioi]
    exact ⟨fun h => h.1, fun h => ⟨h, by subst h; exact thetaCutPt_pos hB⟩⟩
  rw [hinter]
  exact measure_singleton _

/-- Off the cut point the two truncations reassemble `f` pointwise. -/
private lemma thetaCutLo_add_thetaCutHi (B : ℝ) (f : ℝ → ℂ) {u : ℝ}
    (hu : u ≠ thetaCutPt B) : thetaCutLo B f u + thetaCutHi B f u = f u := by
  unfold thetaCutLo thetaCutHi
  rcases lt_or_gt_of_ne hu with h | h
  · rw [if_pos h, if_neg (not_lt.mpr h.le), add_zero]
  · rw [if_neg (not_lt.mpr h.le), if_pos h, zero_add]

/-- `mellin f = mellin (thetaCutLo B f) + mellin (thetaCutHi B f)`:

the two truncations of `f` at the fixed point `c = 1/√B` reassemble `f` off the point `c`
(which is null for `volume.restrict (Ioi 0)`), so the Mellin integrands agree a.e.; the
Mellin integral of the sum is the sum of the Mellin integrals by `integral_add`, using the
two convergence hypotheses to make each summand integrable. -/
theorem levMellinSplit (B : ℝ) (hB : 0 < B) (f : ℝ → ℂ) (t : ℂ)
    (hlo : MellinConvergent (thetaCutLo B f) t) (hhi : MellinConvergent (thetaCutHi B f) t) :
    mellin f t = mellin (thetaCutLo B f) t + mellin (thetaCutHi B f) t := by
  have hne := ae_ne_thetaCutPt B hB
  have hpt : ∀ u : ℝ, u ≠ thetaCutPt B →
      ((u : ℂ) ^ (t - 1)) • f u
        = ((u : ℂ) ^ (t - 1)) • thetaCutLo B f u
          + ((u : ℂ) ^ (t - 1)) • thetaCutHi B f u := by
    intro u hu
    rw [← thetaCutLo_add_thetaCutHi B f hu, smul_add]
  have hae : (fun u : ℝ => ((u : ℂ) ^ (t - 1)) • f u) =ᵐ[volume.restrict (Ioi 0)]
      (fun u : ℝ => ((u : ℂ) ^ (t - 1)) • thetaCutLo B f u
        + ((u : ℂ) ^ (t - 1)) • thetaCutHi B f u) := by
    filter_upwards [hne] with u hu
    exact hpt u hu
  rw [mellin, mellin, mellin, MeasureTheory.integral_congr_ae hae]
  exact MeasureTheory.integral_add (by simpa [MellinConvergent, IntegrableOn] using hlo)
    (by simpa [MellinConvergent, IntegrableOn] using hhi)

end Work.FIArea6Hecke.R
