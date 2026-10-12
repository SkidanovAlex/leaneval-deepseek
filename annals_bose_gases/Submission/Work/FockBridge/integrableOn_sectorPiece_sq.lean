import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FockBridge.Count
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `IntegrableOn` of the squared sector pieces

The sector piece `sectorPiece B k Φ = 1_{sectorSet B k}·Φ` is supported on the (measurable)
count-`k` sector, where it coincides with `Φ`; hence its square is the sector indicator applied to
`Φ²` (`sectorPiece_sq`).  For continuous `Φ` the square `Φ²` is integrable over the (compact, for
every side length) analysis box `abox N L`, and an indicator of a measurable set is dominated by
it, so the squared sector piece is integrable.
-/

namespace Work.FockBridge

open MeasureTheory
open Submission.BoseGases

theorem integrableOn_sectorPiece_sq {N : ℕ} {L : ℝ} {B : Set (EuclideanSpace ℝ (Fin 3))}
    (hB : MeasurableSet B)
    {Φ : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℝ} (hΦ : Continuous Φ) (k : ℕ) :
    MeasureTheory.IntegrableOn (fun x => (Work.FockBridge.sectorPiece B k Φ x) ^ 2)
      (Submission.BoseGases.abox N L) := by
  -- Enlarge the box to a copy of positive side length containing it: `acube L ⊆ acube (max |L| 1)`.
  have hLc : L ≤ max |L| 1 := le_trans (le_abs_self L) (le_max_left _ _)
  have hc : 0 < max |L| 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hsub : abox N L ⊆ abox N (max |L| 1) := by
    rw [abox_eq_pi_acube, abox_eq_pi_acube]
    refine Set.pi_mono (fun i _ => ?_)
    intro y hy
    rw [mem_acube_iff] at hy ⊢
    intro m
    exact ⟨by linarith [(hy m).1], by linarith [(hy m).2]⟩
  -- `Φ²` is integrable over the (compact) enlarged box, hence over `abox N L`.
  have hbig : IntegrableOn (fun x : X N => (Φ x) ^ 2) (abox N (max |L| 1)) :=
    ContinuousOn.integrableOn_compact (abox_compact N hc) ((hΦ.pow 2).continuousOn)
  have hsq : IntegrableOn (fun x : X N => (Φ x) ^ 2) (abox N L) := hbig.mono_set hsub
  -- The sector indicator of `Φ²` is dominated by `Φ²`.
  have hind : IntegrableOn ((Work.FockBridge.sectorSet B k).indicator (fun x => (Φ x) ^ 2))
      (abox N L) := hsq.indicator (Work.FockBridge.sectorSet_measurable B hB k)
  -- `(1_k Φ)² = 1_k Φ²` pointwise.
  exact hind.congr_fun (fun x _ => (Work.FockBridge.sectorPiece_sq B k Φ x).symm)
    (abox_measurable N L)

end Work.FockBridge
