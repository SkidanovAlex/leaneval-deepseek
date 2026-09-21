import Mathlib
import Submission.Work.OddCurve.LowSlope.GlueDefs
import Submission.Work.OddRadon.radonProfile_radonInverse_local

/-!
# The reconstructed body's Radon datum is the glued datum

`radonInverseRhoNewEq` identifies `radonInverse n (radonPhi n (rhoNew R r))` with
`radonInverse n (GlueF n ρa)` on `(0,b)`.  Since `radonInverse n` is a *right* inverse of
`radonProfile (2n+1)` (`radonProfile_radonInverse_local`), this identifies the data themselves:

  `radonPhi n (rhoNew R r) = GlueF n ρa`   on `(0,b)`.

That is the statement that the reconstructed body has the prescribed (glued) spherical-Radon
datum — the Step-3 bridge between the two-power system and the moment equations.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

theorem radonPhiRhoNewEq (n : ℕ) (hn : 1 ≤ n) {ρa R r : ℝ → ℝ} {b : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1)
    (hsmPhi : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Work.OddCurve.LowSlope.radonPhi n (Work.OddCurve.LowSlope.rhoNew R r)) (Set.Icc 0 b))
    (hsmG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Work.OddCurve.LowSlope.GlueF n ρa) (Set.Icc 0 b))
    (hkey : ∀ u ∈ Set.Ioo (0 : ℝ) b, Work.OddRadon.radonInverse n
        (Work.OddCurve.LowSlope.radonPhi n (Work.OddCurve.LowSlope.rhoNew R r)) u
      = Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.GlueF n ρa) u) :
    ∀ c ∈ Set.Ioo (0 : ℝ) b,
      Work.OddCurve.LowSlope.radonPhi n (Work.OddCurve.LowSlope.rhoNew R r) c
        = Work.OddCurve.LowSlope.GlueF n ρa c := by
  intro c hc
  have h1 : Work.OddRadon.radonProfile (2 * n + 1)
      (fun u : ℝ => Work.OddRadon.radonInverse n
        (radonPhi n (rhoNew R r)) |u|) c = radonPhi n (rhoNew R r) c :=
    Work.OddRadon.radonProfile_radonInverse_local n hn hb hb1 hsmPhi
      (radonPhi_neg n (rhoNew R r)) c hc
  have h2 : Work.OddRadon.radonProfile (2 * n + 1)
      (fun u : ℝ => Work.OddRadon.radonInverse n (GlueF n ρa) |u|) c = GlueF n ρa c :=
    Work.OddRadon.radonProfile_radonInverse_local n hn hb hb1 hsmG
      (GlueF_even n ρa) c hc
  rw [← h1, ← h2]
  simp only [Work.OddRadon.radonProfile]
  congr 1
  have hcompl : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ ({0} : Set ℝ) :=
    MeasureTheory.compl_mem_ae_iff.mpr ((Set.finite_singleton (0 : ℝ)).measure_zero volume)
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hcompl] with s hs hmem
  have hs1 : |s| ≤ 1 := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have h : (-1 : ℝ) < s := by
        simpa [min_eq_left (by norm_num : (-1 : ℝ) ≤ 1)] using hmem.1
      linarith
    · have h : s ≤ (1 : ℝ) := by
        simpa [max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)] using hmem.2
      linarith
  have hsne : s ≠ 0 := by simpa using hs
  have habs : |c * s| < b := by
    rw [abs_mul, abs_of_pos hc.1]
    calc c * |s| ≤ c * 1 := mul_le_mul_of_nonneg_left hs1 hc.1.le
      _ = c := mul_one c
      _ < b := hc.2
  have hpos : 0 < |c * s| := abs_pos.mpr (mul_ne_zero (ne_of_gt hc.1) hsne)
  rw [hkey |c * s| ⟨hpos, habs⟩]

end

end Work.OddCurve.LowSlope
