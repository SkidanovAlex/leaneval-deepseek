import Mathlib
import Submission.Work.BoxShrink.sweepNice_of_ae
import Submission.Work.BoxShrink.cruxAE

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set in
open scoped ENNReal Topology in
/-- **A level in an arbitrary conull set, where the box-sphere count holds.**

For *any* conull set `P` of levels there is a level `s ∈ (r, (1+ε) r)` in `P` at which the number of
parameters of the knot on the box sphere `{y | boxNorm c σ y = s}` is at most `10 (1+ε) / ε · d`.
This is the pigeonhole part of `Work.BoxShrink.SweepNice.of_aeAll`: the proof is
`Work.BoxShrink.exists_of_ae_and_lintegral` applied to the level-count function of
`Work.BoxSweep.boxNormCurve`, whose integral bound is
`Work.BoxSweep.lintegral_boxNorm_levelCount_le` composed with
`Work.Sweep.arclengthIn_closedBall_le` (and the arithmetic `cc - r = ε r`, `4 d (5/2 cc) = 10 d cc`
with `cc = (1+ε) r`).  The caller puts *all* the genericity conditions it needs (slicing, general
position of the box sphere, ...) into `P`. -/
theorem exists_level_of_ae_count (K : Knot) {d : ℝ} (hd : 0 ≤ d)
    (hbound : Work.Sweep.IsDistortionBound K d) :
    ∀ (r : ℝ) (hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)) (P : ℝ → Prop),
      (∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), P s) →
      ∃ s ∈ Set.Ioo r ((1 + Submission.eps) * r), P s ∧
        ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
            Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
          ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) := by
  intro r hr c σ P hP
  classical
  set cc : ℝ := (1 + Submission.eps) * r with hcc
  have hrcc : r ≤ cc := by rw [hcc]; nlinarith [Submission.eps_pos]
  have hrcc_lt : r < cc := by rw [hcc]; nlinarith [Submission.eps_pos]
  have hC1_0 : 0 ≤ 10 * (1 + Submission.eps) / Submission.eps * d := by
    have h' : 10 * (1 + Submission.eps) / Submission.eps = 75 := by norm_num [Submission.eps]
    rw [h']; positivity
  -- the integral pigeonhole bound of the sweep
  have hint : ∫⁻ s in Set.Ioo r cc,
        Work.Sweep.levelCount (Work.BoxSweep.boxNormCurve K c σ) (Set.Icc 0 (2 * Real.pi)) s
      ≤ ENNReal.ofReal ((10 * (1 + Submission.eps) / Submission.eps * d) * (cc - r)) := by
    refine (Work.BoxSweep.lintegral_boxNorm_levelCount_le K c σ hr hrcc).trans ?_
    refine (Work.Sweep.arclengthIn_closedBall_le (K := K) hd hbound c (R := 5 / 2 * cc)).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have h' : 10 * (1 + Submission.eps) / Submission.eps * d * (cc - r) = 10 * d * cc := by
      have heps : (Submission.eps : ℝ) ≠ 0 := ne_of_gt Submission.eps_pos
      have hccdiff : cc - r = Submission.eps * r := by rw [hcc]; ring
      rw [hccdiff, hcc]
      calc 10 * (1 + Submission.eps) / Submission.eps * d * (Submission.eps * r)
          = 10 * d * ((1 + Submission.eps) / Submission.eps * Submission.eps * r) := by ring
        _ = 10 * d * ((1 + Submission.eps) * r) := by rw [div_mul_cancel₀ _ heps]
        _ = 10 * d * ((1 + Submission.eps) * r) := by ring
    rw [h', show 4 * d * (5 / 2 * cc) = 10 * d * cc by ring]
  -- intersect the conull set of general-position levels with the pigeonhole bound
  obtain ⟨s, hs, hPs, hcnt⟩ := Work.BoxShrink.exists_of_ae_and_lintegral
    (f := Work.Sweep.levelCount (Work.BoxSweep.boxNormCurve K c σ) (Set.Icc 0 (2 * Real.pi)))
    (A := {s : ℝ | P s}) hrcc_lt hC1_0
    (fun s => Work.BoxSweep.levelCount_eq_top_or_nat _ _ s) hP hint
  refine ⟨s, ?_, hPs, ?_⟩
  · exact hs
  · -- count with the half-open fundamental interval
    have hconv : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
          Submission.boxNorm c σ (K.curve t) = s}) : ENNReal))
        ≤ Work.Sweep.levelCount (Work.BoxSweep.boxNormCurve K c σ)
            (Set.Icc 0 (2 * Real.pi)) s := by
      rw [Work.Sweep.levelCount_eq_encard]
      refine ENat.toENNReal_le.mpr (Set.encard_le_encard ?_)
      rintro t ⟨ht1, ht2⟩
      exact ⟨Set.Ico_subset_Icc_self ht1, ht2⟩
    exact hconv.trans hcnt

end Work.Drive.Mono
