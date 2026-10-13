import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllSol.EllPkgAux.MollDzAux.thMoll_hasDerivAt
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

/-- **The logarithmic Schur bound on the window, with the `L²` window norm on the right.**

For `δ > 0` and any `z`, the functional `y ↦ ∫ t, sKerd δ (log z - t) · y t` is bounded on
`L²({t | |log z - t| ≤ δ})`; the constant can be taken to be `1 + ∫_{|log z - t| ≤ δ} sKerd δ²`,
which is positive and finite because `sKerd δ` is continuous with compact support.

The proof is Cauchy–Schwarz (`Work.Spaces.cs_integral`) on the window
`S = [log z - δ, log z + δ]`: the kernel vanishes off `S`, so the integral defining the
functional is already an integral over `S`. -/
theorem schur_sq_window_le (δ z : ℝ) (hδ : 0 < δ) (hz : 0 < z) :
    ∃ A : ℝ, 0 < A ∧ ∀ (y : ℝ → ℝ), Continuous y →
      (∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * y t) ^ 2
        ≤ A * (∫ t : ℝ, if |Real.log z - t| ≤ δ then (y t) ^ 2 else 0) := by
  -- The window on which the kernel lives.
  set S : Set ℝ := Set.Icc (Real.log z - δ) (Real.log z + δ) with hSdef
  have hSmeas : MeasurableSet S := by rw [hSdef]; exact measurableSet_Icc
  have hScomp : IsCompact S := by rw [hSdef]; exact isCompact_Icc
  -- `volume.restrict S` is a finite measure: `S` is a compact interval.
  haveI hSfin : IsFiniteMeasure (volume.restrict S) := by
    rw [MeasureTheory.isFiniteMeasure_restrict, hSdef, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  -- Membership in `S` is membership in the window.
  have hmem : ∀ t : ℝ, t ∈ S ↔ |Real.log z - t| ≤ δ := by
    intro t
    rw [hSdef, Set.mem_Icc, abs_le]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
  -- The kernel `t ↦ sKerd δ (log z - t)` is continuous and vanishes off `S`.
  have hKcont : Continuous (fun t : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t)) :=
    (Work.FTS.EllSol.EllPkgAux.MollDzAux.continuous_sKerd δ).comp
      (continuous_const.sub continuous_id)
  have hKzero : ∀ t : ℝ, t ∉ S → Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) = 0 := by
    intro t ht
    refine Work.FTS.EllSol.EllPkgAux.MollDzAux.sKerd_eq_zero_of_lt_abs hδ ?_
    exact lt_of_not_ge (fun hc => ht ((hmem t).mpr hc))
  -- The kernel is bounded on the window, hence square-integrable there.
  obtain ⟨C, hC⟩ := hScomp.exists_bound_of_continuousOn hKcont.continuousOn
  have hKmem : MemLp (fun t : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t)) 2
      (volume.restrict S) :=
    MemLp.of_bound hKcont.aestronglyMeasurable C
      (ae_restrict_of_forall_mem hSmeas (fun t ht => hC t ht))
  refine ⟨1 + ∫ t in S, (Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t)) ^ 2, ?_, ?_⟩
  · have hnn : (0 : ℝ) ≤ ∫ t in S, (Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t)) ^ 2 :=
      integral_nonneg (fun t => sq_nonneg _)
    linarith
  · intro y hy
    -- `y` is bounded on the window, hence square-integrable there.
    obtain ⟨D, hD⟩ := hScomp.exists_bound_of_continuousOn hy.continuousOn
    have hymem : MemLp y 2 (volume.restrict S) :=
      MemLp.of_bound hy.aestronglyMeasurable D
        (ae_restrict_of_forall_mem hSmeas (fun t ht => hD t ht))
    -- Cauchy–Schwarz on the window.
    have hcs := Work.Spaces.cs_integral (s := S) hKmem hymem
    -- The integral of the kernel against `y` is already an integral over the window.
    have hset : ∫ t in S, (Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t)) * y t
        = ∫ t : ℝ, (Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t)) * y t :=
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun t ht => by rw [hKzero t ht, zero_mul])
    have hnn : 0 ≤ ∫ t in S, y t ^ 2 := integral_nonneg (fun t => sq_nonneg (y t))
    -- The window `L²`-norm as displayed in the statement.
    have hwind : (∫ t in S, y t ^ 2)
        = ∫ t : ℝ, if |Real.log z - t| ≤ δ then y t ^ 2 else 0 := by
      rw [← MeasureTheory.integral_indicator (f := fun t : ℝ => y t ^ 2) hSmeas]
      refine integral_congr_ae (Eventually.of_forall (fun t => ?_))
      simp only [Set.indicator_apply, hmem t]
    calc (∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * y t) ^ 2
        = (∫ t in S, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * y t) ^ 2 := by
          rw [hset]
      _ ≤ (∫ t in S, (Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t)) ^ 2)
            * (∫ t in S, y t ^ 2) := hcs
      _ ≤ (1 + ∫ t in S, (Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t)) ^ 2)
            * (∫ t in S, y t ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith) hnn
      _ = (1 + ∫ t in S, (Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t)) ^ 2)
            * (∫ t : ℝ, if |Real.log z - t| ≤ δ then y t ^ 2 else 0) := by rw [hwind]

end Work.FTS.EllSol.EllPkgAux.MollDom
