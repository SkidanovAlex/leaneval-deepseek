import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Stability.Cutoff
import Submission.Work.FTS.EllipticEst.TT.logCutDefs
import Submission.Work.FTS.EllipticEst.Blocks.logChiFamily

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst

open MeasureTheory
open Filter

/-- The logarithmic cut-off `logChi n` is measurable: it is the explicit `C^∞` bump
`Work.ChiExplicit.chi` composed with the measurable function `z ↦ log z / log ((n:ℝ)+2)`. -/
lemma measurable_logChi (n : ℕ) :
    Measurable (Work.FTS.EllipticEst.TT.logChi n) :=
  ((Work.ChiExplicit.chi_contDiff 1).continuous.measurable).comp
    (Real.measurable_log.div_const _)

/-- **Monotone convergence along the logarithmic cut-off family**: for a nonnegative
a.e.-measurable `f` on `(0,∞)` (each `f·logChi n²` integrable),

`∫⁻ f = ⨆_n ofReal (∫ f · (logChi n)²)`.

This is Piece 3b of `Submission/Work/EllipticEst/NOTES_AgmonCutoff.md`; it uses
`logChi_mem_Icc`, `logChi_mono_succ`, `logChi_tendsto_one` and monotone convergence. -/
theorem logChi_iSup_lintegral (f : ℝ → ℝ) (hf0 : ∀ z : ℝ, 0 ≤ f z)
    (hfm : AEMeasurable f (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hint : ∀ n : ℕ, MeasureTheory.IntegrableOn
      (fun z : ℝ => f z * (Work.FTS.EllipticEst.TT.logChi n z) ^ 2) (Set.Ioi (0 : ℝ))) :
    (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal (f z))
      = ⨆ n : ℕ, ENNReal.ofReal
          (∫ z in Set.Ioi (0 : ℝ), f z * (Work.FTS.EllipticEst.TT.logChi n z) ^ 2) := by
  -- The truncated integrands are increasing in `n`: `f ≥ 0` and `0 ≤ logChi n ≤ logChi (n+1)`.
  have hmono : ∀ n : ℕ, ∀ z : ℝ,
      f z * (Work.FTS.EllipticEst.TT.logChi n z) ^ 2
        ≤ f z * (Work.FTS.EllipticEst.TT.logChi (n + 1) z) ^ 2 := by
    intro n z
    have h0 : 0 ≤ Work.FTS.EllipticEst.TT.logChi n z :=
      (Work.FTS.EllipticEst.TT.logChi_mem_Icc n z).1
    have hle : Work.FTS.EllipticEst.TT.logChi n z
        ≤ Work.FTS.EllipticEst.TT.logChi (n + 1) z :=
      Work.FTS.EllipticEst.Blocks.logChi_mono_succ n z
    have hs : (Work.FTS.EllipticEst.TT.logChi n z) ^ 2
        ≤ (Work.FTS.EllipticEst.TT.logChi (n + 1) z) ^ 2 := by
      simpa [pow_two] using mul_self_le_mul_self h0 hle
    exact mul_le_mul_of_nonneg_left hs (hf0 z)
  -- Pointwise convergence `f · (logChi n)² → f` on `(0,∞)`.
  have hten : ∀ z : ℝ, 0 < z → Tendsto
      (fun n : ℕ => f z * (Work.FTS.EllipticEst.TT.logChi n z) ^ 2) atTop (nhds (f z)) := by
    intro z hz
    have h1 := Work.FTS.EllipticEst.Blocks.logChi_tendsto_one z hz
    have h2 : Tendsto (fun n : ℕ => (Work.FTS.EllipticEst.TT.logChi n z) ^ 2)
        atTop (nhds 1) := by
      simpa using h1.pow 2
    simpa using (tendsto_const_nhds.mul h2)
  -- The pointwise supremum of the (monotone, convergent) family, on `(0,∞)`.
  have hsup : ∀ z : ℝ, 0 < z →
      (⨆ n : ℕ, ENNReal.ofReal (f z * (Work.FTS.EllipticEst.TT.logChi n z) ^ 2))
        = ENNReal.ofReal (f z) := by
    intro z hz
    refine iSup_eq_of_tendsto ?_ ?_
    · exact monotone_nat_of_le_succ fun n => ENNReal.ofReal_le_ofReal (hmono n z)
    · exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hten z hz)
  have hae : (fun z : ℝ =>
        (⨆ n : ℕ, ENNReal.ofReal (f z * (Work.FTS.EllipticEst.TT.logChi n z) ^ 2)))
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))] fun z : ℝ => ENNReal.ofReal (f z) :=
    (ae_restrict_iff' isOpen_Ioi.measurableSet).mpr
      (Eventually.of_forall fun z hz => hsup z hz)
  calc (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal (f z))
      = ∫⁻ z in Set.Ioi (0 : ℝ),
          (⨆ n : ℕ, ENNReal.ofReal (f z * (Work.FTS.EllipticEst.TT.logChi n z) ^ 2)) :=
        (lintegral_congr_ae hae).symm
    _ = ⨆ n : ℕ, ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (f z * (Work.FTS.EllipticEst.TT.logChi n z) ^ 2) := by
        refine lintegral_iSup' (fun n => ?_) (Eventually.of_forall fun z => ?_)
        · exact (hfm.mul ((measurable_logChi n).pow_const 2).aemeasurable).ennreal_ofReal
        · exact monotone_nat_of_le_succ fun n => ENNReal.ofReal_le_ofReal (hmono n z)
    _ = ⨆ n : ℕ, ENNReal.ofReal
          (∫ z in Set.Ioi (0 : ℝ), f z * (Work.FTS.EllipticEst.TT.logChi n z) ^ 2) :=
        iSup_congr fun n =>
          (ofReal_integral_eq_lintegral_ofReal (hint n)
            (Eventually.of_forall fun z => mul_nonneg (hf0 z) (sq_nonneg _))).symm

end Work.EllipticEst
