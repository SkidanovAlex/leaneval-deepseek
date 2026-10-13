import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.FTS.EllipticEst.interpol_trunc_defs
import Submission.Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeI1Fts

open MeasureTheory Set Filter
open scoped Topology

/-- The truncated gradient weight `|(cut n)'(z)| · z` is uniformly bounded in `n` and converges
pointwise to `0`; since `|g z| ≤ z hh z` with `hh ≥ 0` integrable on `(0,∞)`, dominated
convergence gives `∫_0^∞ (cut n)' g → 0`. -/
theorem cut_deriv_tendsto_zero {g : ℝ → ℝ}
    (h : ∃ hh : ℝ → ℝ, MeasureTheory.IntegrableOn hh (Set.Ioi 0) ∧ (∀ z, 0 ≤ hh z)
      ∧ ∀ z ∈ Set.Ioi 0, |g z| ≤ z * hh z) :
    Filter.Tendsto (fun n : ℕ => ∫ z in Set.Ioi 0, deriv (Work.FTS.EllipticEst.cut n) z * g z)
      Filter.atTop (nhds 0) := by
  obtain ⟨hh, hhint, hhnn, hhg⟩ := h
  obtain ⟨K, hKpos, hKbd, -, hKlim⟩ := Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform
  -- the integrable dominating profile
  have hKhh_int : MeasureTheory.Integrable (fun z : ℝ => K * hh z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := hhint.const_mul K
  -- measurability of the dominating sequence
  have hF_meas : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => |deriv (Work.FTS.EllipticEst.cut n) z| * (z * hh z))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    intro n
    exact ((measurable_deriv (Work.FTS.EllipticEst.cut n)).abs.aestronglyMeasurable).mul
      (measurable_id.aestronglyMeasurable.mul hhint.1)
  -- the pointwise domination
  have hF_bound : ∀ n : ℕ, ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ‖|deriv (Work.FTS.EllipticEst.cut n) z| * (z * hh z)‖ ≤ K * hh z := by
    intro n
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall ?_
    intro z hz
    have hznn : (0 : ℝ) ≤ z := le_of_lt hz
    have h1 : |deriv (Work.FTS.EllipticEst.cut n) z| * (z * hh z)
        = |z * deriv (Work.FTS.EllipticEst.cut n) z| * hh z := by
      rw [abs_mul, abs_of_nonneg hznn]; ring
    rw [Real.norm_eq_abs, h1, abs_of_nonneg (mul_nonneg (abs_nonneg _) (hhnn z))]
    exact mul_le_mul_of_nonneg_right (hKbd n z) (hhnn z)
  -- pointwise convergence
  have hF_lim : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun n : ℕ => |deriv (Work.FTS.EllipticEst.cut n) z| * (z * hh z))
        Filter.atTop (nhds 0) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall ?_
    intro z hz
    have hznn : (0 : ℝ) ≤ z := le_of_lt hz
    have h1 : (fun n : ℕ => |deriv (Work.FTS.EllipticEst.cut n) z| * (z * hh z))
        = fun n : ℕ => |z * deriv (Work.FTS.EllipticEst.cut n) z| * hh z := by
      funext n
      rw [abs_mul, abs_of_nonneg hznn]; ring
    rw [h1]
    have h2 : Filter.Tendsto (fun n : ℕ => |z * deriv (Work.FTS.EllipticEst.cut n) z|)
        Filter.atTop (nhds 0) := by
      simpa using (hKlim z).abs
    simpa using h2.mul_const (hh z)
  -- dominated convergence
  have hmain : Filter.Tendsto
      (fun n : ℕ => ∫ z in Set.Ioi 0,
        |deriv (Work.FTS.EllipticEst.cut n) z| * (z * hh z)) Filter.atTop (nhds 0) := by
    have hD := MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := MeasureTheory.volume.restrict (Set.Ioi 0))
      (F := fun n z => |deriv (Work.FTS.EllipticEst.cut n) z| * (z * hh z))
      (f := fun _ => (0 : ℝ)) (fun z => K * hh z) hF_meas hKhh_int hF_bound hF_lim
    simpa using hD
  -- the comparison of the two integrals
  have hle : ∀ n : ℕ,
      ‖∫ z in Set.Ioi 0, deriv (Work.FTS.EllipticEst.cut n) z * g z‖
        ≤ ∫ z in Set.Ioi 0, |deriv (Work.FTS.EllipticEst.cut n) z| * (z * hh z) := by
    intro n
    refine MeasureTheory.norm_integral_le_of_norm_le ?_ ?_
    · exact MeasureTheory.Integrable.mono' hKhh_int (hF_meas n) (hF_bound n)
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall ?_
      intro z hz
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hhg z hz) (abs_nonneg _)
  exact squeeze_zero_norm hle hmain

end Work.FTS.EllipticEst.AeI1Fts
