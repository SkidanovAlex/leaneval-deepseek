import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.EllipticEst.interpol_trunc_defs
import Submission.Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform
import Submission.Work.FTS.EllipticEst.Final.FlatCut.cutMono
import Submission.Work.FTS.EllipticEst.Final.FlatCut.cutTendstoOne

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A cutoff family whose weighted derivative mass tends to `0`

For `g ∈ L¹(0,∞)` we build a sequence of `C¹` cutoffs `χ_n`, of compact support inside `(0,∞)`,
with `0 ≤ χ_n ≤ 1`, monotone in `n`, tending to `1` pointwise on `(0,∞)`, and such that

`∫_{z>0} |χ_n'(z)| · (z |g z|) dz → 0`.

The family used is the in-tree `Work.FTS.EllipticEst.cut n`: its derivative satisfies the uniform
bound `|z · (cut n)' z| ≤ K` (`AngSecond.cut_deriv_uniform`), and it vanishes identically where
the cutoff is flat-`1`.  Hence the integrand `|(cut n)' z| · z |g z| = |z (cut n)' z| · |g z|`
is dominated by `K |g| ∈ L¹` and converges pointwise to `0` (for each fixed `z > 0` the cutoff
is eventually `1` on a neighbourhood of `z`), so dominated convergence gives the limit.  The key
point is that `|z (cut n)' z| ≤ K` is *uniform* in `n`.
-/

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk

open MeasureTheory Set Filter

/-- The support of `cut n` lies in the compact slab `[1/(n+1), 3(n+1)]`. -/
private theorem support_cut_subset (n : ℕ) :
    Function.support (Work.FTS.EllipticEst.cut n) ⊆
      Set.Icc (1 / ((n : ℝ) + 1)) (3 * ((n : ℝ) + 1)) := by
  intro z hz
  simp only [Function.mem_support] at hz
  by_contra hc
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hc
  rcases hc with hc | hc
  · exact hz (Work.FTS.EllipticEst.cut_apply_zero_of_le n (le_of_lt hc))
  · exact hz (Work.FTS.EllipticEst.cut_apply_zero_of_ge n (le_of_lt hc))

theorem chiDerivLimit (g : ℝ → ℝ) (hg : MeasureTheory.IntegrableOn g (Set.Ioi 0)) :
    ∃ χn : ℕ → ℝ → ℝ,
      (∀ n, ContDiff ℝ 1 (χn n)) ∧
      (∀ n, HasCompactSupport (χn n)) ∧
      (∀ n, tsupport (χn n) ⊆ Set.Ioi (0 : ℝ)) ∧
      (∀ n z, 0 ≤ χn n z) ∧ (∀ n z, χn n z ≤ 1) ∧
      (∀ z, 0 < z → Filter.Tendsto (fun n => χn n z) Filter.atTop (nhds 1)) ∧
      (∀ z, Monotone (fun n => χn n z)) ∧
      Filter.Tendsto (fun n => ∫ z in Set.Ioi 0, |deriv (χn n) z| * (z * |g z|))
        Filter.atTop (nhds 0) := by
  obtain ⟨K, _hKpos, hKbd, _hKone, hKderiv⟩ :=
    Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform
  refine ⟨Work.FTS.EllipticEst.cut, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (Work.FTS.EllipticEst.cut_contDiff n).of_le (by
      rw [Work.Stability.smoothOrder]
      exact WithTop.coe_le_coe.mpr le_top)
  · intro n
    exact IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
      (closure_minimal (support_cut_subset n) isClosed_Icc)
  · intro n z hz
    exact lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))
      ((closure_minimal (support_cut_subset n) isClosed_Icc) hz).1
  · intro n z
    exact Work.FTS.EllipticEst.cut_nonneg n z
  · intro n z
    exact Work.FTS.EllipticEst.cut_le_one n z
  · intro z hz
    exact Work.FTS.EllipticEst.Final.FlatCut.cutTendstoOne z hz
  · intro z
    exact monotone_nat_of_le_succ fun n => Work.FTS.EllipticEst.Final.FlatCut.cutMono n z
  · -- the weighted `L¹`-mass of the transition layers tends to `0`
    set μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) with hμ
    have hgint : MeasureTheory.Integrable g μ := by
      rw [hμ]; exact hg.integrable
    have hbnd_int : MeasureTheory.Integrable (fun z : ℝ => K * |g z|) μ := by
      simpa [Real.norm_eq_abs] using hgint.norm.const_mul K
    have hF_meas : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ => |deriv (Work.FTS.EllipticEst.cut n) z| * (z * |g z|)) μ := by
      intro n
      have hcd : ContDiff ℝ 1 (Work.FTS.EllipticEst.cut n) :=
        (Work.FTS.EllipticEst.cut_contDiff n).of_le (by
          rw [Work.Stability.smoothOrder]
          exact WithTop.coe_le_coe.mpr le_top)
      have hc : Continuous (fun z : ℝ => |deriv (Work.FTS.EllipticEst.cut n) z|) :=
        (hcd.continuous_deriv le_rfl).abs
      have hgabs : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => |g z|) μ := by
        simpa [Real.norm_eq_abs] using hgint.aestronglyMeasurable.norm
      have hid : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => z) μ :=
        continuous_id.aestronglyMeasurable
      exact MeasureTheory.AEStronglyMeasurable.mul
        (f := fun z : ℝ => |deriv (Work.FTS.EllipticEst.cut n) z|)
        (g := fun z : ℝ => z * |g z|) hc.aestronglyMeasurable (hid.mul hgabs)
    have h_bound : ∀ n : ℕ, ∀ᵐ z ∂μ,
        ‖|deriv (Work.FTS.EllipticEst.cut n) z| * (z * |g z|)‖ ≤ K * |g z| := by
      intro n
      rw [hμ]
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall fun z hz => ?_)
      have hz0 : (0 : ℝ) ≤ z := le_of_lt hz
      have hnn : 0 ≤ |deriv (Work.FTS.EllipticEst.cut n) z| * (z * |g z|) :=
        mul_nonneg (abs_nonneg _) (mul_nonneg hz0 (abs_nonneg _))
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have hkey : |deriv (Work.FTS.EllipticEst.cut n) z| * (z * |g z|)
          = |z * deriv (Work.FTS.EllipticEst.cut n) z| * |g z| := by
        rw [abs_mul, abs_of_nonneg hz0]
        ring
      rw [hkey]
      exact mul_le_mul_of_nonneg_right (hKbd n z) (abs_nonneg _)
    have h_lim : ∀ᵐ z ∂μ,
        Filter.Tendsto
          (fun n : ℕ => |deriv (Work.FTS.EllipticEst.cut n) z| * (z * |g z|))
          Filter.atTop (nhds 0) := by
      rw [hμ]
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall fun z hz => ?_)
      have hz0 : z ≠ 0 := ne_of_gt hz
      have hd : Filter.Tendsto (fun n : ℕ => deriv (Work.FTS.EllipticEst.cut n) z)
          Filter.atTop (nhds 0) := by
        have h := (hKderiv z).div_const z
        rw [zero_div] at h
        exact h.congr' (Filter.Eventually.of_forall fun n =>
          mul_div_cancel_left₀ (deriv (Work.FTS.EllipticEst.cut n) z) hz0)
      have := (hd.abs).mul_const (z * |g z|)
      simpa using this
    have hmain : Filter.Tendsto
        (fun n : ℕ => ∫ z, |deriv (Work.FTS.EllipticEst.cut n) z| * (z * |g z|) ∂μ)
        Filter.atTop (nhds 0) := by
      have := MeasureTheory.tendsto_integral_of_dominated_convergence
        (μ := μ)
        (F := fun n z => |deriv (Work.FTS.EllipticEst.cut n) z| * (z * |g z|))
        (f := fun _ : ℝ => (0 : ℝ)) (fun z : ℝ => K * |g z|) hF_meas hbnd_int h_bound h_lim
      simpa using this
    simpa [hμ] using hmain

end Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk
