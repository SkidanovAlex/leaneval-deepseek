import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainDefs
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainSlot.mslot_le_gain
import Submission.Work.FTS.StrongEps.Jker_integral_eq_one

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsSqTools

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

/-! ## Auxiliary facts about the routed kernels `KdK ρ ε a b`

The routed kernels `KdK ρ ε a b = ∂₁^a∂₂^b (Jker ρ ε)` are smooth, compactly supported, and
supported in the closed ball of radius `ε`; this module collects the five facts about them that
the `ε`-square estimates use: the scaling identity in `ε` (with the change of variables
`p ↦ ε⁻¹ • p`), the bound of their mass by the level-`M` mass `Ksm`, their integrability against
functions continuous on the ball, their support bound `|p.1| + |p.2| ≤ 2ε`, and the resulting
exponential-moment estimate. -/

/-- **The change of variables `p ↦ ε⁻¹ • p`** for the rescaled kernel: the mass of `|Jker σ ε|`
equals the mass of `|σ|`.  (`Jker σ ε p = ε⁻¹ ^ 2 · σ (ε⁻¹ • p)` and the substitution has
Jacobian `ε ^ 2` in `ℝ²`.) -/
private lemma integral_abs_Jker (σ : ℝ × ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.Jker σ ε p| = ∫ p : ℝ × ℝ, |σ p| := by
  have hpt : ∀ p : ℝ × ℝ,
      |Work.FTS.StrongEps.Jker σ ε p| = ε⁻¹ ^ 2 * |σ (ε⁻¹ • p)| := by
    intro p
    simp only [Work.FTS.StrongEps.Jker, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε⁻¹ ^ 2)]
  calc ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.Jker σ ε p|
      = ∫ p : ℝ × ℝ, ε⁻¹ ^ 2 * |σ (ε⁻¹ • p)| :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = ε⁻¹ ^ 2 * ∫ p : ℝ × ℝ, |σ (ε⁻¹ • p)| := by
        rw [MeasureTheory.integral_const_mul]
    _ = ε⁻¹ ^ 2 * (ε ^ 2 * ∫ p : ℝ × ℝ, |σ p|) := by
        rw [Work.FTS.StrongEps.integral_comp_inv_smul_two (fun p => |σ p|) hε]
    _ = ∫ p : ℝ × ℝ, |σ p| := by
        rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hε.ne', one_pow, one_mul]

/-- **The routed scaling identity, integrated**: the mass of the routed derivative `∂₁^a∂₂^b`
of `Jker ρ ε` is `ε⁻¹^{a+b}` times the mass of the corresponding derivative of `ρ`. -/
private lemma integral_abs_KdK_eq (ρ : ℝ × ℝ → ℝ)
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (a b : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p|
      = ε⁻¹ ^ (a + b)
          * ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.Kdr ρ a b p| := by
  have hpt : ∀ p : ℝ × ℝ,
      |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p|
        = ε⁻¹ ^ (a + b)
            * |Work.FTS.StrongEps.Jker (Work.FTS.StrongEps.EpsE4Thr.Kdr ρ a b) ε p| := by
    intro p
    show |Work.FTS.StrongEps.Kd (Work.FTS.StrongEps.Jker ρ ε) a b p|
        = ε⁻¹ ^ (a + b)
            * |Work.FTS.StrongEps.Jker (Work.FTS.StrongEps.EpsE4Thr.Kdr ρ a b) ε p|
    rw [congrFun (Work.FTS.StrongEps.EpsE4Thr.Kd_Jker_scale_fn hρ ε a b) p, abs_mul,
      abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hε.le) _)]
  calc ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p|
      = ∫ p : ℝ × ℝ,
          ε⁻¹ ^ (a + b)
            * |Work.FTS.StrongEps.Jker (Work.FTS.StrongEps.EpsE4Thr.Kdr ρ a b) ε p| :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = ε⁻¹ ^ (a + b)
          * ∫ p : ℝ × ℝ,
              |Work.FTS.StrongEps.Jker (Work.FTS.StrongEps.EpsE4Thr.Kdr ρ a b) ε p| := by
        rw [MeasureTheory.integral_const_mul]
    _ = ε⁻¹ ^ (a + b)
          * ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.Kdr ρ a b p| := by
        rw [integral_abs_Jker (Work.FTS.StrongEps.EpsE4Thr.Kdr ρ a b) hε]

/-- **The scaling identity of the routed mass** in the exact form used by the `ε`-square
estimates: `∫ |KdK ρ ε a b| = ε⁻¹^{a+b} ∫ |KdK ρ 1 a b|`. -/
private lemma integral_abs_KdK_scale (ρ : ℝ × ℝ → ℝ)
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (a b : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p|
      = ε⁻¹ ^ (a + b)
          * ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a b p| := by
  rw [integral_abs_KdK_eq ρ hρ a b hε]
  congr 1
  rw [integral_abs_KdK_eq ρ hρ a b one_pos]
  simp

/-- **The mass of a routed kernel is at most the level-`M` mass** `Ksm ρ 1 M` (immediate from the
definition of `Ksm` as the sum over all slots of order `≤ M`). -/
private lemma integral_abs_KdK_le_Ksm (ρ : ℝ × ℝ → ℝ) {M a b : ℕ} (ha : a ≤ M) (hb : b ≤ M) :
    ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a b p|
      ≤ Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 M := by
  simp only [Work.FTS.StrongEps.EpsE4Thr.Ksm]
  calc ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a b p|
      ≤ ∑ a' ∈ Finset.range (M + 1),
          ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a' b p| :=
        Finset.single_le_sum (f := fun a' => ∫ p : ℝ × ℝ,
            |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a' b p|)
          (fun _ _ => integral_nonneg fun p => abs_nonneg _)
          (Finset.mem_range.mpr (by omega))
    _ ≤ ∑ a' ∈ Finset.range (M + 1), ∑ b' ∈ Finset.range (M + 1),
          ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a' b' p| :=
        Finset.sum_le_sum fun a' _ => Finset.single_le_sum
          (f := fun b' => ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a' b' p|)
          (fun _ _ => integral_nonneg fun p => abs_nonneg _)
          (Finset.mem_range.mpr (by omega))

/-- **The routed kernels are supported in the closed ball of radius `ε`.** -/
private lemma tsupport_KdK_subset_closedBall {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) (a b : ℕ) :
    tsupport (Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b)
      ⊆ Metric.closedBall (0 : ℝ × ℝ) ε := by
  have hS : ∀ {F : ℝ × ℝ → ℝ}, tsupport F ⊆ Metric.closedBall (0 : ℝ × ℝ) ε →
      tsupport (Work.FTS.StrongEps.partSnd F) ⊆ Metric.closedBall (0 : ℝ × ℝ) ε := by
    intro F hF
    refine closure_minimal (fun q hq => ?_) Metric.isClosed_closedBall
    exact hF (Work.FTS.StrongEps.EpsE4Thr.mem_tsupport_of_partSnd_ne_zero
      (Function.mem_support.mp hq))
  have hP : ∀ {F : ℝ × ℝ → ℝ}, tsupport F ⊆ Metric.closedBall (0 : ℝ × ℝ) ε →
      tsupport (Work.FTS.StrongEps.partFst F) ⊆ Metric.closedBall (0 : ℝ × ℝ) ε := by
    intro F hF
    refine closure_minimal (fun q hq => ?_) Metric.isClosed_closedBall
    exact hF (Work.FTS.StrongEps.EpsE4Thr.mem_tsupport_of_partFst_ne_zero
      (Function.mem_support.mp hq))
  have hbase : tsupport (Work.FTS.StrongEps.Jker ρ ε) ⊆ Metric.closedBall (0 : ℝ × ℝ) ε := by
    refine closure_minimal (fun q hq => ?_) Metric.isClosed_closedBall
    have h := Work.FTS.StrongEps.Jker_ne_zero_support hρ.moll hε (Function.mem_support.mp hq)
    have h1 : q.1 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg q.2]
    have h2 : q.2 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg q.1]
    have ha : |q.1| ≤ ε := by rw [sq_le_sq] at h1; rwa [abs_of_nonneg hε.le] at h1
    have hb : |q.2| ≤ ε := by rw [sq_le_sq] at h2; rwa [abs_of_nonneg hε.le] at h2
    rw [Metric.mem_closedBall, dist_zero_right]
    exact max_le ha hb
  induction a with
  | zero =>
    induction b with
    | zero =>
      simpa only [Work.FTS.StrongEps.EpsE4Thr.KdK, Work.FTS.StrongEps.Kd_zero_eq,
        Function.iterate_zero_apply] using hbase
    | succ b ih =>
      simpa only [Work.FTS.StrongEps.EpsE4Thr.KdK, Work.FTS.StrongEps.Kd_zero_succ] using hS ih
  | succ a ih =>
    simpa only [Work.FTS.StrongEps.EpsE4Thr.KdK, Work.FTS.StrongEps.Kd_succ_eq] using hP ih

/-- A routed kernel vanishes off the closed ball of radius `ε`. -/
private lemma KdK_eq_zero_of_notMem_closedBall {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) (a b : ℕ) {p : ℝ × ℝ}
    (hp : p ∉ Metric.closedBall (0 : ℝ × ℝ) ε) :
    Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p = 0 := by
  by_contra hne
  refine hp (tsupport_KdK_subset_closedBall hρ hε a b ?_)
  exact subset_tsupport _ (Function.mem_support.mpr hne)

/-- **The sharp support bound**: a point where a routed kernel does not vanish satisfies
`|p.1| + |p.2| ≤ 2ε`. -/
private lemma abs_KdK_sum_le_two_mul {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) (a b : ℕ) {p : ℝ × ℝ}
    (hp : Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p ≠ 0) : |p.1| + |p.2| ≤ 2 * ε := by
  have hmem : p ∈ Metric.closedBall (0 : ℝ × ℝ) ε :=
    tsupport_KdK_subset_closedBall hρ hε a b (subset_tsupport _ (Function.mem_support.mpr hp))
  have h : max |p.1| |p.2| ≤ ε := by
    simpa only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs] using hmem
  have h1 : |p.1| ≤ ε := le_trans (le_max_left _ _) h
  have h2 : |p.2| ≤ ε := le_trans (le_max_right _ _) h
  linarith

/-- **Integrability of a routed kernel against a function continuous on its support**: the product
is supported in the compact ball of radius `ε`, where it is continuous. -/
private lemma integrable_abs_KdK_mul {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) (a b : ℕ)
    {B : ℝ × ℝ → ℝ} (hB : ContinuousOn B (Metric.closedBall (0 : ℝ × ℝ) ε)) :
    Integrable (fun p : ℝ × ℝ => |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p| * B p) := by
  have hon : IntegrableOn (fun p : ℝ × ℝ => |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p| * B p)
      (Metric.closedBall (0 : ℝ × ℝ) ε) :=
    (((Work.FTS.StrongEps.EpsE4Thr.KdK_continuous hρ ε a b).abs.continuousOn).mul hB)
      |>.integrableOn_compact (isCompact_closedBall (0 : ℝ × ℝ) ε)
  refine hon.integrable_of_forall_notMem_eq_zero (fun p hp => ?_)
  rw [KdK_eq_zero_of_notMem_closedBall hρ hε a b hp, abs_zero, zero_mul]

/-- **The exponential moment of a routed kernel**: since the support has `|p.1| + |p.2| ≤ 2ε ≤ 2`,
the exponential weight is bounded by `e^{2(2c+δ)}` on it. -/
private lemma lintegral_abs_KdK_mul_exp_le {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε c δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hc : 0 ≤ c) (hδ : 0 ≤ δ) (a b : ℕ) :
    ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (|Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p|
        * Real.exp ((2 * c + δ) * (|p.1| + |p.2|)))
      ≤ ENNReal.ofReal (Real.exp (2 * (2 * c + δ))
          * ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p|) := by
  have hcd : 0 ≤ 2 * c + δ := by linarith
  have hmono : ∀ p : ℝ × ℝ,
      ENNReal.ofReal (|Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p|
          * Real.exp ((2 * c + δ) * (|p.1| + |p.2|)))
        ≤ ENNReal.ofReal (|Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p|
            * Real.exp (2 * (2 * c + δ))) := by
    intro p
    refine ENNReal.ofReal_le_ofReal ?_
    rcases eq_or_ne (Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p) 0 with h | h
    · rw [h, abs_zero, zero_mul, zero_mul]
    · have hsum := abs_KdK_sum_le_two_mul hρ hε a b h
      have h2 : |p.1| + |p.2| ≤ 2 := by linarith
      have hexp : Real.exp ((2 * c + δ) * (|p.1| + |p.2|)) ≤ Real.exp (2 * (2 * c + δ)) := by
        rw [Real.exp_le_exp]
        nlinarith [hcd, abs_nonneg p.1, abs_nonneg p.2]
      exact mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
  refine (lintegral_mono hmono).trans_eq ?_
  have hEq : ∀ p : ℝ × ℝ,
      ENNReal.ofReal (|Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p|
          * Real.exp (2 * (2 * c + δ)))
        = ENNReal.ofReal (Real.exp (2 * (2 * c + δ)))
            * ENNReal.ofReal (|Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p|) := by
    intro p
    rw [ENNReal.ofReal_mul (abs_nonneg _), mul_comm]
  have hint : Integrable (fun p : ℝ × ℝ =>
      |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p|) := by
    have h := integrable_abs_KdK_mul hρ hε a b (B := fun _ : ℝ × ℝ => (1 : ℝ))
      continuousOn_const
    simpa only [mul_one] using h
  rw [lintegral_congr hEq,
    MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun p => abs_nonneg _)]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]

theorem KdKFacts (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    (∀ {ε : ℝ}, 0 < ε → ∀ a b : ℕ,
        ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p|
          = ε⁻¹ ^ (a + b) * ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a b p|)
    ∧ (∀ {a b : ℕ}, a ≤ 3 → b ≤ 3 →
        ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a b p|
          ≤ Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3)
    ∧ (∀ {ε : ℝ}, 0 < ε → ∀ a b : ℕ, ∀ {B : ℝ × ℝ → ℝ},
        ContinuousOn B (Metric.closedBall (0 : ℝ × ℝ) ε) →
        MeasureTheory.Integrable (fun p : ℝ × ℝ => |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p| * B p))
    ∧ (∀ {ε : ℝ}, 0 < ε → ∀ a b : ℕ, ∀ {p : ℝ × ℝ},
        Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p ≠ 0 → |p.1| + |p.2| ≤ 2 * ε)
    ∧ (∀ {ε c δ : ℝ}, 0 < ε → ε ≤ 1 → 0 ≤ c → 0 ≤ δ → ∀ a b : ℕ,
        ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (|Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p|
            * Real.exp ((2 * c + δ) * (|p.1| + |p.2|)))
          ≤ ENNReal.ofReal (Real.exp (2 * (2 * c + δ))
              * ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p|)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ε hε a b
    exact integral_abs_KdK_scale ρ hρ a b hε
  · intro a b ha hb
    exact integral_abs_KdK_le_Ksm ρ ha hb
  · intro ε hε a b B hB
    exact integrable_abs_KdK_mul hρ hε a b hB
  · intro ε hε a b p hp
    exact abs_KdK_sum_le_two_mul hρ hε a b hp
  · intro ε c δ hε hε1 hc hδ a b
    exact lintegral_abs_KdK_mul_exp_le hρ hε hε1 hc hδ a b

end Work.FTS.StrongEps.EpsSqTools
