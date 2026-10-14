import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.FinalClock.HkIntegrandMulDthSmooth
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainDefs
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongEps.mixed_Jeps_kernel_partial
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNstarBlock
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gAuxDefs
import Submission.Work.FTS.StrongPersist.L3Rhs.N3ssPriced
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.leibnizRem6
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Row19 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The vocabulary of the row -/





/-! ## The row -/


end Work.FTS.Nonlinear.Open
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.DiffAux.ShadowPointwise =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.DiffAux

open Work.FTS.StrongEps (Quad zShift thShift Jker Jeps sin_two_pos)

set_option autoImplicit false
set_option maxHeartbeats 4000000

variable {ρ : ℝ × ℝ → ℝ} {ε c δ : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}

/-! ## The pointwise sum of brackets against the shadow -/

theorem sum_bracket_le_shadow {α : ℝ} (hα : α ∈ Set.Ioc 0 1) (k : ℕ)
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) (y : (ℝ × ℝ) × ℝ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (∑ i ∈ Finset.range (k + 1), bracket (Work.Spaces.DzIter i f) wE z θ y.1 y.2)
      + (∑ q ∈ slots k, bracket (Work.Spaces.mixed q.2 q.1 f) (Work.Spaces.Wt α) z θ y.1 y.2)
      ≤ shadow α k f (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2)) := by
  have hsQ : (zShift z (y.2 * y.1.1), thShift θ (y.2 * y.1.2)) ∈ Quad :=
    shift_mem_Quad hz hθ y
  have hsm : Work.FTS.StrongEps.SmQ (Work.Spaces.DthIter 1 f) :=
    (Work.FTS.StrongEps.smQ_of_forall_nat hf).DthIter 1
  have h1 : ∀ i ∈ Finset.range (k + 1),
      bracket (Work.Spaces.DzIter i f) wE z θ y.1 y.2
        ≤ (Work.Spaces.DzIter (i + 1) f (zShift z (y.2 * y.1.1))
              (thShift θ (y.2 * y.1.2))
            * wE (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) ^ 2
          + 1 / 4 * (Work.Spaces.mixed i 1 f (zShift z (y.2 * y.1.1))
              (thShift θ (y.2 * y.1.2))
            * Work.Spaces.Wt α (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) ^ 2 := by
    intro i _
    have hcomm := Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
      isOpen_Quad hf i 1 hsQ
    have hDth : Work.Spaces.Dth (Work.Spaces.DzIter i f) (zShift z (y.2 * y.1.1))
        (thShift θ (y.2 * y.1.2)) = Work.Spaces.mixed i 1 f (zShift z (y.2 * y.1.1))
          (thShift θ (y.2 * y.1.2)) := hcomm
    have hle : wE (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))
        ≤ Work.Spaces.Wt α (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2)) :=
      wE_le_Wt (z := zShift z (y.2 * y.1.1)) hα hsQ.2
    have hnn : 0 ≤ wE (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2)) :=
      wE_nonneg hsQ.2
    rw [bracket, ← Work.Spaces.DzIter_succ, hDth]
    have h2 : (wE (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))
        * Work.Spaces.mixed i 1 f (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) ^ 2
        ≤ (Work.Spaces.mixed i 1 f (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))
          * Work.Spaces.Wt α (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) ^ 2 := by
      calc (wE (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))
            * Work.Spaces.mixed i 1 f (zShift z (y.2 * y.1.1))
              (thShift θ (y.2 * y.1.2))) ^ 2
          = (Work.Spaces.mixed i 1 f (zShift z (y.2 * y.1.1))
              (thShift θ (y.2 * y.1.2))) ^ 2
            * (wE (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) ^ 2 := by ring
        _ ≤ (Work.Spaces.mixed i 1 f (zShift z (y.2 * y.1.1))
              (thShift θ (y.2 * y.1.2))) ^ 2
            * (Work.Spaces.Wt α (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnn hle 2) (sq_nonneg _)
        _ = (Work.Spaces.mixed i 1 f (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))
            * Work.Spaces.Wt α (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) ^ 2 := by ring
    have h3 : (wE (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))
        * Work.Spaces.DzIter (i + 1) f (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) ^ 2
        = (Work.Spaces.DzIter (i + 1) f (zShift z (y.2 * y.1.1))
            (thShift θ (y.2 * y.1.2))
          * wE (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) ^ 2 := by rw [mul_comm]
    rw [h3]
    linarith [h2]
  have h2 : ∀ q ∈ slots k,
      bracket (Work.Spaces.mixed q.2 q.1 f) (Work.Spaces.Wt α) z θ y.1 y.2
        ≤ (Work.Spaces.mixed (q.2 + 1) q.1 f (zShift z (y.2 * y.1.1))
              (thShift θ (y.2 * y.1.2))
            * Work.Spaces.Wt α (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) ^ 2
          + 1 / 4 * (Work.Spaces.mixed q.2 (q.1 + 1) f (zShift z (y.2 * y.1.1))
              (thShift θ (y.2 * y.1.2))
            * Work.Spaces.Wt α (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) ^ 2 := by
    intro q _
    have hcomm := Work.FTS.EllipticEst.ThetaU.OpenSliceAux.Dth_DzIter_eqOn_of_smooth
      isOpen_Quad ((Work.FTS.StrongEps.smQ_of_forall_nat hf).DthIter q.1) q.2 hsQ
    have hDth : Work.Spaces.Dth (Work.Spaces.mixed q.2 q.1 f)
        (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))
        = Work.Spaces.mixed q.2 (q.1 + 1) f (zShift z (y.2 * y.1.1))
          (thShift θ (y.2 * y.1.2)) := hcomm
    rw [bracket,
      show Work.Spaces.Dz (Work.Spaces.mixed q.2 q.1 f) = Work.Spaces.mixed (q.2 + 1) q.1 f
        from rfl,
      hDth]
    exact le_of_eq (by ring)
  have hsum1 := Finset.sum_le_sum h1
  have hsum2 := Finset.sum_le_sum h2
  have hsum1' : (∑ i ∈ Finset.range (k + 1), bracket (Work.Spaces.DzIter i f) wE z θ y.1 y.2)
      ≤ (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter (i + 1) f (zShift z (y.2 * y.1.1))
              (thShift θ (y.2 * y.1.2))
            * wE (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) ^ 2)
        + 1 / 4 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.mixed i 1 f (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))
              * Work.Spaces.Wt α (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) ^ 2) := by
    have := hsum1
    rwa [Finset.sum_add_distrib, ← Finset.mul_sum] at this
  have hsum2' : (∑ q ∈ slots k,
        bracket (Work.Spaces.mixed q.2 q.1 f) (Work.Spaces.Wt α) z θ y.1 y.2)
      ≤ (∑ q ∈ slots k, (Work.Spaces.mixed (q.2 + 1) q.1 f (zShift z (y.2 * y.1.1))
              (thShift θ (y.2 * y.1.2))
            * Work.Spaces.Wt α (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) ^ 2)
        + 1 / 4 * (∑ q ∈ slots k,
            (Work.Spaces.mixed q.2 (q.1 + 1) f (zShift z (y.2 * y.1.1))
              (thShift θ (y.2 * y.1.2))
              * Work.Spaces.Wt α (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) ^ 2) := by
    have := hsum2
    rwa [Finset.sum_add_distrib, ← Finset.mul_sum] at this
  rw [shadow]
  linarith [hsum1', hsum2']


end Work.FTS.StrongEps.DiffAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.GainSlot.mslot_le_gain =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.GainSlot

/-! ## Auxiliary facts about the routed kernels `KdK ρ ε a b`

The routed kernels are smooth and compactly supported, hence supported in the closed ball of
radius `ε`; this gives both their integrability against any function which is continuous on that
ball, and a sharp bound of their mass by the level-`M` mass `Ksm`. -/

private lemma tsupport_KdK_subset_closedBall {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) (a b : ℕ) :
    tsupport (KdK ρ ε a b) ⊆ Metric.closedBall (0 : ℝ × ℝ) ε := by
  have hS : ∀ {F : ℝ × ℝ → ℝ}, tsupport F ⊆ Metric.closedBall (0 : ℝ × ℝ) ε →
      tsupport (Work.FTS.StrongEps.partSnd F) ⊆ Metric.closedBall (0 : ℝ × ℝ) ε := by
    intro F hF
    refine closure_minimal (fun q hq => ?_) Metric.isClosed_closedBall
    exact hF (mem_tsupport_of_partSnd_ne_zero (Function.mem_support.mp hq))
  have hP : ∀ {F : ℝ × ℝ → ℝ}, tsupport F ⊆ Metric.closedBall (0 : ℝ × ℝ) ε →
      tsupport (Work.FTS.StrongEps.partFst F) ⊆ Metric.closedBall (0 : ℝ × ℝ) ε := by
    intro F hF
    refine closure_minimal (fun q hq => ?_) Metric.isClosed_closedBall
    exact hF (mem_tsupport_of_partFst_ne_zero (Function.mem_support.mp hq))
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
      simpa only [KdK, Work.FTS.StrongEps.Kd_zero_eq,
        Function.iterate_zero_apply] using hbase
    | succ b ih => simpa only [KdK, Work.FTS.StrongEps.Kd_zero_succ] using hS ih
  | succ a ih => simpa only [KdK, Work.FTS.StrongEps.Kd_succ_eq] using hP ih

private lemma KdK_eq_zero_of_notMem_closedBall {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) (a b : ℕ) {p : ℝ × ℝ}
    (hp : p ∉ Metric.closedBall (0 : ℝ × ℝ) ε) : KdK ρ ε a b p = 0 := by
  by_contra hne
  refine hp (tsupport_KdK_subset_closedBall hρ hε a b ?_)
  exact subset_tsupport _ (Function.mem_support.mpr hne)

private lemma integrable_abs_KdK_mul {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) (a b : ℕ) {B : ℝ × ℝ → ℝ}
    (hB : ContinuousOn B (Metric.closedBall (0 : ℝ × ℝ) ε)) :
    Integrable (fun p : ℝ × ℝ => |KdK ρ ε a b p| * B p) := by
  have hon : IntegrableOn (fun p : ℝ × ℝ => |KdK ρ ε a b p| * B p)
      (Metric.closedBall (0 : ℝ × ℝ) ε) :=
    (((KdK_continuous hρ ε a b).abs.continuousOn).mul hB).integrableOn_compact
      (isCompact_closedBall (0 : ℝ × ℝ) ε)
  refine hon.integrable_of_forall_notMem_eq_zero (fun p hp => ?_)
  rw [KdK_eq_zero_of_notMem_closedBall hρ hε a b hp, abs_zero, zero_mul]

/-- The mass of a single routed kernel is bounded by the total mass `Ksm`. -/
private lemma integral_abs_KdK_le_Ksm {ρ : ℝ × ℝ → ℝ}
    (ε : ℝ) {M a b : ℕ} (ha : a ≤ M) (hb : b ≤ M) :
    (∫ p : ℝ × ℝ, |KdK ρ ε a b p|) ≤ Ksm ρ ε M := by
  have hmem : (∫ p : ℝ × ℝ, |KdK ρ ε a b p|)
      ≤ ∑ a' ∈ Finset.range (M + 1), ∑ b' ∈ Finset.range (M + 1),
          ∫ p : ℝ × ℝ, |KdK ρ ε a' b' p| := by
    calc (∫ p : ℝ × ℝ, |KdK ρ ε a b p|)
        ≤ ∑ a' ∈ Finset.range (M + 1), ∫ p : ℝ × ℝ, |KdK ρ ε a' b p| :=
          Finset.single_le_sum (f := fun a' => ∫ p : ℝ × ℝ, |KdK ρ ε a' b p|)
            (fun _ _ => integral_nonneg fun p => abs_nonneg _)
            (Finset.mem_range.mpr (by omega))
      _ ≤ ∑ a' ∈ Finset.range (M + 1), ∑ b' ∈ Finset.range (M + 1),
            ∫ p : ℝ × ℝ, |KdK ρ ε a' b' p| :=
          Finset.sum_le_sum fun a' _ => Finset.single_le_sum
            (f := fun b' => ∫ p : ℝ × ℝ, |KdK ρ ε a' b' p|)
            (fun _ _ => integral_nonneg fun p => abs_nonneg _)
            (Finset.mem_range.mpr (by omega))
  simpa only [Ksm] using hmem

/-- `((2^n a) b)^2 = 2^{2n} (ab)^2`. -/
private lemma sq_mul_pow_two (n : ℕ) (a b : ℝ) :
    ((2 : ℝ) ^ n * a * b) ^ 2 = (2 : ℝ) ^ (2 * n) * (a * b) ^ 2 := by
  rw [mul_pow, mul_pow, ← pow_mul, Nat.mul_comm]
  ring

/-- **The real-valued core of the `θ`-routed slot bound**: the routed identity of
`mixed_Jeps_kernel_partial` (all `j` `z`-derivatives and `i - 1` `θ`-derivatives on the kernel),
then weighted Cauchy–Schwarz (`StepFacts.srb_cs_core`), then the domination of the routed kernel
by `LamFull` (pointwise) and by `Ksm · 2^{2M} = KgainBig` (in mass). -/
private lemma mslot_core {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε α c : ℝ}
    (hε : 0 < ε) {M : ℕ} {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hW : ∀ p : ℝ × ℝ, Work.Spaces.Wt α z θ ≤ Real.exp (c * (|p.1| + |p.2|))
      * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
    {j i : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ M) :
    ((2 : ℝ) ^ (i - 1) * (∫ p : ℝ × ℝ, KdK ρ ε j (i - 1) p
        * Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)) * Work.Spaces.Wt α z θ) ^ 2
      ≤ KgainBig ρ ε M
          * ∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|
              * Real.exp (2 * c * (|p.1| + |p.2|))
              * (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 := by
  have hM1 : i - 1 ≤ M := by omega
  have hjM : j ≤ M := by omega
  have hW₀ : 0 ≤ Work.Spaces.Wt α z θ := Work.FTS.StrongEps.StepFacts.srb_Wt_nonneg α hz hθ
  have hGc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed 0 1 f
      (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
      (Metric.closedBall (0 : ℝ × ℝ) ε) :=
    Work.FTS.StrongEps.HkSqAux.continuousOn_shift_ball hz hθ
      (Work.FTS.StrongEps.HkSqAux.continuousOn_mixed_region hz hε hθ hf 0 1)
  have hWc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α
      (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
      (Metric.closedBall (0 : ℝ × ℝ) ε) :=
    Work.FTS.StrongEps.HkSqAux.continuousOn_shift_ball hz hθ
      (Work.FTS.StrongEps.HkSqAux.continuousOn_Wt_region hz hε hθ)
  have hexp : Continuous (fun p : ℝ × ℝ => Real.exp (2 * c * (|p.1| + |p.2|))) := by
    refine Real.continuous_exp.comp (Continuous.mul continuous_const ?_)
    exact (continuous_abs.comp continuous_fst).add (continuous_abs.comp continuous_snd)
  have hKint : Integrable (fun p : ℝ × ℝ => |KdK ρ ε j (i - 1) p|) := by
    have h := integrable_abs_KdK_mul hρ hε j (i - 1)
      (B := fun _ : ℝ × ℝ => (1 : ℝ)) continuousOn_const
    simpa only [mul_one] using h
  have hQint : Integrable (fun p : ℝ × ℝ => |KdK ρ ε j (i - 1) p|
      * Real.exp (2 * c * (|p.1| + |p.2|))
      * (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) := by
    have h := integrable_abs_KdK_mul hρ hε j (i - 1) (B := fun p : ℝ × ℝ =>
      Real.exp (2 * c * (|p.1| + |p.2|))
        * (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)
          * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)) ^ 2)
      (hexp.continuousOn.mul ((hGc.mul hWc).pow 2))
    simpa only [mul_assoc] using h
  have hK2int : Integrable (fun p : ℝ × ℝ => |KdK ρ ε j (i - 1) p|
      * (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2) * Work.Spaces.Wt α z θ) ^ 2) := by
    have h := integrable_abs_KdK_mul hρ hε j (i - 1) (B := fun p : ℝ × ℝ =>
      (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2) * Work.Spaces.Wt α z θ) ^ 2)
      ((hGc.mul continuousOn_const).pow 2)
    simpa only [mul_assoc] using h
  have hmass : (∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|) ≤ Ksm ρ ε M :=
    integral_abs_KdK_le_Ksm ε hjM hM1
  have hcs := Work.FTS.StrongEps.StepFacts.srb_cs_core
    (K := fun p : ℝ × ℝ => KdK ρ ε j (i - 1) p)
    (G := fun p : ℝ × ℝ => Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
      (Work.FTS.StrongEps.thShift θ p.2))
    (W := fun p : ℝ × ℝ => Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
      (Work.FTS.StrongEps.thShift θ p.2))
    (W₀ := Work.Spaces.Wt α z θ) (c := c)
    (M := ∫ p : ℝ × ℝ, KdK ρ ε j (i - 1) p
        * Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2))
    hW₀ hW hKint hQint hK2int rfl
  have key : (2 : ℝ) ^ (2 * (i - 1))
        * ((∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|)
          * ∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|
              * Real.exp (2 * c * (|p.1| + |p.2|))
              * (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) ^ 2)
      ≤ KgainBig ρ ε M
          * ∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|
              * Real.exp (2 * c * (|p.1| + |p.2|))
              * (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 := by
    have h2pow : (2 : ℝ) ^ (2 * (i - 1)) ≤ 2 ^ (2 * M) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hF0 : 0 ≤ ∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|
              * Real.exp (2 * c * (|p.1| + |p.2|))
              * (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 :=
      integral_nonneg fun p =>
        mul_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) (sq_nonneg _)
    have hK0 : 0 ≤ ∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p| := integral_nonneg fun p => abs_nonneg _
    calc (2 : ℝ) ^ (2 * (i - 1))
          * ((∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|)
            * ∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|
                * Real.exp (2 * c * (|p.1| + |p.2|))
                * (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)
                  * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                      (Work.FTS.StrongEps.thShift θ p.2)) ^ 2)
        ≤ 2 ^ (2 * M) * ((∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|)
            * ∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|
                * Real.exp (2 * c * (|p.1| + |p.2|))
                * (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)
                  * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                      (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) :=
          mul_le_mul_of_nonneg_right h2pow (mul_nonneg hK0 hF0)
      _ ≤ 2 ^ (2 * M) * (Ksm ρ ε M
            * ∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|
                * Real.exp (2 * c * (|p.1| + |p.2|))
                * (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)
                  * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                      (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmass hF0) (by positivity)
      _ = KgainBig ρ ε M
            * ∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|
                * Real.exp (2 * c * (|p.1| + |p.2|))
                * (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)
                  * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                      (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 := by
          simp only [KgainBig]
          ring
  calc ((2 : ℝ) ^ (i - 1) * (∫ p : ℝ × ℝ, KdK ρ ε j (i - 1) p
          * Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)) * Work.Spaces.Wt α z θ) ^ 2
      = (2 : ℝ) ^ (2 * (i - 1)) * ((∫ p : ℝ × ℝ,
            KdK ρ ε j (i - 1) p
          * Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)) * Work.Spaces.Wt α z θ) ^ 2 :=
        sq_mul_pow_two (i - 1) _ _
    _ ≤ (2 : ℝ) ^ (2 * (i - 1))
          * ((∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|)
            * ∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|
                * Real.exp (2 * c * (|p.1| + |p.2|))
                * (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)
                  * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                      (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ ≤ KgainBig ρ ε M
          * ∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|
              * Real.exp (2 * c * (|p.1| + |p.2|))
              * (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 := key

/-- namespace `Work.FTS.StrongEps.EpsE4Thr`, declaration name `mslot_le_gain`.
The `θ`-routed slots: route all `j` `z`-derivatives and `i-1` `θ`-derivatives onto the kernel
(`Work.FTS.StrongEps.mixed_Jeps_kernel_partial ρ hρ hε hf hz hθ j i 0 1 le_rfl hi`), leaving the
level-1 slot `mixed 0 1 f = D_θ f`; Cauchy-Schwarz in the form of
`StepFacts.SlotAux.srb_cs_core` (as in `StepFacts/slot_route_bounds.lean`), the leftover being
dominated by `HkIntegrand α k f` through `Work.Spaces.sq_le_HkIntegrand_mixed` at `(i,j) = (1,0)`
(this is where `hk : 1 ≤ k` is used), and the constants through
`Work.FTS.StrongEps.EpsE4Thr.abs_KdK_mul_exp_le_LamFull` and
`Work.FTS.StrongEps.EpsE4Thr.integral_abs_KdK_le_KgainBig` (the factor `2^(2(i-1)) ≤ 2^(2M)` is
absorbed in `KgainBig = Ksm * 2^(2M)`). -/
theorem mslot_le_gain {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε α c : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hc : 0 ≤ c) {M k : ℕ} (hk : 1 ≤ k) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hW : ∀ p : ℝ × ℝ, Work.Spaces.Wt α z θ ≤ Real.exp (c * (|p.1| + |p.2|))
      * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
    {j i : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ M) :
    ENNReal.ofReal ((Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
        * Work.Spaces.Wt α z θ) ^ 2)
      ≤ ENNReal.ofReal (Work.FTS.StrongEps.EpsE4Thr.KgainBig ρ ε M)
        * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.EpsE4Thr.LamFull ρ ε c M p)
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) := by
  have hcore := mslot_core (ρ := ρ) (α := α) (c := c) (M := M) (f := f) (z := z) (θ := θ)
    (j := j) (i := i) hρ hε hf hz hθ hW hi hij
  -- the routed identity: all `j` `z`-derivatives and `i - 1` `θ`-derivatives sit on the kernel
  have hroute : Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
      = (2 : ℝ) ^ (i - 1) * ∫ p : ℝ × ℝ, KdK ρ ε j (i - 1) p
          * Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) := by
    have hKd : ∀ p : ℝ × ℝ, KdK ρ ε j (i - 1) p
        = iteratedDeriv j (fun s : ℝ => iteratedDeriv (i - 1)
            (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, t)) p.2) p.1 :=
      fun p => congrFun (Work.FTS.StrongEps.Kd_eq (Work.FTS.StrongEps.Jker ρ ε) j (i - 1)) p
    have h := Work.FTS.StrongEps.mixed_Jeps_kernel_partial ρ hρ hε hf hz hθ j i 0 1
      (Nat.zero_le j) hi
    simp only [Nat.sub_zero] at h
    rw [h]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [hKd p]
  rw [hroute]
  refine (ENNReal.ofReal_le_ofReal hcore).trans ?_
  have hF0 : ∀ p : ℝ × ℝ, 0 ≤ |KdK ρ ε j (i - 1) p|
      * Real.exp (2 * c * (|p.1| + |p.2|))
      * (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 :=
    fun p => mul_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) (sq_nonneg _)
  have hF'0 : ∀ p : ℝ × ℝ, 0 ≤ LamFull ρ ε c M p
      * Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2) :=
    fun p => mul_nonneg (LamFull_nonneg hρ hε M p)
      (Work.Spaces.HkIntegrand_nonneg α k f _ _)
  have hFF : ∀ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|
      * Real.exp (2 * c * (|p.1| + |p.2|))
      * (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)) ^ 2
      ≤ LamFull ρ ε c M p
      * Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2) := by
    intro p
    have h1 : |KdK ρ ε j (i - 1) p| * Real.exp (2 * c * (|p.1| + |p.2|))
        ≤ LamFull ρ ε c M p :=
      abs_KdK_mul_exp_le_LamFull hρ hε hε1 hc (by omega) p
    have h2 : (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)) ^ 2
        ≤ Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2) :=
      Work.Spaces.sq_le_HkIntegrand_mixed α k f _ _ 1 0 le_rfl (by omega)
    exact mul_le_mul h1 h2 (sq_nonneg _) (LamFull_nonneg hρ hε M p)
  refine (Work.FTS.StrongEps.StepFacts.ofReal_mul_integral_le_lintegral
    (KgainBig_nonneg hρ ε M) (KgainBig_nonneg hρ ε M) le_rfl hF0 hF'0 hFF).trans ?_
  rw [lintegral_congr (fun p => ENNReal.ofReal_mul (LamFull_nonneg hρ hε M p))]

end Work.FTS.StrongEps.EpsE4Thr.GainSlot
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.GlueParts.continuousOn_junctionStep =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.GlueParts

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.StrongGlobal (P3 uncurry3)

/-- The piecewise derivative field of the boundary junction is continuous on the closed slab
`U = (0,∞) × (0,π/2) × [0, t+δ]`.

**Fix applied after review.**  The two branches must be forced to agree at the junction points of
`U`: without the hypothesis `hjunc` the field is in general discontinuous at `τ = t` (take `G ≡ 0`,
`H z θ σ = σ`).  With `hjunc` supplied, the proof is:

both pieces are `C¹` on their own closed half-slabs, so `fderivWithin` of each piece is continuous
on that half-slab (`ContDiffOn.continuousOn_fderivWithin`, the half-slab being `UniqueDiffOn` since
`Ioi`, `Ioo` and `Icc 0 t` / `Icc t (t+δ)` all are).  Fix `p ∈ U`:
* if `p.2.2 < t`, restrict to `S := U ∩ {τ < t} ⊆ UG`, where the field equals the `G`-branch and
  its value at `p` is the same, so `ContinuousWithinAt` there; upgrade to `U` with
  `ContinuousWithinAt.mono_of_mem_nhdsWithin` (`S ∈ 𝓝[U] p`);
* if `t < p.2.2`, the same with `U ∩ {t < τ} ⊆ UH`;
* if `p.2.2 = t`, the field is the `G`-branch on `U ∩ {τ ≤ t}` and, on `U ∩ {t ≤ τ}`, it splits
  into `A := U ∩ {τ = t}` (where it is again the `G`-branch, its value at `p` being the `G`-branch)
  and `B := U ∩ {t < τ}` (where it is the `H`-branch, whose value at `p` is the `H`-branch —
  `hjunc` is what identifies this with the value of the field at `p`).  `ContinuousWithinAt.union`
  gives the two halves and then the whole of `U`. -/
theorem continuousOn_junctionStep {G H : Work.FTS.Galerkin.Fam} {t δ : ℝ} (ht : 0 < t) (hδ : 0 < δ)
    (hG : ContDiffOn ℝ 1 (Work.FTS.StrongGlobal.uncurry3 G)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 t))
    (hH : ContDiffOn ℝ 1 (Work.FTS.StrongGlobal.uncurry3 H)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc t (t + δ)))
    (hjunc : ∀ p ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ), p.2.2 = t →
      fderivWithin ℝ (Work.FTS.StrongGlobal.uncurry3 G)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 t) p =
        fderivWithin ℝ (Work.FTS.StrongGlobal.uncurry3 H)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc t (t + δ)) p) :
    ContinuousOn (fun p : Work.FTS.StrongGlobal.P3 =>
        if p.2.2 ≤ t then
          fderivWithin ℝ (Work.FTS.StrongGlobal.uncurry3 G)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 t) p
        else
          fderivWithin ℝ (Work.FTS.StrongGlobal.uncurry3 H)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc t (t + δ)) p)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ)) := by
  -- The two half-slabs are sets of unique differentiability.
  have hUG : UniqueDiffOn ℝ (AG t) := by
    unfold AG
    exact (uniqueDiffOn_Ioi 0).prod
      ((uniqueDiffOn_Ioo 0 (Real.pi / 2)).prod (uniqueDiffOn_Icc ht))
  have hUH : UniqueDiffOn ℝ (BT t δ) := by
    unfold BT
    exact (uniqueDiffOn_Ioi 0).prod
      ((uniqueDiffOn_Ioo 0 (Real.pi / 2)).prod (uniqueDiffOn_Icc (by linarith)))
  -- Continuity of the two branches' derivative fields on their half-slabs.
  have hGc : ContinuousOn (fun p : P3 => fderivWithin ℝ (uncurry3 G) (AG t) p) (AG t) :=
    hG.continuousOn_fderivWithin hUG le_rfl
  have hHc : ContinuousOn (fun p : P3 => fderivWithin ℝ (uncurry3 H) (BT t δ) p) (BT t δ) :=
    hH.continuousOn_fderivWithin hUH le_rfl
  -- Restate the goal with the named sets.
  change ContinuousOn (fun p : P3 =>
      if p.2.2 ≤ t then fderivWithin ℝ (uncurry3 G) (AG t) p
      else fderivWithin ℝ (uncurry3 H) (BT t δ) p) (AT t δ)
  set F : P3 → (P3 →L[ℝ] ℝ) := fun p : P3 =>
    if p.2.2 ≤ t then fderivWithin ℝ (uncurry3 G) (AG t) p
    else fderivWithin ℝ (uncurry3 H) (BT t δ) p with hFdef
  -- Membership unfoldings.
  have memAT : ∀ q : P3, q ∈ AT t δ ↔ 0 < q.1 ∧ 0 < q.2.1 ∧ q.2.1 < Real.pi / 2
      ∧ 0 ≤ q.2.2 ∧ q.2.2 ≤ t + δ := by
    intro q
    simp only [AT, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Set.mem_Icc, and_assoc]
  have memAG : ∀ q : P3, q ∈ AG t ↔ 0 < q.1 ∧ 0 < q.2.1 ∧ q.2.1 < Real.pi / 2
      ∧ 0 ≤ q.2.2 ∧ q.2.2 ≤ t := by
    intro q
    simp only [AG, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Set.mem_Icc, and_assoc]
  have memBT : ∀ q : P3, q ∈ BT t δ ↔ 0 < q.1 ∧ 0 < q.2.1 ∧ q.2.1 < Real.pi / 2
      ∧ t ≤ q.2.2 ∧ q.2.2 ≤ t + δ := by
    intro q
    simp only [BT, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Set.mem_Icc, and_assoc]
  have toAG : ∀ q : P3, q ∈ AT t δ → q.2.2 ≤ t → q ∈ AG t := by
    intro q hq hqt
    obtain ⟨h1, h2, h3, h4, _⟩ := (memAT q).mp hq
    exact (memAG q).mpr ⟨h1, h2, h3, h4, hqt⟩
  have toBT : ∀ q : P3, q ∈ AT t δ → t ≤ q.2.2 → q ∈ BT t δ := by
    intro q hq hqt
    obtain ⟨h1, h2, h3, _, h5⟩ := (memAT q).mp hq
    exact (memBT q).mpr ⟨h1, h2, h3, hqt, h5⟩
  -- The two branches of `F`, pointwise.
  have hF_le : ∀ q : P3, q.2.2 ≤ t → F q = fderivWithin ℝ (uncurry3 G) (AG t) q := by
    intro q hq; rw [hFdef]; exact if_pos hq
  have hF_lt : ∀ q : P3, t < q.2.2 → F q = fderivWithin ℝ (uncurry3 H) (BT t δ) q := by
    intro q hq; rw [hFdef]; exact if_neg (not_le.mpr hq)
  -- The `G`-branch step: on a set contained in `AG t` on which `F` is the `G`-branch.
  have stepG : ∀ (S : Set P3), S ⊆ AG t → (∀ q ∈ S, q.2.2 ≤ t) → ∀ p ∈ AG t, p.2.2 ≤ t →
      ContinuousWithinAt F S p := by
    intro S hSsub hSle p hpAG hple
    have hφ : ContinuousWithinAt (fun q : P3 => fderivWithin ℝ (uncurry3 G) (AG t) q) (AG t) p :=
      hGc p hpAG
    exact hφ.congr_mono (fun q hq => hF_le q (hSle q hq)) hSsub (hF_le p hple)
  have hmain : ∀ p ∈ AT t δ, ContinuousWithinAt F (AT t δ) p := by
    intro p hp
    rcases lt_trichotomy p.2.2 t with hlt | heq | hgt
    · -- strictly left of the junction
      have hple : p.2.2 ≤ t := le_of_lt hlt
      have hpAG : p ∈ AG t := toAG p hp hple
      set S : Set P3 := {q : P3 | q.2.2 < t} ∩ AT t δ with hSdef
      have hSsub : S ⊆ AG t := fun q hq => toAG q hq.2 (le_of_lt hq.1)
      have hSle : ∀ q ∈ S, q.2.2 ≤ t := fun q hq => le_of_lt hq.1
      have hS : ContinuousWithinAt F S p := stepG S hSsub hSle p hpAG hple
      have hmem : S ∈ 𝓝[AT t δ] p := by
        rw [hSdef, mem_nhdsWithin_iff_exists_mem_nhds_inter]
        exact ⟨{q : P3 | q.2.2 < t},
          (isOpen_lt (continuous_snd.comp continuous_snd) continuous_const).mem_nhds hlt,
          fun q hq => ⟨hq.1, hq.2⟩⟩
      exact hS.mono_of_mem_nhdsWithin hmem
    · -- at the junction
      have hee : p.2.2 = t := heq
      have hpAG : p ∈ AG t := toAG p hp (le_of_eq hee)
      have hpBT : p ∈ BT t δ := toBT p hp (le_of_eq hee.symm)
      set A1 : Set P3 := {q : P3 | q.2.2 ≤ t} ∩ AT t δ with hA1def
      set B1 : Set P3 := {q : P3 | q.2.2 = t} ∩ AT t δ with hB1def
      set B2 : Set P3 := {q : P3 | t < q.2.2} ∩ AT t δ with hB2def
      have hA1 : ContinuousWithinAt F A1 p :=
        stepG A1 (fun q hq => toAG q hq.2 hq.1) (fun q hq => hq.1) p hpAG (le_of_eq hee)
      have hB1 : ContinuousWithinAt F B1 p :=
        stepG B1 (fun q hq => toAG q hq.2 (le_of_eq hq.1)) (fun q hq => le_of_eq hq.1)
          p hpAG (le_of_eq hee)
      have hB2 : ContinuousWithinAt F B2 p := by
        have hφ : ContinuousWithinAt (fun q : P3 => fderivWithin ℝ (uncurry3 H) (BT t δ) q) B2 p :=
          (hHc p hpBT).mono (fun q hq => toBT q hq.2 (le_of_lt hq.1))
        refine hφ.congr_of_eventuallyEq ?_ ?_
        · filter_upwards [self_mem_nhdsWithin] with q hq
          exact hF_lt q hq.1
        · exact (hF_le p (le_of_eq hee)).trans (hjunc p hp hee)
      have hA2 : ContinuousWithinAt F (AT t δ ∩ {q : P3 | t ≤ q.2.2}) p := by
        have hset : AT t δ ∩ {q : P3 | t ≤ q.2.2} = B1 ∪ B2 := by
          rw [hB1def, hB2def]
          ext q
          simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq]
          constructor
          · rintro ⟨h1, h2⟩
            rcases lt_or_eq_of_le h2 with h3 | h3
            · exact Or.inr ⟨h3, h1⟩
            · exact Or.inl ⟨h3.symm, h1⟩
          · rintro (⟨h2, h1⟩ | ⟨h2, h1⟩)
            · exact ⟨h1, le_of_eq h2.symm⟩
            · exact ⟨h1, le_of_lt h2⟩
        rw [hset]
        exact hB1.union hB2
      have hU : AT t δ = A1 ∪ (AT t δ ∩ {q : P3 | t ≤ q.2.2}) := by
        rw [hA1def]
        ext q
        simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq]
        constructor
        · intro h1
          rcases le_total q.2.2 t with h2 | h2
          · exact Or.inl ⟨h2, h1⟩
          · exact Or.inr ⟨h1, h2⟩
        · rintro (⟨⟨h2, h1⟩⟩ | ⟨h1, _⟩)
          · exact h1
          · exact h1
      rw [hU]
      exact hA1.union hA2
    · -- strictly right of the junction
      have hge : t ≤ p.2.2 := le_of_lt hgt
      have hpBT : p ∈ BT t δ := toBT p hp hge
      set S : Set P3 := {q : P3 | t < q.2.2} ∩ AT t δ with hSdef
      have hSsub : S ⊆ BT t δ := fun q hq => toBT q hq.2 (le_of_lt hq.1)
      have hS : ContinuousWithinAt F S p := by
        have hφ : ContinuousWithinAt (fun q : P3 => fderivWithin ℝ (uncurry3 H) (BT t δ) q) (BT t δ) p :=
          hHc p hpBT
        exact hφ.congr_mono (fun q hq => hF_lt q hq.1) hSsub (hF_lt p hgt)
      have hmem : S ∈ 𝓝[AT t δ] p := by
        rw [hSdef, mem_nhdsWithin_iff_exists_mem_nhds_inter]
        exact ⟨{q : P3 | t < q.2.2},
          (isOpen_lt continuous_const (continuous_snd.comp continuous_snd)).mem_nhds hgt,
          fun q hq => ⟨hq.1, hq.2⟩⟩
      exact hS.mono_of_mem_nhdsWithin hmem
  exact hmain

end Work.FTS.StrongEps.GlueParts
end
-- ===== merged: Submission.Work.FTS.StrongEps.GlueParts.junction_eq_fderivWithin =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.GlueParts

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.StrongGlobal (P3 concat uncurry3)

/-- At a *boundary* junction point `p = (z,θ,t)` (with `0 < t`) of the concatenation
`concat G H t` (`G` for `τ ≤ t`, `H` for `τ > t`) the two one-sided derivatives of the
concatenation agree.

`hA` (resp. `hB`) is a within-derivative of the concatenation on the left (resp. right) half of the
closed slab `U = (0,∞) × (0,π/2) × [0, t+δ]`, i.e. on `U ∩ {τ ≤ t}` (resp. `U ∩ {t ≤ τ}`); the
point `p` lies on the junction hyperplane `τ = t` and in `U`.  `hval` says the two pieces agree on
the hyperplane over the open quadrant of `(z,θ)`, and `hderG`/`hderH` give the one-sided fake-time
derivatives of the two pieces at `t`, both equal to `R`.

Proof (coordinate directions).  The `z`- and `θ`-directions of `cG` and `cH` are the corresponding
partial derivatives of the *same* function `uncurry3 (concat G H t)` at `p`
(`GlueParts.Basic`'s `hasFDerivWithinAt_apply_fst`/`_snd`), hence equal.  The `τ`-direction is
`R p.1 p.2.1` for both: on the left this is `hderG` restricted to `Icc (t-r) t`, on the right
`hderH` restricted to `Icc t (t+r)` together with `hval` at the single point `s = t`
(the concatenation equals `H` on `Icc t (t+r)`), and the derivatives within the closed intervals
are unique (`UniqueDiffWithinAt` for `Icc`). -/
theorem junction_eq_fderivWithin {G H : Work.FTS.Galerkin.Fam} {t δ : ℝ}
    {R : Work.FTS.Galerkin.Fn} {p : Work.FTS.StrongGlobal.P3} {cG cH : Work.FTS.StrongGlobal.P3 →L[ℝ] ℝ}
    (ht : 0 < t) (hδ : 0 < δ)
    (hpU : p ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ))
    (hp4 : p.2.2 = t)
    (hA : HasFDerivWithinAt (Work.FTS.StrongGlobal.uncurry3 (Work.FTS.StrongGlobal.concat G H t)) cG
      ((Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ)) ∩
        {q : Work.FTS.StrongGlobal.P3 | q.2.2 ≤ t}) p)
    (hB : HasFDerivWithinAt (Work.FTS.StrongGlobal.uncurry3 (Work.FTS.StrongGlobal.concat G H t)) cH
      ((Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ)) ∩
        {q : Work.FTS.StrongGlobal.P3 | t ≤ q.2.2}) p)
    (hval : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → G z θ t = H z θ t)
    (hderG : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HasDerivWithinAt (fun s => G z θ s) (R z θ) (Set.Icc 0 t) t)
    (hderH : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HasDerivWithinAt (fun s => H z θ s) (R z θ) (Set.Icc t (t + δ)) t) :
    cG = cH := by
  have hz : 0 < p.1 := hpU.1
  have hθ0 : 0 < p.2.1 := hpU.2.1.1
  have hθ1 : p.2.1 < Real.pi / 2 := hpU.2.1.2
  have hτ0 : 0 ≤ p.2.2 := hpU.2.2.1
  have hτδ : p.2.2 ≤ t + δ := hpU.2.2.2
  have htδ : t ≤ t + δ := by linarith
  have hp4' : p.2.2 ≤ t := le_of_eq hp4
  -- membership in the two half slabs
  have memL : ∀ s θ τ : ℝ, 0 < s → 0 < θ → θ < Real.pi / 2 → τ ∈ Set.Icc (0 : ℝ) t →
      (s, θ, τ) ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ)) ∩
        {q : Work.FTS.StrongGlobal.P3 | q.2.2 ≤ t} := by
    intro s θ τ hs hθ0' hθ1' hτ
    rw [Set.mem_Icc] at hτ
    exact ⟨⟨hs, ⟨hθ0', hθ1'⟩, ⟨hτ.1, le_trans hτ.2 htδ⟩⟩, hτ.2⟩
  have memR : ∀ s θ τ : ℝ, 0 < s → 0 < θ → θ < Real.pi / 2 → τ ∈ Set.Icc t (t + δ) →
      (s, θ, τ) ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ)) ∩
        {q : Work.FTS.StrongGlobal.P3 | t ≤ q.2.2} := by
    intro s θ τ hs hθ0' hθ1' hτ
    rw [Set.mem_Icc] at hτ
    exact ⟨⟨hs, ⟨hθ0', hθ1'⟩, ⟨le_trans ht.le hτ.1, hτ.2⟩⟩, hτ.1⟩
  -- the `z`-direction: both sides read the common hyperplane profile `G ·· t`
  have he1 : cG ((1 : ℝ), 0, 0) = cH ((1 : ℝ), 0, 0) := by
    have hfun : (fun s : ℝ => uncurry3 (concat G H t) (s, p.2.1, p.2.2)) =
        (fun s : ℝ => G s p.2.1 t) := by
      funext s
      rw [Work.FTS.StrongGlobal.uncurry3_apply,
        Work.FTS.StrongGlobal.concat_apply_of_le hp4', hp4]
    have hGd : cG ((1 : ℝ), 0, 0) = deriv (fun s : ℝ => G s p.2.1 t) p.1 := by
      have h := hasFDerivWithinAt_apply_fst (c := cG) (x := p) (r := p.1 / 2) (by linarith) hA
        (fun s hs => by
          rw [Set.mem_Ioo] at hs
          exact memL s p.2.1 p.2.2 (by linarith) hθ0 hθ1 ⟨hτ0, hp4'⟩)
      rw [h, hfun]
    have hHd : cH ((1 : ℝ), 0, 0) = deriv (fun s : ℝ => G s p.2.1 t) p.1 := by
      have h := hasFDerivWithinAt_apply_fst (c := cH) (x := p) (r := p.1 / 2) (by linarith) hB
        (fun s hs => by
          rw [Set.mem_Ioo] at hs
          exact memR s p.2.1 p.2.2 (by linarith) hθ0 hθ1 ⟨le_of_eq hp4.symm, hτδ⟩)
      rw [h, hfun]
    exact hGd.trans hHd.symm
  -- the `θ`-direction: again the common hyperplane profile
  have he2 : cG ((0 : ℝ), 1, 0) = cH ((0 : ℝ), 1, 0) := by
    have hfun : (fun s : ℝ => uncurry3 (concat G H t) (p.1, s, p.2.2)) =
        (fun s : ℝ => G p.1 s t) := by
      funext s
      rw [Work.FTS.StrongGlobal.uncurry3_apply,
        Work.FTS.StrongGlobal.concat_apply_of_le hp4', hp4]
    set rθ : ℝ := min p.2.1 (Real.pi / 2 - p.2.1) / 2 with hrθdef
    have hrθ : 0 < rθ := by
      rw [hrθdef]
      have h : 0 < min p.2.1 (Real.pi / 2 - p.2.1) := lt_min hθ0 (by linarith)
      linarith
    have hrθ1 : rθ ≤ p.2.1 / 2 := by
      rw [hrθdef]; linarith [min_le_left p.2.1 (Real.pi / 2 - p.2.1)]
    have hrθ2 : rθ ≤ (Real.pi / 2 - p.2.1) / 2 := by
      rw [hrθdef]; linarith [min_le_right p.2.1 (Real.pi / 2 - p.2.1)]
    have hGd : cG ((0 : ℝ), 1, 0) = deriv (fun s : ℝ => G p.1 s t) p.2.1 := by
      have h := hasFDerivWithinAt_apply_snd (c := cG) (x := p) (r := rθ) hrθ hA
        (fun s hs => by
          rw [Set.mem_Ioo] at hs
          exact memL p.1 s p.2.2 hz
            (by linarith) (by linarith) ⟨hτ0, hp4'⟩)
      rw [h, hfun]
    have hHd : cH ((0 : ℝ), 1, 0) = deriv (fun s : ℝ => G p.1 s t) p.2.1 := by
      have h := hasFDerivWithinAt_apply_snd (c := cH) (x := p) (r := rθ) hrθ hB
        (fun s hs => by
          rw [Set.mem_Ioo] at hs
          exact memR p.1 s p.2.2 hz
            (by linarith) (by linarith) ⟨le_of_eq hp4.symm, hτδ⟩)
      rw [h, hfun]
    exact hGd.trans hHd.symm
  -- the `τ`-direction: both sides are `R p.1 p.2.1`
  have he3 : cG ((0 : ℝ), 0, 1) = cH ((0 : ℝ), 0, 1) := by
    have huL : UniqueDiffWithinAt ℝ (Set.Icc (0 : ℝ) t) t :=
      uniqueDiffWithinAt_Icc ht ⟨ht.le, le_rfl⟩
    have huR : UniqueDiffWithinAt ℝ (Set.Icc t (t + δ)) t :=
      uniqueDiffWithinAt_Icc (by linarith) ⟨le_rfl, by linarith⟩
    have hGτ : cG ((0 : ℝ), 0, 1) = R p.1 p.2.1 := by
      have h := hasFDerivWithinAt_apply_thd (a := (0 : ℝ)) (b := t) (c := cG) (x := p) hA
        (fun τ hτ => memL p.1 p.2.1 τ hz hθ0 hθ1 hτ)
      rw [hp4] at h
      have hcongr : Set.EqOn (fun s : ℝ => G p.1 p.2.1 s)
          (fun s : ℝ => uncurry3 (concat G H t) (p.1, p.2.1, s)) (Set.Icc (0 : ℝ) t) := by
        intro s hs
        rw [Set.mem_Icc] at hs
        change G p.1 p.2.1 s = uncurry3 (concat G H t) (p.1, p.2.1, s)
        rw [Work.FTS.StrongGlobal.uncurry3_apply,
          Work.FTS.StrongGlobal.concat_apply_of_le hs.2]
      have h1 : derivWithin (fun s : ℝ => G p.1 p.2.1 s) (Set.Icc (0 : ℝ) t) t =
          cG ((0 : ℝ), 0, 1) := by
        rw [derivWithin_congr hcongr
          (hcongr (show t ∈ Set.Icc (0 : ℝ) t from ⟨ht.le, le_rfl⟩)), h.derivWithin huL]
      have h2 := (hderG p.1 p.2.1 hz hθ0 hθ1).derivWithin huL
      rw [← h2, ← h1]
    have hHτ : cH ((0 : ℝ), 0, 1) = R p.1 p.2.1 := by
      have h := hasFDerivWithinAt_apply_thd (a := t) (b := t + δ) (c := cH) (x := p) hB
        (fun τ hτ => memR p.1 p.2.1 τ hz hθ0 hθ1 hτ)
      rw [hp4] at h
      have hcongr : Set.EqOn (fun s : ℝ => H p.1 p.2.1 s)
          (fun s : ℝ => uncurry3 (concat G H t) (p.1, p.2.1, s)) (Set.Icc t (t + δ)) := by
        intro s hs
        rw [Set.mem_Icc] at hs
        change H p.1 p.2.1 s = uncurry3 (concat G H t) (p.1, p.2.1, s)
        rcases lt_or_eq_of_le hs.1 with hlt | heq
        · rw [Work.FTS.StrongGlobal.uncurry3_apply,
            Work.FTS.StrongGlobal.concat_apply_of_gt hlt]
        · rw [← heq, Work.FTS.StrongGlobal.uncurry3_apply,
            Work.FTS.StrongGlobal.concat_apply_of_le (le_refl t), hval p.1 p.2.1 hz hθ0 hθ1]
      have h1 : derivWithin (fun s : ℝ => H p.1 p.2.1 s) (Set.Icc t (t + δ)) t =
          cH ((0 : ℝ), 0, 1) := by
        rw [derivWithin_congr hcongr
          (hcongr (show t ∈ Set.Icc t (t + δ) from ⟨le_rfl, by linarith⟩)), h.derivWithin huR]
      have h2 := (hderH p.1 p.2.1 hz hθ0 hθ1).derivWithin huR
      rw [← h2, ← h1]
    exact hGτ.trans hHτ.symm
  -- assemble: `cG = cH` from equality on the three basis vectors
  refine ContinuousLinearMap.ext fun v => ?_
  have hv : v = v.1 • (((1 : ℝ), 0, 0) : P3) + v.2.1 • (((0 : ℝ), 1, 0) : P3)
      + v.2.2 • (((0 : ℝ), 0, 1) : P3) := by
    ext <;> simp
  rw [hv]
  simp only [map_add, map_smul, smul_eq_mul, he1, he2, he3]

end Work.FTS.StrongEps.GlueParts
end
-- ===== merged: Submission.Work.FTS.StrongEps.StrongEpsP.SolGlueP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.StrongEpsP

open scoped Real Topology
open Set Filter

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## An elementary change of variables for one-sided derivatives -/

/-- Differentiation of a shifted function: `s ↦ f (s - a)` has the derivative of `f` at `s - a`,
on the shifted interval `[a, a+c]`. -/
theorem hasDerivWithinAt_comp_sub_Icc {f : ℝ → ℝ} {f' : ℝ} {x a c : ℝ}
    (h : HasDerivWithinAt f f' (Set.Icc 0 c) (x - a)) :
    HasDerivWithinAt (fun y : ℝ => f (y - a)) f' (Set.Icc a (a + c)) x := by
  have hg : HasDerivWithinAt (fun y : ℝ => y - a) 1 (Set.Icc a (a + c)) x :=
    ((hasDerivAt_id (x := x)).sub_const a).hasDerivWithinAt
  have hst : MapsTo (fun y : ℝ => y - a) (Set.Icc a (a + c)) (Set.Icc 0 c) :=
    fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hcomp := h.comp x hg hst
  have heq : (f ∘ fun y : ℝ => y - a) = (fun y : ℝ => f (y - a)) := funext fun y => rfl
  rw [heq, mul_one] at hcomp
  exact hcomp

/-! ## The glue -/

theorem SolGlueP {α ε t δ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {G H : Work.FTS.Galerkin.Fam} (ht : 0 ≤ t) (hδ : 0 < δ)
    (hG : Work.FTS.StrongEps.IsEpsSolP α ρ ε t Φs E g₀ G)
    (hH : Work.FTS.StrongEps.IsEpsSolP α ρ ε δ Φs E (Work.FTS.Galerkin.slice G t) H) :
    Work.FTS.StrongEps.IsEpsSolP α ρ ε (t + δ) Φs E g₀
      (Work.FTS.StrongGlobal.concat G (Work.FTS.StrongEps.shiftFam H t) t) := by
  refine ⟨?_, ?_⟩
  · -- the datum
    intro z θ
    rw [Work.FTS.StrongGlobal.concat_apply_of_le (τ₀ := t) (τ := 0) ht]
    exact hG.1 z θ
  · -- the equation on `[0, t + δ]`
    intro z θ τ hz hθ hτ
    -- the two pieces agree at the junction (they have the same slice there)
    have hjunc : epsRHSP α ρ ε Φs E G t = epsRHSP α ρ ε Φs E H 0 :=
      epsRHSP_congr (Φs := Φs) (E := E) (W := G) (W' := H) (τ := t) (τ' := 0)
        (funext fun z => funext fun θ => (hH.1 z θ).symm)
    -- the value of the scheme on the concatenation, before/after the junction
    have hVle : ∀ x, x ≤ t →
        epsRHSP α ρ ε Φs E (Work.FTS.StrongGlobal.concat G (shiftFam H t) t) x
          = epsRHSP α ρ ε Φs E G x :=
      fun x hx => epsRHSP_congr (Φs := Φs) (E := E) (W := _) (W' := G) (τ := x) (τ' := x)
        (Work.FTS.StrongGlobal.slice_concat_of_le hx)
    have hVgt : ∀ x, t < x →
        epsRHSP α ρ ε Φs E (Work.FTS.StrongGlobal.concat G (shiftFam H t) t) x
          = epsRHSP α ρ ε Φs E H (x - t) :=
      fun x hx => epsRHSP_congr (Φs := Φs) (E := E) (W := _) (W' := H) (τ := x) (τ' := x - t)
        (Work.FTS.StrongGlobal.slice_concat_of_gt hx)
    -- the glue of the two one-sided statements
    have key : ∀ x ∈ Set.Icc (0 : ℝ) (t + δ),
        HasDerivWithinAt
          (fun s : ℝ => Work.FTS.StrongGlobal.concat G (shiftFam H t) t z θ s)
          (epsRHSP α ρ ε Φs E
            (Work.FTS.StrongGlobal.concat G (shiftFam H t) t) x z θ)
          (Set.Icc 0 (t + δ)) x := by
      have hglue := Work.FTS.Galerkin.Ode.hasDerivWithinAt_glue (E := ℝ)
        (f := fun y : ℝ => G z θ y) (g := fun y : ℝ => H z θ (y - t))
        (a := 0) (b := t) (c := t + δ) ht (by linarith)
        (by show G z θ t = H z θ (t - t); rw [sub_self]; exact (hH.1 z θ).symm)
        (v := fun x => epsRHSP α ρ ε Φs E
          (Work.FTS.StrongGlobal.concat G (shiftFam H t) t) x z θ)
        (fun x hx => by
          show HasDerivWithinAt (fun y : ℝ => G z θ y)
            (epsRHSP α ρ ε Φs E
              (Work.FTS.StrongGlobal.concat G (shiftFam H t) t) x z θ) (Set.Icc 0 t) x
          rw [hVle x hx.2]
          exact hG.2 z θ x hz hθ hx)
        (fun x hx => by
          show HasDerivWithinAt (fun y : ℝ => H z θ (y - t))
            (epsRHSP α ρ ε Φs E
              (Work.FTS.StrongGlobal.concat G (shiftFam H t) t) x z θ)
            (Set.Icc t (t + δ)) x
          have hx' : x - t ∈ Set.Icc (0 : ℝ) δ := ⟨by linarith [hx.1], by linarith [hx.2]⟩
          have hHd := hH.2 z θ (x - t) hz hθ hx'
          have hcomp := hasDerivWithinAt_comp_sub_Icc (a := t) (c := δ) (x := x) hHd
          have hval : epsRHSP α ρ ε Φs E H (x - t)
              = epsRHSP α ρ ε Φs E
                  (Work.FTS.StrongGlobal.concat G (shiftFam H t) t) x := by
            rcases eq_or_lt_of_le hx.1 with hxt | hxt
            · subst hxt
              rw [sub_self]
              exact hjunc.symm.trans (hVle t le_rfl).symm
            · exact (hVgt x hxt).symm
          rw [hval] at hcomp
          exact hcomp)
      -- identify the glued function with the concatenation
      have hfun : (fun y : ℝ => if y ≤ t then G z θ y else H z θ (y - t))
          = fun s : ℝ => Work.FTS.StrongGlobal.concat G (shiftFam H t) t z θ s := by
        funext y
        simp only [Work.FTS.StrongGlobal.concat, Work.FTS.StrongEps.shiftFam]
      intro x hx
      rw [← hfun]
      exact hglue x hx
    exact key τ hτ

end Work.FTS.StrongEps.StrongEpsP
end
-- ===== merged: Submission.Work.FTS.StrongEps.epsSol_eq_integral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps


end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.CoupledVf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

open Work.FTS.Galerkin (Fn)
open Work.Spaces (HkIntegrand HkMem HkNorm HkSq Dz Dth pth)

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem cd_c2m : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Work.Construction.c2m p.2)
    Work.FTS.EllipticEst.Q0 := by
  unfold Work.Construction.c2m
  fun_prop


/-- **The pointwise bound for the `f`-dependent factor `Vf`.** -/
theorem Vf_integrand_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f : Fn,
      Work.FTS.EllipticEst.SmoothOpen f → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        HkIntegrand α 3 (Vf α f) z θ ≤ C * (1 / α) ^ 2 * HkIntegrand α 6 f z θ := by
  obtain ⟨Cang, hCangpos, hCangall⟩ := Work.Blocks.HkMul_ang_le 3
  have hCang2 : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        HkIntegrand α 3 (fun z θ => Real.sin θ ^ 2 * f z θ) z θ
          ≤ Cang * HkIntegrand α 3 f z θ :=
    fun α f hα hα1 hso => (hCangall α f hα hα1 hso).2.1
  refine ⟨21 + 72 * Cang, by positivity, ?_⟩
  intro α hα hα1 f hso z hz θ hθ
  -- the three summands of `Vf`
  set X1 : Fn := fun z θ => (1 / α) * f z θ with hX1
  set X2 : Fn := fun z θ => (3 / (2 * α)) * (Dth f z θ) with hX2
  set X3 : Fn := fun z θ => -(Work.Construction.c2m θ * Dz f z θ) with hX3
  have hVfeq : Vf α f = fun z θ => X1 z θ + X2 z θ + X3 z θ := by
    funext z θ
    simp only [Vf, hX1, hX2, hX3, Dth, Work.Construction.s2_eq]
    ring
  -- the smoothness certificates
  have hX1c : ContDiffOn ℝ 3 (Function.uncurry X1) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_const.mul (hso.forall 3)
  have hX2c : ContDiffOn ℝ 3 (Function.uncurry X2) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_const.mul (hso.Dth.forall 3)
  have hX3c : ContDiffOn ℝ 3 (Function.uncurry X3) Work.FTS.EllipticEst.Q0 :=
    (cd_c2m.mul (hso.Dz.forall 3)).neg
  have hX12c : ContDiffOn ℝ 3 (Function.uncurry (fun z θ => X1 z θ + X2 z θ))
      Work.FTS.EllipticEst.Q0 := hX1c.add hX2c
  -- zero cases
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · subst hz0
    rw [Work.FTS.LocData.HkIntegrand_zero_fst, Work.FTS.LocData.HkIntegrand_zero_fst]
    norm_num
  by_cases hsin : Real.sin (2 * θ) = 0
  · rw [Work.Construction.HkIntegrand_eq_zero_of_sin_two_eq_zero hα hsin,
      Work.Construction.HkIntegrand_eq_zero_of_sin_two_eq_zero hα hsin]
    norm_num
  -- the main case
  have h6 : ∀ (u : Fn), HkIntegrand α 3 u z θ ≤ HkIntegrand α 6 u z θ := fun u =>
    Work.FTS.StrongPersist.HkIntegrand_le_of_le α (by norm_num) u z θ
  have h46 : ∀ (u : Fn), HkIntegrand α 4 u z θ ≤ HkIntegrand α 6 u z θ := fun u =>
    Work.FTS.StrongPersist.HkIntegrand_le_of_le α (by norm_num : 4 ≤ 6) u z θ
  -- `X1`
  have hb1 : HkIntegrand α 3 X1 z θ = (1 / α) ^ 2 * HkIntegrand α 3 f z θ := by
    rw [hX1]
    exact Work.FTS.LocData.HkIntegrand_const_mul α 3 (1 / α) f z θ
  -- `X2`
  have hb2 : HkIntegrand α 3 X2 z θ = (3 / (2 * α)) ^ 2 * HkIntegrand α 3 (Dth f) z θ := by
    rw [hX2]
    exact Work.FTS.LocData.HkIntegrand_const_mul α 3 (3 / (2 * α)) (Dth f) z θ
  have hDth : HkIntegrand α 3 (Dth f) z θ ≤ HkIntegrand α 6 f z θ := by
    have h : Dth f = Work.Spaces.mixed 0 1 f := by
      funext z θ
      simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
        Work.Spaces.DthIter_zero, Dth]
    rw [h]
    exact le_trans (Work.FTS.StrongPersist.L3Aux.HkIntegrand_mixed_shift α hα 3 1 0 hso z hz θ hθ)
      (h46 f)
  -- `X3`
  have hDz : HkIntegrand α 3 (Dz f) z θ ≤ HkIntegrand α 6 f z θ := by
    have h : Dz f = Work.Spaces.mixed 1 0 f := by
      funext z θ
      simp only [Work.Spaces.mixed, Work.Spaces.DthIter_zero, Work.Spaces.DzIter]
    rw [h]
    exact le_trans (Work.FTS.StrongPersist.L3Aux.HkIntegrand_mixed_shift α hα 3 0 1 hso z hz θ hθ)
      (h46 f)
  have hsin2 : HkIntegrand α 3 (fun z θ => Real.sin θ ^ 2 * Dz f z θ) z θ
      ≤ Cang * HkIntegrand α 3 (Dz f) z θ :=
    hCang2 α (Dz f) hα hα1 hso.Dz z hz θ hθ
  -- the two additivity steps
  have step1 : HkIntegrand α 3 (fun z θ => X1 z θ + X2 z θ + X3 z θ) z θ
      ≤ 2 * HkIntegrand α 3 (fun z θ => X1 z θ + X2 z θ) z θ + 2 * HkIntegrand α 3 X3 z θ :=
    Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α 3 hX12c hX3c z hz θ hθ
  have step2 : HkIntegrand α 3 (fun z θ => X1 z θ + X2 z θ) z θ
      ≤ 2 * HkIntegrand α 3 X1 z θ + 2 * HkIntegrand α 3 X2 z θ :=
    Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α 3 hX1c hX2c z hz θ hθ
  -- decompose `X3 = -Dz f + 3 (sin²θ · Dz f)`
  have hX3eq : X3 = fun z θ => (-1 : ℝ) * Dz f z θ + 3 * (Real.sin θ ^ 2 * Dz f z θ) := by
    funext z θ
    simp only [hX3, Work.Construction.c2m_eq]
    have hcos : Real.cos (2 * θ) = 1 - 2 * Real.sin θ ^ 2 := by
      rw [Real.cos_two_mul', Real.cos_sq']; ring
    rw [hcos]
    ring
  have hX3c' : ContDiffOn ℝ 3 (Function.uncurry (fun z θ => (-1 : ℝ) * Dz f z θ
      + 3 * (Real.sin θ ^ 2 * Dz f z θ))) Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_const.mul (hso.Dz.forall 3)).add
      (contDiffOn_const.mul (((by fun_prop : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Real.sin p.2 ^ 2)
        Work.FTS.EllipticEst.Q0)).mul (hso.Dz.forall 3)))
  have step3 : HkIntegrand α 3 X3 z θ
      ≤ 2 * HkIntegrand α 3 (fun z θ => (-1 : ℝ) * Dz f z θ) z θ
        + 2 * HkIntegrand α 3 (fun z θ => 3 * (Real.sin θ ^ 2 * Dz f z θ)) z θ := by
    rw [hX3eq]
    exact Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α 3
      (contDiffOn_const.mul (hso.Dz.forall 3))
      (contDiffOn_const.mul (((by fun_prop : ContDiffOn ℝ 3
        (fun p : ℝ × ℝ => Real.sin p.2 ^ 2) Work.FTS.EllipticEst.Q0)).mul (hso.Dz.forall 3)))
      z hz θ hθ
  have hcm1 : HkIntegrand α 3 (fun z θ => (-1 : ℝ) * Dz f z θ) z θ
      = 1 * HkIntegrand α 3 (Dz f) z θ := by
    rw [Work.FTS.LocData.HkIntegrand_const_mul α 3 (-1) (Dz f) z θ]
    norm_num
  have hcm3 : HkIntegrand α 3 (fun z θ => 3 * (Real.sin θ ^ 2 * Dz f z θ)) z θ
      = 9 * HkIntegrand α 3 (fun z θ => Real.sin θ ^ 2 * Dz f z θ) z θ := by
    rw [Work.FTS.LocData.HkIntegrand_const_mul α 3 3
      (fun z θ => Real.sin θ ^ 2 * Dz f z θ) z θ]
    norm_num
  -- scaling facts
  have hα2le : α ^ 2 ≤ 1 := by nlinarith [hα1, hα]
  have hone : (1 : ℝ) ≤ (1 / α) ^ 2 := by
    rw [div_pow, one_pow]
    exact one_le_one_div (by positivity) hα2le
  have hcoef : (3 / (2 * α)) ^ 2 = (9 / 4) * (1 / α) ^ 2 := by
    field_simp
    ring
  have hI6nn : 0 ≤ HkIntegrand α 6 f z θ := Work.Spaces.HkIntegrand_nonneg α 6 f z θ
  have hX12b : HkIntegrand α 3 (fun z θ => X1 z θ + X2 z θ) z θ
      ≤ (2 * (1 / α) ^ 2 + (9 / 2) * (1 / α) ^ 2) * HkIntegrand α 6 f z θ := by
    have h := step2
    rw [hb1, hb2, hcoef] at h
    have h3 : (9 / 4) * (1 / α) ^ 2 * HkIntegrand α 3 (Dth f) z θ
        ≤ (9 / 4) * (1 / α) ^ 2 * HkIntegrand α 6 f z θ :=
      mul_le_mul_of_nonneg_left hDth (by positivity)
    have h1 : (1 / α) ^ 2 * HkIntegrand α 3 f z θ
        ≤ (1 / α) ^ 2 * HkIntegrand α 6 f z θ :=
      mul_le_mul_of_nonneg_left (h6 f) (by positivity)
    nlinarith [h, h1, h3]
  have hX3b : HkIntegrand α 3 X3 z θ
      ≤ (4 + 36 * Cang) * HkIntegrand α 6 f z θ := by
    have h := step3
    rw [hcm1, hcm3] at h
    have hs : HkIntegrand α 3 (fun z θ => Real.sin θ ^ 2 * Dz f z θ) z θ
        ≤ Cang * HkIntegrand α 6 f z θ :=
      le_trans hsin2 (mul_le_mul_of_nonneg_left hDz hCangpos.le)
    nlinarith [h, hs, hDz, hI6nn, hCangpos]
  have hfinal : HkIntegrand α 3 (fun z θ => X1 z θ + X2 z θ + X3 z θ) z θ
      ≤ (21 + 72 * Cang) * (1 / α) ^ 2 * HkIntegrand α 6 f z θ := by
    have h := step1
    have h2 : 2 * HkIntegrand α 3 (fun z θ => X1 z θ + X2 z θ) z θ
        ≤ 2 * ((2 * (1 / α) ^ 2 + (9 / 2) * (1 / α) ^ 2) * HkIntegrand α 6 f z θ) :=
      mul_le_mul_of_nonneg_left hX12b (by norm_num)
    have h3 : 2 * HkIntegrand α 3 X3 z θ
        ≤ 2 * ((4 + 36 * Cang) * HkIntegrand α 6 f z θ) :=
      mul_le_mul_of_nonneg_left hX3b (by norm_num)
    have h4 : (2 * (2 * (1 / α) ^ 2 + (9 / 2) * (1 / α) ^ 2) + 2 * (4 + 36 * Cang))
        * HkIntegrand α 6 f z θ ≤ (21 + 72 * Cang) * (1 / α) ^ 2 * HkIntegrand α 6 f z θ := by
      refine mul_le_mul_of_nonneg_right ?_ hI6nn
      nlinarith [hone, hCangpos]
    nlinarith [h, h2, h3, h4]
  rw [hVfeq]
  exact hfinal

/-! ## The `Vf`-part of the coupled product -/

theorem smoothOpen_sin_two : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Real.sin (2 * θ)) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun _ θ : ℝ => Real.sin (2 * θ))) Work.FTS.EllipticEst.Q0
  have h1 : Function.uncurry (fun _ θ : ℝ => Real.sin (2 * θ))
      = fun p : ℝ × ℝ => Real.sin (2 * p.2) := rfl
  rw [h1]
  exact (((Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn)).of_le le_top

theorem smoothOpen_c2m : Work.FTS.EllipticEst.SmoothOpen
    (fun _ θ : ℝ => Real.cos (2 * θ) - Real.sin θ ^ 2) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun _ θ : ℝ => Real.cos (2 * θ) - Real.sin θ ^ 2)) Work.FTS.EllipticEst.Q0
  have h1 : Function.uncurry (fun _ θ : ℝ => Real.cos (2 * θ) - Real.sin θ ^ 2)
      = fun p : ℝ × ℝ => Real.cos (2 * p.2) - Real.sin p.2 ^ 2 := rfl
  rw [h1]
  exact ((((Real.contDiff_cos.comp (contDiff_const.mul contDiff_snd)).sub
    ((Real.contDiff_sin.comp contDiff_snd).pow 2)).contDiffOn)).of_le le_top

theorem smoothOpen_Vf {α : ℝ} {f : Fn}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) : Work.FTS.EllipticEst.SmoothOpen (Vf α f) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (1 / α) * f z θ) :=
    contDiffOn_const.mul hso
  have h2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (3 / (2 * α)) * (Real.sin (2 * θ) * Work.Spaces.pth f z θ)) :=
    contDiffOn_const.mul (smoothOpen_sin_two.mul hso.pth)
  have h3 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (Real.cos (2 * θ) - Real.sin θ ^ 2) * Work.Spaces.Dz f z θ) :=
    smoothOpen_c2m.mul hso.Dz
  have hmain : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      (1 / α) * f z θ + (3 / (2 * α)) * (Real.sin (2 * θ) * Work.Spaces.pth f z θ)
        - (Real.cos (2 * θ) - Real.sin θ ^ 2) * Work.Spaces.Dz f z θ) := (h1.add h2).sub h3
  have hfun : (fun z θ =>
      (1 / α) * f z θ + (3 / (2 * α)) * (Real.sin (2 * θ) * Work.Spaces.pth f z θ)
        - (Real.cos (2 * θ) - Real.sin θ ^ 2) * Work.Spaces.Dz f z θ) = Vf α f := by
    funext z θ
    simp only [Vf, Work.Construction.s2_eq, Work.Construction.c2m_eq]
    ring
  rwa [hfun] at hmain

/-- **The pointwise bound for `Mf f · Vf α f`.** -/
theorem P1_integrand_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hL12 : Work.Construction.L12 f 0 = 0)
    {Cjet : ℝ} (hCjetnn : 0 ≤ Cjet)
    (hjet : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 f z) z|
        ≤ Cjet * Work.Spaces.HkNorm α 4 f)
    {CV : ℝ}
    (hVf : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 3 (Vf α f) z θ
        ≤ CV * (1 / α) ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 3 (fun z θ => Mf f z θ * Vf α f z θ) z θ
        ≤ Work.FTS.StrongPersist.L3Aux.zmulConst 3 * (1 + Cjet * Work.Spaces.HkNorm α 4 f) ^ 2
            * CV * (1 / α) ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ := by
  intro z hz θ hθ
  set φ : ℝ → ℝ := fun z => Work.Construction.L12 f z with hφdef
  have hφeq : (fun z θ => Mf f z θ * Vf α f z θ) = fun z θ => φ z * Vf α f z θ := by
    funext z θ
    simp only [Mf, hφdef]
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · subst hz0
    rw [hφeq, Work.FTS.LocData.HkIntegrand_zero_fst, Work.FTS.LocData.HkIntegrand_zero_fst]
    norm_num
  by_cases hsin : Real.sin (2 * θ) = 0
  · rw [hφeq, Work.Construction.HkIntegrand_eq_zero_of_sin_two_eq_zero hα hsin,
      Work.Construction.HkIntegrand_eq_zero_of_sin_two_eq_zero hα hsin]
    norm_num
  have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    refine ⟨?_, ?_⟩
    · rcases lt_or_eq_of_le hθ.1 with h | h
      · exact h
      · exact absurd (by rw [← h]; simp) hsin
    · rcases lt_or_eq_of_le hθ.2 with h | h
      · exact h
      · exact absurd (by rw [h, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]) hsin
  have hsoVf : Work.FTS.EllipticEst.SmoothOpen (Vf α f) := smoothOpen_Vf hso
  have hφc : ∀ i : ℕ, i ≤ 3 → ContDiffOn ℝ (i : WithTop ℕ∞) φ (Set.Ioi (0 : ℝ)) := by
    intro i hi
    have h4 : ContDiffOn ℝ 4 φ (Set.Ioi (0 : ℝ)) :=
      Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 4 f hα hα1 hso hmem (by norm_num)
    exact h4.of_le (by exact_mod_cast (by omega : i ≤ 4))
  have hle : ∀ i : ℕ, (i : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := fun i =>
    WithTop.coe_le_coe.mpr le_top
  have hVs : ∀ i : ℕ, ContDiffOn ℝ (i : WithTop ℕ∞) (fun z' => Vf α f z' θ)
      (Set.Ioi (0 : ℝ)) := fun i =>
    ((hsoVf.curry_z hθ').of_le (hle i))
  have hDs : ∀ i j : ℕ, ContDiffOn ℝ (j : WithTop ℕ∞)
      (fun z' => Work.Spaces.DthIter i (Vf α f) z' θ) (Set.Ioi (0 : ℝ)) := fun i j =>
    (((hsoVf.DthIter i).curry_z hθ').of_le (hle j))
  have hexpZ : ∀ i ≤ 3, Work.Spaces.DzIter i (fun z θ => φ z * Vf α f z θ) z θ
      = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
          * (Work.Spaces.Zop^[b] φ z * Work.Spaces.DzIter (i - b) (Vf α f) z θ) :=
    fun i hi => Work.FTS.FinalClock.DzIter_mul_of_contDiffOn i φ (Vf α f) isOpen_Ioi
      (hφc i hi) (hVs i) z hzpos
  have hexpM : ∀ j i, 1 ≤ i → i + j ≤ 3 →
      Work.Spaces.mixed j i (fun z θ => φ z * Vf α f z θ) z θ
      = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
          * (Work.Spaces.Zop^[b] φ z * Work.Spaces.mixed (j - b) i (Vf α f) z θ) :=
    fun j i hi hij => Work.FTS.FinalClock.mixed_mul_of_contDiffOn j i φ (Vf α f) isOpen_Ioi
      (hφc j (by omega)) (hDs i j) z hzpos
  have hB : ∀ b ≤ 3, |Work.Spaces.Zop^[b] φ z| ≤ Cjet * Work.Spaces.HkNorm α 4 f := by
    intro b hb
    exact hjet b hb z hzpos
  have hKnn : 0 ≤ Cjet * Work.Spaces.HkNorm α 4 f :=
    mul_nonneg hCjetnn (Real.sqrt_nonneg _)
  have hzm := Work.FTS.StrongPersist.L3Aux.zmul_pt α 3 φ (Vf α f) hKnn hB hexpZ hexpM
  rw [hφeq]
  have htarget := hVf z hz θ hθ
  have hzmc : Work.FTS.StrongPersist.L3Aux.zmulConst 3
      * (1 + Cjet * Work.Spaces.HkNorm α 4 f) ^ 2
        * Work.Spaces.HkIntegrand α 3 (Vf α f) z θ
      ≤ Work.FTS.StrongPersist.L3Aux.zmulConst 3
        * (1 + Cjet * Work.Spaces.HkNorm α 4 f) ^ 2
          * (CV * (1 / α) ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) :=
    mul_le_mul_of_nonneg_left htarget
      (mul_nonneg (Work.FTS.StrongPersist.L3Aux.zmulConst_pos 3).le (sq_nonneg _))
  exact le_trans hzm (le_trans hzmc (le_of_eq (by ring)))

end Work.FTS.StrongPersist.L3Rhs
end
end
