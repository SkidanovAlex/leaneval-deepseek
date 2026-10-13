import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.TenOfEight.LamAllDefs
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainSlot.mslot_le_gain
import Submission.Work.FTS.StrongEps.StepFacts.slot_route_bounds
import Submission.Work.FTS.StrongEps.StepFacts.SlotBounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

open Work.FTS.StrongEps.EpsE4Thr

namespace Work.FTS.StrongEps.TenOfEight

set_option maxHeartbeats 1000000

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
by `LamAll` (pointwise) and by `Ksm · 2^{2M} = KgainBig` (in mass). -/
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

/-- `Work.FTS.StrongEps.TenOfEight.mslot_le_gain_all` (namespace `Work.FTS.StrongEps.TenOfEight`).

**Recipe.** Copy `Submission/Work/FTS/StrongEps/EpsE4Thr/GainSlot/mslot_le_gain.lean` into the
new file (including its private helpers `tsupport_KdK_subset_closedBall`,
`KdK_eq_zero_of_notMem_closedBall`, `integrable_abs_KdK_mul`, `integral_abs_KdK_le_Ksm`,
`sq_mul_pow_two` and `mslot_core`, which are `private` and hence must be reproduced; note that
from the new namespace the unqualified names `KdK`, `Ksm`, `LamK`, … need `open Work.FTS.StrongEps.EpsE4Thr`),
then
(i) drop the hypothesis `hε1 : ε ≤ 1`,
(ii) replace the density `Work.FTS.StrongEps.EpsE4Thr.LamFull ρ ε c M` everywhere by
`Work.FTS.StrongEps.TenOfEight.LamAll ρ ε c M` (defined in
`Submission/Work/FTS/StrongEps/TenOfEight/LamAllDefs.lean`),
(iii) replace the three uses of `LamFull_nonneg hρ hε M` by `LamAll_nonneg hρ hε M` and the use
of `abs_KdK_mul_exp_le_LamFull hρ hε hε1 hc (by omega) p` by
`abs_KdK_mul_exp_le_LamAll hρ hε hc (by omega) p`
(both live in `Work.FTS.StrongEps.TenOfEight`).
Nothing else changes: the private core `mslot_core` and the mass constants `KgainBig`/`Ksm`
are unchanged. -/
theorem mslot_le_gain_all {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε α c : ℝ}
    (hε : 0 < ε) (hc : 0 ≤ c) {M k : ℕ} (hk : 1 ≤ k) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hW : ∀ p : ℝ × ℝ, Work.Spaces.Wt α z θ ≤ Real.exp (c * (|p.1| + |p.2|))
      * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
    {j i : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ M) :
    ENNReal.ofReal ((Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
        * Work.Spaces.Wt α z θ) ^ 2)
      ≤ ENNReal.ofReal (Work.FTS.StrongEps.EpsE4Thr.KgainBig ρ ε M)
        * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.TenOfEight.LamAll ρ ε c M p)
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
  have hF'0 : ∀ p : ℝ × ℝ, 0 ≤ LamAll ρ ε c M p
      * Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2) :=
    fun p => mul_nonneg (LamAll_nonneg hρ hε M p)
      (Work.Spaces.HkIntegrand_nonneg α k f _ _)
  have hFF : ∀ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|
      * Real.exp (2 * c * (|p.1| + |p.2|))
      * (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)) ^ 2
      ≤ LamAll ρ ε c M p
      * Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2) := by
    intro p
    have h1 : |KdK ρ ε j (i - 1) p| * Real.exp (2 * c * (|p.1| + |p.2|))
        ≤ LamAll ρ ε c M p :=
      abs_KdK_mul_exp_le_LamAll hρ hε hc (by omega) p
    have h2 : (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)) ^ 2
        ≤ Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2) :=
      Work.Spaces.sq_le_HkIntegrand_mixed α k f _ _ 1 0 le_rfl (by omega)
    exact mul_le_mul h1 h2 (sq_nonneg _) (LamAll_nonneg hρ hε M p)
  refine (Work.FTS.StrongEps.StepFacts.ofReal_mul_integral_le_lintegral
    (KgainBig_nonneg hρ ε M) (KgainBig_nonneg hρ ε M) le_rfl hF0 hF'0 hFF).trans ?_
  rw [lintegral_congr (fun p => ENNReal.ofReal_mul (LamAll_nonneg hρ hε M p))]

end Work.FTS.StrongEps.TenOfEight
