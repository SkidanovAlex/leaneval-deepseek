import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainDefs
import Submission.Work.FTS.StrongEps.mixed_Jeps_kernel_partial
import Submission.Work.FTS.StrongPersist.L3Rhs.CoupledVf
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNstarBlock
import Submission.Work.FTS.StrongPersist.L3Rhs.N3ssPriced
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.SmainHon
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_MuLamOK.Rows.Rl0Open
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.starVop
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.GainPt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem HkIntegrand_Jeps_gain_pt {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε α c : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hc : 0 ≤ c) {M k : ℕ} (hk : 1 ≤ k)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hWη : ∀ p : ℝ × ℝ, Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
      ≤ Real.exp (c * (|p.1| + |p.2|))
        * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
            / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2)) ^ (Work.Spaces.eta / 2)))
    (hWγ : ∀ p : ℝ × ℝ, Work.Spaces.Wt α z θ ≤ Real.exp (c * (|p.1| + |p.2|))
      * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) :
    ENNReal.ofReal (Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ)
      ≤ ENNReal.ofReal (Cgain ρ ε M)
        * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (LamFull ρ ε c M p)
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) := by
  set J : ℝ≥0∞ := ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (LamFull ρ ε c M p)
      * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
          (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) with hJdef
  set Kg : ℝ≥0∞ := ENNReal.ofReal (KgainBig ρ ε M) with hKgdef
  set A : ℝ := ∑ a ∈ Finset.range (M + 1),
    (Work.Spaces.DzIter a (Work.FTS.StrongEps.Jeps ρ ε f) z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 with hAdef
  set B : ℝ := ∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (M + 1),
    (if 1 ≤ i ∧ i + j ≤ M then
      (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ * Work.Spaces.Wt α z θ) ^ 2
      else 0) with hBdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact Finset.sum_nonneg fun a _ => sq_nonneg _
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
      split_ifs with h <;> simp [sq_nonneg]
  have hsplit : Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ = A + B := by
    simp only [Work.Spaces.HkIntegrand]
    rw [← hAdef, ← hBdef]
  -- the per-slot bounds, and the two finite sums
  have hslotA : ∀ a ∈ Finset.range (M + 1),
      ENNReal.ofReal ((Work.Spaces.DzIter a (Work.FTS.StrongEps.Jeps ρ ε f) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) ≤ Kg * J := by
    intro a ha
    have haM : a ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    simpa only [hJdef, hKgdef] using
      GainSlot.zslot_le_gain hρ hε hε1 hc hf hz hθ hWη haM
  have hslotB : ∀ i ∈ Finset.range (M + 1), ∀ j ∈ Finset.range (M + 1),
      ENNReal.ofReal (if 1 ≤ i ∧ i + j ≤ M then
        (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0) ≤ Kg * J := by
    intro i _ j _
    by_cases hc' : 1 ≤ i ∧ i + j ≤ M
    · rw [if_pos hc']
      simpa only [hJdef, hKgdef] using
        GainSlot.mslot_le_gain hρ hε hε1 hc hk hf hz hθ hWγ hc'.1 hc'.2
    · rw [if_neg hc']
      simp only [ENNReal.ofReal_zero]
      exact zero_le
  have hA_le : (∑ a ∈ Finset.range (M + 1),
      ENNReal.ofReal ((Work.Spaces.DzIter a (Work.FTS.StrongEps.Jeps ρ ε f) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
      ≤ ((M + 1 : ℕ) : ℝ≥0∞) * (Kg * J) := by
    refine (Finset.sum_le_card_nsmul (Finset.range (M + 1)) _ (Kg * J) hslotA).trans ?_
    rw [Finset.card_range]
    exact Work.FTS.StrongEps.StepFacts.nsmul_le_natCast_mul (M + 1) (Kg * J)
  have hB_le : (∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (M + 1),
      ENNReal.ofReal (if 1 ≤ i ∧ i + j ≤ M then
        (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)) ≤ (((M + 1) * (M + 1) : ℕ) : ℝ≥0∞) * (Kg * J) := by
    have hinner : ∀ i ∈ Finset.range (M + 1),
        (∑ j ∈ Finset.range (M + 1), ENNReal.ofReal (if 1 ≤ i ∧ i + j ≤ M then
          (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ ((M + 1 : ℕ) : ℝ≥0∞) * (Kg * J) := fun i hi =>
      (Finset.sum_le_card_nsmul (Finset.range (M + 1)) _ (Kg * J)
        (fun j hj => hslotB i hi j hj)).trans (by
          rw [Finset.card_range]
          exact Work.FTS.StrongEps.StepFacts.nsmul_le_natCast_mul (M + 1) (Kg * J))
    refine (Finset.sum_le_card_nsmul (Finset.range (M + 1)) _ _ hinner).trans ?_
    rw [Finset.card_range, nsmul_eq_mul, Nat.cast_mul, mul_assoc]
  -- the `ofReal` split and the numerical bookkeeping
  have hpt : ENNReal.ofReal (Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ)
      = ENNReal.ofReal A + ENNReal.ofReal B := by
    rw [hsplit, ENNReal.ofReal_add hA0 hB0]
  have h1 : ENNReal.ofReal A = ∑ a ∈ Finset.range (M + 1),
      ENNReal.ofReal ((Work.Spaces.DzIter a (Work.FTS.StrongEps.Jeps ρ ε f) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    rw [hAdef, ENNReal.ofReal_sum_of_nonneg]
    exact fun a _ => sq_nonneg _
  have h2 : ENNReal.ofReal B = ∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (M + 1),
      ENNReal.ofReal (if 1 ≤ i ∧ i + j ≤ M then
        (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
          * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
    rw [hBdef, ENNReal.ofReal_sum_of_nonneg]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [ENNReal.ofReal_sum_of_nonneg]
      exact fun j _ => by split_ifs with h <;> simp [sq_nonneg]
    · exact fun i _ => Finset.sum_nonneg fun j _ => by
        split_ifs with h <;> simp [sq_nonneg]
  have hAB : ENNReal.ofReal A + ENNReal.ofReal B
      ≤ ((((M + 1) + (M + 1) * (M + 1) : ℕ)) : ℝ≥0∞) * (Kg * J) := by
    rw [h1, h2]
    refine (add_le_add hA_le hB_le).trans (le_of_eq ?_)
    rw [← add_mul, ← Nat.cast_add]
  have hC : ENNReal.ofReal (Cgain ρ ε M) * J
      = ((((M + 1) + (M + 1) * (M + 1) : ℕ)) : ℝ≥0∞) * (Kg * J) := by
    rw [Cgain, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ← hKgdef]
    rw [pow_two, mul_assoc]
  rw [hpt]
  exact hAB.trans (le_of_eq hC.symm)

end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.TenOfEight.zslot_le_gain_all =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.TenOfEight

set_option maxHeartbeats 1000000

/-! ## Two elementary facts about the routed kernel derivative `KdK ρ ε a b`

The routed density `Λ = LamAll ρ ε c M` of `LamAllDefs.lean` is supported in the closed ball of
radius `ε` (it is a rescaled kernel whose density is supported in the unit ball).  We need the
same for the routed kernel derivative `KdK ρ ε a b = ∂₁^a∂₂^b (Jker ρ ε)`, together with the
integrability of `|KdK|` against any function continuous on that ball — this is the input of the
weighted Cauchy–Schwarz core `StepFacts.SlotAux.srb_cs_core`. -/

/-- The routed kernel derivative vanishes off the ball of radius `ε`. -/
private theorem KdK_eq_zero_of_notMem_ball {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) (a b : ℕ) {p : ℝ × ℝ}
    (hp : p ∉ Metric.closedBall 0 ε) : Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p = 0 := by
  rw [Work.FTS.StrongEps.EpsE4Thr.Kd_Jker_scale hρ ε a b p]
  have hmax : ε < max |p.1| |p.2| := by
    by_contra hcon
    exact hp (by
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
        Real.norm_eq_abs]
      exact not_lt.mp hcon)
  have hzero : Work.FTS.StrongEps.EpsE4Thr.Kdr ρ a b (ε⁻¹ • p) = 0 := by
    by_contra hne
    have h1 := Work.FTS.StrongEps.EpsE4Thr.Kdr_support hρ a b (ε⁻¹ • p) hne
    have hq1 : |(ε⁻¹ • p).1| ≤ 1 := by
      have : (ε⁻¹ • p).1 ^ 2 ≤ 1 := by linarith [sq_nonneg (ε⁻¹ • p).2]
      rwa [sq_le_one_iff_abs_le_one] at this
    have hq2 : |(ε⁻¹ • p).2| ≤ 1 := by
      have : (ε⁻¹ • p).2 ^ 2 ≤ 1 := by linarith [sq_nonneg (ε⁻¹ • p).1]
      rwa [sq_le_one_iff_abs_le_one] at this
    have hqle : max |(ε⁻¹ • p).1| |(ε⁻¹ • p).2| ≤ 1 := max_le hq1 hq2
    have hgt : 1 < max |(ε⁻¹ • p).1| |(ε⁻¹ • p).2| := by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, abs_mul,
        abs_of_nonneg (inv_nonneg.mpr hε.le)]
      rw [← mul_max_of_nonneg _ _ (inv_nonneg.mpr hε.le)]
      have h1 : (1 : ℝ) = ε⁻¹ * ε := (inv_mul_cancel₀ hε.ne').symm
      rw [h1]
      exact mul_lt_mul_of_pos_left hmax (by positivity)
    linarith
  rw [show Work.FTS.StrongEps.Jker (Work.FTS.StrongEps.EpsE4Thr.Kdr ρ a b) ε p = 0 from by
    simp only [Work.FTS.StrongEps.Jker, hzero, mul_zero], mul_zero]

/-- `|KdK ρ ε a b|` is integrable against any function continuous on the ball of radius `ε`
(the kernel derivative is continuous and supported there). -/
private theorem integrable_abs_KdK_mul {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) (a b : ℕ)
    {B : ℝ × ℝ → ℝ} (hB : ContinuousOn B (Metric.closedBall (0 : ℝ × ℝ) ε)) :
    Integrable (fun p : ℝ × ℝ => |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p| * B p) := by
  have hcont : Continuous (fun p : ℝ × ℝ => |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p|) :=
    (Work.FTS.StrongEps.EpsE4Thr.KdK_continuous hρ ε a b).abs
  have hon : IntegrableOn (fun p : ℝ × ℝ => |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p| * B p)
      (Metric.closedBall (0 : ℝ × ℝ) ε) :=
    (hcont.continuousOn.mul hB).integrableOn_compact (isCompact_closedBall (0 : ℝ × ℝ) ε)
  refine hon.integrable_of_forall_notMem_eq_zero (fun p hp => ?_)
  rw [KdK_eq_zero_of_notMem_ball hρ hε a b hp, abs_zero, zero_mul]

/-- `Work.FTS.StrongEps.TenOfEight.zslot_le_gain_all` (namespace `Work.FTS.StrongEps.TenOfEight`).

**Recipe.** Copy `Submission/Work/FTS/StrongEps/EpsE4Thr/GainSlot/zslot_le_gain.lean` into the
new file (including its private helpers `KdK_eq_zero_of_notMem_ball` and
`integrable_abs_KdK_mul`, which are `private` and hence must be reproduced), then
(i) drop the hypothesis `hε1 : ε ≤ 1`,
(ii) replace the density `Work.FTS.StrongEps.EpsE4Thr.LamFull ρ ε c M` everywhere by
`Work.FTS.StrongEps.TenOfEight.LamAll ρ ε c M` (defined in
`Submission/Work/FTS/StrongEps/TenOfEight/LamAllDefs.lean`),
(iii) replace the two uses of `LamFull_nonneg hρ hε M` by `LamAll_nonneg hρ hε M` and the use
of `abs_KdK_mul_exp_le_LamFull hρ hε hε1 hc (by omega) p` by
`abs_KdK_mul_exp_le_LamAll hρ hε hc (by omega) p`
(both live in `Work.FTS.StrongEps.TenOfEight`).
Nothing else changes: the mass constants `KgainBig`/`Ksm` are unchanged. -/
theorem zslot_le_gain_all {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε α c : ℝ}
    (hε : 0 < ε) (hc : 0 ≤ c) {M k : ℕ} {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hW : ∀ p : ℝ × ℝ, Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
      ≤ Real.exp (c * (|p.1| + |p.2|))
        * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
            / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2)) ^ (Work.Spaces.eta / 2)))
    {a : ℕ} (ha : a ≤ M) :
    ENNReal.ofReal ((Work.Spaces.DzIter a (Work.FTS.StrongEps.Jeps ρ ε f) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ ENNReal.ofReal (Work.FTS.StrongEps.EpsE4Thr.KgainBig ρ ε M)
        * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.TenOfEight.LamAll ρ ε c M p)
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) := by
  -- the routed identity: `D_z^a (J_ε f)` against the kernel derivative `KdK ρ ε a 0`
  have hroute : Work.Spaces.DzIter a (Work.FTS.StrongEps.Jeps ρ ε f) z θ
      = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a 0 p
          * f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) := by
    have h := Work.FTS.StrongEps.mixed_Jeps_kernel_partial ρ hρ hε hf hz hθ a 0 0 0
      (Nat.zero_le a) le_rfl
    simp only [Work.Spaces.mixed_zero_right] at h
    rw [h]
    simp only [Nat.sub_zero, pow_zero, one_mul, iteratedDeriv_zero, Work.Spaces.DzIter_zero]
    congr 1
    ext p
    simp only [Work.FTS.StrongEps.EpsE4Thr.KdK, Work.FTS.StrongEps.Kd_eq, iteratedDeriv_zero]
  have hW₀ : 0 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
    Work.FTS.StrongEps.StepFacts.srb_wdiv_nonneg hz hθ
  -- continuity of the two shifted factors on the ball of radius `ε`
  have hGcont : ContinuousOn
      (fun p : ℝ × ℝ => f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
      (Metric.closedBall (0 : ℝ × ℝ) ε) := by
    have hbase : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.mixed 0 0 f q.1 q.2)
        (Work.FTS.StrongEps.Kz z ε ×ˢ Work.FTS.StrongEps.Kth θ ε) :=
      (Work.FTS.StrongEps.HkSqAux.continuousOn_mixed_Quad hf 0 0).mono
        (Work.FTS.StrongEps.Kz_prod_Kth_subset_Quad hz hε hθ)
    have hh := Work.FTS.StrongEps.HkSqAux.continuousOn_shift_ball (ε := ε) hz hθ hbase
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using hh
  have hWcont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
        / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2)) ^ (Work.Spaces.eta / 2))
      (Metric.closedBall (0 : ℝ × ℝ) ε) :=
    Work.FTS.StrongEps.HkSqAux.continuousOn_shift_ball (ε := ε) hz hθ
      (A := fun x y => Work.Spaces.w x / (Real.sin (2 * y)) ^ (Work.Spaces.eta / 2))
      (Work.FTS.StrongEps.HkSqAux.continuousOn_wdiv_region (z := z) (ε := ε) hz hε hθ)
  -- the three integrability inputs of the Cauchy–Schwarz core
  have hKint : Integrable (fun p : ℝ × ℝ =>
      |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a 0 p|) := by
    simpa using integrable_abs_KdK_mul hρ hε a 0 (B := fun _ : ℝ × ℝ => (1 : ℝ))
      continuousOn_const
  have hQ : Integrable (fun p : ℝ × ℝ =>
      |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a 0 p| * Real.exp (2 * c * (|p.1| + |p.2|))
        * (f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
          * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
              / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2))
                ^ (Work.Spaces.eta / 2))) ^ 2) := by
    have hB : ContinuousOn (fun p : ℝ × ℝ => Real.exp (2 * c * (|p.1| + |p.2|))
        * (f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
          * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
              / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2))
                ^ (Work.Spaces.eta / 2))) ^ 2)
        (Metric.closedBall (0 : ℝ × ℝ) ε) :=
      (Work.FTS.StrongEps.StepFacts.srb_continuous_exp_two c).continuousOn.mul
        ((hGcont.mul hWcont).pow 2)
    simpa only [mul_assoc] using integrable_abs_KdK_mul hρ hε a 0 hB
  have hK2 : Integrable (fun p : ℝ × ℝ =>
      |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a 0 p|
        * (f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    have hB : ContinuousOn (fun p : ℝ × ℝ =>
        (f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (Metric.closedBall (0 : ℝ × ℝ) ε) :=
      (hGcont.mul continuousOn_const).pow 2
    exact integrable_abs_KdK_mul hρ hε a 0 hB
  -- the weighted Cauchy–Schwarz core
  have hslot := Work.FTS.StrongEps.StepFacts.srb_cs_core
    (K := fun p : ℝ × ℝ => Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a 0 p)
    (G := fun p : ℝ × ℝ =>
      f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
    (W := fun p : ℝ × ℝ => Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
      / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2)) ^ (Work.Spaces.eta / 2))
    (W₀ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
    (c := c) (M := Work.Spaces.DzIter a (Work.FTS.StrongEps.Jeps ρ ε f) z θ)
    hW₀ hW hKint hQ hK2 hroute
  -- the constants and the pointwise domination by `Λ · HkIntegrand`
  have hK : 0 ≤ ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a 0 p| :=
    integral_nonneg fun p => abs_nonneg _
  have hKK : (∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a 0 p|)
      ≤ Work.FTS.StrongEps.EpsE4Thr.KgainBig ρ ε M :=
    Work.FTS.StrongEps.EpsE4Thr.integral_abs_KdK_le_KgainBig hρ hε ha (Nat.zero_le M)
  have hF : ∀ p : ℝ × ℝ, 0 ≤ |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a 0 p|
      * Real.exp (2 * c * (|p.1| + |p.2|))
      * (f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
          * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
              / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2))
                ^ (Work.Spaces.eta / 2))) ^ 2 :=
    fun p => mul_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) (sq_nonneg _)
  have hF' : ∀ p : ℝ × ℝ, 0 ≤ Work.FTS.StrongEps.TenOfEight.LamAll ρ ε c M p
      * Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2) :=
    fun p => mul_nonneg (LamAll_nonneg hρ hε M p)
      (Work.Spaces.HkIntegrand_nonneg α k f _ _)
  have hFF : ∀ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a 0 p|
      * Real.exp (2 * c * (|p.1| + |p.2|))
      * (f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
          * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
              / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2))
                ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Work.FTS.StrongEps.TenOfEight.LamAll ρ ε c M p
        * Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2) := by
    intro p
    have h1 : |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a 0 p|
        * Real.exp (2 * c * (|p.1| + |p.2|))
        ≤ Work.FTS.StrongEps.TenOfEight.LamAll ρ ε c M p :=
      abs_KdK_mul_exp_le_LamAll hρ hε hc (by omega) p
    have h2 : (f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
          * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
              / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2))
                ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2) := by
      have := Work.Spaces.sq_le_HkIntegrand_z α k f (Work.FTS.StrongEps.zShift z p.1)
        (Work.FTS.StrongEps.thShift θ p.2) 0 (Nat.zero_le k)
      simpa only [Work.Spaces.DzIter_zero] using this
    exact mul_le_mul h1 h2 (sq_nonneg _) (LamAll_nonneg hρ hε M p)
  have hfinal : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.TenOfEight.LamAll ρ ε c M p
        * Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)))
      = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.TenOfEight.LamAll ρ ε c M p)
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
              (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) :=
    lintegral_congr_ae (Eventually.of_forall fun p =>
      ENNReal.ofReal_mul (LamAll_nonneg hρ hε M p))
  refine ((ENNReal.ofReal_le_ofReal hslot).trans
    (Work.FTS.StrongEps.StepFacts.ofReal_mul_integral_le_lintegral hK
      (Work.FTS.StrongEps.EpsE4Thr.KgainBig_nonneg hρ ε M) hKK hF hF' hFF)).trans ?_
  rw [hfinal]

end Work.FTS.StrongEps.TenOfEight
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.N2ssPriced =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L3Rhs

/-- **Priced row 15**: the `ℋ⁴`-honesty and the `α²`-bound of the star piece `N₂^{**} = -2 · 𝒰(Φ̃_*) · ∂_θF_*`, with the constant *uniform* in `Cs` (linear loss in `1 + |Cs|`).

This is the priced form of `Work.FTS.NonlinRows.NRow15T2`: that result states
`∃ K, 0 < K ∧ ∀ …, Ctx2 … → HkMem α 4 (N2ss α Φs) ∧ Xn α (N2ss α Φs) ≤ K * α ^ 2`, where
`Ctx2` = `0 < α ∧ α ≤ 1 ∧ α ≤ α₂ ∧ GalClass α g ∧ StarPkgo2 α Cs Φs ∧ EllPkgGo α Ce g Φg`.
Its proof *constructs* the explicit constant `Cw * KW15 * (max Cs 0 + 1) + 1` (`Cw` = constant of
`Work.FTS.NonlinRows.wtoHQ_of_pointwise_open`, `KW15` a fixed positive constant of
`Work.FTS.NonlinRows.NRow15T2Aux`), and its body uses nothing but `0 < α`, `α ≤ 1`,
`StarPkgo α Cs Φs` and the two `𝒲^{4,∞}` facts about `G15 α Φs` (the field `StarPkgo2.UszW` is
exactly `WlInfMem α 4 (G15 α Φs) ∧ WlInf α 4 (G15 α Φs) ≤ Cs * α`).  So the proof is a copy of
that proof with `g`, `Φg`, `hgal`, `hell` dropped and `C = Cw * KW15 + 1`, using
`max Cs 0 + 1 ≤ 1 + |Cs|`. -/
theorem N2ssPriced : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ (Cs : ℝ) (Φs : Work.FTS.Galerkin.Fn),
    Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
    Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N2ss α Φs) ∧
    Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2ss α Φs) ≤ C * (1 + |Cs|) * α ^ 2 := by
  obtain ⟨Cw, hCw, hwto⟩ := Work.FTS.NonlinRows.wtoHQ_of_pointwise_open
  refine ⟨Cw * Work.FTS.NonlinRows.KW15 + 1, ?_, ?_⟩
  · have h : 0 ≤ Cw * Work.FTS.NonlinRows.KW15 :=
      mul_nonneg hCw.le (le_of_lt Work.FTS.NonlinRows.KW15_pos)
    linarith
  · intro α hαIoc Cs Φs hs
    obtain ⟨hα, hα1⟩ := hαIoc
    -- the underlying star package, and the two `𝒲^{4,∞}`-facts about `G15 α Φs`
    have hsp : Work.FTS.VocabO.StarPkgo α Cs Φs := hs.toStarPkgo
    have hGm : Work.Spaces.WlInfMem α 4 (Work.FTS.NonlinRows.G15 α Φs) := hs.UszW.1
    have hGle : Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs) ≤ Cs * α := hs.UszW.2
    have hB0 : 0 ≤ Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs) :=
      Work.FTS.H2.WlInf_nonneg hGm
    -- smoothness of the three objects
    have hGs : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.NonlinRows.G15 α Φs) :=
      Work.FTS.NonlinRows.smoothOpen_G15 hα hα1 hsp
    have hNsO : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.NonlinRows.N2ssO α Φs) :=
      Work.FTS.NonlinRows.smoothOpen_N2ssO hα hα1 hsp
    have hNs : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N2ss α Φs) :=
      Work.FTS.NonlinRows.smoothOpen_N2ss hα hα1 hsp
    -- the pointwise bounds of the open representative
    have hpt := Work.FTS.NonlinRows.row15_ptBound (α := α) (Φs := Φs) hα hα1 hGs hGm
    have hW0 : (0 : ℝ) ≤ Work.FTS.NonlinRows.KW15 * α
        * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs) :=
      mul_nonneg (mul_nonneg (le_of_lt Work.FTS.NonlinRows.KW15_pos) hα.le) hB0
    have hmain := hwto α (Work.FTS.NonlinRows.N2ssO α Φs)
      (Work.FTS.NonlinRows.KW15 * α * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs))
      hα hα1 hW0 hNsO hpt.1 hpt.2
    -- the two representatives agree on the open quadrant
    have hAgree : Work.FTS.EllipticEst.AgreeOnQ (Work.FTS.Nonlin.N2ss α Φs)
        (Work.FTS.NonlinRows.N2ssO α Φs) := by
      intro z θ hz hθ0 hθ1
      rw [Work.FTS.NonlinRows.N2ss_open_eq hα hz hθ0 hθ1]
      simp only [Work.FTS.NonlinRows.N2ssO, Work.FTS.NonlinRows.AG15]
    -- the honesty clause
    constructor
    · -- `ℋ⁴`-honesty of `N₂^{ss}`, by domination of the open representative
      have hmaj : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
          Work.Spaces.HkIntegrand α 4 (Work.FTS.Nonlin.N2ss α Φs) z θ
            ≤ 1 * Work.Spaces.HkIntegrand α 4 (Work.FTS.NonlinRows.N2ssO α Φs) z θ := by
        intro z hz θ hθ
        rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
        · rw [← h0, one_mul,
            Work.FTS.NonlinRows.NRow10aux.HkIntegrand_zero α 4 _ θ,
            Work.FTS.NonlinRows.NRow10aux.HkIntegrand_zero α 4 _ θ]
        · rw [one_mul, ← Work.FTS.EllipticEst.HkIntegrand_congr (α := α) (k := 4) hAgree
            z θ hz0 hθ.1 hθ.2]
      exact (Work.FTS.NonlinRows.NRow10aux.hkmem_of_majorant α 4 (show (0 : ℝ) ≤ 1 by norm_num)
        hNs hmain.1 hmaj).1
    · -- the `α²`-bound, along the agreement of the two `ℋ⁴`-norms
      have hsq : Work.Spaces.HkSq α 4 (Work.FTS.Nonlin.N2ss α Φs)
          = Work.Spaces.HkSq α 4 (Work.FTS.NonlinRows.N2ssO α Φs) :=
        Work.FTS.EllipticEst.HkSq_congr_open α 4 hAgree
      have hXn : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2ss α Φs)
          = Work.FTS.Nonlin.Xn α (Work.FTS.NonlinRows.N2ssO α Φs) := by
        simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, hsq]
      rw [hXn]
      calc Work.FTS.Nonlin.Xn α (Work.FTS.NonlinRows.N2ssO α Φs)
          ≤ Cw * (Work.FTS.NonlinRows.KW15 * α
              * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)) := hmain.2
        _ ≤ Cw * (Work.FTS.NonlinRows.KW15 * α * (Cs * α)) := by
            refine mul_le_mul_of_nonneg_left ?_ hCw.le
            exact mul_le_mul_of_nonneg_left hGle
              (mul_nonneg (le_of_lt Work.FTS.NonlinRows.KW15_pos) hα.le)
        _ = Cw * Work.FTS.NonlinRows.KW15 * Cs * α ^ 2 := by ring
        _ ≤ (Cw * Work.FTS.NonlinRows.KW15 + 1) * (1 + |Cs|) * α ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg α)
            have hCK : 0 ≤ Cw * Work.FTS.NonlinRows.KW15 :=
              mul_nonneg hCw.le (le_of_lt Work.FTS.NonlinRows.KW15_pos)
            have hCsle : Cs ≤ 1 + |Cs| := by
              linarith [le_abs_self Cs, abs_nonneg Cs]
            have h1Cs : 0 ≤ 1 + |Cs| := by positivity
            calc Cw * Work.FTS.NonlinRows.KW15 * Cs
                ≤ Cw * Work.FTS.NonlinRows.KW15 * (1 + |Cs|) :=
                  mul_le_mul_of_nonneg_left hCsle hCK
              _ ≤ (Cw * Work.FTS.NonlinRows.KW15 + 1) * (1 + |Cs|) :=
                  mul_le_mul_of_nonneg_right (by linarith) h1Cs

end Work.FTS.StrongPersist.L3Rhs
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.PieceSmooth =====
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

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary smoothness of the explicit angular and radial factors

The five summands of `NSsSum` are built out of the following factors, each of which is `C^∞` on
the open quadrant `(0,∞) × (0,π/2)` for elementary reasons:

* the angular factors `s2 θ = sin 2θ` and `sin²θ`;
* the radial factor `FK (F_*) z = α·2z/(1+z)²` (`Work.FTS.Nonlinear.FstarPkg.FK_Fstar`);
* the profile `F_* = α(Γ/c)·2z/(1+z)²` (`Work.FTS.LocData.SmoothQuad_Fstar`);
* the star residual `Φ̃_* = Φ_* - Θ_*(α)` (`Work.FTS.NonlinRows.smoothOpen_PhiTs`),
  and the coefficient fields `ℛ(Φ̃_*)`, `𝒰(Φ̃_*)`, `𝒱(Φ̃_*)` built from it. -/

/-- `s2 θ = sin(2θ)` is `C^∞` on the open quadrant. -/
theorem smoothOpen_s2 :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Work.Construction.s2 θ) := by
  have h : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.sin (2 * θ))
      (Set.Ioo 0 (π / 2)) :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).contDiffOn
  have h2 := Work.FTS.NonlinRows.smoothOpen_theta_only (a := fun θ : ℝ => Real.sin (2 * θ)) h
  simpa only [Work.Construction.s2] using h2

/-- `sin²θ` is `C^∞` on the open quadrant. -/
theorem smoothOpen_sin_sq :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Real.sin θ ^ 2) := by
  refine Work.FTS.NonlinRows.smoothOpen_theta_only (a := fun θ : ℝ => Real.sin θ ^ 2) ?_
  have h : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.sin θ)
      (Set.Ioo 0 (π / 2)) := Real.contDiff_sin.contDiffOn
  simpa only [Pi.pow_apply] using h.pow 2

/-- **`FK (F_*)` is a `C^∞` radial function.**  By `FK_Fstar` it is the explicit function
`z ↦ α·2z/(1+z)²`, which is smooth on `(0,∞)` (indeed on `(-1,∞)`). -/
theorem smoothOpen_FK_Fstar {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.FK (Work.Construction.Fstar α) z) := by
  have hrad : Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => 2 * z / (1 + z) ^ 2) := by
    refine Work.FTS.NonlinRows.smoothOpen_z_only (r := fun z : ℝ => 2 * z / (1 + z) ^ 2) ?_
    exact ContDiffOn.div (contDiffOn_const.mul contDiffOn_id)
      ((contDiffOn_const.add contDiffOn_id).pow 2) (fun z hz => by
        have h1 : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
        positivity)
  refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (f := fun z (_ : ℝ) => α * (2 * z / (1 + z) ^ 2))
    (Work.FTS.NonlinRows.smoothOpen_const_mul α hrad) ?_
  intro z _ _ _ _
  exact (Work.FTS.Nonlinear.FstarPkg.FK_Fstar (α := α) (z := z) hα hα1).symm

/-- **Smoothness of the five `ss` pieces**: for `0 < α ≤ 1` and star data
`StarPkgo2 α Cs Φs`, each of the five summands of
`Work.FTS.StrongPersist.L3Rhs.NSsSum α Φs` is `C^∞` on the open quadrant `Q0` (all finite
orders, i.e. `Work.FTS.EllipticEst.SmoothOpen`), the profile-only pieces `N4ss α`, `N5ss α`
being independent of the star data.

The three star pieces reduce to `StarPkgo.smooth : SmoothOpen Φs` together with the explicit
smoothness of `Theta α (Fstar α)`, `Work.Spaces.c α`, `Work.Spaces.Gam α`, `s2`, `FK (Fstar α)`
and `Work.Spaces.pz`-slices of those.  The two profile pieces are products `a θ * r z` of an
angular-only and a radial-only `C^∞` function on `(0,π/2)` resp. `(0,∞)`; the angular factors are
`D_θ`-iterates of `sin²θ · Γ`, whose smoothness is `row23_smoothOpen_dthU_Gam`, and the radial
factor is `Work.Spaces.hKer`-based (`row23_contDiffOn_hKer`,
`Work.FTS.NonlinRows.smoothOpen_radial`).  This bundle is a tool for the `ℋ³`-norm assembly of
`L3RhsNssBlock` (`HkNorm_add_le`, `HkMem_mono_open`, and the `ContDiffOn ℝ 3` conjunct all need
it), not an estimate. -/
theorem PieceSmooth : ∀ α ∈ Set.Ioc 0 1, ∀ (Cs : ℝ) (Φs : Work.FTS.Galerkin.Fn),
    Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N1ss α Φs) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N2ss α Φs) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N3ss α Φs) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N4ss α) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N5ss α) := by
  intro α hαIoc Cs Φs hs
  obtain ⟨hα, hα1⟩ : 0 < α ∧ α ≤ 1 := hαIoc
  have hsO : Work.FTS.VocabO.StarPkgo α Cs Φs := hs.toStarPkgo
  -- the star residual, the profile, and the angular moment
  have hPhi : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) :=
    Work.FTS.NonlinRows.smoothOpen_PhiTs hα hα1 hsO
  have hF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hFK : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.FK (Work.Construction.Fstar α) z) :=
    smoothOpen_FK_Fstar hα hα1
  -- the three coefficient fields
  have hRop : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) :=
    Work.FTS.NonlinRows.smoothOpen_Rop hPhi
  have hUop : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) :=
    Work.FTS.NonlinRows.smoothOpen_Uop_PhiTs hα hα1 hsO
  have hVop : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) :=
    Work.FTS.NonlinRows.smoothOpen_Vop hPhi
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `N₁^{**} = 2 ℛ(Φ̃_*) F_*`
    refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (f := fun z θ => 2 * (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
        * Work.Construction.Fstar α z θ))
      (Work.FTS.NonlinRows.smoothOpen_const_mul 2
        (Work.FTS.NonlinRows.smoothOpen_mul hRop hF)) ?_
    intro z θ _ _ _
    simp only [Work.FTS.Nonlin.N1ss]
    ring
  · -- `N₂^{**} = -2 𝒰(Φ̃_*) ∂_θF_*`
    refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (f := fun z θ => -2 * (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
        * Work.Spaces.pth (Work.Construction.Fstar α) z θ))
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-2)
        (Work.FTS.NonlinRows.smoothOpen_mul hUop hF.pth)) ?_
    intro z θ _ _ _
    simp only [Work.FTS.Nonlin.N2ss]
    ring
  · -- `N₃^{**} = -2α 𝒱(Φ̃_*) D_zF_*`
    refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (f := fun z θ => (-2 * α) * (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ
        * Work.Spaces.Dz (Work.Construction.Fstar α) z θ))
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-2 * α)
        (Work.FTS.NonlinRows.smoothOpen_mul hVop hF.Dz)) ?_
    intro z θ _ _ _
    simp only [Work.FTS.Nonlin.N3ss]
    ring
  · -- `N₄^{**} = -(1/2) sin 2θ · FK(F_*) · ∂_θF_*`
    refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (f := fun z θ => (-(1 / 2)) * ((Work.Construction.s2 θ
        * Work.Construction.FK (Work.Construction.Fstar α) z)
          * Work.Spaces.pth (Work.Construction.Fstar α) z θ))
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-(1 / 2))
        (Work.FTS.NonlinRows.smoothOpen_mul
          (Work.FTS.NonlinRows.smoothOpen_mul smoothOpen_s2 hFK) hF.pth)) ?_
    intro z θ _ _ _
    simp only [Work.FTS.Nonlin.N4ss]
    ring
  · -- `N₅^{**} = -sin²θ · FK(F_*) · F_*`
    refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (f := fun z θ => (-1) * ((Real.sin θ ^ 2
        * Work.Construction.FK (Work.Construction.Fstar α) z)
          * Work.Construction.Fstar α z θ))
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-1)
        (Work.FTS.NonlinRows.smoothOpen_mul
          (Work.FTS.NonlinRows.smoothOpen_mul smoothOpen_sin_sq hFK) hF)) ?_
    intro z θ _ _ _
    simp only [Work.FTS.Nonlin.N5ss]
    ring

end Work.FTS.StrongPersist.L3Rhs
end
end
