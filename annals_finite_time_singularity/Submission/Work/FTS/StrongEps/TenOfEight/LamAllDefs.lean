/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/TenOfEight/LamAllDefs.lean`

**The mollifier gain at every scale.**  `EpsE4Thr.HkMem_Jeps_gain` proves
`HkMem α k f → HkMem α (k+m) (J_ε f)` only for `ε ≤ 1`: the density
`LamFull ρ ε c M = ε⁻¹^M · e^{4cε} · Λ_raw` dominates every routed kernel derivative
`∂₁^a∂₂^b (Jker ρ ε)` of order `a + b ≤ M` using `ε⁻¹^{a+b} ≤ ε⁻¹^M`, which requires
`1 ≤ ε⁻¹`.

Here we introduce the **scale-free density**

  `LamAll ρ ε c M = max 1 (ε⁻¹^M) · e^{4cε} · Λ_raw = Jker (LamSigAll ρ ε c M) ε`,

whose kernel-side factor `max 1 (ε⁻¹^M)` dominates `ε⁻¹^{a+b}` for *every* `ε > 0`
(for `ε ≤ 1` because `ε⁻¹^{a+b} ≤ ε⁻¹^M`, for `ε ≥ 1` because `ε⁻¹^{a+b} ≤ 1`).  Hence the
pointwise domination `abs_KdK_mul_exp_le_LamAll` holds for every `ε > 0`, and the whole slot /
summation / membership chain of the gain goes through with `LamAll` in place of `LamFull`
(`TenOfEight/zslot_le_gain_all.lean`, `TenOfEight/mslot_le_gain_all.lean`,
`TenOfEight/GainPtAll.lean`, `TenOfEight/GainAll.lean`).

Since `LamAll` is again a rescaled kernel `Jker Λ_sig ε` with `Λ_sig` continuous,
nonnegative and supported in the closed unit ball, all the generic facts about
`Λ = Jker Λ_sig ε` (measurability of the pair integrands, finiteness of the weighted mass,
finiteness of the `p₁`-substitution) are available from `JepsHkMem` / `GainDens` / `HkSqAux`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.RingTheory.Finiteness.Prod
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainDefs
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainDens
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainDens.Jker_lintegral_mul_exp_lt_top
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainDens.Jker_comp_zShift_exp_lt_top
import Submission.Work.FTS.StrongEps.JepsHkMem.aemeasurable_pair_slice
import Submission.Work.FTS.StrongEps.HkSqAux.aemeasurable_shift_pair

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

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## 1. The scale-free density -/

/-- The kernel-side datum of `LamAll`: `max 1 (ε⁻¹^M) · e^{4cε} · Σ_{a,b≤M}|∂₁^a∂₂^b ρ|`. -/
def LamSigAll (ρ : ℝ × ℝ → ℝ) (ε c : ℝ) (M : ℕ) : ℝ × ℝ → ℝ :=
  fun q => max 1 (ε⁻¹ ^ M) * Real.exp (4 * c * ε) * sigKd ρ M q

/-- **The scale-free routed density**: `Jker (LamSigAll ρ ε c M) ε`.  It dominates every routed
kernel derivative of order `≤ M` with its weight-shift factor, for every `ε > 0`. -/
def LamAll (ρ : ℝ × ℝ → ℝ) (ε c : ℝ) (M : ℕ) : ℝ × ℝ → ℝ :=
  Work.FTS.StrongEps.Jker (LamSigAll ρ ε c M) ε

/-- The kernel-side datum of `LamAll` is nonnegative. -/
theorem LamSigAll_nonneg {ρ : ℝ × ℝ → ℝ} (ε c : ℝ) (M : ℕ) (q : ℝ × ℝ) :
    0 ≤ LamSigAll ρ ε c M q :=
  mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (Real.exp_pos _).le)
    (sigKd_nonneg ρ M q)

/-- The kernel-side datum of `LamAll` is continuous. -/
theorem LamSigAll_continuous {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) (ε c : ℝ) (M : ℕ) :
    Continuous (LamSigAll ρ ε c M) :=
  (sigKd_continuous hρ M).const_mul _

/-- The kernel-side datum of `LamAll` is supported in the closed unit ball. -/
theorem LamSigAll_support {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) (ε c : ℝ) (M : ℕ)
    (q : ℝ × ℝ) (hq : LamSigAll ρ ε c M q ≠ 0) : q.1 ^ 2 + q.2 ^ 2 ≤ 1 := by
  have hk : sigKd ρ M q ≠ 0 := by
    intro h
    refine hq ?_
    simp only [LamSigAll, h]
    ring
  exact sigKd_support hρ M hk

/-- `LamAll` as a constant multiple of the raw routed density. -/
theorem LamAll_eq (ρ : ℝ × ℝ → ℝ) (ε c : ℝ) (M : ℕ) (p : ℝ × ℝ) :
    LamAll ρ ε c M p = max 1 (ε⁻¹ ^ M) * Real.exp (4 * c * ε) * LamK ρ ε M p := by
  simp only [LamAll, LamSigAll, LamK, Work.FTS.StrongEps.Jker]
  ring

/-- `LamAll` is nonnegative. -/
theorem LamAll_nonneg {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {c : ℝ} (M : ℕ) (p : ℝ × ℝ) : 0 ≤ LamAll ρ ε c M p := by
  rw [LamAll_eq]
  exact mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (Real.exp_pos _).le)
    (LamK_nonneg hρ hε M p)

/-- `LamAll` is continuous. -/
theorem LamAll_continuous {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) (ε c : ℝ) (M : ℕ) :
    Continuous (LamAll ρ ε c M) := by
  simp only [LamAll, Work.FTS.StrongEps.Jker]
  exact continuous_const.mul (continuous_const.mul
    ((sigKd_continuous hρ M).comp (continuous_const_smul ε⁻¹)))

/-- The support of `LamAll` sits in the closed ball of radius `ε`. -/
theorem LamAll_support {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {ε c : ℝ} (M : ℕ)
    {p : ℝ × ℝ} (hp : LamAll ρ ε c M p ≠ 0) : p.1 ^ 2 + p.2 ^ 2 ≤ ε ^ 2 := by
  rw [LamAll_eq] at hp
  refine LamK_support hρ M fun h => hp ?_
  rw [h, mul_zero]

/-! ## 2. The pointwise domination at every scale -/

/-- The key elementary comparison: `ε⁻¹^{a+b} ≤ max 1 (ε⁻¹^M)` for `a + b ≤ M` and `ε > 0`. -/
theorem inv_pow_le_max {ε : ℝ} (hε : 0 < ε) {M a b : ℕ} (hab : a + b ≤ M) :
    ε⁻¹ ^ (a + b) ≤ max 1 (ε⁻¹ ^ M) := by
  by_cases h1 : ε ≤ 1
  · exact le_trans (pow_le_pow_right₀ ((one_le_inv₀ hε).mpr h1) hab) (le_max_right _ _)
  · have hlt : 1 < ε := not_le.mp h1
    have hinv : ε⁻¹ ≤ 1 := by
      have h2 : (1 : ℝ) ≤ ε := le_of_lt hlt
      have h3 : ε⁻¹ ≤ (1 : ℝ)⁻¹ := (inv_le_inv₀ hε (by norm_num)).mpr h2
      simpa using h3
    exact le_trans (pow_le_one₀ (inv_nonneg.mpr hε.le) hinv) (le_max_left _ _)

/-- **The pointwise domination of every routed kernel derivative by `LamAll`**, for every
`ε > 0`: this is `abs_KdK_mul_exp_le_LamFull` with the scale-free exponent
`max 1 (ε⁻¹^M)` in place of `ε⁻¹^M`. -/
theorem abs_KdK_mul_exp_le_LamAll {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {c : ℝ} (hc : 0 ≤ c) {M a b : ℕ} (hab : a + b ≤ M) (p : ℝ × ℝ) :
    |KdK ρ ε a b p| * Real.exp (2 * c * (|p.1| + |p.2|)) ≤ LamAll ρ ε c M p := by
  have ha : a ≤ M := by omega
  have hb : b ≤ M := by omega
  rcases eq_or_ne (KdK ρ ε a b p) 0 with hzero | hne
  · rw [hzero, abs_zero, zero_mul]
    exact LamAll_nonneg hρ hε M p
  · have hscale := Kd_Jker_scale hρ ε a b p
    have hεinv : ε⁻¹ ^ (a + b) ≠ 0 := pow_ne_zero _ (inv_ne_zero hε.ne')
    have hJne : Work.FTS.StrongEps.Jker (Kdr ρ a b) ε p ≠ 0 := by
      intro h
      exact hne (by rw [hscale, h, mul_zero])
    have hkey : Kdr ρ a b (ε⁻¹ • p) ≠ 0 := by
      intro h
      refine hJne ?_
      simp only [Work.FTS.StrongEps.Jker, h, mul_zero]
    have hball := Kdr_support hρ a b (ε⁻¹ • p) hkey
    rw [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, smul_eq_mul] at hball
    have hsq1 : (ε⁻¹ * p.1) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (ε⁻¹ * p.2)]
    have hsq2 : (ε⁻¹ * p.2) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (ε⁻¹ * p.1)]
    have hb1 : ε⁻¹ * |p.1| ≤ 1 := by
      have h : |ε⁻¹ * p.1| ≤ 1 := abs_le.mpr ⟨by nlinarith [hsq1], by nlinarith [hsq1]⟩
      rwa [abs_mul, abs_of_nonneg (inv_nonneg.mpr hε.le)] at h
    have hb2 : ε⁻¹ * |p.2| ≤ 1 := by
      have h : |ε⁻¹ * p.2| ≤ 1 := abs_le.mpr ⟨by nlinarith [hsq2], by nlinarith [hsq2]⟩
      rwa [abs_mul, abs_of_nonneg (inv_nonneg.mpr hε.le)] at h
    have hmul1 : ε * (ε⁻¹ * |p.1|) = |p.1| := by
      rw [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul]
    have hmul2 : ε * (ε⁻¹ * |p.2|) = |p.2| := by
      rw [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul]
    have hp1 : |p.1| ≤ ε := by
      calc |p.1| = ε * (ε⁻¹ * |p.1|) := hmul1.symm
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hb1 hε.le
        _ = ε := mul_one ε
    have hp2 : |p.2| ≤ ε := by
      calc |p.2| = ε * (ε⁻¹ * |p.2|) := hmul2.symm
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hb2 hε.le
        _ = ε := mul_one ε
    have hexp : Real.exp (2 * c * (|p.1| + |p.2|)) ≤ Real.exp (4 * c * ε) := by
      rw [Real.exp_le_exp]
      nlinarith [hc]
    have habs : |Work.FTS.StrongEps.Jker (Kdr ρ a b) ε p|
        = Work.FTS.StrongEps.Jker (fun q => |Kdr ρ a b q|) ε p := by
      simp only [Work.FTS.StrongEps.Jker, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε⁻¹ ^ 2)]
    have hpt : ∀ q : ℝ × ℝ, |Kdr ρ a b q| ≤ sigKd ρ M q := by
      intro q
      have h1 : |Kdr ρ a b q| ≤ ∑ b' ∈ Finset.range (M + 1), |Kdr ρ a b' q| :=
        Finset.single_le_sum (f := fun b' => |Kdr ρ a b' q|) (fun _ _ => abs_nonneg _)
          (show b ∈ Finset.range (M + 1) from Finset.mem_range.mpr (by omega))
      have h2 : (∑ b' ∈ Finset.range (M + 1), |Kdr ρ a b' q|)
          ≤ ∑ a' ∈ Finset.range (M + 1), ∑ b' ∈ Finset.range (M + 1), |Kdr ρ a' b' q| :=
        Finset.single_le_sum (f := fun a' => ∑ b' ∈ Finset.range (M + 1), |Kdr ρ a' b' q|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (show a ∈ Finset.range (M + 1) from Finset.mem_range.mpr (by omega))
      exact h1.trans h2
    have hmono : Work.FTS.StrongEps.Jker (fun q => |Kdr ρ a b q|) ε p ≤ LamK ρ ε M p := by
      rw [LamK]
      exact mul_le_mul_of_nonneg_left (hpt (ε⁻¹ • p)) (by positivity)
    have hpow : ε⁻¹ ^ (a + b) ≤ max 1 (ε⁻¹ ^ M) := inv_pow_le_max hε hab
    have hker : |KdK ρ ε a b p| ≤ max 1 (ε⁻¹ ^ M) * LamK ρ ε M p := by
      rw [hscale, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε⁻¹ ^ (a + b)), habs]
      exact mul_le_mul hpow hmono (by
        simp only [Work.FTS.StrongEps.Jker]
        positivity) (by positivity)
    calc |KdK ρ ε a b p| * Real.exp (2 * c * (|p.1| + |p.2|))
        ≤ |KdK ρ ε a b p| * Real.exp (4 * c * ε) :=
          mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
      _ ≤ (max 1 (ε⁻¹ ^ M) * LamK ρ ε M p) * Real.exp (4 * c * ε) :=
          mul_le_mul_of_nonneg_right hker (Real.exp_pos _).le
      _ = LamAll ρ ε c M p := by
          rw [LamAll_eq]; ring

/-! ## 3. Measurability of the pair integrands against `LamAll` -/

/-- **Slice measurability** of `LamAll` against the shifted level-`k` integrand (fixed `z > 0`). -/
theorem LamAll_aemeasurable_slice {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {α : ℝ} {k : ℕ}
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    {ε c : ℝ} (M : ℕ) {z : ℝ} (hz : 0 < z) :
    AEMeasurable (fun q : ℝ × (ℝ × ℝ) =>
        ENNReal.ofReal (LamAll ρ ε c M q.2)
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
              (Work.FTS.StrongEps.zShift z q.2.1) (Work.FTS.StrongEps.thShift q.1 q.2.2)))
      ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod MeasureTheory.volume) := by
  have hH : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k f q.1 q.2)
      Work.FTS.StrongEps.Quad := HkSqAux.continuousOn_HkIntegrand_Quad α k hf
  have hbase := JepsHkMem.aemeasurable_pair_slice (H := fun z' θ' =>
      Work.Spaces.HkIntegrand α k f z' θ') hH (LamSigAll_continuous hρ ε c M) (ε := ε) (c := 0)
    (z := z) hz
  refine hbase.congr (Eventually.of_forall fun q => ?_)
  have hLam : LamAll ρ ε c M q.2 = Work.FTS.StrongEps.Jker (LamSigAll ρ ε c M) ε q.2 := rfl
  simp only [hLam, mul_zero, zero_mul, Real.exp_zero, ENNReal.ofReal_one, mul_one]

/-- **Joint measurability** of `LamAll` against the shifted level-`k` integrand. -/
theorem LamAll_aemeasurable_joint {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {α : ℝ} {k : ℕ}
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    {ε c : ℝ} (M : ℕ) :
    AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
        ENNReal.ofReal (LamAll ρ ε c M q.2)
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
              (Work.FTS.StrongEps.zShift q.1.1 q.2.1) (Work.FTS.StrongEps.thShift q.1.2 q.2.2)))
      (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume) := by
  have hH : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k f q.1 q.2)
      Work.FTS.StrongEps.Quad := HkSqAux.continuousOn_HkIntegrand_Quad α k hf
  have hbase := HkSqAux.aemeasurable_shift_pair (G := fun z' θ' =>
      Work.Spaces.HkIntegrand α k f z' θ') hH (LamSigAll ρ ε c M)
    (LamSigAll_continuous hρ ε c M) ε
  refine hbase.congr (Eventually.of_forall fun q => ?_)
  have hLam : LamAll ρ ε c M q.2 = Work.FTS.StrongEps.Jker (LamSigAll ρ ε c M) ε q.2 := rfl
  simp only [hLam]

/-! ## 4. Finiteness of the weighted mass at every scale

The membered `Jker_moment_le` / `Jker_lintegral_mul_exp_lt_top` prove the finiteness of the
`δ`-moment of `Jker σ ε` only for `ε ≤ 1`, through the *comparison* `γ ε ≤ γ`.  Only the
finiteness is used by the gain, and that holds at every scale: after the substitution
`p ↦ ε⁻¹ p` the moment is `∫ t, σ t · exp (δ ε (|t₁| + |t₂|))`, which is finite by compact
support of `σ`. -/

/-- A continuous function supported in the closed unit ball, multiplied by
`exp (c (|t₁| + |t₂|))`, is integrable. -/
private theorem integrable_sigma_exp (σ : ℝ × ℝ → ℝ) (hσc : Continuous σ)
    (hσsupp : ∀ p : ℝ × ℝ, σ p ≠ 0 → p.1 ^ 2 + p.2 ^ 2 ≤ 1) (c : ℝ) :
    MeasureTheory.Integrable (fun t : ℝ × ℝ => σ t * Real.exp (c * (|t.1| + |t.2|))) := by
  have hexp : Continuous fun t : ℝ × ℝ => Real.exp (c * (|t.1| + |t.2|)) := by fun_prop
  have hsupp : ∀ t : ℝ × ℝ, t ∉ Metric.closedBall (0 : ℝ × ℝ) 1 →
      σ t * Real.exp (c * (|t.1| + |t.2|)) = 0 := by
    intro t ht
    have hσt : σ t = 0 := by
      by_contra hne
      refine ht ?_
      have h := hσsupp t hne
      have h1 : |t.1| ≤ 1 := by
        have h2 : t.1 ^ 2 ≤ (1 : ℝ) ^ 2 := by nlinarith [h, sq_nonneg t.2]
        rwa [sq_le_sq, abs_one] at h2
      have h2 : |t.2| ≤ 1 := by
        have h3 : t.2 ^ 2 ≤ (1 : ℝ) ^ 2 := by nlinarith [h, sq_nonneg t.1]
        rwa [sq_le_sq, abs_one] at h3
      rw [Metric.mem_closedBall, dist_zero_right]
      exact max_le h1 h2
    rw [hσt, zero_mul]
  have hon : MeasureTheory.IntegrableOn
      (fun t : ℝ × ℝ => σ t * Real.exp (c * (|t.1| + |t.2|)))
      (Metric.closedBall (0 : ℝ × ℝ) 1) :=
    ((hσc.continuousOn).mul hexp.continuousOn).integrableOn_compact
      (isCompact_closedBall (0 : ℝ × ℝ) 1)
  exact hon.integrable_of_forall_notMem_eq_zero hsupp

/-- **Finiteness of the `δ`-moment of `Jker σ ε` at every scale `ε > 0`.**  This is
`GainDens.Jker_lintegral_mul_exp_lt_top` without the hypothesis `ε ≤ 1`. -/
theorem Jker_lintegral_mul_exp_lt_top_pos {σ : ℝ × ℝ → ℝ} (hσ0 : ∀ q : ℝ × ℝ, 0 ≤ σ q)
    (hσc : Continuous σ) (hσs : ∀ q : ℝ × ℝ, σ q ≠ 0 → q.1 ^ 2 + q.2 ^ 2 ≤ 1)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) :
    (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.Jker σ ε p
        * Real.exp (δ * (|p.1| + |p.2|)))) < ⊤ := by
  have hker_nonneg : ∀ p : ℝ × ℝ, 0 ≤ Work.FTS.StrongEps.Jker σ ε p := by
    intro p
    have h := hσ0 (ε⁻¹ • p)
    rw [Work.FTS.StrongEps.Jker]
    nlinarith [sq_nonneg (ε⁻¹ : ℝ)]
  have hnonneg : ∀ p : ℝ × ℝ,
      0 ≤ Work.FTS.StrongEps.Jker σ ε p * Real.exp (δ * (|p.1| + |p.2|)) :=
    fun p => mul_nonneg (hker_nonneg p) (Real.exp_nonneg _)
  have hInt : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.FTS.StrongEps.Jker σ ε p * Real.exp (δ * (|p.1| + |p.2|))) := by
    have hG : MeasureTheory.Integrable
        (fun t : ℝ × ℝ => σ t * Real.exp (δ * ε * (|t.1| + |t.2|))) :=
      integrable_sigma_exp σ hσc hσs (δ * ε)
    have harg : ∀ a b : ℝ, δ * ε * (ε⁻¹ * a + ε⁻¹ * b) = δ * (a + b) := by
      intro a b
      have hne : ε ≠ 0 := hε.ne'
      field_simp
    have hpoint : ∀ p : ℝ × ℝ, σ (ε⁻¹ • p) * Real.exp (δ * (|p.1| + |p.2|))
        = (fun t : ℝ × ℝ => σ t * Real.exp (δ * ε * (|t.1| + |t.2|))) (ε⁻¹ • p) := by
      intro p
      have h : δ * (|p.1| + |p.2|) = δ * ε * (|(ε⁻¹ • p).1| + |(ε⁻¹ • p).2|) := by
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, abs_mul,
          abs_of_nonneg (inv_nonneg.mpr hε.le)]
        exact (harg |p.1| |p.2|).symm
      rw [h]
    have hpt : ∀ p : ℝ × ℝ, Work.FTS.StrongEps.Jker σ ε p * Real.exp (δ * (|p.1| + |p.2|))
        = ε⁻¹ ^ 2 * (σ (ε⁻¹ • p) * Real.exp (δ * (|p.1| + |p.2|))) := by
      intro p
      simp only [Work.FTS.StrongEps.Jker]
      ring
    have h1 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (fun t : ℝ × ℝ => σ t * Real.exp (δ * ε * (|t.1| + |t.2|))) (ε⁻¹ • p)) :=
      hG.comp_smul (inv_ne_zero hε.ne')
    have h2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => ε⁻¹ ^ 2 *
        ((fun t : ℝ × ℝ => σ t * Real.exp (δ * ε * (|t.1| + |t.2|))) (ε⁻¹ • p))) :=
      h1.const_mul _
    have h3 : MeasureTheory.Integrable (fun p : ℝ × ℝ => ε⁻¹ ^ 2 *
        (σ (ε⁻¹ • p) * Real.exp (δ * (|p.1| + |p.2|)))) :=
      h2.congr (Filter.Eventually.of_forall fun p => by
        show ε⁻¹ ^ 2 * ((fun t : ℝ × ℝ =>
            σ t * Real.exp (δ * ε * (|t.1| + |t.2|))) (ε⁻¹ • p))
          = ε⁻¹ ^ 2 * (σ (ε⁻¹ • p) * Real.exp (δ * (|p.1| + |p.2|)))
        rw [hpoint p])
    exact h3.congr (Filter.Eventually.of_forall fun p => (hpt p).symm)
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
    (Filter.Eventually.of_forall hnonneg)]
  exact ENNReal.ofReal_lt_top

/-- **Finiteness of the weighted mass of `LamAll`**, at every scale: the membership step
`GainMem.HkMem_Jeps_of_pointwise_gain` consumes this as `hΛmass`. -/
theorem LamAll_mass_lt_top {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {ε c : ℝ} (hε : 0 < ε)
    (hc : 0 ≤ c) (M : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (LamAll ρ ε c M p
        * Real.exp (δ * (|p.1| + |p.2|)))) < ⊤ := by
  have hC0 : (0 : ℝ) ≤ max 1 (ε⁻¹ ^ M) * Real.exp (4 * c * ε) :=
    mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (Real.exp_pos _).le
  have hpt : ∀ p : ℝ × ℝ, LamAll ρ ε c M p * Real.exp (δ * (|p.1| + |p.2|))
      = (max 1 (ε⁻¹ ^ M) * Real.exp (4 * c * ε))
        * (LamK ρ ε M p * Real.exp (δ * (|p.1| + |p.2|))) := by
    intro p
    rw [LamAll_eq]
    ring
  have hkey : ∀ p : ℝ × ℝ, ENNReal.ofReal (LamAll ρ ε c M p
        * Real.exp (δ * (|p.1| + |p.2|)))
      = ENNReal.ofReal (max 1 (ε⁻¹ ^ M) * Real.exp (4 * c * ε))
        * ENNReal.ofReal (LamK ρ ε M p * Real.exp (δ * (|p.1| + |p.2|))) := by
    intro p
    rw [hpt p]
    exact ENNReal.ofReal_mul hC0
  calc (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (LamAll ρ ε c M p
        * Real.exp (δ * (|p.1| + |p.2|))))
      = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (max 1 (ε⁻¹ ^ M) * Real.exp (4 * c * ε))
          * ENNReal.ofReal (LamK ρ ε M p * Real.exp (δ * (|p.1| + |p.2|))) :=
        lintegral_congr hkey
    _ = ENNReal.ofReal (max 1 (ε⁻¹ ^ M) * Real.exp (4 * c * ε))
          * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (LamK ρ ε M p
              * Real.exp (δ * (|p.1| + |p.2|))) := by
        rw [← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (Jker_lintegral_mul_exp_lt_top_pos (sigKd_nonneg ρ M) (sigKd_continuous hρ M)
          (fun q hq => sigKd_support hρ M hq) hε hδ)

end Work.FTS.StrongEps.TenOfEight
