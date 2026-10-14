import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.RingTheory.Finiteness.Prod
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainDefs
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainDens
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2Sup.FinalAux
import Submission.Work.FTS.TransportS.T2Sup.smainBound
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Row26 =====
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

set_option linter.unusedVariables false

/-! ## The sharp `D_θ`-iterate bound for the angular factor `sin²θ·Γ(θ)` -/

/-- **The `D_θ`-iterates of `sin²θ·Γ(θ)` are bounded by `B·Γ(θ)·(α + sin 2θ)`.**

This is the `Iθ`-version (the closed angular interval) of the sharp iterate bound
`RNP26.psiB_Lop_bound`, which is stated on the open interval with the majorant
`Γ·(sin²(2θ) + α)`; since `0 ≤ sin 2θ ≤ 1` on `Iθ`, that majorant is dominated by
`Γ·(α + sin 2θ)`.  At the two endpoints both sides vanish: `Γ(0) = Γ(π/2) = 0`
(`Gam_zero_left`/`Gam_zero_right`) and `D_θ^i f = sin(2θ)·∂_θ(D_θ^{i-1}f) = 0` for `i ≥ 1`. -/
theorem Row26Ang :
    ∃ B : ℝ, 0 < B ∧ ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ i : ℕ, 1 ≤ i → i ≤ 4 →
      ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') 0 θ|
          ≤ B * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) := by
  obtain ⟨D, hDpos, hD⟩ := Work.FTS.Nonlinear.Pieces.RNP26.psiB_Lop_bound
  refine ⟨D, hDpos, ?_⟩
  intro α hα hα1 i hi1 hi4 θ hθ
  have hΓnn : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  -- split the two endpoints off
  rcases eq_or_lt_of_le hθ.1 with h0 | h0pos
  · -- `θ = 0`
    have hθ0 : θ = 0 := h0.symm
    subst hθ0
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hi1)
    have hz : Work.Spaces.DthIter (j + 1)
        (fun _ (θ' : ℝ) => Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') 0 0 = 0 := by
      rw [Work.Spaces.DthIter_succ]
      simp [Work.Spaces.Dth]
    rw [hz, abs_zero, Work.Spaces.Gam_zero_left α (ne_of_gt hα)]
    simp
  · rcases eq_or_lt_of_le hθ.2 with hpi | hpilt
    · -- `θ = π/2`
      subst hpi
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hi1)
      have hz : Work.Spaces.DthIter (j + 1)
          (fun _ (θ' : ℝ) => Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') 0 (Real.pi / 2) = 0 := by
        rw [Work.Spaces.DthIter_succ]
        simp only [Work.Spaces.Dth]
        rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi, zero_mul]
      rw [hz, abs_zero, Work.Spaces.Gam_zero_right α (ne_of_gt hα),
        show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      simp
    · -- interior: the `Lop`-iterate bound of `psiB_Lop_bound`
      have hioo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨h0pos, hpilt⟩
      have hL : Work.Spaces.DthIter i
          (fun _ (θ' : ℝ) => Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') 0 θ
          = Work.Spaces.Lop^[i] (fun θ' : ℝ => Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') θ := by
        rw [Work.Spaces.DthIter_eq_iterate_Lop]
      rw [hL]
      have h := hD α hα hα1 i hi1 hi4 θ hioo
      have hs2 : Real.sin (2 * θ) ^ 2 ≤ Real.sin (2 * θ) := by
        have hs0 : 0 ≤ Real.sin (2 * θ) :=
          (Real.sin_pos_of_pos_of_lt_pi (by linarith [h0pos])
            (by linarith [hpilt, Real.pi_pos])).le
        nlinarith [Real.sin_le_one (2 * θ)]
      calc |Work.Spaces.Lop^[i] (fun θ' : ℝ => Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') θ|
          ≤ D * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α) := h
        _ ≤ D * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) := by
            refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = D * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) := by ring

/-! ## The row -/


end Work.FTS.Nonlinear.Open
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.TenOfEight.LamAllDefs =====
section

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
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.Wgt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_mono)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. Measure-theoretic bookkeeping -/

theorem restrict_Iθ_eq_Ioo :
    volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
  Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo

theorem restrict_Iz_eq_Ioi :
    volume.restrict Work.Spaces.Iz = volume.restrict (Set.Ioi (0 : ℝ)) := by
  have h : Set.Ioi (0 : ℝ) =ᵐ[volume] Set.Ici (0 : ℝ) := Ioi_ae_eq_Ici
  simpa [Work.Spaces.Iz] using (MeasureTheory.Measure.restrict_congr_set h).symm

theorem ae_Iθ_mem_Ioo :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  rw [restrict_Iθ_eq_Ioo]
  exact ae_restrict_mem measurableSet_Ioo

theorem integral_Iθ_mono_ae {f g : ℝ → ℝ}
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), f θ ≤ g θ)
    (h0 : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), 0 ≤ f θ) (hg : IntegrableOn g Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, f θ) ≤ ∫ θ in Work.Spaces.Iθ, g θ := by
  refine integral_mono_of_nonneg ?_ hg ?_
  · rw [restrict_Iθ_eq_Ioo]; exact ae_restrict_of_forall_mem measurableSet_Ioo h0
  · rw [restrict_Iθ_eq_Ioo]; exact ae_restrict_of_forall_mem measurableSet_Ioo h

theorem integral_Iz_mono_ae {f g : ℝ → ℝ}
    (h : ∀ z ∈ Set.Ioi (0 : ℝ), f z ≤ g z)
    (h0 : ∀ z ∈ Set.Ioi (0 : ℝ), 0 ≤ f z) (hg : IntegrableOn g Work.Spaces.Iz) :
    (∫ z in Work.Spaces.Iz, f z) ≤ ∫ z in Work.Spaces.Iz, g z := by
  refine integral_mono_of_nonneg ?_ hg ?_
  · rw [restrict_Iz_eq_Ioi]; exact ae_restrict_of_forall_mem measurableSet_Ioi h0
  · rw [restrict_Iz_eq_Ioi]; exact ae_restrict_of_forall_mem measurableSet_Ioi h

theorem one_le_alpha_rpow_neg_half {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (1 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := by
  rw [Real.rpow_neg hα.le, ← Real.sqrt_eq_rpow]
  refine (one_le_inv₀ (Real.sqrt_pos.mpr hα)).mpr ?_
  calc Real.sqrt α ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hα1
    _ = 1 := Real.sqrt_one

theorem gam_pos' {α : ℝ} (hα : 0 < α) : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα

/-- Continuity of the (uncurried) datum on the open quadrant. -/
theorem smoothOpen_continuousOn_Q0 {F : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen F) :
    ContinuousOn (Function.uncurry F) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
  h.continuousOn

/-! ## 2. Comparisons of canonical weights -/

/-- `canonW q ≤ canonW (gam α)` on the open interval for `0 ≤ q ≤ gam α`. -/
theorem canonW_le_gam {α q : ℝ} (hα : 0 < α) (hq0 : 0 ≤ q) (hqγ : q ≤ Work.Spaces.gam α) :
    ∀ z θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (π / 2) →
      canonW q z θ ≤ canonW (Work.Spaces.gam α) z θ := by
  intro z θ hθ
  rcases eq_or_lt_of_le hq0 with hq | hq
  · rw [← hq]
    have h1 : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
      Work.FTS.TransportS.one_le_rpow_neg (gam_pos' hα).le hθ
    calc canonW 0 z θ = (Work.Spaces.w z) ^ 2 := by
            simp only [canonW, neg_zero, Real.rpow_zero, mul_one]
      _ = (Work.Spaces.w z) ^ 2 * 1 := by ring
      _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = canonW (Work.Spaces.gam α) z θ := by simp only [canonW]
  · exact canonW_mono hq hqγ (Set.Ioo_subset_Icc_self hθ)

/-- `canonW q ≤ canonW eta` on the open interval for `0 ≤ q ≤ eta`. -/
theorem canonW_le_eta {q : ℝ} (hq0 : 0 ≤ q) (hqη : q ≤ Work.Spaces.eta) :
    ∀ z θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (π / 2) → canonW q z θ ≤ canonW Work.Spaces.eta z θ := by
  intro z θ hθ
  rcases eq_or_lt_of_le hq0 with hq | hq
  · rw [← hq]
    have h1 : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      Work.FTS.TransportS.one_le_rpow_neg Work.Spaces.eta_nonneg hθ
    calc canonW 0 z θ = (Work.Spaces.w z) ^ 2 := by
            simp only [canonW, neg_zero, Real.rpow_zero, mul_one]
      _ = (Work.Spaces.w z) ^ 2 * 1 := by ring
      _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = canonW Work.Spaces.eta z θ := by simp only [canonW]
  · exact canonW_mono hq hqη (Set.Ioo_subset_Icc_self hθ)

/-! ## 3. Pointwise slot dominations -/

/-- A mixed slot of order `≤ 6` is dominated by the level-`6` integrand, weighted by
`canonW q` with `0 ≤ q ≤ γ`, on the whole closed angular interval. -/
theorem canonW_mul_mixed_le6 {α : ℝ} (hα : 0 < α) {q : ℝ} (hq0 : 0 ≤ q)
    (hqγ : q ≤ Work.Spaces.gam α) {g : ℝ → ℝ → ℝ} {j' i' : ℕ}
    (hi : 1 ≤ i') (hij : i' + j' ≤ 6) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    canonW q z θ * (Work.Spaces.mixed j' i' g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
  rcases eq_or_lt_of_le hθ.1 with h0 | h0pos
  · have hw : canonW q z 0 * (Work.Spaces.mixed j' i' g z 0) ^ 2 = 0 := by
      rw [Work.Spaces.mixed_eq_zero_of_sin_eq_zero (H := g) (z := z) (θ := 0) (by simp) hi]
      ring
    rw [← h0, hw]
    exact Work.Spaces.HkIntegrand_nonneg α 6 g z 0
  · rcases eq_or_lt_of_le hθ.2 with h2 | h2lt
    · have hw : canonW q z (π / 2) * (Work.Spaces.mixed j' i' g z (π / 2)) ^ 2 = 0 := by
        rw [Work.Spaces.mixed_eq_zero_of_sin_eq_zero (H := g) (z := z) (θ := π / 2)
          (by rw [show (2 : ℝ) * (π / 2) = π by ring, Real.sin_pi]) hi]
        ring
      rw [h2, hw]
      exact Work.Spaces.HkIntegrand_nonneg α 6 g z (π / 2)
    · exact le_trans (mul_le_mul_of_nonneg_right
        (canonW_le_gam hα hq0 hqγ z θ ⟨h0pos, h2lt⟩) (sq_nonneg _))
        (Work.FTS.StrongPersist.N6Trans.T1SixAux.canonW_mul_mixed_le6 α g
          (gam_pos' hα) le_rfl hθ j' i' hi hij)

/-- A mixed slot of order `≤ 4` is dominated by the level-`4` integrand, weighted by
`canonW q` with `0 ≤ q ≤ γ`, on the whole closed angular interval. -/
theorem canonW_mul_mixed_le4 {α : ℝ} (hα : 0 < α) {q : ℝ} (hq0 : 0 ≤ q)
    (hqγ : q ≤ Work.Spaces.gam α) {g : ℝ → ℝ → ℝ} {j' i' : ℕ}
    (hi : 1 ≤ i') (hij : i' + j' ≤ 4) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    canonW q z θ * (Work.Spaces.mixed j' i' g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  rcases eq_or_lt_of_le hθ.1 with h0 | h0pos
  · have hw : canonW q z 0 * (Work.Spaces.mixed j' i' g z 0) ^ 2 = 0 := by
      rw [Work.Spaces.mixed_eq_zero_of_sin_eq_zero (H := g) (z := z) (θ := 0) (by simp) hi]
      ring
    rw [← h0, hw]
    exact Work.Spaces.HkIntegrand_nonneg α 4 g z 0
  · rcases eq_or_lt_of_le hθ.2 with h2 | h2lt
    · have hw : canonW q z (π / 2) * (Work.Spaces.mixed j' i' g z (π / 2)) ^ 2 = 0 := by
        rw [Work.Spaces.mixed_eq_zero_of_sin_eq_zero (H := g) (z := z) (θ := π / 2)
          (by rw [show (2 : ℝ) * (π / 2) = π by ring, Real.sin_pi]) hi]
        ring
      rw [h2, hw]
      exact Work.Spaces.HkIntegrand_nonneg α 4 g z (π / 2)
    · rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hz0
      · rw [← hz0, Work.FTS.TransportS.SlotT2.canonW_zero_z, zero_mul]
        exact Work.Spaces.HkIntegrand_nonneg α 4 g 0 θ
      · exact le_trans (mul_le_mul_of_nonneg_right
          (canonW_le_gam hα hq0 hqγ z θ ⟨h0pos, h2lt⟩) (sq_nonneg _))
          (Work.FTS.TransportS.SlotT2.canonW_mul_mixed_le α g (gam_pos' hα)
            le_rfl hz0 hθ j' i' hi hij)

/-- A pure `D_z`-slot of order `≤ 6` is dominated by the level-`6` integrand on the open
angular interval, for `0 < q ≤ η`. -/
theorem canonW_mul_z_pos_le6 {α q : ℝ} (hq0 : 0 < q) (hqη : q ≤ Work.Spaces.eta)
    {g : ℝ → ℝ → ℝ} {j' : ℕ} (hj : j' ≤ 6) {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    canonW q z θ * (Work.Spaces.DzIter j' g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
  le_trans (mul_le_mul_of_nonneg_right (canonW_le_eta hq0.le hqη z θ hθ) (sq_nonneg _))
    (Work.FTS.StrongPersist.N6Trans.T1SixAux.canonW_mul_z_le6 α g
      (q := Work.Spaces.eta) Work.Spaces.eta_pos le_rfl (Set.Ioo_subset_Icc_self hθ) j' hj)

/-- The pure `D_z`-slot bound at the exponent `q = 0`. -/
theorem canonW_mul_z_zero_le6 {α : ℝ} {g : ℝ → ℝ → ℝ} {j' : ℕ} (hj : j' ≤ 6)
    {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    canonW 0 z θ * (Work.Spaces.DzIter j' g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
  le_trans (mul_le_mul_of_nonneg_right
      (canonW_le_eta le_rfl Work.Spaces.eta_nonneg z θ hθ) (sq_nonneg _))
    (Work.FTS.StrongPersist.N6Trans.T1SixAux.canonW_mul_z_le6 α g
      (q := Work.Spaces.eta) Work.Spaces.eta_pos le_rfl (Set.Ioo_subset_Icc_self hθ) j' hj)

/-- A pure `D_z`-slot of order `≤ 6` is dominated by the level-`6` integrand on the open
angular interval, for `0 ≤ q ≤ η`. -/
theorem canonW_mul_z_le6 {α q : ℝ} (hq0 : 0 ≤ q) (hqη : q ≤ Work.Spaces.eta)
    {g : ℝ → ℝ → ℝ} {j' : ℕ} (hj : j' ≤ 6) {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    canonW q z θ * (Work.Spaces.DzIter j' g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
  rcases eq_or_lt_of_le hq0 with hq | hq
  · rw [← hq]; exact canonW_mul_z_zero_le6 hj hθ
  · exact canonW_mul_z_pos_le6 hq hqη hj hθ


/-! ## 4. Continuity of the weighted slot integrands -/

theorem continuousOn_canonW_slot_mixed {q : ℝ} {g : ℝ → ℝ → ℝ}
    (hgsm : Work.FTS.EllipticEst.SmoothOpen g) {j' i' : ℕ} :
    ContinuousOn (fun p : ℝ × ℝ => canonW q p.1 p.2
        * (Work.Spaces.mixed j' i' g p.1 p.2) ^ 2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
  (Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul
    ((hgsm.mixed j' i').continuousOn.pow 2)

theorem continuousOn_canonW_slot_z {q : ℝ} {g : ℝ → ℝ → ℝ}
    (hgsm : Work.FTS.EllipticEst.SmoothOpen g) {j' : ℕ} :
    ContinuousOn (fun p : ℝ × ℝ => canonW q p.1 p.2
        * (Work.Spaces.DzIter j' g p.1 p.2) ^ 2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
  (Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul
    ((hgsm.DzIter j').continuousOn.pow 2)

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.Hon.SdelGamHon =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.Hon

set_option autoImplicit false

open Work.FTS.TransportS
open Work.FTS.TransportS.SlotT2
open Work.FTS.TransportS.T2Sup

/-- The `Sdel` summand at the exponent `γ` in the honest class (the delicate case). -/
theorem sdel_integral_le_of_gam_hon {α Cd : ℝ} {f g : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hsf : HonF α f)
    (hSmoG : Work.FTS.EllipticEst.SmoothOpen g) (hHk4g : Work.Spaces.HkMem α 4 g)
    (hDelb : ∀ q : ℝ, 0 ≤ q → q ≤ Work.Spaces.gam α →
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
            * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
            * |Work.Spaces.mixed 3 1 g z θ|)
        ≤ Cd * α ^ (-(1 / 2 : ℝ))
            * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
            * Work.Spaces.HkSq α 4 g) :
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        canonW (Work.Spaces.gam α) z θ * Sdel f g 1 3 z θ
          * Work.Spaces.mixed 3 1 g z θ|
      ≤ Cd * α ^ (-(1 / 2 : ℝ))
          * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
          * Work.Spaces.HkSq α 4 g := by
  have hγpos : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα
  have hgam : 0 ≤ Work.Spaces.gam α := le_of_lt hγpos
  have hHd_int : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
            * |Work.Spaces.mixed 3 1 g z θ|) Work.Spaces.Iz :=
    delicateMargInt_hon α (Work.Spaces.gam α) f g hα hα1 hgam le_rfl hsf hSmoG hHk4g
  have hslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => canonW (Work.Spaces.gam α) z θ * |Work.Spaces.DzIter 3 f z θ|
        * |Work.Spaces.mixed 1 1 g z θ| * |Work.Spaces.mixed 3 1 g z θ|)
      Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      rw [show (fun θ => canonW (Work.Spaces.gam α) 0 θ * |Work.Spaces.DzIter 3 f 0 θ|
            * |Work.Spaces.mixed 1 1 g 0 θ| * |Work.Spaces.mixed 3 1 g 0 θ|)
          = fun _ => (0 : ℝ) from by
        funext θ; rw [canonW_zero_z]; ring]
      exact MeasureTheory.integrableOn_zero
    · exact integrableOnSliceDelicate hα hα1 hsf.1 hsf.2.1
        hSmoG hHk4g hz0
  have hpoint : ∀ z ∈ Work.Spaces.Iz,
      |∫ θ in Work.Spaces.Iθ, canonW (Work.Spaces.gam α) z θ * Sdel f g 1 3 z θ
          * Work.Spaces.mixed 3 1 g z θ|
        ≤ ∫ θ in Work.Spaces.Iθ, canonW (Work.Spaces.gam α) z θ
            * |Work.Spaces.DzIter 3 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
            * |Work.Spaces.mixed 3 1 g z θ| := by
    intro z hz
    have hnorm : |∫ θ in Work.Spaces.Iθ, canonW (Work.Spaces.gam α) z θ * Sdel f g 1 3 z θ
          * Work.Spaces.mixed 3 1 g z θ|
        ≤ ∫ θ in Work.Spaces.Iθ, |canonW (Work.Spaces.gam α) z θ * Sdel f g 1 3 z θ
          * Work.Spaces.mixed 3 1 g z θ| := by
      simpa only [Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm
          (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
          (f := fun θ => canonW (Work.Spaces.gam α) z θ * Sdel f g 1 3 z θ
            * Work.Spaces.mixed 3 1 g z θ))
    refine le_trans hnorm ?_
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall
      (fun θ => abs_nonneg _)) (hslice z hz) ?_
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      filter_upwards with θ
      rw [canonW_zero_z, zero_mul, zero_mul, abs_zero]
      simp
    · refine ae_of_forall_Ioo (fun θ hθ => ?_)
      dsimp only
      have hsdel : Sdel f g 1 3 z θ
          = Work.Spaces.mixed 3 0 f z θ * Work.Spaces.mixed 1 1 g z θ := by
        simp only [Sdel, Nat.choose_self, Nat.cast_one, one_mul, Nat.reduceSub]
      rw [hsdel, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (canonW_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)]
      simp only [Work.Spaces.mixed_zero_right]
      exact le_of_eq (by ring)
  have hstep1 : |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        canonW (Work.Spaces.gam α) z θ * Sdel f g 1 3 z θ * Work.Spaces.mixed 3 1 g z θ|
      ≤ ∫ z in Work.Spaces.Iz,
        |∫ θ in Work.Spaces.Iθ, canonW (Work.Spaces.gam α) z θ * Sdel f g 1 3 z θ
          * Work.Spaces.mixed 3 1 g z θ| := by
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
        (f := fun z => ∫ θ in Work.Spaces.Iθ, canonW (Work.Spaces.gam α) z θ * Sdel f g 1 3 z θ
          * Work.Spaces.mixed 3 1 g z θ))
  have hstep2 : (∫ z in Work.Spaces.Iz,
        |∫ θ in Work.Spaces.Iθ, canonW (Work.Spaces.gam α) z θ * Sdel f g 1 3 z θ
          * Work.Spaces.mixed 3 1 g z θ|)
      ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          canonW (Work.Spaces.gam α) z θ * |Work.Spaces.DzIter 3 f z θ|
            * |Work.Spaces.mixed 1 1 g z θ| * |Work.Spaces.mixed 3 1 g z θ| :=
    MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => abs_nonneg _))
      hHd_int (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
        (fun z hz => hpoint z hz))
  refine le_trans (le_trans hstep1 hstep2) ?_
  simpa only [Work.FTS.TransportS.SlotT2.canonW, Work.Spaces.mixed_zero_right] using
    hDelb (Work.Spaces.gam α) hgam le_rfl

end Work.FTS.StrongPersist.N6Trans.Hon
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.Hon.SmainHon =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.Hon

open Work.FTS.TransportS.SlotT2 (canonW continuousOn_canonW)
open Work.FTS.TransportS.T2Sup (Smain ae_of_forall_Ioi canonW_mul_z_le_of_le
  canonW_mul_mixed_le_of_le smain_slice_abs_le)

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Integrability of the radial marginal -/

/-- **The marginal of the `Smain` summand is integrable** (honest class). -/
theorem smain_marginal_integrable_hon {α q Mf : ℝ} (hMf : 0 ≤ Mf) {f g : ℝ → ℝ → ℝ} {a b : ℕ}
    {k₁ k₂ : ℕ}
    (hFsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hGsm : Work.FTS.EllipticEst.SmoothOpen g)
    (hm1 : Work.Spaces.HkMem α k₁ g) (hm2 : Work.Spaces.HkMem α k₂ g)
    (hf : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Mf)
    (hX : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      canonW q z θ * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α k₁ g z θ)
    (hY : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α k₂ g z θ) :
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * f z θ * Work.Spaces.mixed (b + 1) a g z θ
          * Work.Spaces.mixed b a g z θ) Work.Spaces.Iz := by
  have hdom : MeasureTheory.Integrable
      (fun z => Mf * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k₁ g z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k₂ g z θ)))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := (hm1.2.add hm2.2).const_mul Mf
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
          * Work.Spaces.mixed (b + 1) a g z θ
          * Work.Spaces.mixed b a g z θ) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (Work.Spaces.aesm_of_continuousOn_Qd
        (fun p : ℝ × ℝ => canonW q p.1 p.2 * f p.1 p.2
          * Work.Spaces.mixed (b + 1) a g p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2)
        ((((continuousOn_canonW q).mul hFsm.continuousOn).mul
          ((hGsm.mixed (b + 1) a) |>.continuousOn)).mul
          ((hGsm.mixed b a) |>.continuousOn)))
  refine MeasureTheory.Integrable.mono' hdom haesm ?_
  refine ae_of_forall_Ioi (fun z hz => ?_)
  have hslice := smain_slice_abs_le (α := α) (q := q) (Mf := Mf) hMf (z := z)
    (hm1.1 z (le_of_lt hz)) (hm2.1 z (le_of_lt hz))
    (fun θ hθ hθ2 => hf z θ hz hθ hθ2) (fun θ hθ hθ2 => hX z θ hz hθ hθ2)
    (fun θ hθ hθ2 => hY z θ hz hθ hθ2)
  simpa [Real.norm_eq_abs] using hslice

/-! ## The easy case `a + b ≤ 3` -/

/-- **The easy case** (honest class): when `a + b ≤ 3` both `g`-factors are honest order-`≤ 4`
slots, so the pointwise AM–GM bound gives the sharp constant `2 Mf`. -/
theorem smain_easy_hon {α q Mf : ℝ} (hMf : 0 ≤ Mf) {f g : ℝ → ℝ → ℝ} {a b : ℕ}
    (hFsm : Work.FTS.EllipticEst.SmoothOpen f) (hGsm : Work.FTS.EllipticEst.SmoothOpen g)
    (hm4 : Work.Spaces.HkMem α 4 g)
    (hf : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Mf)
    (hX : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      canonW q z θ * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 g z θ)
    (hY : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 g z θ) :
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
        * Work.Spaces.mixed (b + 1) a g z θ * Work.Spaces.mixed b a g z θ)
        Work.Spaces.Iz ∧
      |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
          * Work.Spaces.mixed (b + 1) a g z θ * Work.Spaces.mixed b a g z θ|
        ≤ 2 * Mf * Work.Spaces.HkSq α 4 g := by
  refine ⟨smain_marginal_integrable_hon (k₁ := 4) (k₂ := 4) hMf hFsm hGsm hm4 hm4 hf hX hY, ?_⟩
  have h1 : |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
        * Work.Spaces.mixed (b + 1) a g z θ * Work.Spaces.mixed b a g z θ|
      ≤ ∫ z in Work.Spaces.Iz, Mf * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)) := by
    rw [← Real.norm_eq_abs]
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => norm_nonneg _)
      ((hm4.2.add hm4.2).const_mul Mf) ?_
    refine ae_of_forall_Ioi fun z hz => ?_
    have hslice := smain_slice_abs_le (α := α) (q := q) (Mf := Mf) hMf (z := z)
      (hm4.1 z (le_of_lt hz)) (hm4.1 z (le_of_lt hz))
      (fun θ hθ hθ2 => hf z θ hz hθ hθ2) (fun θ hθ hθ2 => hX z θ hz hθ hθ2)
      (fun θ hθ hθ2 => hY z θ hz hθ hθ2)
    simpa [Real.norm_eq_abs] using hslice
  refine le_trans h1 (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hm4.2 hm4.2,
    Work.Spaces.HkSq]
  ring

/-! ## The main statement -/

/-- **The `Smain` bound in the honest class.**  The top case `a + b = 4` is discharged by the
honest radial integration by parts (`TopSlotHonProp`), the easy case by AM–GM. -/
theorem smainBound_hon (hTop : TopSlotHonProp) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ) (a b : ℕ) (q Mf : ℝ),
      0 < α → α ≤ 1 → 0 ≤ Mf → a + b ≤ 4 → (a = 0 → q ≤ Work.Spaces.eta) →
      q ≤ Work.Spaces.gam α →
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.EllipticEst.SmoothOpen g →
      Work.Spaces.HkMem α 4 g → Work.Spaces.HkMem α 5 g → Work.Spaces.DecayAll 4 g →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Mf) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |Work.Spaces.Dz f z θ| ≤ Mf) →
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
          canonW q z θ * Smain f g a b z θ * Work.Spaces.mixed b a g z θ) Work.Spaces.Iz ∧
        |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            canonW q z θ * Smain f g a b z θ * Work.Spaces.mixed b a g z θ|
          ≤ C * Mf * Work.Spaces.HkSq α 4 g := by
  obtain ⟨Ct, hCt, hTop⟩ := hTop
  refine ⟨max 2 Ct, le_trans (by norm_num : (1:ℝ) ≤ 2) (le_max_left 2 Ct), ?_⟩
  intro α f g a b q Mf hα hα1 hMf hab hq0 hqγ hFsm hGsm hmg4 hmg5 hdec hf hDf
  have hHknn : 0 ≤ Work.Spaces.HkSq α 4 g := Work.Spaces.HkSq_nonneg α 4 g
  -- unfold `Smain` (up to the reassociation of the product)
  have hInt : (fun z => ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * Smain f g a b z θ * Work.Spaces.mixed b a g z θ)
      = fun z => ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
          * Work.Spaces.mixed (b + 1) a g z θ * Work.Spaces.mixed b a g z θ := by
    funext z
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    dsimp only
    rw [show Smain f g a b z θ = f z θ * Work.Spaces.mixed (b + 1) a g z θ from rfl]
    ring
  rw [hInt]
  rcases lt_or_eq_of_le hab with hlt | heq
  · -- ## Case `a + b ≤ 3`
    have hle : 2 * Mf * Work.Spaces.HkSq α 4 g ≤ max 2 Ct * Mf * Work.Spaces.HkSq α 4 g :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left (2:ℝ) Ct) hMf) hHknn
    rcases eq_or_ne a 0 with ha0 | ha0
    · -- `a = 0`, `b ≤ 3`: two pure `D_z`-slots
      have hqη : q ≤ Work.Spaces.eta := hq0 ha0
      have hX : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
          canonW q z θ * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2
            ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
        intro z θ hz hθ0 hθ2
        rw [ha0]
        simpa only [Work.Spaces.mixed_zero_right] using
          (canonW_mul_z_le_of_le (α := α) (q := q) 4 hqη (z := z) (θ := θ) hθ0 hθ2
            (j := b + 1) (by omega))
      have hY : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
          canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2
            ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
        intro z θ hz hθ0 hθ2
        rw [ha0]
        simpa only [Work.Spaces.mixed_zero_right] using
          (canonW_mul_z_le_of_le (α := α) (q := q) 4 hqη (z := z) (θ := θ) hθ0 hθ2
            (j := b) (by omega))
      exact ⟨(smain_easy_hon (α := α) (q := q) (Mf := Mf) (a := a) (b := b) hMf hFsm hGsm
          hmg4 hf hX hY).1,
        le_trans (smain_easy_hon (α := α) (q := q) (Mf := Mf) (a := a) (b := b) hMf hFsm
          hGsm hmg4 hf hX hY).2 hle⟩
    · -- `a ≥ 1`, `a + b ≤ 3`: two mixed slots
      have ha1 : 1 ≤ a := by omega
      have hX : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
          canonW q z θ * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2
            ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
        fun z θ hz hθ0 hθ2 =>
          canonW_mul_mixed_le_of_le (α := α) 4 hqγ hθ0 hθ2 (j := b + 1) (i := a)
            ha1 (by omega)
      have hY : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
          canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2
            ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
        fun z θ hz hθ0 hθ2 =>
          canonW_mul_mixed_le_of_le (α := α) 4 hqγ hθ0 hθ2 (j := b) (i := a)
            ha1 (by omega)
      exact ⟨(smain_easy_hon (α := α) (q := q) (Mf := Mf) (a := a) (b := b) hMf hFsm hGsm
          hmg4 hf hX hY).1,
        le_trans (smain_easy_hon (α := α) (q := q) (Mf := Mf) (a := a) (b := b) hMf hFsm
          hGsm hmg4 hf hX hY).2 hle⟩
  · -- ## Case `a + b = 4`: the top slot
    have hsub : 4 - a = b := by omega
    have hDzfun : Work.Spaces.Dz (Work.Spaces.mixed b a g)
        = Work.Spaces.mixed (b + 1) a g := by
      funext z θ
      simp only [Work.Spaces.mixed]
      rw [Work.Spaces.DzIter_succ]
    have hint : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
        * Work.Spaces.mixed (b + 1) a g z θ * Work.Spaces.mixed b a g z θ)
        Work.Spaces.Iz := by
      rcases eq_or_ne a 0 with ha0 | ha0
      · have hqη : q ≤ Work.Spaces.eta := hq0 ha0
        have hX : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
            canonW q z θ * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2
              ≤ Work.Spaces.HkIntegrand α 5 g z θ := by
          intro z θ hz hθ0 hθ2
          rw [ha0]
          simpa only [Work.Spaces.mixed_zero_right] using
            (canonW_mul_z_le_of_le (α := α) (q := q) 5 hqη (z := z) (θ := θ) hθ0 hθ2
              (j := b + 1) (by omega))
        have hY : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
            canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2
              ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
          intro z θ hz hθ0 hθ2
          rw [ha0]
          simpa only [Work.Spaces.mixed_zero_right] using
            (canonW_mul_z_le_of_le (α := α) (q := q) 4 hqη (z := z) (θ := θ) hθ0 hθ2
              (j := b) (by omega))
        exact smain_marginal_integrable_hon (k₁ := 5) (k₂ := 4) (a := a) (b := b) hMf hFsm
          hGsm hmg5 hmg4 hf hX hY
      · have ha1 : 1 ≤ a := by omega
        have hX : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
            canonW q z θ * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2
              ≤ Work.Spaces.HkIntegrand α 5 g z θ :=
          fun z θ hz hθ0 hθ2 =>
            canonW_mul_mixed_le_of_le (α := α) 5 hqγ hθ0 hθ2 (j := b + 1) (i := a)
              ha1 (by omega)
        have hY : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
            canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2
              ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
          fun z θ hz hθ0 hθ2 =>
            canonW_mul_mixed_le_of_le (α := α) 4 hqγ hθ0 hθ2 (j := b) (i := a)
              ha1 (by omega)
        exact smain_marginal_integrable_hon (k₁ := 5) (k₂ := 4) (a := a) (b := b) hMf hFsm
          hGsm hmg5 hmg4 hf hX hY
    refine ⟨hint, ?_⟩
    -- the integrand is the top slot with the weight `canonW q`
    have hgoal_eq : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
          * Work.Spaces.mixed (b + 1) a g z θ * Work.Spaces.mixed b a g z θ)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
          * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ
          * Work.Spaces.mixed b a g z θ := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      rw [hDzfun]
    rw [hgoal_eq]
    have hres := hTop α f g a b q Mf hα hα1 hMf heq hq0 hqγ hFsm hGsm hdec hmg4 hmg5 hf hDf
    calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
            * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ
            * Work.Spaces.mixed b a g z θ|
        ≤ Ct * Mf * Work.Spaces.HkSq α 4 g := hres
      _ ≤ max 2 Ct * Mf * Work.Spaces.HkSq α 4 g :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right (2:ℝ) Ct) hMf) hHknn

end Work.FTS.StrongPersist.N6Trans.Hon
end
end
