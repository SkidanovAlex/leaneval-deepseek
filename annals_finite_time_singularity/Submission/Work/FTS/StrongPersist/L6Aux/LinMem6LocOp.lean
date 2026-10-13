/-
# `Work.FTS.StrongPersist.L6Aux.LinMem6LocOp` — the local summand `locOp = -(𝓛 f) + Transport f`

`locOp` is a first-order operator with smooth coefficients; its `ℋ⁶`-integrand is dominated by
the `ℋ⁷`-integrand of `f` (the slots `D_z⁶(D_z f)`, `D_θ⁶(D_θ f)` are `ℋ⁷`-slots of `f`
uppercase by `HkIntegrand_mixed_shift`, and the multiplicative slots by the multiplier estimate
`zmul_quad`).  This is where the hypothesis `HkMem α 7 f` is spent.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib
import Submission.Work.FTS.StrongPersist.Defs
import Submission.Work.FTS.StrongPersist.Basic
import Submission.Work.FTS.StrongPersist.L3_lin_mem
import Submission.Work.FTS.StrongPersist.HkAddFin
import Submission.Work.FTS.StrongPersist.N6_L12H
import Submission.Work.FTS.StrongPersist.L3Aux.HkIntegrand_mixed_shift
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.StrongPersist.L3Aux.GamJetBounds
import Submission.Work.FTS.LocData.HkIntegrand_neg
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.PthIter2VftsAux
import Submission.Work.Coercivity.dthIterAng_sq_integrable
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.StrongPersist.L6Aux.LinMem6Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn)
open Work.Spaces (HkMem HkSq HkNorm HkIntegrand Dz Dth mixed)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## §3 The local summand `locOp = -(𝓛 f) + Transport f`

`locOp` is a first-order operator with smooth coefficients; its `ℋ⁶`-integrand is dominated by
the `ℋ⁷`-integrand of `f`. -/

private theorem smoothOpen_DzCoeff {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => -(2 * f z θ / (1 + z))) := by
  have h2 : (fun z θ => -(2 * f z θ / (1 + z)))
      = fun z θ => (fun z : ℝ => -(2 / (1 + z))) z * f z θ := by
    funext z θ
    ring
  rw [h2]
  exact linMem_mul (linMem_radial linMem_two_div_smooth.neg) hf

private theorem smoothOpen_L {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Coercivity.L f) := by
  have hL : Work.Coercivity.L f
      = fun z θ => (f z θ + Work.Spaces.Dz f z θ) + (-(2 * f z θ / (1 + z))) := by
    funext z θ
    simp only [Work.Coercivity.L, Work.Spaces.Dz, Work.Spaces.pz]
    ring
  rw [hL]
  exact Work.FTS.EllipticEst.smoothOpen_add
    (Work.FTS.EllipticEst.smoothOpen_add hf (hf.DzIter 1)) (smoothOpen_DzCoeff hf)

private theorem smoothOpen_Transport {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Coercivity.Transport f) := by
  have hT : Work.Coercivity.Transport f
      = fun z θ => (fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth f z θ := by
    funext z θ
    simp only [Work.Coercivity.Transport, Work.Spaces.Dth, Work.Spaces.pth]
    ring
  rw [hT]
  exact linMem_mul
    (linMem_radial (contDiffOn_iff_forall_nat_le.mpr
      (fun m _ => Work.FTS.FinalClock.contDiffOn_phiThree m))) hf.Dth

/-- `locOp f` is `C^∞` on the open quadrant whenever `f` is. -/
theorem locOp_smoothOpen {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (locOp f) := by
  have h : locOp f
      = fun z θ => -(Work.Coercivity.L f z θ) + Work.Coercivity.Transport f z θ := rfl
  rw [h]
  exact Work.FTS.EllipticEst.smoothOpen_add
    (linMem_neg (smoothOpen_L hf)) (smoothOpen_Transport hf)

/-- The `ℋ⁶`-integrand of `locOp f` is dominated by `100(1+C_{zmul}(1+K)²)` times the
`ℋ⁷`-integrand of `f`. -/
theorem locOp_integrand_le {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α) {K : ℝ} (hK : 0 ≤ K)
    (hzb : ∀ b ≤ 6, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[b] (fun z : ℝ => 3 / (1 + z)) z| ≤ K)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (locOp f) z θ
        ≤ (100 * (1 + Work.FTS.StrongPersist.L3Aux.zmulConst 6 * (1 + K) ^ 2))
            * Work.Spaces.HkIntegrand α 7 f z θ := by
  intro z hz θ hθ
  set Z : ℝ := Work.FTS.StrongPersist.L3Aux.zmulConst 6 * (1 + K) ^ 2 with hZdef
  have hZnn : 0 ≤ Z := by
    rw [hZdef]
    exact mul_nonneg (Work.FTS.StrongPersist.L3Aux.zmulConst_pos 6).le (sq_nonneg _)
  have hphism : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => 3 / (1 + z))
      (Set.Ioi (-1)) :=
    contDiffOn_iff_forall_nat_le.mpr (fun m _ => Work.FTS.FinalClock.contDiffOn_phiThree m)
  have hAnn : 0 ≤ Work.Spaces.HkIntegrand α 7 f z θ := Work.Spaces.HkIntegrand_nonneg α 7 f z θ
  -- the three individual slot bounds
  have hf6 : Work.Spaces.HkIntegrand α 6 f z θ ≤ Work.Spaces.HkIntegrand α 7 f z θ :=
    Work.FTS.StrongPersist.HkIntegrand_le_of_le α (by norm_num) f z θ
  have hDz : Work.Spaces.HkIntegrand α 6 (Work.Spaces.Dz f) z θ
      ≤ Work.Spaces.HkIntegrand α 7 f z θ := by
    have h := Work.FTS.StrongPersist.L3Aux.HkIntegrand_mixed_shift α hα 6 0 1 hf z hz θ hθ
    simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
      Nat.reduceAdd] using h
  have hDth : Work.Spaces.HkIntegrand α 6 (Work.Spaces.Dth f) z θ
      ≤ Work.Spaces.HkIntegrand α 7 f z θ := by
    have h := Work.FTS.StrongPersist.L3Aux.HkIntegrand_mixed_shift α hα 6 1 0 hf z hz θ hθ
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero,
      Nat.reduceAdd] using h
  have hzmu : Work.Spaces.HkIntegrand α 6
        (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * f z θ) z θ
      ≤ Z * Work.Spaces.HkIntegrand α 6 f z θ := by
    rw [hZdef]
    exact Work.FTS.StrongPersist.L3Aux.zmul_quad α 6 (fun z : ℝ => 3 / (1 + z)) f hK hzb
      hphism hf z hz θ hθ
  have hzmd : Work.Spaces.HkIntegrand α 6
        (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth f z θ) z θ
      ≤ Z * Work.Spaces.HkIntegrand α 6 (Work.Spaces.Dth f) z θ := by
    rw [hZdef]
    exact Work.FTS.StrongPersist.L3Aux.zmul_quad α 6 (fun z : ℝ => 3 / (1 + z))
      (Work.Spaces.Dth f) hK hzb hphism hf.Dth z hz θ hθ
  -- `f + D_z f`
  have hsum1 : Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ + Work.Spaces.Dz f z θ) z θ
      ≤ 4 * Work.Spaces.HkIntegrand α 7 f z θ := by
    have h := Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α 6
      (f := f) (g := Work.Spaces.Dz f) (hf.forall 6) ((hf.DzIter 1).forall 6) z hz θ hθ
    linarith
  -- `-(2f/(1+z))`
  have hmid : Work.Spaces.HkIntegrand α 6 (fun z θ => -(2 * f z θ / (1 + z))) z θ
      ≤ (2 / 3) ^ 2 * Z * Work.Spaces.HkIntegrand α 7 f z θ := by
    have hfun : (fun z θ => -(2 * f z θ / (1 + z)))
        = fun z θ => (-(2 / 3)) * ((fun z : ℝ => 3 / (1 + z)) z * f z θ) := by
      funext z θ
      rw [linMem_two_mul_div_eq (f z θ) (1 + z)]
      ring
    rw [hfun, Work.FTS.LocData.hkIntegrand_const_mul]
    have h2 : (-(2 / 3)) ^ 2 * Work.Spaces.HkIntegrand α 6
          (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * f z θ) z θ
        ≤ (-(2 / 3)) ^ 2 * (Z * Work.Spaces.HkIntegrand α 7 f z θ) :=
      mul_le_mul_of_nonneg_left (le_trans hzmu (mul_le_mul_of_nonneg_left hf6 hZnn)) (sq_nonneg _)
    calc (-(2 / 3)) ^ 2 * Work.Spaces.HkIntegrand α 6
          (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * f z θ) z θ
        ≤ (-(2 / 3)) ^ 2 * (Z * Work.Spaces.HkIntegrand α 7 f z θ) := h2
      _ = (2 / 3) ^ 2 * Z * Work.Spaces.HkIntegrand α 7 f z θ := by ring
  -- `Transport f`
  have htrans : Work.Spaces.HkIntegrand α 6 (Work.Coercivity.Transport f) z θ
      ≤ Z * Work.Spaces.HkIntegrand α 7 f z θ := by
    have hfun : Work.Coercivity.Transport f
        = fun z θ => (fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth f z θ := by
      funext z θ
      simp only [Work.Coercivity.Transport, Work.Spaces.Dth, Work.Spaces.pth]
      ring
    rw [hfun]
    nlinarith [hzmd, hDth, hZnn, Work.Spaces.HkIntegrand_nonneg α 6 (Work.Spaces.Dth f) z θ, hAnn]
  -- `𝓛 f`
  have hLf : Work.Spaces.HkIntegrand α 6 (Work.Coercivity.L f) z θ
      ≤ 2 * (4 * Work.Spaces.HkIntegrand α 7 f z θ)
        + 2 * ((2 / 3) ^ 2 * Z * Work.Spaces.HkIntegrand α 7 f z θ) := by
    have hL : Work.Coercivity.L f
        = fun z θ => (f z θ + Work.Spaces.Dz f z θ) + (-(2 * f z θ / (1 + z))) := by
      funext z θ
      simp only [Work.Coercivity.L, Work.Spaces.Dz, Work.Spaces.pz]
      ring
    rw [hL]
    have h := Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α 6
      (f := fun z θ => f z θ + Work.Spaces.Dz f z θ)
      (g := fun z θ => -(2 * f z θ / (1 + z))) ((hf.forall 6).add ((hf.DzIter 1).forall 6)) ?_ z hz θ hθ
    · linarith
    · have h2 : (fun z θ => -(2 * f z θ / (1 + z)))
          = fun z θ => (fun z : ℝ => -(2 / (1 + z))) z * f z θ := by
        funext z θ; ring
      rw [h2]
      refine linMem_zmul_joint (n := 6) ?_ (hf.forall 6)
      exact ((linMem_two_div 6).neg).mono (fun z hz' => by
        simp only [Set.mem_Ioi] at hz' ⊢
        linarith)
  -- `locOp`
  change Work.Spaces.HkIntegrand α 6 (fun z θ => -(Work.Coercivity.L f z θ)
      + Work.Coercivity.Transport f z θ) z θ ≤ _
  have h := Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α 6
    (f := fun z θ => -(Work.Coercivity.L f z θ)) (g := Work.Coercivity.Transport f)
    ((smoothOpen_L hf).forall 6).neg ((smoothOpen_Transport hf).forall 6) z hz θ hθ
  have hneg : Work.Spaces.HkIntegrand α 6 (fun z θ => -(Work.Coercivity.L f z θ)) z θ
      = Work.Spaces.HkIntegrand α 6 (Work.Coercivity.L f) z θ :=
    Work.FTS.LocData.HkIntegrand_neg α 6 (Work.Coercivity.L f) z θ
  rw [hneg] at h
  nlinarith [h, hLf, htrans, hZnn, hAnn]

/-- **The local summand is in `ℋ⁶`.** -/
theorem LocOp_mem6_of {α : ℝ} {f : Fn} (hα : 0 < α) {K : ℝ} (hK : 0 ≤ K)
    (hzb : ∀ b ≤ 6, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[b] (fun z : ℝ => 3 / (1 + z)) z| ≤ K)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 7 f) :
    Work.Spaces.HkMem α 6 (locOp f) := by
  refine Work.FTS.LocData.HkMem_of_majorant α 6 (f := locOp f)
    (M := fun z θ => (100 * (1 + Work.FTS.StrongPersist.L3Aux.zmulConst 6 * (1 + K) ^ 2))
      * Work.Spaces.HkIntegrand α 7 f z θ) ?_ ?_ ?_ ?_
  · exact Work.FTS.EllipticEst.Cores.DiagEstEllT.continuousOn_HkIntegrand_of_contDiffOn
      ((locOp_smoothOpen hsm).forall 6) α
  · intro z hz
    exact (hmem.1 z hz).const_mul _
  · have h1 : (fun z => ∫ θ in Work.Spaces.Iθ,
          (100 * (1 + Work.FTS.StrongPersist.L3Aux.zmulConst 6 * (1 + K) ^ 2))
            * Work.Spaces.HkIntegrand α 7 f z θ)
        = fun z => (100 * (1 + Work.FTS.StrongPersist.L3Aux.zmulConst 6 * (1 + K) ^ 2))
            * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 7 f z θ := by
      funext z
      rw [MeasureTheory.integral_const_mul]
    rw [h1]
    exact hmem.2.const_mul _
  · intro z hz θ hθ
    exact locOp_integrand_le hα hK hzb hsm z hz θ hθ



end Work.FTS.StrongPersist
