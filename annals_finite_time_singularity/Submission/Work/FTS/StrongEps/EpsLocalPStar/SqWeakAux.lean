import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSXrhs
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSPLipX
import Submission.Work.FTS.StrongEps.EComparison.E_slots_diff_le
import Submission.Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le
import Submission.Work.FTS.StrongEps.EpsRLX.DeltaXnBound
import Submission.Work.Spaces.Linf_H2_of_decay
import Submission.Work.FTS.StrongEps.EpsRLX.DeltaData
import Submission.Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le
import Submission.Work.FTS.StrongEps.EpsLocalPStar.TraceToEpsMem
import Submission.Work.FTS.StrongEps.EpsSqTools.L12_sub_EpsSq_le
import Submission.Work.FTS.StrongEps.EpsSqTools.L12_zero_le_EpsSq
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSqIter_mixed_Jeps_le6
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_Pz_sub_le
import Submission.Work.FTS.StrongEps.EpsSq_Jeps_le
import Submission.Work.FTS.StrongEps.HkSq_const_mul
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.StrongEps.PZeroAux.hkNorm_Pz_le
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.EllipticEst.EllHyp_certificates

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `profRHS_sub_sup_le_Sq`

**The pointwise Lipschitz estimate for the projected scheme's right-hand side, in the
`X = (EpsMem, EpsSq)`-interface.**

The sibling `profRHS_sub_sup_le` proves the same pointwise bound from the stronger `ℋ⁶`-ball
hypotheses (`SmoothOpen u`, `HkMem α 6 u`, `HkNorm α 6 u ≤ B`).  The present module replaces the
`ℋ⁶`-data of the *datum* by the `X`-data (`EpsMem α u`, `EpsSq α u ≤ R`) that the Picard
iteration of the projected `ε`-scheme can actually maintain, together with the class-`C` data of
the *mollified* profile `W_u = Wp ρ ε u`.

The only genuinely new input is the `ℋ⁵`-Lipschitz bound for the projected mollifier
(`HkSq_Wp_sub_le_weak`): with only `SmoothOpen`, `EpsMem` and `ClassC (W_u)` available, the
difference `W_u − W_v` satisfies

`HkSq α 5 (W_u − W_v) ≤ C · EpsSq α (u − v)`.

Its proof does *not* need the additivity `W_u − W_v = W_{u−v}` (which is unavailable at this
regularity): rewriting `Pz` through its definition (`Pz_apply`, `Pz_sub_apply`) and using the
`X`-continuity of the zero mode `L₁₂(·)(0)` (`L12_le_sqrt_EpsSq`, `L12_sub_EpsSq_le`) gives

`W_u − W_v = Pz (J_ε (u − v)) + corr · bump`,

with `|corr| ≤ C √(EpsSq α (u − v))`; the two summands are then estimated by
`HkSq_JepsPz_le` (the projected mollifier of `u − v`) and by homogeneity of `HkSq`
(`HkSq_const_mul`) against the fixed profile `bump`.

Everything else is a verbatim weakening of the sibling's proof: the per-profile `ℋ⁶`-size of
`W_u` comes from `HkSq_JepsPz_le` (with `EpsSq α u ≤ R` instead of `HkNorm α 6 u ≤ B`), the
`ℋ⁴`-data of the right-hand sides from `XDataClean`, the difference data from `DeltaXnBound`,
the traces from `DiffTraces` and the `ℋ¹ → X` descent from `TraceToEpsMem`.
-/

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Bookkeeping for `HkMem` and `HkSq` on the open-quadrant class -/

/-- `SmoothOpen` is closed under pointwise negation. -/
private theorem smoothOpen_neg_of {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => -f z θ) := by
  have hfun : Function.uncurry (fun z θ => -f z θ) = -(Function.uncurry f) := by
    funext p; rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, hfun]
  exact hf.neg

/-- `HkMem` is invariant under pointwise negation (the `ℋ^k`-integrand is unchanged). -/
private theorem hkMem_neg_of {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k (fun z θ => -f z θ) := by
  have hI : ∀ z θ, Work.Spaces.HkIntegrand α k (fun z θ => -f z θ) z θ
      = Work.Spaces.HkIntegrand α k f z θ := by
    intro z θ
    show Work.Spaces.HkIntegrand α k (-f) z θ = Work.Spaces.HkIntegrand α k f z θ
    exact congrFun (congrFun (Work.FTS.EllipticEst.HkIntegrand_neg α k f) z) θ
  constructor
  · intro z hz
    exact IntegrableOn.congr_fun (hf.1 z hz) (fun θ _ => (hI z θ).symm) measurableSet_Icc
  · have h : (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => -f z θ) z θ)
        = fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
      funext z
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => hI z θ)
    rw [h]
    exact hf.2

/-- `ℋ^k` is closed under differences of open-quadrant-smooth data (write `f - g = f + (-g)`). -/
private theorem hkMem_sub_open {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => f z θ - g z θ) := by
  have hfun : (fun z θ => f z θ - g z θ) = (fun z θ => f z θ + -g z θ) := by
    funext z θ; ring
  rw [hfun]
  exact Work.FTS.EllipticEst.HkMem_add_open hf (smoothOpen_neg_of hg) hmf (hkMem_neg_of hmg)

/-- **Subadditivity of `HkSq` on the open-quadrant class**: the pointwise inequality for the
`ℋ^k`-integrands of a sum is `HkIntegrand_add_le_of_contDiffOn`, and integrating it against the
honest `HkMem`-certificates gives the integrated form. -/
private theorem hkSq_add_le_open {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkSq α k (fun z θ => f z θ + g z θ)
      ≤ 2 * Work.Spaces.HkSq α k f + 2 * Work.Spaces.HkSq α k g :=
  Work.FTS.EllipticEst.HkSq_add_le_of_pointwise α k hmf hmg
    (Work.FTS.EllipticEst.HkIntegrand_add_le_of_contDiffOn α k hf hg)

/-! ## The `ℋ⁵`-Lipschitz bound for the projected mollifier in the weak interface -/

/-- **`HkMem α 4` of `J_ε w` from the class-`C` data of `W_w`.**

`W_w = Pz (J_ε w)` differs from `J_ε w` by a multiple of the fixed smooth profile `bump`
(`Pz_apply`), so the `ℋ⁴`-membership of `J_ε w` follows from that of `W_w` (which the class-`C`
data supplies at order `7`), of `bump`, and the closure of `HkMem` under sums
(`HkMem_add_open`), transported back along the pointwise identity
(`HkMem_congr_Q0`).  No `ℋ⁶`-membership of the *datum* `w` is needed. -/
theorem hkMem_four_Jeps_of_classC {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {w : Fn}
    (hw : Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε w)) :
    Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.Jeps ρ ε w) := by
  have hsrc : Work.Spaces.HkMem α 4
      ((fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ ε w z θ)
        + fun z θ => (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε w) 0
            / Work.FTS.StrongEps.pzNorm) * Work.FTS.StrongEps.bump z θ) :=
    Work.FTS.EllipticEst.HkMem_add_open hw.reg
      (Work.FTS.StrongEps.PZeroAux.smoothOpen_const_mul_gen _ Work.FTS.StrongEps.smoothOpen_bump)
      (Work.FTS.OpenPkg.HkMem_mono_open hw.reg 4 (by norm_num) hw.mem)
      (Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen _
        (Work.FTS.StrongEps.PZeroAux.hkMem_bump α 4))
  refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hsrc ?_
  intro z hz θ hθ
  show Work.FTS.StrongEps.EpsRLX.Wp ρ ε w z θ
      + (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε w) 0
          / Work.FTS.StrongEps.pzNorm) * Work.FTS.StrongEps.bump z θ
      = Work.FTS.StrongEps.Jeps ρ ε w z θ
  show Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε w) z θ + _ = _
  rw [Work.FTS.StrongEps.Pz_apply]
  ring

/-- **The `ℋ⁵`-Lipschitz bound for the projected-mollified profile in the weak interface.**

For `u`, `v` which are `C^∞` on the open quadrant, `X`-integrable (`EpsMem`) and such that their
projected-mollified profiles are of class `C`,

`HkSq α 5 (W_u − W_v) ≤ C · EpsSq α (u − v)`.

This is the `X`-form of `HkSq_Wp_sub_le6`; the proof avoids the unavailable additivity
`W_u − W_v = W_{u−v}` by writing the difference as `Pz (J_ε (u−v)) + corr·bump` and bounding the
scalar `corr` through the `X`-continuity of the zero mode `L₁₂(·)(0)`. -/
theorem HkSq_Wp_sub_le_weak {α : ℝ} {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hα : α ∈ Set.Ioc 0 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {u v : Fn},
      Work.FTS.EllipticEst.SmoothOpen u → Work.FTS.EllipticEst.SmoothOpen v →
      Work.FTS.StrongEps.EpsMem α u → Work.FTS.StrongEps.EpsMem α v →
      Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) →
      Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) →
      Work.Spaces.HkSq α 5 (fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ
          - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ)
        ≤ C * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ) := by
  obtain ⟨CH, hCHpos, hCH⟩ := Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le ρ hρ
  obtain ⟨CL, hCLpos, hCL⟩ := Work.FTS.StrongEps.EpsSqTools.L12_le_sqrt_EpsSq
  obtain ⟨CS, hCSpos, hCS⟩ := Work.FTS.StrongEps.EpsSqTools.L12_sub_EpsSq_le
  obtain ⟨CE, hCEpos, hCE⟩ := Work.FTS.StrongEps.EpsSq_Jeps_le ρ hρ.moll
  obtain ⟨CM, hCMpos, hCM⟩ := Work.FTS.StrongEps.EpsSqTools.EpsSqIter_mixed_Jeps_le6 ρ hρ
  obtain ⟨B, hBpos, hB⟩ := Work.FTS.StrongEps.PZeroAux.exists_HkNorm_bump_le
  have hpzpos : 0 < Work.FTS.StrongEps.pzNorm := Work.FTS.StrongEps.PZeroAux.pzNorm_pos
  -- the `ℋ⁵`-size of the fixed profile `bump`
  have hbump5 : Work.Spaces.HkSq α 5 Work.FTS.StrongEps.bump ≤ B ^ 2 := by
    have h6 : Work.Spaces.HkNorm α 6 Work.FTS.StrongEps.bump ≤ B := hB α hα 6 le_rfl
    have hsq : Work.Spaces.HkSq α 6 Work.FTS.StrongEps.bump
        = (Work.Spaces.HkNorm α 6 Work.FTS.StrongEps.bump) ^ 2 := by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 _)]
    calc Work.Spaces.HkSq α 5 Work.FTS.StrongEps.bump
        ≤ Work.Spaces.HkSq α 6 Work.FTS.StrongEps.bump :=
          Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num)
            (Work.FTS.StrongEps.PZeroAux.hkMem_bump α 6)
      _ = (Work.Spaces.HkNorm α 6 Work.FTS.StrongEps.bump) ^ 2 := hsq
      _ ≤ B ^ 2 := by
          have h0 : 0 ≤ Work.Spaces.HkNorm α 6 Work.FTS.StrongEps.bump :=
            Work.Spaces.HkNorm_nonneg α 6 _
          nlinarith [h0, hBpos.le]
  -- the size constant of the correction coefficient
  set Kc : ℝ := (CL + CS) * Real.exp CE / Work.FTS.StrongEps.pzNorm with hKc
  have hKc0 : 0 ≤ Kc := by
    rw [hKc]
    exact div_nonneg (mul_nonneg (by linarith) (Real.exp_nonneg _)) hpzpos.le
  refine ⟨2 * CH * (CH / ε) ^ 10 + 2 * B ^ 2 * Kc ^ 2, by positivity, ?_⟩
  intro u v hsu hsv hmu hmv hclu hclv
  have hα0 : 0 < α := hα.1
  -- ## the difference datum
  set h : Fn := fun z θ => u z θ - v z θ with hhdef
  have hsmh : Work.FTS.EllipticEst.SmoothOpen h := by
    rw [hhdef]
    exact Work.FTS.StrongEps.EpsSqTools.smoothOpen_subP hsu hsv
  have hquadh : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry h) Work.FTS.StrongEps.Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall h).mp hsmh
  have hquadu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Work.FTS.StrongEps.Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall u).mp hsu
  have hquadv : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry v) Work.FTS.StrongEps.Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall v).mp hsv
  have hak_u : Work.FTS.StrongEps.EpsSqTools.AK α u :=
    Work.FTS.StrongEps.EpsSqTools.AK_of_uncurry
      (Work.Spaces.aesm_of_continuousOn_Qd (Function.uncurry u)
        (((Work.FTS.EllipticEst.smoothOpen_iff_forall u).mp hsu 0).continuousOn))
  have hak_v : Work.FTS.StrongEps.EpsSqTools.AK α v :=
    Work.FTS.StrongEps.EpsSqTools.AK_of_uncurry
      (Work.Spaces.aesm_of_continuousOn_Qd (Function.uncurry v)
        (((Work.FTS.EllipticEst.smoothOpen_iff_forall v).mp hsv 0).continuousOn))
  have hmemh : Work.FTS.StrongEps.EpsMem α h := by
    rw [hhdef]
    exact Work.FTS.StrongEps.EpsSqTools.EpsMem_sub hak_u hak_v hmu hmv
  -- ## the three `J_ε`-images
  have hmemJh : Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.Jeps ρ ε h) :=
    (hCM α hα ε hε hε1 h hquadh hmemh).1
  have hmemJu : Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.Jeps ρ ε u) :=
    (hCM α hα ε hε hε1 u hquadu hmu).1
  have hmemJv : Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.Jeps ρ ε v) :=
    (hCM α hα ε hε hε1 v hquadv hmv).1
  have hsmJu : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε u) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε hquadu
  have hsmJv : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε v) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε hquadv
  have hmem4Ju : Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.Jeps ρ ε u) :=
    hkMem_four_Jeps_of_classC (ρ := ρ) (ε := ε) hclu
  have hmem4Jv : Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.Jeps ρ ε v) :=
    hkMem_four_Jeps_of_classC (ρ := ρ) (ε := ε) hclv
  have hJsub : Work.FTS.StrongEps.Jeps ρ ε u - Work.FTS.StrongEps.Jeps ρ ε v
      = Work.FTS.StrongEps.Jeps ρ ε h := by
    rw [hhdef]
    exact Work.FTS.StrongEps.EpsRLX.Jeps_sub_eq hρ.moll hε hsu hsv
  have hmemJsub : Work.FTS.StrongEps.EpsMem α
      (Work.FTS.StrongEps.Jeps ρ ε u - Work.FTS.StrongEps.Jeps ρ ε v) := by
    refine Work.FTS.StrongEps.EpsSqTools.EpsMem_congr (f := Work.FTS.StrongEps.Jeps ρ ε h) ?_ hmemJh
    intro z θ
    exact (congrFun (congrFun hJsub z) θ).symm
  -- ## the `X`-comparison of the two `J_ε`-images
  have hEpsJh : Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.Jeps ρ ε h)
      ≤ Real.exp (CE * ε) * Work.FTS.StrongEps.EpsSq α h :=
    hCE α hα ε hε hε1 h hmemh hmemJh
  have hEpsJsub : Work.FTS.StrongEps.EpsSq α
      (Work.FTS.StrongEps.Jeps ρ ε u - Work.FTS.StrongEps.Jeps ρ ε v)
      ≤ Real.exp (CE * ε) * Work.FTS.StrongEps.EpsSq α h := by
    rw [show (Work.FTS.StrongEps.Jeps ρ ε u - Work.FTS.StrongEps.Jeps ρ ε v)
        = Work.FTS.StrongEps.Jeps ρ ε h from hJsub]
    exact hEpsJh
  -- ## the bounds on the two `L₁₂`-terms
  have hL1 : |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε h) 0|
      ≤ CL * Real.sqrt (Real.exp (CE * ε) * Work.FTS.StrongEps.EpsSq α h) := by
    refine (hCL α hα (Work.FTS.StrongEps.Jeps ρ ε h) hmemJh 0 (by simp [Work.Spaces.Iz])).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hEpsJh) hCLpos.le
  have hL2 : |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε u) 0
        - Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε v) 0|
      ≤ CS * Real.sqrt (Real.exp (CE * ε) * Work.FTS.StrongEps.EpsSq α h) := by
    refine (hCS α hα (Work.FTS.StrongEps.Jeps ρ ε u) (Work.FTS.StrongEps.Jeps ρ ε v)
      hsmJu hsmJv hmem4Ju hmem4Jv hmemJsub 0 (by simp [Work.Spaces.Iz])).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hEpsJsub) hCSpos.le
  have hexpε : Real.exp (CE * ε) ≤ Real.exp CE :=
    Real.exp_le_exp.mpr (by nlinarith [hCEpos.le, hε1])
  -- ## the correction coefficient
  set corr : ℝ := (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε h) 0
      - Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε u) 0
      + Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε v) 0) / Work.FTS.StrongEps.pzNorm
    with hcorrdef
  have hcorr : |corr| ≤ Kc * Real.sqrt (Work.FTS.StrongEps.EpsSq α h) := by
    have hnum : |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε h) 0
          - Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε u) 0
          + Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε v) 0|
        ≤ (CL + CS) * Real.exp CE * Real.sqrt (Work.FTS.StrongEps.EpsSq α h) := by
      have h1 : |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε h) 0
            - Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε u) 0
            + Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε v) 0|
          ≤ |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε h) 0|
            + |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε u) 0
              - Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε v) 0| := by
        have hAb := abs_add_le (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε h) 0)
          (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε v) 0
            - Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε u) 0)
        rw [abs_sub_comm (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε v) 0)
          (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε u) 0)] at hAb
        have harg : Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε h) 0
              - Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε u) 0
              + Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε v) 0
            = Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε h) 0
              + (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε v) 0
                - Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε u) 0) := by ring
        rw [harg]
        exact hAb
      have hsq : Real.sqrt (Real.exp (CE * ε) * Work.FTS.StrongEps.EpsSq α h)
          ≤ Real.exp CE * Real.sqrt (Work.FTS.StrongEps.EpsSq α h) := by
        rw [Real.sqrt_mul (Real.exp_nonneg _)]
        refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
        rw [Real.sqrt_le_iff]
        refine ⟨Real.exp_nonneg _, ?_⟩
        rw [sq, ← Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith [hε1, hCEpos.le])
      calc |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε h) 0
            - Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε u) 0
            + Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε v) 0|
          ≤ |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε h) 0|
            + |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε u) 0
              - Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε v) 0| := h1
        _ ≤ CL * Real.sqrt (Real.exp (CE * ε) * Work.FTS.StrongEps.EpsSq α h)
            + CS * Real.sqrt (Real.exp (CE * ε) * Work.FTS.StrongEps.EpsSq α h) := by
            linarith [hL1, hL2]
        _ = (CL + CS) * Real.sqrt (Real.exp (CE * ε) * Work.FTS.StrongEps.EpsSq α h) := by ring
        _ ≤ (CL + CS) * (Real.exp CE * Real.sqrt (Work.FTS.StrongEps.EpsSq α h)) :=
            mul_le_mul_of_nonneg_left hsq (by linarith)
        _ = (CL + CS) * Real.exp CE * Real.sqrt (Work.FTS.StrongEps.EpsSq α h) := by ring
    rw [hcorrdef, abs_div, abs_of_pos hpzpos, hKc]
    calc |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε h) 0
            - Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε u) 0
            + Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε v) 0| / Work.FTS.StrongEps.pzNorm
        ≤ ((CL + CS) * Real.exp CE * Real.sqrt (Work.FTS.StrongEps.EpsSq α h))
            / Work.FTS.StrongEps.pzNorm :=
          (div_le_div_iff_of_pos_right hpzpos).mpr hnum
      _ = (CL + CS) * Real.exp CE / Work.FTS.StrongEps.pzNorm
            * Real.sqrt (Work.FTS.StrongEps.EpsSq α h) := by ring
  -- ## the `ℋ⁵`-memberships of the two summands and of their sum
  have hmemWpu : Work.Spaces.HkMem α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) :=
    Work.FTS.OpenPkg.HkMem_mono_open hclu.reg 5 (by norm_num) hclu.mem
  have hmemWpv : Work.Spaces.HkMem α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) :=
    Work.FTS.OpenPkg.HkMem_mono_open hclv.reg 5 (by norm_num) hclv.mem
  have hsmWpu : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) := hclu.reg
  have hsmWpv : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) := hclv.reg
  have hmemD : Work.Spaces.HkMem α 5 (fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ
      - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ) :=
    hkMem_sub_open hsmWpu hsmWpv hmemWpu hmemWpv
  have hsmR : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => corr * Work.FTS.StrongEps.bump z θ) :=
    Work.FTS.StrongEps.PZeroAux.smoothOpen_const_mul_gen corr Work.FTS.StrongEps.smoothOpen_bump
  have hmemR : Work.Spaces.HkMem α 5 (fun z θ => corr * Work.FTS.StrongEps.bump z θ) :=
    Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen corr
      (Work.FTS.StrongEps.PZeroAux.hkMem_bump α 5)
  have hsmD : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ
        - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ) :=
    Work.FTS.StrongEps.EpsSqTools.smoothOpen_subP hsmWpu hsmWpv
  have hsmG : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ
        - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ - corr * Work.FTS.StrongEps.bump z θ) :=
    Work.FTS.StrongEps.EpsSqTools.smoothOpen_subP hsmD hsmR
  have hmemG : Work.Spaces.HkMem α 5 (fun z θ =>
      Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ
        - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ - corr * Work.FTS.StrongEps.bump z θ) :=
    hkMem_sub_open hsmD hsmR hmemD hmemR
  -- ## the pointwise identity
  have hid : (fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ
        - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ)
      = fun z θ => Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε h) z θ
          + corr * Work.FTS.StrongEps.bump z θ := by
    funext z θ
    have hJ : Work.FTS.StrongEps.Jeps ρ ε u z θ - Work.FTS.StrongEps.Jeps ρ ε v z θ
        = Work.FTS.StrongEps.Jeps ρ ε h z θ := by
      have := congrFun (congrFun hJsub z) θ
      simpa only [Pi.sub_apply] using this
    show (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u)
        - Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε v)) z θ
        = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε h) z θ
          + corr * Work.FTS.StrongEps.bump z θ
    rw [Work.FTS.StrongEps.EpsSqTools.Pz_sub_apply, Work.FTS.StrongEps.Pz_apply, hJ, hcorrdef]
    ring
  -- ## the `ℋ⁵`-membership of `Pz (J_ε h)`
  have hmemPz : Work.Spaces.HkMem α 5 (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε h)) := by
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 5 hmemG ?_
    intro z hz θ hθ
    have hzθ := congrFun (congrFun hid z) θ
    linarith [hzθ]
  have hsmPz : Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε h)) :=
    smoothOpen_Pz (Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε hquadh)
  -- ## the two summands of the decomposition
  have hsub : Work.Spaces.HkSq α 5
      (fun z θ => Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε h) z θ
        + corr * Work.FTS.StrongEps.bump z θ)
      ≤ 2 * Work.Spaces.HkSq α 5 (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε h))
        + 2 * Work.Spaces.HkSq α 5 (fun z θ => corr * Work.FTS.StrongEps.bump z θ) :=
    hkSq_add_le_open hsmPz hsmR hmemPz hmemR
  have hPzb : Work.Spaces.HkSq α 5 (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε h))
      ≤ CH * (CH / ε) ^ 10 * Work.FTS.StrongEps.EpsSq α h :=
    hCH α hα ε hε hε1 5 (by norm_num) h hsmh hmemh
  have hcorr2 : corr ^ 2 ≤ Kc ^ 2 * Work.FTS.StrongEps.EpsSq α h := by
    have hsq := pow_le_pow_left₀ (abs_nonneg corr) hcorr 2
    rw [sq_abs, mul_pow, Real.sq_sqrt (Work.FTS.StrongEps.EpsSq_nonneg α h)] at hsq
    exact hsq
  have hbumpterm : Work.Spaces.HkSq α 5 (fun z θ => corr * Work.FTS.StrongEps.bump z θ)
      ≤ B ^ 2 * Kc ^ 2 * Work.FTS.StrongEps.EpsSq α h := by
    rw [Work.FTS.StrongEps.HkSq_const_mul]
    calc corr ^ 2 * Work.Spaces.HkSq α 5 Work.FTS.StrongEps.bump
        ≤ corr ^ 2 * B ^ 2 := mul_le_mul_of_nonneg_left hbump5 (sq_nonneg corr)
      _ ≤ (Kc ^ 2 * Work.FTS.StrongEps.EpsSq α h) * B ^ 2 :=
          mul_le_mul_of_nonneg_right hcorr2 (sq_nonneg B)
      _ = B ^ 2 * Kc ^ 2 * Work.FTS.StrongEps.EpsSq α h := by ring
  have hE0 : 0 ≤ Work.FTS.StrongEps.EpsSq α h := Work.FTS.StrongEps.EpsSq_nonneg α h
  have hfac0 : 0 ≤ CH * (CH / ε) ^ 10 := by positivity
  calc Work.Spaces.HkSq α 5 (fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ
        - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ)
      = Work.Spaces.HkSq α 5 (fun z θ => Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε h) z θ
          + corr * Work.FTS.StrongEps.bump z θ) := Work.FTS.EllipticEst.HkSq_congr_open α 5
            (fun z θ _ _ _ => congrFun (congrFun hid z) θ)
    _ ≤ 2 * Work.Spaces.HkSq α 5 (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε h))
          + 2 * Work.Spaces.HkSq α 5 (fun z θ => corr * Work.FTS.StrongEps.bump z θ) := hsub
    _ ≤ 2 * (CH * (CH / ε) ^ 10 * Work.FTS.StrongEps.EpsSq α h)
          + 2 * (B ^ 2 * Kc ^ 2 * Work.FTS.StrongEps.EpsSq α h) := by
        linarith [mul_le_mul_of_nonneg_left hPzb (by norm_num : (0:ℝ) ≤ 2),
          mul_le_mul_of_nonneg_left hbumpterm (by norm_num : (0:ℝ) ≤ 2)]
    _ = (2 * CH * (CH / ε) ^ 10 + 2 * B ^ 2 * Kc ^ 2) * Work.FTS.StrongEps.EpsSq α h := by ring

end Work.FTS.StrongEps.EpsLocalPStar
