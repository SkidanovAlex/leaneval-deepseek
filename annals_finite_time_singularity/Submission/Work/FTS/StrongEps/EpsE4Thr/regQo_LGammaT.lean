import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.StrongEps.EpsZero.ClassCHk.LGammaTMem
import Submission.Work.FTS.GalFields.RHS.smoothOpen_LGammaT_of_L12
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.ClassC.A1
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_LGammaT_Aux
import Submission.Work.FTS.StrongEps.EpsE4Thr.L12Aux.Qang_small_z
import Submission.Work.FTS.StrongEps.EpsE4Thr.L12Aux.ampA_dzdIter_abs_le
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_Gam_mul_rad
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_Lhat
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.radA_traces

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.StrongEps.EpsE4Thr.regQo_LGammaT`

**`𝓛_Γ^T x ∈ RegQo α 4` for every profile `x` of the class `ClassC α`, `α ∈ (0,1]`.**

`RegQo α k f = SmoothOpen f ∧ HkMem α k f ∧ BdryTraces α k f` (`EpsE4Thr/OpenClass.lean`).
The three conjuncts:

* `SmoothOpen`: `GalFields.RHS.smoothOpen_LGammaT_of_L12` with the smoothness of the angular
  moment `z ↦ L₁₂ x z` supplied by `ClassCRHS.smoothOpen_L12_radial_classC` (the `ClassC.fsm`
  field);
* `HkMem α 4`: `EpsZero.ClassCHk.HkMem_Lhat_of_classC` + `HkMem_Corr_of_classC` glued by
  `OpenPkg.HkMem_add_of_contDiffOn_four` through `𝓛_Γ^T = 𝓛̂ + Corr`;
* `BdryTraces α 4`: `ClassC.bdryTraces_add` on the same splitting, with
  `TracesAux.BdryTraces_Lhat` (the clean part) and `BdryTraces_Corr` (the transfer part,
  which is `Transfer.Corr_eq_radA` plus `TracesAux.BdryTraces_Gam_mul_rad` fed by the radial
  traces `TracesAux.radA_traces`).

The bounds underlying `radA_traces` are in `regQo_LGammaT_Aux`; the analytic input
(`Qang x k = O(z^{3/2})`, from the Poincaré argument) is `L12Aux.Qang_small_z`, and the
`z`-decay of the transfer profile `ampA` (its `Zop`-iterates are dominated by `z/(1+z)²`) is
`L12Aux.ampA_dzdIter_abs_le`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- `L₁₂ x` is `C^n` on `(0,∞)` for a `ClassC` profile. -/
theorem contDiffOn_L12f {α : ℝ} (hα : 0 < α) {x : Fn}
    (hx : Work.FTS.ClassC.ClassC α x) (n : ℕ) :
    ContDiffOn ℝ n (Work.Coercivity.L12f x) (Set.Ioi 0) := by
  rw [L12f_eq_elliptic]
  have hsm := Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα hx
  have h := hsm.curry_z (θ := (1 : ℝ) / 2) ⟨by norm_num, by linarith [Real.pi_gt_three]⟩
  exact contDiffOn_infty.mp h n

/-- `radA α x` is `C^n` on `(0,∞)`. -/
theorem contDiffOn_radA {α : ℝ} (hα : 0 < α) {x : Fn}
    (hx : Work.FTS.ClassC.ClassC α x) (n : ℕ) :
    ContDiffOn ℝ n (Work.FTS.CoercivityFix.Transfer.radA α x) (Set.Ioi 0) := by
  have hampA : ContDiffOn ℝ n (Work.FTS.CoercivityFix.Transfer.ampA α) (Set.Ioi 0) := by
    by_cases hc : Work.Spaces.c α = 0
    · have hzero : Work.FTS.CoercivityFix.Transfer.ampA α = fun _ : ℝ => 0 := by
        funext z
        simp only [Work.FTS.CoercivityFix.Transfer.ampA, hc, zero_mul, div_zero]
      rw [hzero]
      exact contDiffOn_const
    · exact (contDiffOn_const.mul contDiffOn_id).div
        (contDiffOn_const.mul ((contDiffOn_const.add contDiffOn_id).pow 2))
        (fun z hz => by
          have h1 : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
          exact mul_ne_zero hc (pow_ne_zero 2 (ne_of_gt h1)))
  have hampB : ContDiffOn ℝ n (Work.FTS.CoercivityFix.Transfer.ampB α) (Set.Ioi 0) :=
    (contDiffOn_const.mul (contDiffOn_id.pow 2)).div
      ((contDiffOn_const.add contDiffOn_id).pow 3)
      (fun z hz => by
        have h1 : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
        exact pow_ne_zero 3 (ne_of_gt h1))
  have hfun : Work.FTS.CoercivityFix.Transfer.radA α x
      = fun z => (Work.Coercivity.L12f (Work.Coercivity.Transport x) 0 / Work.Spaces.c α)
          * Work.FTS.CoercivityFix.Transfer.ampB α z
        + -(Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f x z) := by
    funext z
    simp only [Work.FTS.CoercivityFix.Transfer.radA, Work.FTS.CoercivityFix.Transfer.ampA,
      Work.FTS.CoercivityFix.Transfer.ampB]
    ring
  rw [hfun]
  refine ContDiffOn.add ?_ ?_
  · exact contDiffOn_const.mul hampB
  · exact (hampA.mul (contDiffOn_L12f hα hx n)).neg

/-- A single constant dominating `|Qang x k z| / z^{3/2}` for all `k ≤ 3`, `z ∈ (0,1)`. -/
theorem exists_Qang_bound {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {x : Fn}
    (hx : Work.FTS.ClassC.ClassC α x) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z → z < 1 →
      |Work.Elliptic.Qang x k z| ≤ C * z ^ ((3 : ℝ) / 2) := by
  obtain ⟨C0, hC0, hQ0⟩ := Work.FTS.StrongEps.EpsE4Thr.L12Aux.Qang_small_z hα hx
    (k := 0) (by norm_num)
  obtain ⟨C1, hC1, hQ1⟩ := Work.FTS.StrongEps.EpsE4Thr.L12Aux.Qang_small_z hα hx
    (k := 1) (by norm_num)
  obtain ⟨C2, hC2, hQ2⟩ := Work.FTS.StrongEps.EpsE4Thr.L12Aux.Qang_small_z hα hx
    (k := 2) (by norm_num)
  obtain ⟨C3, hC3, hQ3⟩ := Work.FTS.StrongEps.EpsE4Thr.L12Aux.Qang_small_z hα hx
    (k := 3) (by norm_num)
  set M : ℝ := max (max (max C0 C1) C2) C3 with hM
  have hC0M : C0 ≤ M := by rw [hM]; exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hC1M : C1 ≤ M := by rw [hM]; exact le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hC2M : C2 ≤ M := by rw [hM]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hC3M : C3 ≤ M := by rw [hM]; exact le_max_right _ _
  refine ⟨M, lt_of_lt_of_le hC0 hC0M, fun k hk z hz hz1 => ?_⟩
  have hzr : 0 ≤ z ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hz.le _
  interval_cases k
  · exact le_trans (hQ0 z hz hz1) (mul_le_mul_of_nonneg_right hC0M hzr)
  · exact le_trans (hQ1 z hz hz1) (mul_le_mul_of_nonneg_right hC1M hzr)
  · exact le_trans (hQ2 z hz hz1) (mul_le_mul_of_nonneg_right hC2M hzr)
  · exact le_trans (hQ3 z hz hz1) (mul_le_mul_of_nonneg_right hC3M hzr)

/-- **The boundary traces of the transfer part** `Corr α x = Γ(θ)·radA α x (z)`. -/
theorem BdryTraces_Corr {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {x : Fn}
    (hx : Work.FTS.ClassC.ClassC α x) :
    Work.FTS.Nonlin.BdryTraces α 4 (Work.FTS.CoercivityFix.Corr α x) := by
  obtain ⟨C, hC, hQ⟩ := exists_Qang_bound hα hx
  obtain ⟨hr0, hr1⟩ := Work.FTS.StrongEps.EpsE4Thr.TracesAux.radA_traces (x := x) hα hx hC
    hQ (fun b => Work.FTS.StrongEps.EpsE4Thr.L12Aux.ampA_dzdIter_abs_le α b)
  have hmain := Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_Gam_mul_rad
    (α := α) (k := 4) (r := Work.FTS.CoercivityFix.Transfer.radA α x) hα.1
    (Cg := 100000) (by norm_num)
    (fun a _ θ hθ0 hθ1 =>
      Work.FTS.LocData6.DthIter_Gam_abs_le6 a (by omega) α hα.1 hα.2
        ⟨le_of_lt hθ0, le_of_lt hθ1⟩)
    (contDiffOn_radA hα.1 hx 5) hr0 hr1
  rw [show Work.FTS.CoercivityFix.Corr α x
      = fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radA α x z from by
    funext z θ
    exact Work.FTS.CoercivityFix.Transfer.Corr_eq_radA α x z θ]
  exact hmain

theorem regQo_LGammaT {α : ℝ} {x : Work.FTS.Galerkin.Fn} (hα : α ∈ Set.Ioc 0 1)
    (hx : Work.FTS.ClassC.ClassC α x) :
    Work.FTS.StrongEps.EpsE4Thr.RegQo α 4 (Work.Coercivity.LGammaT α x) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Work.FTS.GalFields.RHS.smoothOpen_LGammaT_of_L12
      (α := α) (Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα.1 hx) hx.reg
  · have hmemL : Work.Spaces.HkMem α 4 (Work.FTS.CoercivityFix.Lhat x) :=
      Work.FTS.StrongEps.EpsZero.ClassCHk.HkMem_Lhat_of_classC hα.1 hx
    have hmemC : Work.Spaces.HkMem α 4 (Work.FTS.CoercivityFix.Corr α x) :=
      Work.FTS.StrongEps.EpsZero.ClassCHk.HkMem_Corr_of_classC hα.1 hα.2 hx
    have hsmC : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.CoercivityFix.Corr α x))
        Work.FTS.EllipticEst.Q0 :=
      Work.FTS.StrongEps.EpsZero.ClassCHk.contDiffOn_Corr_of_classC hα.1 hα.2 hx
    rw [Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr α x]
    exact Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
      ((Work.FTS.StrongPersist.H6Aux.smoothOpen_Lhat hx.reg).forall 4) hsmC hmemL hmemC
  · have hsmL := Work.FTS.StrongPersist.H6Aux.smoothOpen_Lhat hx.reg
    have hLGT := Work.FTS.GalFields.RHS.smoothOpen_LGammaT_of_L12
      (α := α) (Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα.1 hx) hx.reg
    have hsmC := Work.FTS.NonlinRows.smoothOpen_sub hLGT hsmL
    rw [Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr α x]
    exact Work.FTS.ClassC.bdryTraces_add hsmL hsmC
      (Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_Lhat hα.1 hx)
      (BdryTraces_Corr hα hx)

end Work.FTS.StrongEps.EpsE4Thr
