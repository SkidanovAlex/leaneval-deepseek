import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved
import Submission.Work.FTS_RegExport.RXB.l12_zero_lim_proved
import Submission.Work.FTS_RegExport.RXT.Sys.slice_tau_modulus_weighted2
import Submission.Work.FTS.GalBasis.cc.integral_abs_L12dens_le_Ioi
import Submission.Work.FTS.GalBasis.cc.abs_L12_le_HkNorm
import Submission.Work.FTS_RegExport.RXT.Ftau_bounds
import Submission.Work.Construction.Basic
import Submission.Work.FM.Core
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.L12Deriv
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.L12_limit_bound
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.Horizon
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.QlimSelf
import Submission.Work.FTS.StrongEps.SupPort.classC_mixed_sup_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L12FK_family_jets`

The order-`≤ 2` `z`-jet package of the radial transforms `L₁₂` and `𝔽K` of the profile
`F(τ) = F_* + slice (GR α g) τ`, uniformly on the fake-time horizon `τ ∈ [0,T]`, from the
`LimApprox` approximation clause alone:

* `|D_z^j (𝔽K F(τ))| ≤ C` for `j ≤ 2`;
* `|L₁₂ F(τ)| ≤ C`;
* `D_z (L₁₂ F(τ)) = -𝔽K F(τ)`;
* the fake-time Lipschitz bounds of `L₁₂ F(τ)` and of `𝔽K F(τ)`.

Everything is obtained by passing to the limit along the class-`C` approximating families of
`LimApprox` (the limit profile itself is *not* known to be smooth): the standing estimates on the
horizon are `L12FKaux.Horizon` (`approx_slot_bound`, `ftau_slot_bound`, `app_diff_le_Icc`), the
jet identities of the limit family are `L12FKaux.FKDeriv`/`L12FKaux.L12Deriv`, and the
perturbation of the fake time is controlled by `L12FKaux.L12_tau_lip`-type estimates
(`L12FKaux.L12_limit_bound`, `L12FKaux.QlimSelf`).
-/

namespace Work.FTS_RegExport.RXT.Sys

open Work.FTS.Galerkin (Fn Fam slice)
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS_RegExport.RXT.Sys.L12FKaux

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem L12FK_family_jets {α C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hA : Work.FTS.FinalV2.LimApprox (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
        |Work.Spaces.DzIter j (fun z _ => Work.Construction.FK
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) τ) z) z 0| ≤ C) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ z : ℝ, 0 < z →
        |Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) z| ≤ C) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ z : ℝ, 0 < z →
        Work.Spaces.DzIter 1 (fun z _ => Work.Construction.L12
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z) z 0
          = -(Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z)) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ τ' ∈ Set.Icc (0 : ℝ) T, ∀ z : ℝ, 0 < z →
        |Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z
            - Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ') z| ≤ C * |τ - τ'|) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ τ' ∈ Set.Icc (0 : ℝ) T, ∀ z : ℝ, 0 < z →
        |Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z
            - Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ') z| ≤ C * |τ - τ'|) := by
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- ## the approximating families
  obtain ⟨gn, B, L, hC, hLip, hjet0, -⟩ := hA (max T 1)
    (lt_of_lt_of_le zero_lt_one (le_max_right T 1))
  have hmemT : ∀ τ ∈ Set.Icc (0 : ℝ) T, τ ∈ Set.Icc (0 : ℝ) (max T 1) :=
    fun τ hτ => ⟨hτ.1, le_trans hτ.2 (le_max_left T 1)⟩
  have hcl : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) (slice (gn n) τ) :=
    fun n τ hτ => (hC n τ (hmemT τ hτ)).1
  have hXn : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
        ≤ C₀ * (Work.FTS.Regularity.pExp α) ^ 2 :=
    fun n τ hτ => (hC n τ (hmemT τ hτ)).2.1
  have hXn6 : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      Work.FTS.StrongGlobal.Xn6 (Work.FTS.Regularity.pExp α) (slice (gn n) τ) ≤ B :=
    fun n τ hτ => (hC n τ (hmemT τ hτ)).2.2
  have hlip : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T → ∀ τ' ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4
        (slice (gn n) τ - slice (gn n) τ') ≤ L * |τ - τ'| :=
    fun n τ hτ τ' hτ' => hLip n τ (hmemT τ hτ) τ' (hmemT τ' hτ')
  -- ## the standing bounds on the horizon
  obtain ⟨CwA, hCwA0, hbdA⟩ := approx_slot_bound (C₀ := C₀) hα hα13 hT hcl hXn
  obtain ⟨CB, hCBnn, hCB⟩ := ftau_slot_bound (B := B) hα hα13 hcl hXn6
  obtain ⟨CwD, hCwDnn, hwdA⟩ := app_diff_le_Icc hβ hβ1 hcl hlip
  -- ## the three remaining clauses of the siblings
  obtain ⟨C2, hC2nn, hC2⟩ := L12_limit_bound (α := α) (C₀ := C₀) hα hα13 hA T hT
  obtain ⟨C5, hC5nn, hC5⟩ := Qlim_zero_tau_lip_self (α := α) (C₀ := C₀) hα hα13 hA T hT
  have hC1nn : (0 : ℝ) ≤ 3 * (Real.pi / 2) * CB :=
    mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hCBnn
  have hC4nn : (0 : ℝ) ≤ 3 * (Real.pi / 2) * CwD * 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hCwDnn) (by norm_num)
  refine ⟨max (3 * (Real.pi / 2) * CB) (max C2 (max (3 * (Real.pi / 2) * CwD * 3) C5)),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans hC1nn (le_max_left _ _)
  · -- ## (1) the `z`-jets of `𝔽K F(τ)`
    intro τ hτ j hj z hz
    have hbdτ : ∀ (n : ℕ) (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.DzIter k (slice (gn n) τ) z θ| ≤ CwA * SW z :=
      fun n k hk z θ hz' h0 h1 => hbdA n τ hτ k hk z θ hz' h0 h1
    have h2τ : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ))
        Work.FTS.EllipticEst.Q0 := fun n =>
      (Fstar_contDiffOn hβ hβ1 4).add ((hcl n τ hτ).reg.forall 4)
    have hslτ : ∀ (n : ℕ) (k : ℕ), k ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (gn n) τ) z θ| ≤ CB :=
      fun n k hk z θ hz' h0 h1 => hCB τ hτ n k hk z θ hz' h0 h1
    have hjetτ : ∀ (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
        Filter.Tendsto (fun n => Work.Spaces.DzIter k (slice (gn n) τ) z θ) Filter.atTop
          (𝓝 (Work.Spaces.DzIter k (slice g τ) z θ)) := by
      intro k hk z θ hzθ
      simpa only [Work.Spaces.mixed_zero_right] using
        hjet0 τ (hmemT τ hτ) k 0 (by omega) z θ hzθ
    have e1 := FK_DzIter_eq (α := α) hα hα13 hτ.1 hCwA0 hCBnn
      (fun n => (hcl n τ hτ).reg.forall 4) hbdτ h2τ hslτ hjetτ hz hj
    have e2 := Qlim_bound (α := α) hα hα13 hCwA0 hCBnn
      (fun n => (hcl n τ hτ).reg.forall 4) hbdτ h2τ hslτ hjetτ (k := j) hj hz
    rw [e1]
    exact le_trans e2 (le_max_left _ _)
  · -- ## (2) the uniform bound on `L₁₂ F(τ)`
    intro τ hτ z hz
    exact le_trans (hC2 τ hτ z hz)
      (le_trans (le_max_left _ _) (le_max_right _ _))
  · -- ## (3) `D_z (L₁₂ F(τ)) = -𝔽K F(τ)`
    intro τ hτ z hz
    have hbdτ : ∀ (n : ℕ) (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.DzIter k (slice (gn n) τ) z θ| ≤ CwA * SW z :=
      fun n k hk z θ hz' h0 h1 => hbdA n τ hτ k hk z θ hz' h0 h1
    have hconvτ : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
        Filter.Tendsto (fun n => slice (gn n) τ z θ) Filter.atTop
          (𝓝 (slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ)) := by
      intro z θ hzθ
      have h := hjet0 τ (hmemT τ hτ) 0 0 (by norm_num) z θ hzθ
      have hGR : Work.FTS.RegExportIface.RXT.GR α g z θ τ = g z θ τ :=
        Work.FTS_RegExport.RXT.ftau_GR_of_quad (α := α) (g := g) hτ.1 hzθ.1
          hzθ.2.1.le hzθ.2.2.le
      simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero,
        Work.FTS.Galerkin.slice_apply, hGR] using h
    have hder := L12_hasDerivAt (α := α) hα hα13 hCwA0 (fun n => (hcl n τ hτ).reg.forall 4)
      hbdτ hconvτ hz
    show Work.Spaces.DzIter 1 (fun z _ => Work.Construction.L12 (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z) z 0
      = -(Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) z)
    rw [show Work.Spaces.DzIter 1 (fun z _ => Work.Construction.L12 (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z) z 0
        = z * deriv (fun y => Work.Construction.L12 (Work.Construction.Ftau
            (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) τ) y) z from rfl,
      hder.deriv]
    have hmul := Work.Construction.mul_L12dens_eq_FK
      (F := Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) τ) (z := z) (ne_of_gt hz)
    rw [mul_neg, hmul]
  · -- ## (4) the fake-time Lipschitz bound of `L₁₂ F(τ)`
    intro τ hτ τ' hτ' z hz
    have hconvτ : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
        Filter.Tendsto (fun n => slice (gn n) τ z θ) Filter.atTop
          (𝓝 (slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ)) := by
      intro z θ hzθ
      have h := hjet0 τ (hmemT τ hτ) 0 0 (by norm_num) z θ hzθ
      have hGR : Work.FTS.RegExportIface.RXT.GR α g z θ τ = g z θ τ :=
        Work.FTS_RegExport.RXT.ftau_GR_of_quad (α := α) (g := g) hτ.1 hzθ.1
          hzθ.2.1.le hzθ.2.2.le
      simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero,
        Work.FTS.Galerkin.slice_apply, hGR] using h
    have hconvτ' : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
        Filter.Tendsto (fun n => slice (gn n) τ' z θ) Filter.atTop
          (𝓝 (slice (Work.FTS.RegExportIface.RXT.GR α g) τ' z θ)) := by
      intro z θ hzθ
      have h := hjet0 τ' (hmemT τ' hτ') 0 0 (by norm_num) z θ hzθ
      have hGR : Work.FTS.RegExportIface.RXT.GR α g z θ τ' = g z θ τ' :=
        Work.FTS_RegExport.RXT.ftau_GR_of_quad (α := α) (g := g) hτ'.1 hzθ.1
          hzθ.2.1.le hzθ.2.2.le
      simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero,
        Work.FTS.Galerkin.slice_apply, hGR] using h
    have hlim := (L12_tendsto (β := Work.FTS.Regularity.pExp α) hβ hβ1 hCwA0
        (fun n => (hcl n τ hτ).reg.forall 4)
        (fun n k hk z θ hz' h0 h1 => hbdA n τ hτ k hk z θ hz' h0 h1)
        (h := Work.FTS.RegExportIface.RXT.GR α g) hconvτ hz).sub
      (L12_tendsto (β := Work.FTS.Regularity.pExp α) hβ hβ1 hCwA0
        (fun n => (hcl n τ' hτ').reg.forall 4)
        (fun n k hk z θ hz' h0 h1 => hbdA n τ' hτ' k hk z θ hz' h0 h1)
        (h := Work.FTS.RegExportIface.RXT.GR α g) hconvτ' hz)
    refine le_of_tendsto hlim.abs (Filter.Eventually.of_forall fun n => ?_)
    obtain ⟨hsm, hm, hb⟩ := Work.FTS_RegExport.RXR1.classC_sub_hyp
      (hcl n τ hτ) (hcl n τ' hτ')
    have hdiff : Work.Construction.L12 (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (gn n) τ) z
        - Work.Construction.L12 (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (gn n) τ') z
        = Work.Construction.L12 (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ) z := by
      have h1 := Work.FTS_RegExport.RXT.L12_Fstar_add_c4 (α := Work.FTS.Regularity.pExp α)
        hβ hβ1 (u := slice (gn n) τ) ((hcl n τ hτ).reg.forall 4)
        (Work.FTS.ClassC.classC_hkMem_four (hcl n τ hτ)) hz.le
      have h2 := Work.FTS_RegExport.RXT.L12_Fstar_add_c4 (α := Work.FTS.Regularity.pExp α)
        hβ hβ1 (u := slice (gn n) τ') ((hcl n τ' hτ').reg.forall 4)
        (Work.FTS.ClassC.classC_hkMem_four (hcl n τ' hτ')) hz.le
      have h3 := Work.FTS_RegExport.RXT.STC.L12_sub_C4 (α := Work.FTS.Regularity.pExp α)
        ((hcl n τ hτ).reg.forall 4) ((hcl n τ' hτ').reg.forall 4)
        (Work.FTS.ClassC.classC_hkMem_four (hcl n τ hτ))
        (Work.FTS.ClassC.classC_hkMem_four (hcl n τ' hτ')) z (Set.mem_Ici.mpr hz.le)
      rw [show Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ
          = fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
            + slice (gn n) τ z θ from rfl]
      rw [show Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ'
          = fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
            + slice (gn n) τ' z θ from rfl]
      rw [h1, h2]
      have hL : Work.Construction.L12 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z
            + Work.Construction.L12 (slice (gn n) τ) z
          - (Work.Construction.L12 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z
            + Work.Construction.L12 (slice (gn n) τ') z)
          = Work.Construction.L12 (slice (gn n) τ) z
            - Work.Construction.L12 (slice (gn n) τ') z := by ring
      rw [hL, h3]
    rw [hdiff]
    have hbnd := abs_L12_le_majorant (u := fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ)
      (C0 := CwD * |τ - τ'|) (mul_nonneg hCwDnn (abs_nonneg _))
      (hsm.forall 4)
      (fun k hk z θ hz' h0 h1 => hwdA n τ hτ τ' hτ' k hk z θ hz' h0 h1) hz
    refine le_trans hbnd ?_
    have hval : 3 * (Real.pi / 2) * (CwD * |τ - τ'|) * 3
        = (3 * (Real.pi / 2) * CwD * 3) * |τ - τ'| := by ring
    rw [hval]
    exact mul_le_mul_of_nonneg_right
      (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) (abs_nonneg _)
  · -- ## (5) the fake-time Lipschitz bound of `𝔽K F(τ)`
    intro τ hτ τ' hτ' z hz
    rw [Qlim_eq_FK (α := α) hα hτ.1 hz, Qlim_eq_FK (α := α) hα hτ'.1 hz]
    exact le_trans (hC5 τ hτ τ' hτ' z hz)
      (mul_le_mul_of_nonneg_right
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
        (abs_nonneg _))

end Work.FTS_RegExport.RXT.Sys
