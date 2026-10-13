import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.GalFields.RHS.sharp_LGammaT_diff
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnLGammaT
import Submission.Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS
import Submission.Work.FTS.StrongEps.EpsZero.ClassCHk.LGammaTMem
import Submission.Work.FTS.StrongEps.EpsRLX.RadBound.L12fSlotLe
import Submission.Work.FTS.StrongEps.EpsRLX.RadBound.radA_slot5_le_classC_of

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The `ℋ⁴`-slot bound for the transfer profile `radA`

The two facts about the transfer profile that the sharp bound of `𝓛_Γ^T` on the class `C`
consumes.  `L12fSlotLe` is the `L₁₂`-side slot estimate (a corollary of
`Work.FTS.OpenPkg.l12H_field` + `Work.Elliptic.HkSq_rad`), and `radA_slot5_le_classC_of` is the
`radA`-side one, whose proof needs the Leibniz expansion of `radA α f = −ampA α·L₁₂f +
(ampB α/c)·L₁₂(Transport f)(0)` together with the uniform boundedness of the `D_z`-iterates of
`ampA`, `ampB/c` and of the constant `L₁₂(Transport f)(0)`. -/

/-- **(radial `L₁₂`-slot estimate, order 4.)**  The `L₁₂`-side of the transfer slot bound:
for `HQo α 4 f` with vanishing zero mode, the order-four weighted `D_z`-slot sum of the radial
profile `z ↦ L₁₂(f)(z)` is integrable and bounded by `C·|f|²_{ℋ⁴}`, with `C` independent of
`α ∈ (0,1]` and of `f`. -/
def L12SlotHyp : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ f : Work.FTS.Galerkin.Fn,
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.Construction.L12 f 0 = 0 →
    MeasureTheory.IntegrableOn (fun z : ℝ =>
        ∑ c ∈ Finset.range 5, (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
    (∫ z in Work.Spaces.Iz, ∑ c ∈ Finset.range 5,
        (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
          * (Work.Spaces.w z) ^ 2) ≤ C * Work.Spaces.HkSq α 4 f

/-- **(transfer-slot estimate, order 4.)**  The `radA`-side of the transfer slot bound, derived
from `L12SlotHyp`. -/
def RadASlotHyp : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ f : Work.FTS.Galerkin.Fn,
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.Construction.L12 f 0 = 0 →
    MeasureTheory.IntegrableOn (fun z : ℝ =>
        Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.radA α f) z)
      Work.Spaces.Iz ∧
    (∫ z in Work.Spaces.Iz, Work.FTS.GalFields.Norm.slot5
        (Work.FTS.CoercivityFix.Transfer.radA α f) z) ≤ C * Work.Spaces.HkSq α 4 f

/-! ## The sharp `ℋ⁴`-bound of `𝓛_Γ^T` on the class `C`

`𝓛_Γ^T = 𝓛̂ + Corr` (`CoercivityFix.LGammaT_eq_Lhat_add_Corr`).  The clean part is
`HkSq_Lhat_le_uniform`, and the transfer defect `Corr α h = Γ(θ)·radA α h z` is handled by the
separated pointwise majorant `HkIntegrand_Corr_le` (`HkSq_Corr_le_classC`) together with the
radial slot bound `RadASlotHyp`. -/

private theorem lgtProfile (hrad : RadASlotHyp) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {h : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α h →
      Work.Spaces.HkSq α 4 (Work.Coercivity.LGammaT α h) ≤ K * Work.Spaces.HkSq α 5 h := by
  obtain ⟨Cl, hClpos, hL⟩ := Work.FTS.GalFields.Norm.HkSq_Lhat_le_uniform
  obtain ⟨Kang, hKangpos, hang⟩ := Work.FTS.GalFields.Norm.ang_fac_integrable_bound
  obtain ⟨Crad, hCradpos, hradspec⟩ := hrad
  refine ⟨2 * Cl + 2 * (Kang * Crad) + 1, by positivity, ?_⟩
  intro α hαIoc h hC
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have h5 : Work.Spaces.HkMem α 5 h :=
    Work.FTS.OpenPkg.HkMem_mono_open hC.reg 5 (by norm_num) hC.mem
  have h4 : Work.Spaces.HkMem α 4 h :=
    Work.FTS.OpenPkg.HkMem_mono_open hC.reg 4 (by norm_num) hC.mem
  -- ## the clean part `𝓛̂ h`
  have hLhat_mem : Work.Spaces.HkMem α 4 (Work.FTS.CoercivityFix.Lhat h) :=
    Work.FTS.StrongPersist.H6Aux.Lhat_mem α hα 4 hC.reg h5
  have hLhat_bd : Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Lhat h)
      ≤ Cl * Work.Spaces.HkSq α 5 h := hL α hα h hC.reg h5
  have hLhat_sm : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.CoercivityFix.Lhat h))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.StrongPersist.H6Aux.smoothOpen_Lhat hC.reg).forall 4
  -- ## the transfer defect `Corr α h`
  have hCorr_mem : Work.Spaces.HkMem α 4 (Work.FTS.CoercivityFix.Corr α h) :=
    Work.FTS.StrongEps.EpsZero.ClassCHk.HkMem_Corr_of_classC hα hα1 hC
  have hCorr_sm : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.CoercivityFix.Corr α h))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.GalFields.Norm.radA_Corr_contDiffOn_four hα hα1 hC.reg h5).2
  obtain ⟨hslot_int, hslot_bd⟩ := hradspec α hαIoc h hC.reg h4 hC.l12
  have hCorr_bd : Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Corr α h)
      ≤ Kang * (Crad * Work.Spaces.HkSq α 4 h) :=
    (Work.FTS.StrongEps.ClassCRHS.HkSq_Corr_le_classC hα hα1 hKangpos
      (hang α hα hα1) hslot_int).trans (mul_le_mul_of_nonneg_left hslot_bd hKangpos.le)
  -- ## the sum
  have hLGT_mem : Work.Spaces.HkMem α 4 (Work.FTS.CoercivityFix.Lhat h
      + Work.FTS.CoercivityFix.Corr α h) :=
    Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four hLhat_sm hCorr_sm hLhat_mem hCorr_mem
  have hpt_add : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (Work.FTS.CoercivityFix.Lhat h
          + Work.FTS.CoercivityFix.Corr α h) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α 4 (Work.FTS.CoercivityFix.Lhat h) z θ
          + 2 * Work.Spaces.HkIntegrand α 4 (Work.FTS.CoercivityFix.Corr α h) z θ :=
    fun z hz θ hθ =>
      Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α 4
        (f := Work.FTS.CoercivityFix.Lhat h) (g := Work.FTS.CoercivityFix.Corr α h)
        hLhat_sm hCorr_sm z hz θ hθ
  have hsum : Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Lhat h
        + Work.FTS.CoercivityFix.Corr α h)
      ≤ 2 * Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Lhat h)
        + 2 * Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Corr α h) :=
    Work.FTS.CoercivityFix.Transfer.E2norm.HkSq_add_le α 4 hLhat_mem hCorr_mem hLGT_mem hpt_add
  have hmono : Work.Spaces.HkSq α 4 h ≤ Work.Spaces.HkSq α 5 h :=
    Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) h5
  have h5nn : 0 ≤ Work.Spaces.HkSq α 5 h := Work.Spaces.HkSq_nonneg α 5 h
  have hstep : 2 * (Cl * Work.Spaces.HkSq α 5 h) + 2 * (Kang * (Crad * Work.Spaces.HkSq α 4 h))
      ≤ (2 * Cl + 2 * (Kang * Crad)) * Work.Spaces.HkSq α 5 h := by
    have hKC : 0 ≤ 2 * (Kang * Crad) := by positivity
    calc 2 * (Cl * Work.Spaces.HkSq α 5 h) + 2 * (Kang * (Crad * Work.Spaces.HkSq α 4 h))
        = (2 * Cl) * Work.Spaces.HkSq α 5 h
          + (2 * (Kang * Crad)) * Work.Spaces.HkSq α 4 h := by ring
      _ ≤ (2 * Cl) * Work.Spaces.HkSq α 5 h
          + (2 * (Kang * Crad)) * Work.Spaces.HkSq α 5 h :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hmono hKC)
      _ = (2 * Cl + 2 * (Kang * Crad)) * Work.Spaces.HkSq α 5 h := by ring
  have hmain : Work.Spaces.HkSq α 4 (Work.Coercivity.LGammaT α h)
      ≤ (2 * Cl + 2 * (Kang * Crad)) * Work.Spaces.HkSq α 5 h := by
    rw [Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr α h]
    calc Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Lhat h
            + Work.FTS.CoercivityFix.Corr α h)
        ≤ 2 * Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Lhat h)
          + 2 * Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Corr α h) := hsum
      _ ≤ 2 * (Cl * Work.Spaces.HkSq α 5 h) + 2 * (Kang * (Crad * Work.Spaces.HkSq α 4 h)) :=
          add_le_add (mul_le_mul_of_nonneg_left hLhat_bd (by norm_num))
            (mul_le_mul_of_nonneg_left hCorr_bd (by norm_num))
      _ ≤ (2 * Cl + 2 * (Kang * Crad)) * Work.Spaces.HkSq α 5 h := hstep
  exact hmain.trans (mul_le_mul_of_nonneg_right (by linarith) h5nn)

/-! ## The difference statement

`𝓛_Γ^T` is linear on the open quadrant (`sharp_LGammaT_diff_eqOn`), so the difference of the two
values is `𝓛_Γ^T` of the difference, and all three clauses transfer along the pointwise identity
(`smoothOpen_of_eqOn`-style congruence, `HkMem_congr_Q0`, `HkSq_congr_open`). -/

private theorem lgtDiff_assembly (hrad : RadASlotHyp) :
    ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 →
      ∃ K : ℝ, 0 < K ∧ ∀ {W₁ W₂ : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α W₁ → Work.FTS.ClassC.ClassC α W₂ →
      Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
        Work.Coercivity.LGammaT α W₁ z θ - Work.Coercivity.LGammaT α W₂ z θ) ∧
      Work.Spaces.HkMem α 4 (fun z θ =>
        Work.Coercivity.LGammaT α W₁ z θ - Work.Coercivity.LGammaT α W₂ z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ =>
        Work.Coercivity.LGammaT α W₁ z θ - Work.Coercivity.LGammaT α W₂ z θ)
        ≤ K * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
  intro α hαIoc
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  obtain ⟨Kp, hKppos, hprof⟩ := lgtProfile hrad
  refine ⟨Real.sqrt Kp + 1, by positivity, ?_⟩
  intro W₁ W₂ hW₁ hW₂
  have h4₁ : Work.Spaces.HkMem α 4 W₁ :=
    Work.FTS.OpenPkg.HkMem_mono_open hW₁.reg 4 (by norm_num) hW₁.mem
  have h4₂ : Work.Spaces.HkMem α 4 W₂ :=
    Work.FTS.OpenPkg.HkMem_mono_open hW₂.reg 4 (by norm_num) hW₂.mem
  -- the pointwise identity on the open quadrant
  have hid : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Coercivity.LGammaT α W₁ z θ - Work.Coercivity.LGammaT α W₂ z θ
        = Work.Coercivity.LGammaT α (fun z θ => W₁ z θ - W₂ z θ) z θ :=
    fun z θ hz hθ0 hθ1 =>
      Work.FTS.GalFields.RHS.sharp_LGammaT_diff_eqOn hα hα1 hW₁.reg hW₂.reg h4₁ h4₂
        z θ hz hθ0 hθ1
  have hhC : Work.FTS.ClassC.ClassC α (fun z θ => W₁ z θ - W₂ z θ) :=
    Work.FTS.StrongEps.EComparison.classC_sub hW₁ hW₂
  -- the two `𝓛_Γ^T Wᵢ` are `C^∞` on the open quadrant
  have hsm₁ : Work.FTS.EllipticEst.SmoothOpen (Work.Coercivity.LGammaT α W₁) :=
    Work.FTS.GalFields.RHS.smoothOpen_LGammaT_of_L12
      (Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα hW₁) hW₁.reg
  have hsm₂ : Work.FTS.EllipticEst.SmoothOpen (Work.Coercivity.LGammaT α W₂) :=
    Work.FTS.GalFields.RHS.smoothOpen_LGammaT_of_L12
      (Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα hW₂) hW₂.reg
  -- the `ℋ⁴`-honesty of `𝓛_Γ^T (W₁ − W₂)`
  have h5h : Work.Spaces.HkMem α 5 (fun z θ => W₁ z θ - W₂ z θ) :=
    Work.FTS.OpenPkg.HkMem_mono_open hhC.reg 5 (by norm_num) hhC.mem
  have hLhat_sm : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.CoercivityFix.Lhat
      (fun z θ => W₁ z θ - W₂ z θ))) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.StrongPersist.H6Aux.smoothOpen_Lhat hhC.reg).forall 4
  have hCorr_sm : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.CoercivityFix.Corr α
      (fun z θ => W₁ z θ - W₂ z θ))) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.GalFields.Norm.radA_Corr_contDiffOn_four hα hα1 hhC.reg h5h).2
  have hLhat_mem : Work.Spaces.HkMem α 4 (Work.FTS.CoercivityFix.Lhat
      (fun z θ => W₁ z θ - W₂ z θ)) :=
    Work.FTS.StrongPersist.H6Aux.Lhat_mem α hα 4 hhC.reg h5h
  have hCorr_mem : Work.Spaces.HkMem α 4 (Work.FTS.CoercivityFix.Corr α
      (fun z θ => W₁ z θ - W₂ z θ)) :=
    Work.FTS.StrongEps.EpsZero.ClassCHk.HkMem_Corr_of_classC hα hα1 hhC
  have hmemh : Work.Spaces.HkMem α 4 (Work.Coercivity.LGammaT α
      (fun z θ => W₁ z θ - W₂ z θ)) := by
    rw [Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr α (fun z θ => W₁ z θ - W₂ z θ)]
    exact Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four hLhat_sm hCorr_sm hLhat_mem hCorr_mem
  -- the sharp profile bound for the difference
  have hb : Work.Spaces.HkSq α 4 (Work.Coercivity.LGammaT α
      (fun z θ => W₁ z θ - W₂ z θ)) ≤ Kp * Work.Spaces.HkSq α 5
        (fun z θ => W₁ z θ - W₂ z θ) := hprof hαIoc hhC
  have hsq : Work.Spaces.HkSq α 4 (fun z θ =>
        Work.Coercivity.LGammaT α W₁ z θ - Work.Coercivity.LGammaT α W₂ z θ)
      = Work.Spaces.HkSq α 4 (Work.Coercivity.LGammaT α
        (fun z θ => W₁ z θ - W₂ z θ)) :=
    Work.FTS.EllipticEst.HkSq_congr_open α 4 (fun z θ hz hθ0 hθ1 => hid z θ hz hθ0 hθ1)
  refine ⟨?_, ?_, ?_⟩
  · -- conjunct 1: open-quadrant smoothness
    exact Work.FTS.NonlinRows.smoothOpen_sub hsm₁ hsm₂
  · -- conjunct 2: `ℋ⁴`-honesty, transported along the identity
    exact Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hmemh
      (fun z hz θ hθ => (hid z θ hz hθ.1 hθ.2).symm)
  · -- conjunct 3: the `Xn`-bound
    have hKpnn : 0 ≤ Kp := hKppos.le
    have h5nn : 0 ≤ Work.Spaces.HkSq α 5 (fun z θ => W₁ z θ - W₂ z θ) :=
      Work.Spaces.HkSq_nonneg α 5 _
    have hXnb : Work.FTS.Nonlin.Xn α (Work.Coercivity.LGammaT α
          (fun z θ => W₁ z θ - W₂ z θ)) ≤ Real.sqrt Kp * Work.FTS.GalFields.Xn5 α
            (fun z θ => W₁ z θ - W₂ z θ) := by
      show Real.sqrt (Work.Spaces.HkSq α 4 (Work.Coercivity.LGammaT α
            (fun z θ => W₁ z θ - W₂ z θ)))
          ≤ Real.sqrt Kp * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)
      calc Real.sqrt (Work.Spaces.HkSq α 4 (Work.Coercivity.LGammaT α
              (fun z θ => W₁ z θ - W₂ z θ)))
          ≤ Real.sqrt (Kp * Work.Spaces.HkSq α 5 (fun z θ => W₁ z θ - W₂ z θ)) :=
            Real.sqrt_le_sqrt hb
        _ = Real.sqrt Kp * Real.sqrt (Work.Spaces.HkSq α 5 (fun z θ => W₁ z θ - W₂ z θ)) :=
            Real.sqrt_mul hKpnn _
        _ = Real.sqrt Kp * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := rfl
    have hXnEq : Work.FTS.Nonlin.Xn α (fun z θ =>
          Work.Coercivity.LGammaT α W₁ z θ - Work.Coercivity.LGammaT α W₂ z θ)
        = Work.FTS.Nonlin.Xn α (Work.Coercivity.LGammaT α
          (fun z θ => W₁ z θ - W₂ z θ)) := by
      show Real.sqrt (Work.Spaces.HkSq α 4 _) = Real.sqrt (Work.Spaces.HkSq α 4 _)
      rw [hsq]
    rw [hXnEq]
    calc Work.FTS.Nonlin.Xn α (Work.Coercivity.LGammaT α (fun z θ => W₁ z θ - W₂ z θ))
        ≤ Real.sqrt Kp * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := hXnb
      _ ≤ (Real.sqrt Kp + 1) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
          have h0 : 0 ≤ Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) :=
            Work.Spaces.HkNorm_nonneg α 5 _
          linarith [mul_nonneg (Real.sqrt_nonneg Kp) h0]

theorem LGTDiffClassC {α : ℝ} (hα : α ∈ Set.Ioc 0 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ {W₁ W₂ : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α W₁ → Work.FTS.ClassC.ClassC α W₂ →
      Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
        Work.Coercivity.LGammaT α W₁ z θ - Work.Coercivity.LGammaT α W₂ z θ) ∧
      Work.Spaces.HkMem α 4 (fun z θ =>
        Work.Coercivity.LGammaT α W₁ z θ - Work.Coercivity.LGammaT α W₂ z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ =>
        Work.Coercivity.LGammaT α W₁ z θ - Work.Coercivity.LGammaT α W₂ z θ)
        ≤ K * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) :=
  lgtDiff_assembly (RadBound.radA_slot5_le_classC_of RadBound.L12fSlotLe) hα

end Work.FTS.StrongEps.EpsRLX
