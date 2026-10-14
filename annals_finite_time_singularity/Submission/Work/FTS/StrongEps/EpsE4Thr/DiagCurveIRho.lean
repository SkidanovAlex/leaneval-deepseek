import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongEps.EpsE4Thr.EnergyDiagAssembly
import Submission.Work.FTS.StrongEps.EpsE4Thr.WipEqIntegral
import Submission.Work.FTS.StrongEps.EpsZero.ClassCHk.LGammaTMem
import Submission.Work.FTS.StrongEps.EpsZero.ClassCHk.SlotSumRadAOpen
import Submission.Work.FTS.StrongPersist.H6Aux.RadialAsm
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBound
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.Spaces.SmoothCompact_HkMem
-- ===== merged: Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnLGammaT =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.ClassCRHS

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

/-- **The `ℋ⁴`-energy of the transfer part is controlled by the radial slot sum of `radA`.**

This is the `ClassC`-flavoured form of the `Corr`-half of `GalFields.Norm.HkSq_Corr_le`: the
pointwise separation `GalFields.Norm.HkIntegrand_Corr_le` (`Corr α w = Γ(θ)·radA α w z`) is
integrated against the `α`-uniformly bounded angular factor `afac4 α`. -/
theorem HkSq_Corr_le_classC {α Kang : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hKang : 0 < Kang)
    (hang : MeasureTheory.IntegrableOn (Work.FTS.GalFields.Norm.afac4 α) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, Work.FTS.GalFields.Norm.afac4 α θ) ≤ Kang)
    {w : Work.FTS.Galerkin.Fn}
    (hslot : MeasureTheory.IntegrableOn
      (fun z : ℝ => Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.radA α w) z)
      Work.Spaces.Iz) :
    Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Corr α w)
      ≤ Kang * (∫ z in Work.Spaces.Iz,
          Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.radA α w) z) := by
  obtain ⟨hafInt, hafBd⟩ := hang
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (Work.FTS.CoercivityFix.Corr α w) z θ
        ≤ Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.radA α w) z
          * Work.FTS.GalFields.Norm.afac4 α θ :=
    fun _ _ θ hθ => Work.FTS.GalFields.Norm.HkIntegrand_Corr_le hα hα1 w hθ
  have hMslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.radA α w) z
        * Work.FTS.GalFields.Norm.afac4 α θ) Work.Spaces.Iθ :=
    fun z _ => hafInt.const_mul _
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 (Work.FTS.CoercivityFix.Corr α w) z θ)
        ≤ Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.radA α w) z * Kang := by
    intro z hz
    have h1 := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 4 (Work.FTS.CoercivityFix.Corr α w) z θ)
      (hMslice z hz)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hpt z hz θ hθ))
    rw [MeasureTheory.integral_const_mul] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hafBd
      (Work.FTS.GalFields.Norm.slot5_nonneg _ z))
  have houter : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (Work.FTS.CoercivityFix.Corr α w) z θ)
      ≤ Kang * (∫ z in Work.Spaces.Iz,
          Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.radA α w) z) := by
    have hInt : MeasureTheory.IntegrableOn
        (fun z => Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.radA α w) z
          * Kang) Work.Spaces.Iz := hslot.mul_const Kang
    have h1 := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 4 (Work.FTS.CoercivityFix.Corr α w) z θ)
      hInt
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hinner z hz))
    rw [MeasureTheory.integral_mul_const] at h1
    exact h1.trans_eq (by ring)
  exact houter

/-- **The linear part `𝓛_Γ^T w` of the scheme's right-hand side is `ℋ⁴`-honest and bounded, for
`ClassC` data of small `ℋ⁴`-size and bounded `ℋ⁶`-size.**

This is the open-class (`ClassC`, i.e. `SmoothOpen`) counterpart of the `GalClass`-based
`Work.FTS.GalFields.Norm.Xn_LGammaT_le`; `SmoothQuad`/`CoerAdm` are **not** derivable from
`ClassC α w`, so the argument must be redone.

Route hints.  With `L12f = Work.Coercivity.L12f`, `Transport f = 3·Dth f/(1+z)`,
`Proj α f = f - (Γ/c)·(2z²/(1+z)³)·L12f f 0`, `LGammaT α w` expands to
`L w - (2zΓ/(c(1+z)²))·L12f w - Transport w + (Γ/c)(2z²/(1+z)³)·L12f (Transport w) 0`, and each
summand is an `ℋ⁴`-bounded combination of the atoms

* `w` (smallness `Xn α w ≤ C₀α²`) and `Dz w` (`Work.FTS.GalFields.Xn_Dz_le_Xn5`, `≤ Xn5 α w ≤ B`);
* `L12f w`: `Work.FTS.OpenPkg.l12H_field` with `HQo α 4 w` and `L12 w 0 = 0` (both from `hw`);
* `Dth w` (`Work.FTS.GalFields.Xn_Dth_le_Xn5`) and the fixed smooth bounded coefficients
  `Γ(θ)`, `c`, `2z/(1+z)²`, `2z²/(1+z)³`, `1/(1+z)` (use `Work.FTS.OpenPkg.prod_field` for the
  products, `Work.FTS.GalFields.RHS.HkNorm_add_le_open` for the sums);
* the scalar `L12f (Transport w) 0`: `Work.FTS.OpenPkg.l12zero_field` applied to
  `Transport w = 3·Dth w/(1+z)` (an `HQo α 4` profile), so it is bounded by `Ci·Xn α (Transport w)`.

`K` may depend on `α, C₀, B` but **not** on `w`. -/
theorem HkMemXnLGammaT : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B : ℝ},
    ∃ K : ℝ, 0 < K ∧ ∀ {w : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      Work.Spaces.HkNorm α 6 w ≤ B →
      Work.Spaces.HkMem α 4 (Work.Coercivity.LGammaT α w) ∧
      Work.FTS.Nonlin.Xn α (Work.Coercivity.LGammaT α w) ≤ K := by
  intro α hαI C₀ B
  have hα : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  -- ## the constants of the three block estimates
  obtain ⟨Cl, hClpos, hLhatbd⟩ := Work.FTS.GalFields.Norm.HkSq_Lhat_le_uniform
  obtain ⟨Kang, hKangpos, hang⟩ := Work.FTS.GalFields.Norm.ang_fac_integrable_bound
  obtain ⟨CS, hCSpos, hSlotSum⟩ := Work.FTS.StrongEps.EpsZero.ClassCHk.SlotSumRadAOpen
  set M : ℝ := max B 0 with hMdef
  have hMnn : 0 ≤ M := le_max_right _ _
  refine ⟨Real.sqrt (2 * (Cl * M ^ 2 + Kang * (CS * M ^ 2))) + 1, by positivity, ?_⟩
  intro w hw _hsmall hB
  -- ## the `ℋ⁵`/`ℋ⁶`-honesty of the datum and the two bounds on its energy
  have hmem5 : Work.Spaces.HkMem α 5 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 5 (by norm_num) hw.mem
  have hmem6 : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 6 (by norm_num) hw.mem
  have hN6 : Work.Spaces.HkNorm α 6 w ≤ M := le_trans hB (le_max_left _ _)
  have hSq6 : Work.Spaces.HkSq α 6 w ≤ M ^ 2 := by
    have hs : Work.Spaces.HkSq α 6 w = (Work.Spaces.HkNorm α 6 w) ^ 2 := by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 w)]
    rw [hs]
    exact pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 6 w) hN6 2
  have hSq5 : Work.Spaces.HkSq α 5 w ≤ M ^ 2 :=
    le_trans (Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hmem6) hSq6
  -- ## the two summands of `𝓛_Γ^T = 𝓛̂ + Corr`
  have hLhatmem : Work.Spaces.HkMem α 4 (Work.FTS.CoercivityFix.Lhat w) :=
    Work.FTS.StrongPersist.H6Aux.Lhat_mem α hα 4 hw.reg hmem5
  have hCorrmem : Work.Spaces.HkMem α 4 (Work.FTS.CoercivityFix.Corr α w) :=
    Work.FTS.StrongEps.EpsZero.ClassCHk.HkMem_Corr_of_classC hα hα1 hw
  have hLhatsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.CoercivityFix.Lhat w) :=
    Work.FTS.StrongPersist.H6Aux.smoothOpen_Lhat hw.reg
  have hLGTsm : Work.FTS.EllipticEst.SmoothOpen (Work.Coercivity.LGammaT α w) :=
    Work.FTS.GalFields.RHS.smoothOpen_LGammaT_of_L12
      (Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα hw) hw.reg
  have hCorrsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.CoercivityFix.Corr α w) :=
    Work.FTS.NonlinRows.smoothOpen_sub hLGTsm hLhatsm
  -- ## the membership
  have hLGmem : Work.Spaces.HkMem α 4 (Work.Coercivity.LGammaT α w) := by
    rw [Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr α w]
    exact Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four (hLhatsm.forall 4) (hCorrsm.forall 4)
      hLhatmem hCorrmem
  -- ## the two norm bounds
  have hLhatSq : Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Lhat w) ≤ Cl * M ^ 2 :=
    le_trans (hLhatbd α hα w hw.reg hmem5) (mul_le_mul_of_nonneg_left hSq5 hClpos.le)
  have hCorrSq : Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Corr α w) ≤ Kang * (CS * M ^ 2) := by
    obtain ⟨hSSint, hSSbd⟩ := hSlotSum α hαI w hw.reg hw.mem hw.l12
    have hslot : MeasureTheory.IntegrableOn
        (fun z : ℝ => Work.FTS.GalFields.Norm.slot5
          (Work.FTS.CoercivityFix.Transfer.radA α w) z) Work.Spaces.Iz :=
      Work.FTS.StrongEps.EpsZero.ClassCHk.integrableOn_slot5_radA_of_classC hα hα1 hw
    have hslotBd : (∫ z in Work.Spaces.Iz,
          Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.radA α w) z)
        ≤ CS * M ^ 2 := by
      have h1 : (∫ z in Work.Spaces.Iz,
            Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.radA α w) z)
          ≤ ∫ z in Work.Spaces.Iz,
              Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α w) z :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun z =>
            Work.FTS.GalFields.Norm.slot5_nonneg _ z) hSSint
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
            (fun _ _ => Work.FTS.StrongEps.EpsZero.ClassCHk.slot5_le_SlotSum _ _))
      exact h1.trans (hSSbd.trans (mul_le_mul_of_nonneg_left hSq6 hCSpos.le))
    exact (HkSq_Corr_le_classC hα hα1 hKangpos (hang α hα hα1) hslot).trans
      (mul_le_mul_of_nonneg_left hslotBd hKangpos.le)
  -- ## the assembly
  have hSqLG : Work.Spaces.HkSq α 4 (Work.Coercivity.LGammaT α w)
      ≤ 2 * (Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Lhat w)
        + Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Corr α w)) := by
    rw [Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr α w]
    exact Work.FTS.GalFields.RHS.HkSq_add_le_open α 4 hα hLhatsm hCorrsm hLhatmem hCorrmem
  have hfinal : Work.Spaces.HkSq α 4 (Work.Coercivity.LGammaT α w)
      ≤ 2 * (Cl * M ^ 2 + Kang * (CS * M ^ 2)) := by
    linarith [hSqLG, hLhatSq, hCorrSq]
  refine ⟨hLGmem, ?_⟩
  calc Work.FTS.Nonlin.Xn α (Work.Coercivity.LGammaT α w)
      = Real.sqrt (Work.Spaces.HkSq α 4 (Work.Coercivity.LGammaT α w)) := rfl
    _ ≤ Real.sqrt (2 * (Cl * M ^ 2 + Kang * (CS * M ^ 2))) := Real.sqrt_le_sqrt hfinal
    _ ≤ Real.sqrt (2 * (Cl * M ^ 2 + Kang * (CS * M ^ 2))) + 1 :=
        le_add_of_nonneg_right zero_le_one

end

end Work.FTS.StrongEps.ClassCRHS
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.DiagCurveIRho =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false



end Work.FTS.StrongEps.EpsE4Thr
end
end
