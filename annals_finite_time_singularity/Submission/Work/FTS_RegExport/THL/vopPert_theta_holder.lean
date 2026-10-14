import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Open.Row25Aux
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgEngine
import Submission.Work.FTS.OpenPkg.prod_field
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS.StrongEps.SupPort.classC_sup_le
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsRadAux.aestronglyMeasurable_slotSum
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_RegExport.RXA1w.Helpers
import Submission.Work.FTS_RegExport.RXB.l12_aux
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Slots.v2_paramC2
import Submission.Work.FTS_RegExport.RXT.Slots.v2_velPert
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_RegExport.RXT.st1_stdata
import Submission.Work.FTS_RegExport.RXT.velPert
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_RegExport.THL.angular_L2_noTrace
import Submission.Work.FTS_RegExport.THL.theta_holder_of_HkMem
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
-- ===== merged: Submission.Work.FTS.StrongEps.ClassCRHS.FtotMoments =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.ClassCRHS


end Work.FTS.StrongEps.ClassCRHS
end
-- ===== merged: Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnNAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.ClassCRHS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! ## The two product-rule wrappers -/

/-- **Product of two `ℋ⁴`-honest factors with a scalar.** -/
theorem mulHQo {α Cprod : ℝ} (hα : 0 < α) (hCprod : 0 < Cprod)
    (hfield : ∀ f g : Fn, Work.FTS.VocabO.HQo α 4 f → Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Cprod * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g)
    {C G : Fn} {c a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hC : Work.FTS.VocabO.HQo α 4 C) (hG : Work.FTS.VocabO.HQo α 4 G)
    (hCa : Work.FTS.Nonlin.Xn α C ≤ a) (hGb : Work.FTS.Nonlin.Xn α G ≤ b) :
    Work.Spaces.HkMem α 4 (fun z θ => c * (C z θ * G z θ)) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => c * (C z θ * G z θ))
        ≤ |c| * Cprod * α ^ (-(1 / 2 : ℝ)) * a * b := by
  obtain ⟨hm, hbnd⟩ := hfield C G hC hG
  have hAr : 0 ≤ Cprod * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hCprod.le (Real.rpow_nonneg hα.le _)
  have hXnC : 0 ≤ Work.FTS.Nonlin.Xn α C := Real.sqrt_nonneg _
  have hXnG : 0 ≤ Work.FTS.Nonlin.Xn α G := Real.sqrt_nonneg _
  refine ⟨Work.FTS.LocData.HkMem_const_mul α 4 c hm, ?_⟩
  rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul α c (fun z θ => C z θ * G z θ)]
  calc |c| * Work.FTS.Nonlin.Xn α (fun z θ => C z θ * G z θ)
      ≤ |c| * (Cprod * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α C * Work.FTS.Nonlin.Xn α G) :=
        mul_le_mul_of_nonneg_left hbnd (abs_nonneg c)
    _ ≤ |c| * (Cprod * α ^ (-(1 / 2 : ℝ)) * a * b) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)
        calc Cprod * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α C * Work.FTS.Nonlin.Xn α G
            ≤ Cprod * α ^ (-(1 / 2 : ℝ)) * a * Work.FTS.Nonlin.Xn α G :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCa hAr) hXnG
          _ ≤ Cprod * α ^ (-(1 / 2 : ℝ)) * a * b :=
              mul_le_mul_of_nonneg_left hGb (mul_nonneg hAr ha)
    _ = |c| * Cprod * α ^ (-(1 / 2 : ℝ)) * a * b := by ring

/-- **Product of a `𝒲^{4,∞}`-factor with an `ℋ⁴`-honest factor, with a scalar.** -/
theorem mulW {α Cw : ℝ} (hα : 0 < α) (hCw : 0 < Cw)
    (hfield : ∀ f g : Fn, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 4 f →
      Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Cw * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g)
    {F G : Fn} {c a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hFs : Work.FTS.EllipticEst.SmoothOpen F) (hFm : Work.Spaces.WlInfMem α 4 F)
    (hFa : Work.Spaces.WlInf α 4 F ≤ a)
    (hG : Work.FTS.VocabO.HQo α 4 G) (hGb : Work.FTS.Nonlin.Xn α G ≤ b) :
    Work.Spaces.HkMem α 4 (fun z θ => c * (F z θ * G z θ)) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => c * (F z θ * G z θ))
        ≤ |c| * Cw * α ^ (-(1 / 2 : ℝ)) * a * b := by
  obtain ⟨hm, hbnd⟩ := hfield F G hFs hFm hG
  have hAr : 0 ≤ Cw * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hCw.le (Real.rpow_nonneg hα.le _)
  have hWnn : 0 ≤ Work.Spaces.WlInf α 4 F := Work.Spaces.WlInf_nonneg α 4 F hFm
  have hXnG : 0 ≤ Work.FTS.Nonlin.Xn α G := Real.sqrt_nonneg _
  refine ⟨Work.FTS.LocData.HkMem_const_mul α 4 c hm, ?_⟩
  rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul α c (fun z θ => F z θ * G z θ)]
  calc |c| * Work.FTS.Nonlin.Xn α (fun z θ => F z θ * G z θ)
      ≤ |c| * (Cw * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 F * Work.FTS.Nonlin.Xn α G) :=
        mul_le_mul_of_nonneg_left hbnd (abs_nonneg c)
    _ ≤ |c| * (Cw * α ^ (-(1 / 2 : ℝ)) * a * b) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)
        calc Cw * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 F * Work.FTS.Nonlin.Xn α G
            ≤ Cw * α ^ (-(1 / 2 : ℝ)) * a * Work.FTS.Nonlin.Xn α G :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hFa hAr) hXnG
          _ ≤ Cw * α ^ (-(1 / 2 : ℝ)) * a * b :=
              mul_le_mul_of_nonneg_left hGb (mul_nonneg hAr ha)
    _ = |c| * Cw * α ^ (-(1 / 2 : ℝ)) * a * b := by ring

/-! ## Generic smoothness atoms -/

theorem smoothOpen_zdiv : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (1 + z)) := by
  refine Work.FTS.NonlinRows.smoothOpen_radial (r := fun z : ℝ => z / (1 + z)) ?_
  intro n
  refine ContDiffOn.div contDiffOn_id (contDiffOn_const.add contDiffOn_id) ?_
  intro z hz
  have hz' : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
  positivity

theorem smoothOpen_phi_mul {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z / (1 + z) * f z θ) :=
  Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl smoothOpen_zdiv hf

theorem smoothOpen_FKw_of_classC {α : ℝ} {w : Fn} (hw : Work.FTS.ClassC.ClassC α w) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK w z) := by
  have hr : ∀ n : ℕ, ContDiffOn ℝ n (fun z : ℝ => 3 * Work.Elliptic.Fstar w z)
      (Set.Ioi 0) := fun n => contDiffOn_const.mul (hw.fsm n)
  have hmain := Work.FTS.NonlinRows.smoothOpen_radial
    (r := fun z : ℝ => 3 * Work.Elliptic.Fstar w z) hr
  refine hmain.congr ?_
  rintro z θ _ _ _
  exact (Work.FTS_RegExport.RXT.velPert_FK_eq w z).symm

theorem smoothOpen_FKneg (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => (-(2 * α)) * Work.Spaces.hKer z) := by
  refine Work.FTS.NonlinRows.smoothOpen_radial
    (r := fun z : ℝ => (-(2 * α)) * Work.Spaces.hKer z) ?_
  intro n
  have hker : ContDiffOn ℝ n (fun z : ℝ => Work.Spaces.hKer z) (Set.Ioi 0) := by
    simp only [Work.Spaces.hKer_apply]
    refine ContDiffOn.div contDiffOn_id ((contDiffOn_const.add contDiffOn_id).pow 2) ?_
    intro z hz
    have hz' : (0 : ℝ) < z := hz
    positivity
  exact contDiffOn_const.mul hker

theorem smoothOpen_Rs_of_star {α Cs : ℝ} {Φs : Fn} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hsw : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) :=
  Work.FTS.NonlinRows.NRow10aux.starH_smoothOpen hα0 hα1 hsw

theorem smoothOpen_Us_of_star {α Cs : ℝ} {Φs : Fn} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hsw : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z *
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ)) :=
  Work.FTS.NonlinRows.NRow10aux.smoothOpen_mul
    Work.FTS.NonlinRows.NRow10aux.smoothOpen_zPlusOne_div_z
    (Work.FTS.EllipticEst.RPFresh.smoothOpen_div_sin
      (Work.FTS.EllipticEst.smoothOpen_Uop
        (Work.FTS.NonlinRows.NRow10aux.smoothOpen_PhiTs hα0 hα1 hsw)))

theorem smoothOpen_Vs_of_star {α Cs : ℝ} {Φs : Fn} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hsw : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ) :=
  Work.FTS.NonlinRows.NRow10aux.smoothOpen_mul
    Work.FTS.NonlinRows.NRow10aux.smoothOpen_zPlusOne_div_z
    (Work.FTS.StrongEps.EComparison.smoothOpen_Vop
      (Work.FTS.NonlinRows.NRow10aux.smoothOpen_PhiTs hα0 hα1 hsw))

/-! ## Generic bound atoms

The three coefficients of `EllPkgGo` (paired with `F_*` or with `w`) are bounded by
`max Ce 0 · max C₀ 0 · α²` on the smallness ball. -/

theorem Xn_Rop_le {α C₀ Ce : ℝ} {w Φg : Fn} (hw : Work.FTS.ClassC.ClassC α w)
    (hell : Work.FTS.VocabO.EllPkgGo α Ce w Φg) (hXw : Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2) :
    Work.FTS.Nonlin.Xn α (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg))
      ≤ max Ce 0 * max C₀ 0 * α ^ 2 := by
  have h1 : Work.FTS.Nonlin.Xn α w ≤ max C₀ 0 * α ^ 2 :=
    le_trans hXw (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (by positivity))
  refine le_trans hell.R.2 ?_
  calc Ce * Work.FTS.Nonlin.Xn α w ≤ max Ce 0 * (max C₀ 0 * α ^ 2) :=
        mul_le_mul (le_max_left Ce 0) h1 (Real.sqrt_nonneg _) (by positivity)
    _ = max Ce 0 * max C₀ 0 * α ^ 2 := by ring

theorem Xn_UopDiv_le {α C₀ Ce : ℝ} {w Φg : Fn} (hw : Work.FTS.ClassC.ClassC α w)
    (hell : Work.FTS.VocabO.EllPkgGo α Ce w Φg) (hXw : Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2) :
    Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ
        / Work.Construction.s2 θ) ≤ max Ce 0 * max C₀ 0 * α ^ 2 := by
  have h1 : Work.FTS.Nonlin.Xn α w ≤ max C₀ 0 * α ^ 2 :=
    le_trans hXw (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (by positivity))
  refine le_trans hell.U.2 ?_
  calc Ce * Work.FTS.Nonlin.Xn α w ≤ max Ce 0 * (max C₀ 0 * α ^ 2) :=
        mul_le_mul (le_max_left Ce 0) h1 (Real.sqrt_nonneg _) (by positivity)
    _ = max Ce 0 * max C₀ 0 * α ^ 2 := by ring

theorem Xn_Vop_le {α C₀ Ce : ℝ} {w Φg : Fn} (hw : Work.FTS.ClassC.ClassC α w)
    (hell : Work.FTS.VocabO.EllPkgGo α Ce w Φg) (hXw : Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2) :
    Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg))
      ≤ max Ce 0 * max C₀ 0 * α ^ 2 := by
  have h1 : Work.FTS.Nonlin.Xn α w ≤ max C₀ 0 * α ^ 2 :=
    le_trans hXw (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (by positivity))
  refine le_trans hell.V.2 ?_
  calc Ce * Work.FTS.Nonlin.Xn α w ≤ max Ce 0 * (max C₀ 0 * α ^ 2) :=
        mul_le_mul (le_max_left Ce 0) h1 (Real.sqrt_nonneg _) (by positivity)
    _ = max Ce 0 * max C₀ 0 * α ^ 2 := by ring

/-- The `𝒲^{4,∞}`-bounds of the three `(z+1)/z`-weighted star coefficients. -/
theorem WlInf_Rs_le {α Cs : ℝ} {Φs : Fn} (hα0 : 0 < α) (hs : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    Work.Spaces.WlInf α 4
      (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
      ≤ max Cs 0 * α :=
  le_trans hs.RW.2 (mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα0.le)

theorem WlInf_Us_le {α Cs : ℝ} {Φs : Fn} (hα0 : 0 < α) (hs : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    Work.Spaces.WlInf α 4 (fun z θ => (z + 1) / z *
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ))
      ≤ max Cs 0 * α :=
  le_trans hs.UszW.2 (mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα0.le)

theorem WlInf_Vs_le {α Cs : ℝ} {Φs : Fn} (hα0 : 0 < α) (hs : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    Work.Spaces.WlInf α 4
      (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ)
      ≤ max Cs 0 * α :=
  le_trans hs.VzW.2 (mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα0.le)

/-- The `FK`-atom of the perturbation: honest in `ℋ⁴`, bounded by `Cfk · max C₀ 0 · α²`. -/
theorem FKw_data {α C₀ Cfk : ℝ} {w : Fn} (hXw : Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2)
    (hfk : ∀ g : Fn, Work.FTS.VocabO.HQo α 4 g → Work.Construction.L12 g 0 = 0 →
      Work.Spaces.HkMem α 4 (fun z _ => Work.Construction.FK g z) ∧
      Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK g z) ≤ Cfk * Work.FTS.Nonlin.Xn α g)
    (hqow : Work.FTS.VocabO.HQo α 4 w) (hl12 : Work.Construction.L12 w 0 = 0)
    (hCfk : 0 < Cfk) :
    Work.Spaces.HkMem α 4 (fun z _ => Work.Construction.FK w z) ∧
      Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK w z) ≤ Cfk * max C₀ 0 * α ^ 2 := by
  have h1 : Work.FTS.Nonlin.Xn α w ≤ max C₀ 0 * α ^ 2 :=
    le_trans hXw (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (by positivity))
  obtain ⟨hm, hb⟩ := hfk w hqow hl12
  refine ⟨hm, ?_⟩
  calc Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK w z)
      ≤ Cfk * Work.FTS.Nonlin.Xn α w := hb
    _ ≤ Cfk * (max C₀ 0 * α ^ 2) := mul_le_mul_of_nonneg_left h1 hCfk.le
    _ = Cfk * max C₀ 0 * α ^ 2 := by ring

/-- The `hKer`-atom: `𝒲^{4,∞}` with the explicit bound `200·(2α)`. -/
theorem hKerNeg_data (α : ℝ) (hα0 : 0 < α) :
    Work.Spaces.WlInfMem α 4 (fun z _ : ℝ => (-(2 * α)) * Work.Spaces.hKer z) ∧
      Work.Spaces.WlInf α 4 (fun z _ : ℝ => (-(2 * α)) * Work.Spaces.hKer z) ≤ 200 * (2 * α) := by
  obtain ⟨hm, hb⟩ := Work.FTS.Nonlinear.Pieces.RNP.hKerConstWlInf α (-(2 * α))
  refine ⟨hm, le_trans hb ?_⟩
  rw [abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * α)]

/-- Multiplication by `z/(1+z)` in `ℋ⁴`, with an explicit constant. -/
theorem phi_mul_data {α Cphi : ℝ} (hCphi : 0 < Cphi)
    (hphi : ∀ g : Fn, Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => z / (1 + z) * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * g z θ) ≤ Cphi * Work.FTS.Nonlin.Xn α g)
    {X : Fn} {b : ℝ} (hX : Work.FTS.VocabO.HQo α 4 X) (hXb : Work.FTS.Nonlin.Xn α X ≤ b) :
    Work.Spaces.HkMem α 4 (fun z θ => z / (1 + z) * X z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * X z θ) ≤ Cphi * b := by
  obtain ⟨hm, hb⟩ := hphi X hX
  exact ⟨hm, le_trans hb (mul_le_mul_of_nonneg_left hXb hCphi.le)⟩


/-! ## Smoothness of the twenty product forms -/

theorem NBlk_smooth {α Cs Ce : ℝ} {w Φs Φg : Fn} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hw : Work.FTS.ClassC.ClassC α w) (hell : Work.FTS.VocabO.EllPkgGo α Ce w Φg)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    ∀ k ∈ Finset.range 20, Work.FTS.EllipticEst.SmoothOpen (NBlk α w Φs Φg k) := by
  have hsw : Work.FTS.VocabO.StarPkgo α Cs Φs := hstar.toStarPkgo
  have hRsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) := hell.R.1.1
  have hUcsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ) :=
    hell.U.1.1
  have hVcsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg)) := hell.V.1.1
  have hRssm : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) :=
    smoothOpen_Rs_of_star hα0 hα1 hsw
  have hUssm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z *
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ)) :=
    smoothOpen_Us_of_star hα0 hα1 hsw
  have hVssm : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      (z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ) :=
    smoothOpen_Vs_of_star hα0 hα1 hsw
  have hFWsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.Fstar α z θ) :=
    Work.FTS.EllipticEst.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hDthFssm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dth (Work.Construction.Fstar α)) := hFWsm.Dth
  have hDzFssm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dz (Work.Construction.Fstar α)) := hFWsm.Dz
  have hDthwsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth w) := hw.reg.Dth
  have hDzwsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz w) := hw.reg.Dz
  have hFKesm : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z) :=
    Work.FTS.GalFields.RHS.smoothOpen_FK_Fstar_rad α hα0 hα1
  have hFKws : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK w z) :=
    smoothOpen_FKw_of_classC hw
  have hFKnegsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ : ℝ => (-(2 * α)) * Work.Spaces.hKer z) := smoothOpen_FKneg α
  have hSinSq : Work.FTS.EllipticEst.SmoothOpen (fun x θ : ℝ => -Real.sin θ ^ 2) :=
    Work.FTS.Nonlinear.Open.row25_smoothOpen_neg_sinSq
  have hG : ∀ (A B : Fn), Work.FTS.EllipticEst.SmoothOpen A →
      Work.FTS.EllipticEst.SmoothOpen B →
      Work.FTS.EllipticEst.SmoothOpen (fun z θ => A z θ * B z θ) :=
    fun A B hA hB => Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hA hB
  have hC : ∀ (c : ℝ) (A : Fn), Work.FTS.EllipticEst.SmoothOpen A →
      Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * A z θ) :=
    fun c A hA => Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl c hA
  have hpw := hG (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) w hRsm hw.reg
  have hps := hG (fun z θ => Work.Construction.Fstar α z θ)
    (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) hFWsm hRsm
  have hphiw : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z / (1 + z) * w z θ) :=
    smoothOpen_phi_mul hw.reg
  have hphiFs : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) :=
    smoothOpen_phi_mul hFWsm
  have hphiDthw : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z / (1 + z) * Work.Spaces.Dth w z θ) :=
    smoothOpen_phi_mul (hw.reg.Dth)
  have hphiDzw : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z / (1 + z) * Work.Spaces.Dz w z θ) :=
    smoothOpen_phi_mul (hw.reg.Dz)
  have hphiDthFs : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) :=
    smoothOpen_phi_mul hFWsm.Dth
  have hphiDzFs : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) :=
    smoothOpen_phi_mul hFWsm.Dz
  intro k hk
  have hk20 : k < 20 := Finset.mem_range.mp hk
  interval_cases k
  · simp only [NBlk]; exact hC 2 _ hpw
  · simp only [NBlk]; exact hC 2 _ hps
  · simp only [NBlk]; exact hC 2 _ (hG _ _ hRssm hphiw)
  · simp only [NBlk]; exact hC 2 _ (hG _ _ hRssm hphiFs)
  · simp only [NBlk]; exact hC (-2) _ (hG _ _ hUcsm hDthwsm)
  · simp only [NBlk]; exact hC (-2) _ (hG _ _ hDthFssm hUcsm)
  · simp only [NBlk]; exact hC (-2) _ (hG _ _ hUssm hphiDthw)
  · simp only [NBlk]; exact hC (-2) _ (hG _ _ hUssm hphiDthFs)
  · simp only [NBlk]; exact hC (-(2 * α)) _ (hG _ _ hVcsm hDzwsm)
  · simp only [NBlk]; exact hC (-(2 * α)) _ (hG _ _ hDzFssm hVcsm)
  · simp only [NBlk]; exact hC (-(2 * α)) _ (hG _ _ hVssm hphiDzw)
  · simp only [NBlk]; exact hC (-(2 * α)) _ (hG _ _ hVssm hphiDzFs)
  · simp only [NBlk]; exact hC (-(1 / 2)) _ (hG _ _ hFKws hDthwsm)
  · simp only [NBlk]; exact hC (-(1 / 2)) _ (hG _ _ hDthFssm hFKws)
  · simp only [NBlk]; exact hC (1 / 2) _ (hG _ _ hFKnegsm hDthwsm)
  · simp only [NBlk]; exact hC (-(1 / 2)) _ (hG _ _ hFKesm hDthFssm)
  · simp only [NBlk]; exact hG _ _ hSinSq (hG _ _ hFKws hw.reg)
  · simp only [NBlk]; exact hG _ _ hSinSq (hG _ _ hFWsm hFKws)
  · simp only [NBlk]; exact hG _ _ hSinSq (hG _ _ hFKesm hw.reg)
  · simp only [NBlk]; exact hG _ _ hSinSq (hG _ _ hFKesm hFWsm)

end Work.FTS.StrongEps.ClassCRHS
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.ClassCRHS

/-- **The right-hand side of the `ε`-scheme is `C^∞` on the open quadrant for `ClassC` data.**

Route for the prover (all ingredients are on disk):

* conjunct 1 (`L₁₂(F_*+w)`) and conjunct 2 (`FK(F_*+w)`): additivity over `F = F_* + w`
  (`StrongPersist.H6Rows.NZaux.L12AddFstar` for `L₁₂` and `GalFields.RHS.FK_add_of_slices` for
  `FK`, with the θ-slice integrability from `Stability.integrableOn_slice_Fstar` and
  `GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem`).  The `F_*`-moments are explicit:
  `GalFields.RHS.smoothOpen_L12_Fstar_rad`, `smoothOpen_FK_Fstar_rad` (and
  `Nonlinear.FstarPkg.FK_Fstar`, `Construction.L12_Fstar_eq`).
* **`FK w` needs no elliptic data at all**: `Construction.FK F z = 3 * Elliptic.Fstar F z`
  (`RXT.velPert_FK_eq`), so `ClassC.fsm` (`∀ m, ContDiffOn ℝ m (Elliptic.Fstar w) (Ioi 0)`)
  gives `SmoothOpen (fun z _ => FK w z)` through `NonlinRows.smoothOpen_radial` +
  `smoothOpen_const_mul`.  (This is the honed counterpart of the `SmoothQuad`-based
  `smoothOpen_FK_radial`; **do not** try to get `SmoothQuad w` from `ClassC α w` — it does not
  follow.)
* conjunct 3 (`LGammaT α w`): `GalFields.RHS.smoothOpen_LGammaT_of_L12` with
  `SmoothOpen (L12 w)` from `NonlinRows.smoothOpen_L12_radial` (needs only `SmoothOpen Φg` and
  `SmoothOpen (Vop (PhiTil α w Φg))`, both from `hell`), `hw.reg` for `SmoothOpen w`.
* conjunct 4 (`N0`): `StrongPersist.H6Pair6Aux.SmoothN0` with `SmoothOpen w`, conjunct 1.
* conjunct 5 (`N`): copy the proof of `GalFields.RHS.smoothOpen_N_Ftot_gal` verbatim, with the
  single `hFKg` step replaced by the `fsm`-route above and `hmem4` from `ClassC.mem`
  (`OpenPkg.HkMem_mono_open hw.reg 4 _ hw.mem`). -/
theorem SmoothOpenRHS {α Ce Cs : ℝ} {Φs w Φg : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hw : Work.FTS.ClassC.ClassC α w)
    (hell : Work.FTS.VocabO.EllPkgGo α Ce w Φg)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 (Work.Construction.Ftot α w) z) ∧
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK (Work.Construction.Ftot α w) z) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.Coercivity.LGammaT α w) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.N0 α (Work.Construction.Ftot α w) w) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.N α (Work.Construction.Ftot α w)
      (fun z θ => Φs z θ + Φg z θ)) := by
  -- the `ℋ⁴`-honesty of the perturbation `w`, from the `ℋ⁷`-honesty of the class
  have hmem4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 4 (by norm_num) hw.mem
  -- `SmoothOpen (z ↦ L₁₂(w)(z))`: the perturbation half of the first moment
  have hL12w : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.L12 w z) :=
    Work.FTS.NonlinRows.smoothOpen_L12_radial hα hell.smooth hell.V.1.1
  -- `SmoothOpen (z ↦ FK(w)(z))`: via `FK F = 3 F_*(F)`, so only `ClassC.fsm` is used
  have hFKw : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.FK w z) := by
    have hfs : Work.FTS.EllipticEst.SmoothOpen
        (fun z (_ : ℝ) => Work.Elliptic.Fstar w z) :=
      Work.FTS.NonlinRows.smoothOpen_radial (r := Work.Elliptic.Fstar w) hw.fsm
    refine (Work.FTS.NonlinRows.smoothOpen_const_mul 3 hfs).congr ?_
    intro z _ hz _ _
    exact (Work.FTS_RegExport.RXT.velPert_FK_eq w z).symm
  -- the two `F_*`-moments are explicit
  have hL12F : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.L12 (Work.Construction.Fstar α) z) :=
    Work.FTS.GalFields.RHS.smoothOpen_L12_Fstar_rad α hα hα1
  have hFKF : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.FK (Work.Construction.Fstar α) z) :=
    Work.FTS.GalFields.RHS.smoothOpen_FK_Fstar_rad α hα hα1
  -- the first moment `L₁₂(F_* + w)`
  have hL12tot : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.L12 (Work.Construction.Ftot α w) z) :=
    (Work.FTS.NonlinRows.smoothOpen_add hL12F hL12w).congr (by
      intro z _ hz _ _
      exact (Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar hα hα1 hw.reg hmem4 z hz).symm)
  -- the second moment `FK(F_* + w)`
  have hFKadd : ∀ z : ℝ, 0 < z → Work.Construction.FK (Work.Construction.Ftot α w) z
      = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK w z := by
    intro z hz
    exact Work.FTS.GalFields.RHS.FK_add_of_slices
      (a := Work.Construction.Fstar α) (b := w) (ne_of_gt hz)
      (Work.Stability.integrableOn_slice_Fstar α hα z)
      (Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hw.reg hmem4 hz)
  have hFKtot : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.FK (Work.Construction.Ftot α w) z) :=
    (Work.FTS.NonlinRows.smoothOpen_add hFKF hFKw).congr (by
      intro z _ hz _ _
      exact (hFKadd z hz).symm)
  -- conjunct 3: the transport-modified linearised operator
  have hLG : Work.FTS.EllipticEst.SmoothOpen (Work.Coercivity.LGammaT α w) :=
    Work.FTS.GalFields.RHS.smoothOpen_LGammaT_of_L12 hL12w hw.reg
  -- conjunct 4: the quadratic term of the modulation
  have hN0 : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.N0 α (Work.Construction.Ftot α w) w) :=
    Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0 hα hw.reg hL12w
  -- conjunct 5: the elliptic correction term `N` (a verbatim transcription of
  -- `GalFields.RHS.smoothOpen_N_Ftot_gal`, with the `FK w` slot fed by `hFKw`)
  have hN : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.N α (Work.Construction.Ftot α w)
        (fun z θ => Φs z θ + Φg z θ)) := by
    have hΦ : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Φs z θ + Φg z θ) :=
      Work.FTS.NonlinRows.smoothOpen_add hstar.smooth hell.smooth
    have hTheta : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (1 / (4 * α)) * (Real.sin (2 * θ)
          * Work.Construction.L12 (Work.Construction.Ftot α w) z)) :=
      Work.FTS.NonlinRows.smoothOpen_const_mul (1 / (4 * α))
        (Work.FTS.NonlinRows.smoothOpen_mul
          (Work.FTS.GalFields.RHS.smoothOpen_sin_two) hL12tot)
    have hPsi_eq : Work.Construction.PhiTil α (Work.Construction.Ftot α w)
          (fun z θ => Φs z θ + Φg z θ)
        = fun z θ => (Φs z θ + Φg z θ)
          - (1 / (4 * α)) * (Real.sin (2 * θ)
            * Work.Construction.L12 (Work.Construction.Ftot α w) z) := by
      funext z θ
      simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.s2]
      ring
    have hPsi : Work.FTS.EllipticEst.SmoothOpen
        (Work.Construction.PhiTil α (Work.Construction.Ftot α w)
          (fun z θ => Φs z θ + Φg z θ)) :=
      hPsi_eq ▸ (Work.FTS.NonlinRows.smoothOpen_sub hΦ hTheta)
    have hRop := Work.FTS.NonlinRows.smoothOpen_Rop (α := α) hPsi
    have hUop : Work.FTS.EllipticEst.SmoothOpen
        (Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α w)
          (fun z θ => Φs z θ + Φg z θ))) :=
      Work.FTS.EllipticEst.smoothOpen_Uop hPsi
    have hVop := Work.FTS.NonlinRows.smoothOpen_Vop hPsi
    have hF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Ftot α w) :=
      Work.FTS.NonlinRows.smoothOpen_add
        (Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)) hw.reg
    have hpthF := Work.FTS.EllipticEst.SmoothOpen.pth hF
    have hDzF := Work.FTS.EllipticEst.SmoothOpen.Dz hF
    have t1 : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (2 * Work.Construction.Rop α (Work.Construction.PhiTil α
            (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ)
          * Work.Construction.Ftot α w z θ) :=
      Work.FTS.NonlinRows.smoothOpen_mul
        (Work.FTS.NonlinRows.smoothOpen_const_mul 2 hRop) hF
    have t2 : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (2 * Work.Construction.Uop α (Work.Construction.PhiTil α
            (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ)
          * Work.Spaces.pth (Work.Construction.Ftot α w) z θ) :=
      Work.FTS.NonlinRows.smoothOpen_mul
        (Work.FTS.NonlinRows.smoothOpen_const_mul 2 hUop) hpthF
    have t3 : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => ((2 * α) * Work.Construction.Vop (Work.Construction.PhiTil α
            (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ)
          * Work.Spaces.Dz (Work.Construction.Ftot α w) z θ) :=
      Work.FTS.NonlinRows.smoothOpen_mul
        (Work.FTS.NonlinRows.smoothOpen_const_mul (2 * α) hVop) hDzF
    have t4 : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (((1 / 2) * Real.sin (2 * θ)) * Work.Construction.FK
            (Work.Construction.Ftot α w) z)
          * Work.Spaces.pth (Work.Construction.Ftot α w) z θ) :=
      Work.FTS.NonlinRows.smoothOpen_mul
        (Work.FTS.NonlinRows.smoothOpen_mul
          (Work.FTS.NonlinRows.smoothOpen_const_mul (1 / 2)
            (Work.FTS.GalFields.RHS.smoothOpen_sin_two)) hFKtot) hpthF
    have t5 : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftot α w) z)
          * Work.Construction.Ftot α w z θ) :=
      Work.FTS.NonlinRows.smoothOpen_mul
        (Work.FTS.NonlinRows.smoothOpen_mul
          (Work.FTS.GalFields.RHS.smoothOpen_sin_sq) hFKtot) hF
    have hmain : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => 2 * Work.Construction.Rop α (Work.Construction.PhiTil α
              (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ
            * Work.Construction.Ftot α w z θ
          - 2 * Work.Construction.Uop α (Work.Construction.PhiTil α
              (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ
            * Work.Spaces.pth (Work.Construction.Ftot α w) z θ
          - 2 * α * Work.Construction.Vop (Work.Construction.PhiTil α
              (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ
            * Work.Spaces.Dz (Work.Construction.Ftot α w) z θ
          - (1 / 2) * Real.sin (2 * θ) * Work.Construction.FK (Work.Construction.Ftot α w) z
            * Work.Spaces.pth (Work.Construction.Ftot α w) z θ
          - Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftot α w) z
            * Work.Construction.Ftot α w z θ) :=
      Work.FTS.NonlinRows.smoothOpen_sub
        (Work.FTS.NonlinRows.smoothOpen_sub
          (Work.FTS.NonlinRows.smoothOpen_sub
            (Work.FTS.NonlinRows.smoothOpen_sub t1 t2) t3) t4) t5
    change Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => 2 * Work.Construction.Rop α (Work.Construction.PhiTil α
              (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ
            * Work.Construction.Ftot α w z θ
          - 2 * Work.Construction.Uop α (Work.Construction.PhiTil α
              (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ
            * Work.Spaces.pth (Work.Construction.Ftot α w) z θ
          - 2 * α * Work.Construction.Vop (Work.Construction.PhiTil α
              (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ
            * Work.Spaces.Dz (Work.Construction.Ftot α w) z θ
          - (1 / 2) * Work.Construction.s2 θ * Work.Construction.FK
              (Work.Construction.Ftot α w) z
            * Work.Spaces.pth (Work.Construction.Ftot α w) z θ
          - Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftot α w) z
            * Work.Construction.Ftot α w z θ)
    exact hmain
  exact ⟨hL12tot, hFKtot, hLG, hN0, hN⟩

end Work.FTS.StrongEps.ClassCRHS
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.PairingT.Atoms =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C

open Work.FTS.Galerkin (Fn)
open Work.FTS.EllipticEst (SmoothOpen)
open Work.FTS.VocabO (HQo)
open Work.FTS.Nonlin (PhiTg PhiTs)
open Work.Construction (Fstar FK L12 Rop Uop Vop PhiTil)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The atoms -/

/-- **The twelve smoothness atoms of the §8 pieces**: the profile `g`, the two angular moments
`L₁₂` and the two `FK`-moments, the fixed profile `F_*`, and the six transported coefficients
`ℛ`/`𝒰`/`𝒱` of the residuals `Φ̃_g` and `Φ̃_*`. -/
structure AtomsO (α : ℝ) (g Φs Φg : Fn) : Prop where
  sg : SmoothOpen g
  sFs : SmoothOpen (Fstar α)
  sLg : SmoothOpen (fun z _ => L12 g z)
  sLFs : SmoothOpen (fun z _ => L12 (Fstar α) z)
  sFKg : SmoothOpen (fun z _ => FK g z)
  sFKFs : SmoothOpen (fun z _ => FK (Fstar α) z)
  sRg : SmoothOpen (Rop α (PhiTg α g Φg))
  sUg : SmoothOpen (Uop α (PhiTg α g Φg))
  sVg : SmoothOpen (Vop (PhiTg α g Φg))
  sRs : SmoothOpen (Rop α (PhiTs α Φs))
  sUs : SmoothOpen (Uop α (PhiTs α Φs))
  sVs : SmoothOpen (Vop (PhiTs α Φs))

/-- `SmoothOpen (x ↦ f x)` from all-order smoothness of `f` on `(0,∞)` bundled with our
convention (`_`-named angular variable). -/
theorem atomsO_sFKg {α : ℝ} {g : Fn} (hfsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar g) (Set.Ioi 0)) :
    SmoothOpen (fun z _ => FK g z) := by
  have hfs : SmoothOpen (fun z _ : ℝ => Work.Elliptic.Fstar g z) :=
    Work.FTS.NonlinRows.smoothOpen_radial (r := Work.Elliptic.Fstar g) hfsm
  refine (SmoothOpen.congr (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul 3 hfs) ?_)
  intro z _ _ _ _
  exact (Work.FTS_RegExport.RXT.velPert_FK_eq g z).symm

/-- `sin(2θ)` as a smooth function of the quadrant. -/
theorem smoothOpen_s2 : SmoothOpen (fun _ (θ : ℝ) => Work.Construction.s2 θ) :=
  SmoothOpen.congr Work.FTS.GalFields.RHS.smoothOpen_sin_two
    (fun _ _ _ _ _ => rfl)

/-- `Uop` of a smooth residual is smooth: `Uop = sin(2θ)·(Uop/sin(2θ))` on the quadrant. -/
theorem smoothOpen_Uop_of_div {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (h : SmoothOpen (fun z θ => Work.Construction.Uop α Ψ z θ / Work.Construction.s2 θ)) :
    SmoothOpen (Work.Construction.Uop α Ψ) := by
  refine SmoothOpen.congr
    (Work.FTS.StrongPersist.H6Pair6Aux.so_mul smoothOpen_s2 h) ?_
  intro z θ hz hθ _
  have hs : Work.Construction.s2 θ ≠ 0 := by
    rw [Work.Construction.s2_eq]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  rw [mul_div_cancel₀ _ hs]

/-- **The atoms from the honest context.** -/
theorem atomsO_of_ctx {Cs Ce α : ℝ} {g Φs Φg : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hg : Work.FTS.ClassC.ClassC α g) (hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) : AtomsO α g Φs Φg where
  sg := hg.reg
  sFs := Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  sLg := Work.FTS.NonlinRows.smoothOpen_L12_radial hα hell.smooth hell.V.1.1
  sLFs := Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_L12_Fstar α
  sFKg := atomsO_sFKg (α := α) hg.fsm
  sFKFs := Work.FTS.GalFields.RHS.smoothOpen_FK_Fstar_rad α hα hα1
  sRg := hell.R.1.1
  sUg := smoothOpen_Uop_of_div hell.U.1.1
  sVg := hell.V.1.1
  sRs := Work.FTS.NonlinRows.smoothOpen_Rop
    (Work.FTS.NonlinRows.smoothOpen_PhiTs hα hα1 hstar.toStarPkgo)
  sUs := Work.FTS.NonlinRows.Rl1.smoothOpen_Uop_open
    (Work.FTS.NonlinRows.smoothOpen_PhiTs hα hα1 hstar.toStarPkgo)
  sVs := Work.FTS.NonlinRows.smoothOpen_Vop
    (Work.FTS.NonlinRows.smoothOpen_PhiTs hα hα1 hstar.toStarPkgo)

/-! ## `GoodO = HQo α 4`: closure properties -/

/-- The honest class of the §8 assembly: interior `C^∞` plus `ℋ⁴`-honesty.  This is exactly the
class of the `N4ExtraH` interface. -/
abbrev GoodO (α : ℝ) (F : Fn) : Prop := HQo α 4 F

theorem goodO_add {α : ℝ} {f g : Fn} (hf : GoodO α f) (hg : GoodO α g) :
    GoodO α (fun z θ => f z θ + g z θ) :=
  ⟨Work.FTS.StrongPersist.H6Pair6Aux.so_add hf.1 hg.1,
    Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hf.1 4)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall g).mp hg.1 4) hf.2 hg.2⟩

theorem goodO_const_mul {α : ℝ} (c : ℝ) {f : Fn} (hf : GoodO α f) :
    GoodO α (fun z θ => c * f z θ) :=
  ⟨Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul c hf.1,
    Work.FTS.LocData.HkMem_const_mul α 4 c hf.2⟩

/-- Transfer of goodness along equality on the open quadrant. -/
theorem goodO_of_eqOn_Qd {α : ℝ} {f g : Fn} (hf : GoodO α f)
    (h : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → f z θ = g z θ) : GoodO α g :=
  ⟨SmoothOpen.congr hf.1 (fun z θ hz hθ hlt => h z θ ⟨hz, ⟨hθ, hlt⟩⟩),
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hf.2
      (fun z hz θ hθ => h z θ ⟨hz, hθ⟩)⟩


/-! ## Linearity of `IP` on the honest class -/


theorem IPO_add4 {IP : ℝ → Fn → Fn → ℝ} {α₂ Ct α : ℝ} (hE : N4ExtraH IP α₂ Ct)
    (hα : α ∈ Set.Ioc 0 α₂) {g f₁ f₂ f₃ f₄ : Fn} (hg : HQo α 4 g)
    (h1 : HQo α 4 f₁) (h2 : HQo α 4 f₂) (h3 : HQo α 4 f₃) (h4 : HQo α 4 f₄)
    (h12 : HQo α 4 (f₁ + f₂)) (h123 : HQo α 4 (f₁ + f₂ + f₃)) :
    IP α (f₁ + f₂ + f₃ + f₄) g = IP α f₁ g + IP α f₂ g + IP α f₃ g + IP α f₄ g := by
  rw [hE.add α hα (f₁ + f₂ + f₃) f₄ g h123 h4 hg,
    hE.add α hα (f₁ + f₂) f₃ g h12 h3 hg,
    hE.add α hα f₁ f₂ g h1 h2 hg]

theorem IPO_add5 {IP : ℝ → Fn → Fn → ℝ} {α₂ Ct α : ℝ} (hE : N4ExtraH IP α₂ Ct)
    (hα : α ∈ Set.Ioc 0 α₂) {g f₁ f₂ f₃ f₄ f₅ : Fn} (hg : HQo α 4 g)
    (h1 : HQo α 4 f₁) (h2 : HQo α 4 f₂) (h3 : HQo α 4 f₃) (h4 : HQo α 4 f₄)
    (h5 : HQo α 4 f₅)
    (h12 : HQo α 4 (f₁ + f₂)) (h123 : HQo α 4 (f₁ + f₂ + f₃))
    (h1234 : HQo α 4 (f₁ + f₂ + f₃ + f₄)) :
    IP α (f₁ + f₂ + f₃ + f₄ + f₅) g
      = IP α f₁ g + IP α f₂ g + IP α f₃ g + IP α f₄ g + IP α f₅ g := by
  rw [hE.add α hα (f₁ + f₂ + f₃ + f₄) f₅ g h1234 h5 hg]
  exact congrArg (· + IP α f₅ g) (IPO_add4 hE hα hg h1 h2 h3 h4 h12 h123)

theorem IPO_add7 {IP : ℝ → Fn → Fn → ℝ} {α₂ Ct α : ℝ} (hE : N4ExtraH IP α₂ Ct)
    (hα : α ∈ Set.Ioc 0 α₂) {g f₁ f₂ f₃ f₄ f₅ f₆ f₇ : Fn} (hg : HQo α 4 g)
    (h1 : HQo α 4 f₁) (h2 : HQo α 4 f₂) (h3 : HQo α 4 f₃) (h4 : HQo α 4 f₄)
    (h5 : HQo α 4 f₅) (h6 : HQo α 4 f₆) (h7 : HQo α 4 f₇)
    (h12 : HQo α 4 (f₁ + f₂)) (h123 : HQo α 4 (f₁ + f₂ + f₃))
    (h1234 : HQo α 4 (f₁ + f₂ + f₃ + f₄))
    (h12345 : HQo α 4 (f₁ + f₂ + f₃ + f₄ + f₅))
    (h123456 : HQo α 4 (f₁ + f₂ + f₃ + f₄ + f₅ + f₆)) :
    IP α (f₁ + f₂ + f₃ + f₄ + f₅ + f₆ + f₇) g
      = IP α f₁ g + IP α f₂ g + IP α f₃ g + IP α f₄ g + IP α f₅ g + IP α f₆ g + IP α f₇ g := by
  rw [hE.add α hα (f₁ + f₂ + f₃ + f₄ + f₅ + f₆) f₇ g h123456 h7 hg]
  have h56 : IP α (f₁ + f₂ + f₃ + f₄ + f₅ + f₆) g
      = IP α f₁ g + IP α f₂ g + IP α f₃ g + IP α f₄ g + IP α f₅ g + IP α f₆ g := by
    rw [hE.add α hα (f₁ + f₂ + f₃ + f₄ + f₅) f₆ g h12345 h6 hg]
    exact congrArg (· + IP α f₆ g) (IPO_add5 hE hα hg h1 h2 h3 h4 h5 h12 h123 h1234)
  rw [h56]

end Work.FTS.StrongEps.E4R3.N4C
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.pert_tilde_contDiffOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.pert_tilde_contDiffOn` — `Φ̃(τ)` is `C³` on the open quadrant

The residual `Φ̃(τ) = PhiTil (pExp α) (g(τ)) (E (g(τ)))` — i.e.
`E (g(τ)) - Θ(pExp α)(g(τ))` with `Θ α F = (1/(4α)) sin 2θ · L₁₂(F)`, written in the
`PhiTil`-form of `Work.Construction` — is of class `C³` on the open quadrant, for every
`τ ≥ 0`, under the two hypotheses `EllLimOK3 (pExp α) E` and `DynOK' (pExp α) C₀ Φs E g`.

This is the `ContDiffOn` half of the block inside `RXT.velPert` (which also computes the
convergence of the jets of `Φ̃` along the class-`C` approximating sequence); only the
regularity statement is needed here, so the proof is that block with the jet analysis removed.

* the `E`-part: `EllLimOK3` applied to the constant-in-`n` limit `f = slice g τ` along the
  class-`C` approximants `gn` supplied by the `LimApprox` clause of `DynOK'`, at a horizon
  `T = max 1 (τ+1) ≥ τ`.  Its hypotheses are `ClassC (pExp α) (slice (gn n) τ)`,
  `Xn6 (pExp α) (slice (gn n) τ) ≤ B` (both from `LimApprox`), the `C⁴`-regularity of the limit
  (`RegPkgMin.c4`) and the order-`4` jet convergence (`LimApprox`);
* the `Θ`-part: `Θ = const · sin 2θ · L₁₂(g(τ))` factors through the radial function
  `L₁₂(g(τ))`, which is `C³` as soon as the angular moment `𝔽K(g(τ)) = ∫_θ g(τ)·K` is `C²`;
  that in turn is the parametric-integral lemma `paramC2`, whose pointwise bound hypothesis
  comes from the trace-free `ℋ⁴ → L^∞` trade-off `Slots.v2_hkMem_pointwise_min` (wrapped in
  `pert_hkMem_bound` below), applied with the uniform `ℋ⁴`-bound `Xn (g(τ)) ≤ C₀α²` of `DynOK`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT.Sys

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Regularity (pExp)

set_option autoImplicit false

/-- The trace-free `ℋ⁴ → L^∞` trade-off `v2_hkMem_pointwise_min`, in the wrapper form used
below (`min z 1 ≤ 1`).  This is `RXT.velPert_hkMem_bound` with the trace-free input
`Slots.v2_hkMem_pointwise_min` in place of `RXT.hkMem_pointwise_min` (which is not available
`sorry`-free). -/
private theorem pert_hkMem_bound {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℝ → ℝ → ℝ) (M : ℝ),
      ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 → Work.Spaces.HkMem α 4 f →
      Work.Spaces.HkNorm α 4 f ≤ M →
      ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i f z θ| ≤ C * M * min z 1 := by
  obtain ⟨C, hC0, hC⟩ := Work.FTS_RegExport.RXT.v2_hkMem_pointwise_min hα hα1
  refine ⟨C, hC0, ?_⟩
  intro f M hsm hmem hMn j i hji z θ hz hθ hθ2
  have h1 := hC f hsm hmem j i (by omega) z θ hz hθ hθ2
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hMn
  have hm0 : 0 ≤ min z 1 := le_min hz.le zero_le_one
  calc |Work.Spaces.mixed j i f z θ| ≤ C * min z 1 * Work.Spaces.HkNorm α 4 f := h1
    _ ≤ C * min z 1 * M := mul_le_mul_of_nonneg_left hMn (mul_nonneg hC0 hm0)
    _ = C * M * min z 1 := by ring

theorem pert_tilde_contDiffOn {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 3 (Function.uncurry (fun z θ => Work.Construction.PhiTil
        (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice g τ)
        (E (Work.FTS.Galerkin.slice g τ)) z θ)) Work.FTS.EllipticEst.Q0 := by
  intro τ hτ
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- a horizon `T > 0` with `τ ∈ [0,T]`, for the approximating sequence of `LimApprox`
  have hS : (0 : ℝ) < max 1 (τ + 1) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hτS : τ ∈ Set.Icc (0 : ℝ) (max 1 (τ + 1)) :=
    ⟨hτ, le_trans (by linarith) (le_max_right (1 : ℝ) (τ + 1))⟩
  obtain ⟨gn, B, L, hApprox, _hLip, hJet, _hμ⟩ := hOK.2 (max 1 (τ + 1)) hS
  -- the data of the limit slice
  have hF4 : ContDiffOn ℝ 4 (Function.uncurry (slice g τ)) Work.FTS.EllipticEst.Q0 :=
    hOK.1.1.c4 τ hτ
  have hFmem : Work.Spaces.HkMem (Work.FTS.Regularity.pExp α) 4 (slice g τ) :=
    hOK.1.1.mem4 τ hτ
  have hFnorm : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (slice g τ)
      ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 := by
    have h2 : C₀ * (Work.FTS.Regularity.pExp α) ^ 2
        ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (sq_nonneg (Work.FTS.Regularity.pExp α))
    exact le_trans (hOK.1.2 τ hτ) h2
  -- ## the `E`-part: `E (g(τ))` is `C³` on the open quadrant
  obtain ⟨_hBsl, hElim3, _hEconv⟩ := hEL3 (fun n => slice (gn n) τ) (slice g τ) B
    (fun n => (hApprox n τ hτS).1) (fun n => (hApprox n τ hτS).2.2) hF4
    (fun j i hji z' θ' hzθ => hJet τ hτS j i hji z' θ' hzθ)
  -- ## the `Θ`-part: `L₁₂(g(τ))` is `C³` on `(0,∞)`
  obtain ⟨C4, hC40, hC4⟩ := pert_hkMem_bound hαG hαG1
  have hFKlim : ContDiffOn ℝ 2 (Work.Construction.FK (slice g τ)) (Set.Ioi 0) := by
    have hF2 : ContDiffOn ℝ 2 (Function.uncurry (slice g τ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hF4.of_le (by norm_num)
    have hbase : ∀ (b : ℕ), b ≤ 2 → ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
        |Work.Spaces.mixed b 0 (slice g τ) z' θ'|
          ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) := by
      intro b hb z' θ' hz' hθ' hθ'2
      have h1 := hC4 (slice g τ) (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) hF4 hFmem
        hFnorm b 0 (by omega) z' θ' hz' hθ' hθ'2
      have h2 : C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) * min z' 1
          ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left (min_le_right _ _)
          (mul_nonneg hC40 (mul_nonneg (le_max_right C₀ 0)
            (sq_nonneg (Work.FTS.Regularity.pExp α))))
      linarith [h1, h2]
    have hb : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
        |(slice g τ) z' θ'| ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) ∧
        |Work.Spaces.Dz (slice g τ) z' θ'|
          ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) ∧
        |Work.Spaces.DzIter 2 (slice g τ) z' θ'|
          ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) :=
      fun z' θ' hz' hθ' hθ'2 =>
        ⟨by simpa using hbase 0 (by norm_num) z' θ' hz' hθ' hθ'2,
         by simpa using hbase 1 (by norm_num) z' θ' hz' hθ' hθ'2,
         by simpa using hbase 2 (by norm_num) z' θ' hz' hθ' hθ'2⟩
    exact Work.FTS_RegExport.RXT.velPertAux.paramC2 (φ := Work.Spaces.K)
      (C := C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2))
      Work.FTS_RegExport.RXT.velPert_continuousOn_K hF2 hb
  have hL12lim : ContDiffOn ℝ 3 (Work.Construction.L12 (slice g τ)) (Set.Ioi 0) :=
    Work.FTS_RegExport.RXT.contDiffOn_three_L12 hFKlim
  have hΘ3lim : ContDiffOn ℝ 3
      (Function.uncurry (Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice g τ)))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.velPert_contDiffOn_Theta (α := Work.FTS.Regularity.pExp α) hL12lim
  -- ## `Φ̃ = E(g(τ)) - Θ(g(τ))`
  refine ((hElim3.sub hΘ3lim)).congr fun p _ => ?_
  rcases p with ⟨z', θ'⟩
  simp only [Function.uncurry, Work.Construction.PhiTil]

end Work.FTS_RegExport.RXT.Sys
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT0.SJC.slotJetsTendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT0.SJC

open scoped Real Topology
open Set Filter
open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Regularity (pExp)
set_option autoImplicit false
set_option maxHeartbeats 1600000
variable {α Ce C₀ : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}

/-- **The residual of the class-`C` approximants is `C³` and its jets converge.**

This is the bundle consumed by `Slots.v2_SlotJetsTendsto`: on the open quadrant the
residual `Ξ n = Φ̃(gn n) = PhiTil (pExp α) (slice (gn n) τ) (E (slice (gn n) τ))` is `C³`, the
limit residual `Ξlim = Φ̃(g)` is `C³`, and every mixed jet of order `≤ 3` of `Ξ n` converges to
the corresponding jet of `Ξlim` at every point of the open quadrant `(0,∞) × (0,π/2)`.

The proof follows the jet-convergence block of `RXT.SysAux.pertSlot_tendsto`: the `E`-part is
handled by `EllLimOK3` (giving both `C³`-regularity of the limit and jet convergence), the
singular part `Θ = (1/(4α))·sin 2θ·L₁₂` by the `L₁₂`-tower (`v2_L12DzIterTendsto` +
`v2_thetaJetsTendsto`), and the split `Φ̃ = E(·) − Θ` by
`velPert_mixed_sub_three`. -/
private theorem phiTil_jets_conv
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (pExp α) E)
    (hOK : Work.FTS.FinalV2.DynOK' (pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S) {gn : ℕ → Fam} {B : ℝ}
    (hApprox : ∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) S,
      Work.FTS.ClassC.ClassC (pExp α) (slice (gn n) τ) ∧
        Work.FTS.Nonlin.Xn (pExp α) (slice (gn n) τ) ≤ C₀ * (pExp α) ^ 2 ∧
        Work.FTS.StrongGlobal.Xn6 (pExp α) (slice (gn n) τ) ≤ B)
    (hJet : ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.Construction.Qd →
        Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (slice (gn n) τ) z θ)
          Filter.atTop (nhds (Work.Spaces.mixed j i (slice g τ) z θ)))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) S) :
    (∀ n : ℕ, ContDiffOn ℝ 3 (Function.uncurry (fun z θ => Work.Construction.PhiTil (pExp α)
        (slice (gn n) τ) (E (slice (gn n) τ)) z θ)) Work.FTS.EllipticEst.Q0) ∧
      ContDiffOn ℝ 3 (Function.uncurry (fun z θ => Work.Construction.PhiTil (pExp α)
        (slice g τ) (E (slice g τ)) z θ)) Work.FTS.EllipticEst.Q0 ∧
      (∀ b a : ℕ, a + b ≤ 3 → ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
        Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed b a (fun z θ =>
            Work.Construction.PhiTil (pExp α) (slice (gn n) τ)
              (E (slice (gn n) τ)) z θ) z' θ') Filter.atTop
          (nhds (Work.Spaces.mixed b a (fun z θ =>
            Work.Construction.PhiTil (pExp α) (slice g τ) (E (slice g τ)) z θ) z' θ'))) := by
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- the two trace-free `ℋ⁴ → L^∞` trade-offs
  obtain ⟨CA1, hCA10, hA1⟩ := Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved hαG hαG1
  obtain ⟨C4, hC40, hC4⟩ := Work.FTS_RegExport.RXT.velPert_hkMem_bound hαG hαG1
  -- ## regularity of the class-`C` approximants
  have hReg : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ))
        Work.FTS.EllipticEst.Q0 ∧ Work.Spaces.HkMem (Work.FTS.Regularity.pExp α) 4
          (slice (gn n) τ) ∧
      Work.FTS.Nonlin.BdryTraces (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ) ∧
      Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ)
        ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 := by
    intro n
    obtain ⟨hCn, hXn, _⟩ := hApprox n τ hτ
    have h2 : C₀ * (Work.FTS.Regularity.pExp α) ^ 2
        ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (sq_nonneg (Work.FTS.Regularity.pExp α))
    exact ⟨hCn.reg.of_le (by norm_num),
      Work.FTS.IPGen.HkMem_mono_le hCn.reg 4 (by norm_num) hCn.mem,
      hCn.bdry_le_six (by norm_num), le_trans hXn h2⟩
  -- ## the limit slice and its data
  have hF4 : ContDiffOn ℝ 4 (Function.uncurry (slice g τ)) Work.FTS.EllipticEst.Q0 :=
    hOK.1.1.c4 τ hτ.1
  have hFmem : Work.Spaces.HkMem (Work.FTS.Regularity.pExp α) 4 (slice g τ) :=
    hOK.1.1.mem4 τ hτ.1
  have hFnorm : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (slice g τ)
      ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 := by
    have h2 : C₀ * (Work.FTS.Regularity.pExp α) ^ 2
        ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (sq_nonneg (Work.FTS.Regularity.pExp α))
    exact le_trans (hOK.1.2 τ hτ.1) h2
  -- ## the `E`-jets of the limit slice
  obtain ⟨_hBsl, hE3lim, hEconv⟩ := hEL3 (fun n => slice (gn n) τ) (slice g τ) B
    (fun n => (hApprox n τ hτ).1) (fun n => (hApprox n τ hτ).2.2) hF4
    (fun j i hji z' θ' hzθ => hJet τ hτ j i hji z' θ' hzθ)
  -- ## `𝔽K` and `L₁₂` of the limit slice
  have hFKlim : ContDiffOn ℝ 2 (Work.Construction.FK (slice g τ)) (Set.Ioi 0) := by
    have hF2 : ContDiffOn ℝ 2 (Function.uncurry (slice g τ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hF4.of_le (by norm_num)
    have hbase : ∀ (b : ℕ), b ≤ 2 → ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
        |Work.Spaces.mixed b 0 (slice g τ) z' θ'|
          ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) := by
      intro b hb z' θ' hz' hθ' hθ'2
      have h1 := hC4 (slice g τ) (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) hF4 hFmem
        hFnorm b 0 (by omega) z' θ' hz' hθ' hθ'2
      have h2 : C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) * min z' 1
          ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left (min_le_right _ _)
          (mul_nonneg hC40 (mul_nonneg (le_max_right C₀ 0)
            (sq_nonneg (Work.FTS.Regularity.pExp α))))
      linarith [h1, h2]
    have hb : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
        |slice g τ z' θ'| ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) ∧
        |Work.Spaces.Dz (slice g τ) z' θ'|
          ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) ∧
        |Work.Spaces.DzIter 2 (slice g τ) z' θ'|
          ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) :=
      fun z' θ' hz' hθ' hθ'2 =>
        ⟨by simpa using hbase 0 (by norm_num) z' θ' hz' hθ' hθ'2,
         by simpa using hbase 1 (by norm_num) z' θ' hz' hθ' hθ'2,
         by simpa using hbase 2 (by norm_num) z' θ' hz' hθ' hθ'2⟩
    exact Work.FTS_RegExport.RXT.Slots.v2_paramC2 (φ := Work.Spaces.K)
      (C := C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2))
      Work.FTS_RegExport.RXT.velPert_continuousOn_K hF2 hb
  have hL12lim : ContDiffOn ℝ 3 (Work.Construction.L12 (slice g τ)) (Set.Ioi 0) :=
    Work.FTS_RegExport.RXT.contDiffOn_three_L12 hFKlim
  have hΘ3lim : ContDiffOn ℝ 3
      (Function.uncurry (Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice g τ)))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.velPert_contDiffOn_Theta (α := Work.FTS.Regularity.pExp α) hL12lim
  have hElim3 : ContDiffOn ℝ 3 (Function.uncurry (fun z θ => E (slice g τ) z θ))
      Work.FTS.EllipticEst.Q0 := hE3lim
  -- ## `𝔽K`-jets of the approximants and the `Θ`-jets
  have hL12jets : ∀ j : ℕ, j ≤ 3 → ∀ z' : ℝ, 0 < z' →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.DzIter j
          (fun z _ => Work.Construction.L12 (slice (gn n) τ) z) z' 0) Filter.atTop
        (nhds (Work.Spaces.DzIter j
          (fun z _ => Work.Construction.L12 (slice g τ) z) z' 0)) := by
    intro j hj z' hz'
    refine Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
      (C0 := CA1 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2))
      (F := fun n => slice (gn n) τ) (G := slice g τ) (by positivity) ?_ hF4 ?_ ?_ j hj z' hz'
    · intro n; exact (hReg n).1
    · intro n b a hba z'' θ'' hz'' hθ'' hθ''2
      have h1 := hA1 (slice (gn n) τ) (hReg n).1 (hReg n).2.1 (hReg n).2.2.1 b a hba
        z'' θ'' hz'' hθ'' hθ''2
      have h2 : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ)
          ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 := (hReg n).2.2.2
      have hA0 : 0 ≤ CA1 * (z'' ^ ((3 : ℝ) / 2) / (1 + z'') ^ 2) :=
        mul_nonneg hCA10 (div_nonneg (Real.rpow_nonneg hz''.le _) (by positivity))
      calc |Work.Spaces.mixed b a (slice (gn n) τ) z'' θ''|
          ≤ CA1 * (z'' ^ ((3 : ℝ) / 2) / (1 + z'') ^ 2)
              * Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ) := h1
        _ ≤ CA1 * (z'' ^ ((3 : ℝ) / 2) / (1 + z'') ^ 2)
              * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) :=
            mul_le_mul_of_nonneg_left h2 hA0
        _ = CA1 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2)
              * (z'' ^ ((3 : ℝ) / 2) / (1 + z'') ^ 2) := by ring
    · intro b a hab z'' θ'' hz'' hθ'' hθ''2
      exact hJet τ hτ b a (by omega) z'' θ'' ⟨hz'', hθ'', hθ''2⟩
  have hΘconv : ∀ j i : ℕ, j + i ≤ 3 → ∀ z' θ' : ℝ, 0 < z' → 0 < θ' →
      θ' < Real.pi / 2 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i
          (Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice (gn n) τ)) z' θ')
        Filter.atTop
        (nhds (Work.Spaces.mixed j i
          (Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice g τ)) z' θ')) :=
    Work.FTS_RegExport.RXT.Slots.v2_thetaJetsTendsto (α := Work.FTS.Regularity.pExp α)
      (F := fun n => slice (gn n) τ) (G := slice g τ) hL12jets
  -- ## `C³`-regularity of the residuals
  have hΦ3 : ∀ n : ℕ, ContDiffOn ℝ 3
      (Function.uncurry (fun z θ => E (slice (gn n) τ) z θ)) Work.FTS.EllipticEst.Q0 := by
    intro n
    exact ((hEll _ (hApprox n τ hτ).1).1.smooth).of_le (by norm_num)
  have hΘ3 : ∀ n : ℕ, ContDiffOn ℝ 3 (Function.uncurry
      (Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice (gn n) τ)))
      Work.FTS.EllipticEst.Q0 := by
    intro n
    refine Work.FTS_RegExport.RXT.velPert_contDiffOn_Theta
      (α := Work.FTS.Regularity.pExp α) ?_
    refine Work.FTS_RegExport.RXT.contDiffOn_three_L12 ?_
    have h1 : ContDiffOn ℝ 2 (fun z => 3 * Work.Elliptic.Fstar (slice (gn n) τ) z)
        (Set.Ioi 0) := contDiffOn_const.mul ((hApprox n τ hτ).1.fsm 2)
    refine h1.congr fun z' _ => ?_
    rw [Work.FTS_RegExport.RXT.velPert_FK_eq]
  have hΞ3 : ∀ n : ℕ, ContDiffOn ℝ 3 (Function.uncurry (fun z θ =>
      Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
        (E (slice (gn n) τ)) z θ)) Work.FTS.EllipticEst.Q0 := by
    intro n
    refine ((hΦ3 n).sub (hΘ3 n)).congr fun p _ => ?_
    rcases p with ⟨z', θ'⟩
    simp only [Function.uncurry, Pi.sub_apply, Work.Construction.PhiTil]
  have hΞ3lim : ContDiffOn ℝ 3 (Function.uncurry (fun z θ =>
      Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
        (E (slice g τ)) z θ)) Work.FTS.EllipticEst.Q0 := by
    refine ((hElim3.sub hΘ3lim)).congr fun p _ => ?_
    rcases p with ⟨z', θ'⟩
    simp only [Function.uncurry, Pi.sub_apply, Work.Construction.PhiTil]
  -- ## the jets of the residuals converge
  have hΞconv : ∀ b a : ℕ, a + b ≤ 3 → ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed b a (fun z θ =>
          Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
            (E (slice (gn n) τ)) z θ) z' θ') Filter.atTop
        (nhds (Work.Spaces.mixed b a (fun z θ =>
          Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ)) z θ) z' θ')) := by
    intro b a hba z' θ' hz' hθ' hθ'2
    have hfun : (fun n : ℕ => Work.Spaces.mixed b a (fun z θ =>
          Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
            (E (slice (gn n) τ)) z θ) z' θ')
        = fun n : ℕ => Work.Spaces.mixed b a (fun z θ => E (slice (gn n) τ) z θ) z' θ'
            - Work.Spaces.mixed b a (fun z θ =>
                Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice (gn n) τ) z θ)
                z' θ' := by
      funext n
      exact Work.FTS_RegExport.RXT.velPert_mixed_sub_three (b := b) (a := a) hba
        (hΦ3 n) (hΘ3 n) hz' hθ' hθ'2
    have hlim : Work.Spaces.mixed b a (fun z θ =>
          Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ)) z θ) z' θ'
        = Work.Spaces.mixed b a (fun z θ => E (slice g τ) z θ) z' θ'
            - Work.Spaces.mixed b a (fun z θ =>
                Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice g τ) z θ)
                z' θ' :=
      Work.FTS_RegExport.RXT.velPert_mixed_sub_three (b := b) (a := a) hba hElim3 hΘ3lim
        hz' hθ' hθ'2
    rw [hfun, hlim]
    exact (hEconv b a (by omega) z' θ' ⟨hz', hθ', hθ'2⟩).sub
      (hΘconv b a (by omega) z' θ' hz' hθ' hθ'2)
  exact ⟨hΞ3, hΞ3lim, hΞconv⟩

theorem slotJetsTendsto
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (pExp α) E)
    (hOK : Work.FTS.FinalV2.DynOK' (pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S) {gn : ℕ → Fam} {B : ℝ}
    (hApprox : ∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) S,
      Work.FTS.ClassC.ClassC (pExp α) (slice (gn n) τ) ∧
        Work.FTS.Nonlin.Xn (pExp α) (slice (gn n) τ) ≤ C₀ * (pExp α) ^ 2 ∧
        Work.FTS.StrongGlobal.Xn6 (pExp α) (slice (gn n) τ) ≤ B)
    (hJet : ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.Construction.Qd →
        Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (slice (gn n) τ) z θ)
          Filter.atTop (nhds (Work.Spaces.mixed j i (slice g τ) z θ)))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) S) :
    ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (Work.Construction.Rop (pExp α)
          (Work.Construction.PhiTil (pExp α) (slice (gn n) τ) (E (slice (gn n) τ)))) z θ)
        Filter.atTop (nhds (Work.Spaces.mixed j i (Work.Construction.Rop (pExp α)
          (Work.Construction.PhiTil (pExp α) (slice g τ) (E (slice g τ)))) z θ))) ∧
      (Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (Work.Construction.Vop
          (Work.Construction.PhiTil (pExp α) (slice (gn n) τ) (E (slice (gn n) τ)))) z θ)
        Filter.atTop (nhds (Work.Spaces.mixed j i (Work.Construction.Vop
          (Work.Construction.PhiTil (pExp α) (slice g τ) (E (slice g τ)))) z θ))) ∧
      (Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (fun z θ =>
          Work.Construction.Uop (pExp α)
            (Work.Construction.PhiTil (pExp α) (slice (gn n) τ) (E (slice (gn n) τ))) z θ
            / Real.sin (2 * θ)) z θ)
        Filter.atTop (nhds (Work.Spaces.mixed j i (fun z θ =>
          Work.Construction.Uop (pExp α)
            (Work.Construction.PhiTil (pExp α) (slice g τ) (E (slice g τ))) z θ
            / Real.sin (2 * θ)) z θ))) := by
  intro j i hji z θ hz hθ hθ2
  obtain ⟨hΞ3, hΞ3lim, hΞconv⟩ := phiTil_jets_conv hα hα13 hEll hEL3 hOK hS hApprox hJet hτ
  have hslot := Work.FTS_RegExport.RXT.Slots.v2_SlotJetsTendsto
    (α := Work.FTS.Regularity.pExp α)
    (Ξ := fun n => fun z θ => Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
      (slice (gn n) τ) (E (slice (gn n) τ)) z θ)
    (Ξlim := fun z θ => Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
      (slice g τ) (E (slice g τ)) z θ) hΞ3 hΞ3lim hΞconv j i hji z θ hz hθ hθ2
  exact ⟨by simpa using hslot.1, by simpa using hslot.2.1, by simpa using hslot.2.2⟩

end Work.FTS_RegExport.RXT0.SJC
end
-- ===== merged: Submission.Work.FTS_RegExport.THL.ropPert_theta_holder =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.THL

theorem ropPert_theta_holder {α Ce C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    {g : Work.FTS.Galerkin.Fam} (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∀ S > 0, ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 < z →
      ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), ∀ θ' ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
        |Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))) z θ
          - Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))) z θ'|
          ≤ M * min z 1 * |θ - θ'| ^ (Work.FTS.Regularity.pExp α / 20) := by
  intro S hS
  -- the exponent data for the `ℋ⁴ ⟹` Hölder leaf `theta_holder_of_HkMem`
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  obtain ⟨C, hC0, hA3⟩ := theta_holder_of_HkMem hαG hαG1
  -- the class-`C` approximants of the solution on `[0,S]`
  obtain ⟨gn, B, L, hApprox, _hLip, hJet, _hμ⟩ := hOK.2 S hS
  refine ⟨C * (max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2)), ?_, ?_⟩
  · exact mul_nonneg hC0 (mul_nonneg (le_max_right Ce 0)
      (mul_nonneg (le_max_right C₀ 0) (sq_nonneg _)))
  · intro τ hτ z hz θ hθ θ' hθ'
    -- the perturbation slot of the approximants converges to the one of the limit slice
    have htend := Work.FTS_RegExport.RXT.SysAux.pertSlot_tendsto (α := α) (Ce := Ce) (C₀ := C₀)
      (Φs := Φs) (E := E) (g := g) hα hα13 hEll hEL3 hOK hS (gn := gn) (B := B) hApprox hJet hτ
    have hconvθ := (htend z θ hz hθ.1 hθ.2).1
    have hconvθ' := (htend z θ' hz hθ'.1 hθ'.2).1
    refine le_of_tendsto' ((hconvθ.sub hconvθ').abs) (fun n => ?_)
    -- the per-approximant estimate: `EllPkgGo` puts the slot in `ℋ⁴` with a bounded norm
    obtain ⟨hCn, hXn, _⟩ := hApprox n τ hτ
    obtain ⟨hGo, _⟩ := hEll (Work.FTS.Galerkin.slice (gn n) τ) hCn
    have hR4 : ContDiffOn ℝ 4 (Function.uncurry (Work.Construction.Rop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) τ)
          (E (Work.FTS.Galerkin.slice (gn n) τ))))) Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.SmoothOpen.forall hGo.R.1.1 4
    have hRmem : Work.Spaces.HkMem (Work.FTS.Regularity.pExp α) 4
        (Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (Work.FTS.Galerkin.slice (gn n) τ) (E (Work.FTS.Galerkin.slice (gn n) τ)))) :=
      hGo.R.1.2
    have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α)
        (Work.FTS.Galerkin.slice (gn n) τ) := Work.Spaces.HkNorm_nonneg _ _ _
    have hnorm : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4
        (Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (Work.FTS.Galerkin.slice (gn n) τ) (E (Work.FTS.Galerkin.slice (gn n) τ))))
        ≤ max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) := by
      refine le_trans hGo.R.2 (le_trans (mul_le_mul_of_nonneg_right (le_max_left Ce 0) hXn0) ?_)
      exact mul_le_mul_of_nonneg_left
        (le_trans hXn (mul_le_mul_of_nonneg_right (le_max_left C₀ 0)
          (sq_nonneg (Work.FTS.Regularity.pExp α)))) (le_max_right Ce 0)
    have h3 := hA3 (Work.Construction.Rop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) τ)
          (E (Work.FTS.Galerkin.slice (gn n) τ)))) hR4 hRmem z hz θ hθ θ' hθ'
    rw [Work.Spaces.gam_sub_one (Work.FTS.Regularity.pExp α),
      show Work.FTS.Regularity.pExp α / 10 / 2 = Work.FTS.Regularity.pExp α / 20 by ring] at h3
    refine le_trans h3 ?_
    have hm0 : 0 ≤ min z 1 := le_min hz.le zero_le_one
    have hp0 : (0 : ℝ) ≤ |θ - θ'| ^ (Work.FTS.Regularity.pExp α / 20) :=
      Real.rpow_nonneg (abs_nonneg _) _
    refine le_trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hnorm (mul_nonneg hC0 hm0)) hp0) (le_of_eq ?_)
    ring

end Work.FTS_RegExport.THL
end
-- ===== merged: Submission.Work.FTS_RegExport.THL.vopPert_theta_holder =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.THL

set_option autoImplicit false

/-!
# `THL.vopPert_theta_holder` — the `θ`-Hölder modulus of the perturbation slot `𝒱(Φ̃)`

**Leaf A5v** of `THL.Leaves`.  The perturbation residual of the strong route is
`Φ̃(τ) = PhiTil (pExp α) (g(τ)) (E (g(τ)))`; its slot `𝒱(Φ̃) = Vop Φ̃` obeys a uniform `θ`-Hölder
modulus of exponent `pExp α / 20` on every horizon `[0,S]`, uniformly in the fake time and with
the radial weight `min z 1`.

**Route** (the one announced in `THL.Leaves`): the class-`C` approximants `σₙ = slice (gn n) τ`
of the `LimApprox` clause of `DynOK'` are class `C`, so `hEll` gives `EllPkgGo` for the
`σₙ`-slots, i.e. `SmoothOpen`/`HkMem` of `𝒱(Φ̃ₙ)` with the *uniform* `ℋ⁴`-norm bound
`HkNorm ≤ Ce · Xn σₙ ≤ max Ce 0 · (max C₀ 0 · (pExp α)²)` (the estimate of `v2_velPert`).
The trace-free leaf **A3** `theta_holder_of_HkMem` then converts that per-`n` `ℋ⁴`-membership into
the Hölder bound `C · min z 1 · HkNorm · |Δθ|^{pExp α/20}` (using `gam β - 1 = β/10`), and the
value of the slot passes to the limit `n → ∞` by `SysAux.pertSlot_tendsto` (order-`(0,0)` jet
convergence).  `le_of_tendsto'` closes.
-/

theorem vopPert_theta_holder {α Ce C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    {g : Work.FTS.Galerkin.Fam} (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∀ S > 0, ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 < z →
      ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), ∀ θ' ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
        |Work.Construction.Vop
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))) z θ
          - Work.Construction.Vop
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))) z θ'|
          ≤ M * min z 1 * |θ - θ'| ^ (Work.FTS.Regularity.pExp α / 20) := by
  intro S hS
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- **A3**, at the exponent `β = pExp α`
  obtain ⟨C, hC0, hA3⟩ := theta_holder_of_HkMem hαG hαG1
  -- the `ℋ⁴`-norm bound of the perturbation slots
  set Mc : ℝ := max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) with hMc
  have hMc0 : 0 ≤ Mc :=
    mul_nonneg (le_max_right Ce 0) (mul_nonneg (le_max_right C₀ 0) (sq_nonneg _))
  -- the approximating family of the `LimApprox` clause
  obtain ⟨gn, B, L, hApprox, _hLip, hJet, _hμ⟩ := hOK.2 S hS
  refine ⟨C * Mc, mul_nonneg hC0 hMc0, ?_⟩
  intro τ hτ z hz θ hθ θ' hθ'
  -- the exponent of A3 is `pExp α / 20`
  have hexp : (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) / 2
      = Work.FTS.Regularity.pExp α / 20 := by
    rw [Work.Spaces.gam_sub_one]; ring
  -- the per-`n` Hölder bound, uniformly in `n` and `τ`
  have hper : ∀ n : ℕ,
      |Work.Construction.Vop
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (Work.FTS.Galerkin.slice (gn n) τ) (E (Work.FTS.Galerkin.slice (gn n) τ))) z θ
        - Work.Construction.Vop
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (Work.FTS.Galerkin.slice (gn n) τ) (E (Work.FTS.Galerkin.slice (gn n) τ))) z θ'|
      ≤ C * Mc * min z 1 * |θ - θ'| ^ (Work.FTS.Regularity.pExp α / 20) := by
    intro n
    obtain ⟨hCn, hXn, _⟩ := hApprox n τ hτ
    obtain ⟨hGo, _⟩ := hEll _ hCn
    -- the `ℋ⁴`-norm of the slot is at most `Mc`, uniformly in `n` and `τ`
    have hkey : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4
        (Work.Construction.Vop
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (Work.FTS.Galerkin.slice (gn n) τ) (E (Work.FTS.Galerkin.slice (gn n) τ)))) ≤ Mc := by
      have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α)
          (Work.FTS.Galerkin.slice (gn n) τ) := Work.Spaces.HkNorm_nonneg _ _ _
      have h2 : Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α)
          (Work.FTS.Galerkin.slice (gn n) τ) ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 :=
        le_trans hXn (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (sq_nonneg _))
      refine le_trans hGo.V.2 ?_
      calc Ce * Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice (gn n) τ)
          ≤ max Ce 0 * Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice (gn n) τ) :=
            mul_le_mul_of_nonneg_right (le_max_left Ce 0) hXn0
        _ ≤ Mc := by
            rw [hMc]
            exact mul_le_mul_of_nonneg_left h2 (le_max_right Ce 0)
    -- A3 on the approximant slot
    have h3 := hA3 (Work.Construction.Vop
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.Galerkin.slice (gn n) τ) (E (Work.FTS.Galerkin.slice (gn n) τ))))
      (hGo.V.1.1.of_le (by norm_num)) hGo.V.1.2 z hz θ hθ θ' hθ'
    rw [hexp] at h3
    have hm0 : 0 ≤ min z 1 := le_min hz.le zero_le_one
    have hrpow : 0 ≤ |θ - θ'| ^ (Work.FTS.Regularity.pExp α / 20) :=
      Real.rpow_nonneg (abs_nonneg _) _
    have hstep : C * min z 1 * Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4
          (Work.Construction.Vop
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice (gn n) τ) (E (Work.FTS.Galerkin.slice (gn n) τ))))
          * |θ - θ'| ^ (Work.FTS.Regularity.pExp α / 20)
        ≤ C * min z 1 * Mc * |θ - θ'| ^ (Work.FTS.Regularity.pExp α / 20) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hkey (mul_nonneg hC0 hm0)) hrpow
    calc _ ≤ C * min z 1 * Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4
            (Work.Construction.Vop
              (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
                (Work.FTS.Galerkin.slice (gn n) τ) (E (Work.FTS.Galerkin.slice (gn n) τ))))
            * |θ - θ'| ^ (Work.FTS.Regularity.pExp α / 20) := h3
      _ ≤ C * min z 1 * Mc * |θ - θ'| ^ (Work.FTS.Regularity.pExp α / 20) := hstep
      _ = C * Mc * min z 1 * |θ - θ'| ^ (Work.FTS.Regularity.pExp α / 20) := by ring
  -- the value of the slot converges along `gn` at both angles
  have hcθ := (Work.FTS_RegExport.RXT.SysAux.pertSlot_tendsto (gn := gn) (B := B)
    hα hα13 hEll hEL3 hOK hS hApprox hJet hτ z θ hz hθ.1 hθ.2).2.1
  have hcθ' := (Work.FTS_RegExport.RXT.SysAux.pertSlot_tendsto (gn := gn) (B := B)
    hα hα13 hEll hEL3 hOK hS hApprox hJet hτ z θ' hz hθ'.1 hθ'.2).2.1
  exact le_of_tendsto' ((hcθ.sub hcθ').abs) hper

end Work.FTS_RegExport.THL
end
