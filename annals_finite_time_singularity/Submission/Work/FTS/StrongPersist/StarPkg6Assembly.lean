import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.NormNum.RealSqrt
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData6.zfarR_jet_le6_of_jets
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.Honesty.continuousOn_cmode_of_hkMem_one
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.sg_open
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Assembly6
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNstarBlock
import Submission.Work.FTS.StrongPersist.L3Rhs.N3ssPriced
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof
import Submission.Work.FTS.StrongPersist.SP6.EUz6
import Submission.Work.FTS.StrongPersist.SP6.F0SixYblk
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS.StrongPersist.StarPkg6Aux
import Submission.Work.FTS.StrongPersist.StarPkg6Fields
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.PkgJets.cosTailB
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.ClassCHon.aemeasurable_acoeff_of_source =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon

/-- **The radial mode coefficients of a general-source modal solution are a.e. measurable on
`Iz = [0,∞)`.**

`acoeff α m F = radGreen α m (cmode m F)`; for a source which is `C^∞` on the open quadrant and
honest at levels `0` and `1`, `cmode m F` is continuous on `(0,∞)`
(`Work.FTS.PhiStar.Honesty.continuousOn_cmode_of_hkMem_one`) and `(cmode m F)² ∈ L¹(0,∞)`
(`Work.FTS.PhiStar.Honesty.cmode_modeEnergy_integrable`, whose two halves are `c²/t⁴` on
`(0,1)` and `c²` on `(1,∞)`), so `z ↦ radGreen α m (cmode m F) z` is continuous on `(0,∞)` by
`Work.FTS.H2.ModalSolR.radGreenContinuousOn`; the missing point `z = 0` is null, and
`volume.restrict Iz` is `volume.restrict (Ioi 0)` up to that null set.

This is the `hacm` input of the measurability bundle of the level-`0` honesty of
`psiSeries α F`.  (The sibling `Work.FTS.ClassCHon.CmpSupp.acoeff_aemeasurable` proves the same
for a *compactly supported* source, where continuity comes from the compact support of
`cmode m F` instead.) -/
theorem aemeasurable_acoeff_of_source {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hF0 : Work.Spaces.HkMem α 0 F) (hF1 : Work.Spaces.HkMem α 1 F) :
    ∀ m : ℕ, AEMeasurable (fun z : ℝ => Work.FTS.PhiStar.Series.acoeff α m F z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  intro m
  have hα1 : α ≤ 1 := by linarith
  -- continuity of the mode coefficient `cmode m F` on `(0,∞)`
  have hcont : ContinuousOn (fun z : ℝ => Work.FTS.PhiStar.Series.cmode m F z) (Set.Ioi 0) :=
    Work.FTS.PhiStar.Honesty.continuousOn_cmode_of_hkMem_one m hsm hF1
  -- square integrability of `cmode m F` on `(0,∞)`, from the two halves of the mode energy
  have hsq : MeasureTheory.IntegrableOn
      (fun t : ℝ => (Work.FTS.PhiStar.Series.cmode m F t) ^ 2) (Set.Ioi 0) := by
    obtain ⟨hnear, hfar⟩ :=
      Work.FTS.PhiStar.Honesty.cmode_modeEnergy_integrable (α := α) m hsm hF0
    -- near `0`: `c² ≤ c²/t⁴` on `(0,1)`
    have hn1 : MeasureTheory.IntegrableOn
        (fun t : ℝ => (Work.FTS.PhiStar.Series.cmode m F t) ^ 2) (Set.Ioo 0 1) := by
      refine MeasureTheory.Integrable.mono' hnear ?_ ?_
      · have hmeas : MeasureTheory.AEStronglyMeasurable
            (fun t : ℝ => (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)
            (MeasureTheory.volume.restrict (Set.Ioo 0 1)) :=
          ((hcont.aestronglyMeasurable measurableSet_Ioi).mono_set
            (fun t ht => ht.1)).pow 2
        simpa only [Pi.pow_apply] using hmeas
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
        have ht4 : (0 : ℝ) < t ^ 4 := pow_pos ht.1 4
        have hle : t ^ 4 ≤ 1 := pow_le_one₀ ht.1.le ht.2.le
        rw [Real.norm_of_nonneg (sq_nonneg _), le_div_iff₀ ht4]
        have hmul : (Work.FTS.PhiStar.Series.cmode m F t) ^ 2 * t ^ 4
            ≤ (Work.FTS.PhiStar.Series.cmode m F t) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hle (sq_nonneg _)
        simpa using hmul
    -- far out: `(1,∞)` versus `[1,∞)` differ by the null set `{1}`
    have hn2 : MeasureTheory.IntegrableOn
        (fun t : ℝ => (Work.FTS.PhiStar.Series.cmode m F t) ^ 2) (Set.Ici 1) :=
      hfar.congr_set_ae (MeasureTheory.Ioi_ae_eq_Ici (a := (1 : ℝ))).symm
    have hun : Set.Ioi (0 : ℝ) = Set.Ioo 0 1 ∪ Set.Ici 1 := by
      ext t
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioo, Set.mem_Ici]
      constructor
      · intro ht
        rcases lt_or_ge t 1 with h | h
        · exact Or.inl ⟨ht, h⟩
        · exact Or.inr h
      · rintro (⟨h1, _⟩ | h1)
        · exact h1
        · linarith
    rw [hun]
    exact hn1.union hn2
  -- a.e. strong measurability of `cmode m F` on `(0,∞)`
  have hcm : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => Work.FTS.PhiStar.Series.cmode m F z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    hcont.aestronglyMeasurable measurableSet_Ioi
  -- continuity of the modal radial Green function on `(0,∞)`
  have hrg : ContinuousOn (Work.FTS.PhiStar.Radial.radGreen α m
      (fun t => Work.FTS.PhiStar.Series.cmode m F t)) (Set.Ioi 0) :=
    Work.FTS.H2.ModalSolR.radGreenContinuousOn hα hα1 m hsq hcm
  have hae : AEMeasurable (Work.FTS.PhiStar.Radial.radGreen α m
      (fun t => Work.FTS.PhiStar.Series.cmode m F t))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    hrg.aemeasurable measurableSet_Ioi
  -- `Iz = [0,∞)` and `(0,∞)` differ by the null set `{0}`
  have hIz : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
    rw [Work.Spaces.Iz,
      ← MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
  rw [hIz]
  simpa only [Work.FTS.PhiStar.Series.acoeff] using hae

end Work.FTS.ClassCHon
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.RadGreenFarField =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.PhiStar.Honesty

open Work.FTS.EllExist.Honesty (G1 G2 G1f radPsi_eq_G2 radPsi_hasDerivAt)
open Work.FTS.PhiStar.RadialWAux (radP radQ radPsi)

/-- `G2` is differentiable on all of `(0,∞)` with `z G2' = p·G2 - c` (`p = 2m/α`).  (Compare
`Work.FTS.EllExist.Honesty.G2_hasDerivAt`, stated on `(1,∞)` only; we need `z = 1` for the
fundamental theorem of calculus.) -/
private theorem G2_hasDerivAt_pos {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : ContinuousOn c (Set.Ioi 0))
    (hinf : MeasureTheory.IntegrableOn (fun t : ℝ => |c t| * t ^ (-(radP α m) - 1))
      (Set.Ioi 1)) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (G2 α m c) ((radP α m * G2 α m c z - c z) / z) z := by
  intro z hz
  have h := radPsi_hasDerivAt hα hα4 m hm hc hinf z hz
  have hev : radPsi α m c =ᶠ[𝓝 z] G2 α m c := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact radPsi_eq_G2 α m c hy
  have hd : (radP α m * radPsi α m c z - c z) / z
      = (radP α m * G2 α m c z - c z) / z := by
    rw [radPsi_eq_G2 α m c hz]
  exact (h.congr_of_eventuallyEq hev.symm).congr_deriv hd

/-- **The tail bound for `G2`**: `y·G2(y)² ≤ (1/p)·∫_1^∞ c²` for `p = 2m/α`. -/
private theorem G2_tail_bound {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hm : 1 ≤ m) (hc : ContinuousOn c (Set.Ioi 0))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∀ y : ℝ, 1 < y → y * (G2 α m c y) ^ 2
      ≤ (1 / radP α m) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    have h : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hp : 0 < radP α m := by
    rw [radP]
    exact div_pos (by linarith) hα
  have hp1 : 0 < 1 / radP α m := div_pos (by norm_num) hp
  have hc1 : ContinuousOn c (Set.Ioi 1) :=
    hc.mono (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  intro y hy
  have hy0 : 0 < y := lt_trans one_pos hy
  have hcs := psi_cs_of_aesm (p := radP α m) hp hy0
    ((hc1.mono (Set.Ioi_subset_Ioi hy.le)).aestronglyMeasurable measurableSet_Ioi)
    (hfar.mono_set (Set.Ioi_subset_Ioi hy.le))
  have hwt : (∫ t in Set.Ioi y, (c t) ^ 2 * t ^ (-radP α m - 1))
      ≤ y ^ (-radP α m - 1) * (∫ t in Set.Ioi y, (c t) ^ 2) := by
    have hfy : IntegrableOn (fun t : ℝ => (c t) ^ 2 * t ^ (-radP α m - 1)) (Set.Ioi y) := by
      refine Integrable.mono' (hfar.mono_set (Set.Ioi_subset_Ioi hy.le)) ?_ ?_
      · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
        exact ((hc1.mono (Set.Ioi_subset_Ioi hy.le)).pow 2).mul
          (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_trans hy0 ht))))
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := lt_trans hy0 ht
        have ht1 : (1 : ℝ) ≤ t := le_of_lt (lt_trans hy ht)
        have hpow : t ^ (-radP α m - 1) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos ht1 (by linarith)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (c t)),
          abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
        calc (c t) ^ 2 * t ^ (-radP α m - 1) ≤ (c t) ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
          _ = (c t) ^ 2 := by rw [mul_one]
    have hgy : IntegrableOn (fun t : ℝ => y ^ (-radP α m - 1) * (c t) ^ 2) (Set.Ioi y) :=
      (hfar.mono_set (Set.Ioi_subset_Ioi hy.le)).const_mul _
    have hmono := setIntegral_mono_on hfy hgy measurableSet_Ioi
      (fun t ht => by
        have hpow : t ^ (-radP α m - 1) ≤ y ^ (-radP α m - 1) :=
          Real.rpow_le_rpow_of_nonpos hy0 (le_of_lt ht) (by linarith : -radP α m - 1 ≤ 0)
        rw [mul_comm (y ^ (-radP α m - 1)) ((c t) ^ 2)]
        exact mul_le_mul_of_nonneg_left hpow (sq_nonneg _))
    rw [MeasureTheory.integral_const_mul] at hmono
    exact hmono
  have htailP : (∫ t in Set.Ioi y, (c t) ^ 2) ≤ ∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2 :=
    MeasureTheory.setIntegral_mono_set hfar (ae_of_all _ fun t => sq_nonneg (c t))
      (ae_of_all _ fun t ht => lt_trans hy ht)
  have hsq : (G2 α m c y) ^ 2
      = y ^ (2 * radP α m) * (∫ t in Set.Ioi y, c t * t ^ (-radP α m - 1)) ^ 2 := by
    have hG2y : G2 α m c y
        = y ^ (radP α m) * (∫ t in Set.Ioi y, c t * t ^ (-radP α m - 1)) := rfl
    rw [hG2y, mul_pow, ← Real.rpow_natCast (y ^ radP α m) 2, ← Real.rpow_mul hy0.le,
      show radP α m * ((2 : ℕ) : ℝ) = 2 * radP α m by push_cast; ring]
  have hA : (∫ t in Set.Ioi y, c t * t ^ (-radP α m - 1)) ^ 2
      ≤ (1 / radP α m) * y ^ (-2 * radP α m - 1)
        * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2) := by
    have hB : (∫ t in Set.Ioi y, (c t) ^ 2 * t ^ (-radP α m - 1))
        ≤ y ^ (-radP α m - 1) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2) :=
      hwt.trans (mul_le_mul_of_nonneg_left htailP (Real.rpow_nonneg hy0.le _))
    calc (∫ t in Set.Ioi y, c t * t ^ (-radP α m - 1)) ^ 2
        ≤ (1 / radP α m) * y ^ (-radP α m)
            * (∫ t in Set.Ioi y, (c t) ^ 2 * t ^ (-radP α m - 1)) := hcs
      _ ≤ (1 / radP α m) * y ^ (-radP α m)
            * (y ^ (-radP α m - 1) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)) :=
          mul_le_mul_of_nonneg_left hB
            (mul_nonneg (le_of_lt hp1) (Real.rpow_nonneg hy0.le _))
      _ = (1 / radP α m) * (y ^ (-radP α m) * y ^ (-radP α m - 1))
            * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2) := by ring
      _ = (1 / radP α m) * y ^ (-2 * radP α m - 1)
            * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2) := by
          rw [← Real.rpow_add hy0,
            show -radP α m + (-radP α m - 1) = -2 * radP α m - 1 by ring]
  have hG2sq : (G2 α m c y) ^ 2
      ≤ (1 / radP α m) * y ^ (-1 : ℝ) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2) := by
    calc (G2 α m c y) ^ 2
        = y ^ (2 * radP α m)
            * (∫ t in Set.Ioi y, c t * t ^ (-radP α m - 1)) ^ 2 := hsq
      _ ≤ y ^ (2 * radP α m)
            * ((1 / radP α m) * y ^ (-2 * radP α m - 1)
              * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)) :=
          mul_le_mul_of_nonneg_left hA (Real.rpow_nonneg hy0.le _)
      _ = (1 / radP α m) * (y ^ (2 * radP α m) * y ^ (-2 * radP α m - 1))
            * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2) := by ring
      _ = (1 / radP α m) * y ^ (-1 : ℝ) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2) := by
          rw [← Real.rpow_add hy0,
            show 2 * radP α m + (-2 * radP α m - 1) = -1 by ring]
  calc y * (G2 α m c y) ^ 2
      ≤ y * ((1 / radP α m) * y ^ (-1 : ℝ) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)) :=
        mul_le_mul_of_nonneg_left hG2sq hy0.le
    _ = (1 / radP α m) * (y * y ^ (-1 : ℝ)) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2) := by ring
    _ = (1 / radP α m) * 1 * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2) := by
        rw [Real.rpow_neg_one, mul_inv_cancel₀ (ne_of_gt hy0)]
    _ = (1 / radP α m) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2) := by ring

/-- **The `G2` interval estimate**: for every `y > 1`,
`∫_1^y G2² ≤ 2/(1+2p)·((1/p)·P + (2/(1+2p))·P)`, `P = ∫_1^∞ c²`. -/
private theorem G2_far_interval_bound {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : ContinuousOn c (Set.Ioi 0))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∀ y : ℝ, 1 < y → (∫ z in (1 : ℝ)..y, (G2 α m c z) ^ 2)
      ≤ 2 / (1 + 2 * radP α m)
        * ((1 / radP α m) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)
          + (2 / (1 + 2 * radP α m)) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)) := by
  have hp : 0 < radP α m := by
    rw [radP]
    exact div_pos (by positivity) hα
  have hp1 : 0 < 1 + 2 * radP α m := by linarith
  have hc1 : ContinuousOn c (Set.Ioi 1) :=
    hc.mono (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  have hinf : MeasureTheory.IntegrableOn (fun t : ℝ => |c t| * t ^ (-(radP α m) - 1))
      (Set.Ioi 1) :=
    integrableOn_abs_mul_rpow_of_sq (p := radP α m) (by linarith) hc1 hfar
  have hderiv0 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (G2 α m c) ((radP α m * G2 α m c z - c z) / z) z :=
    G2_hasDerivAt_pos hα hα4 hm hc hinf
  have henergy : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun y : ℝ => y * (G2 α m c y) ^ 2)
      ((1 + 2 * radP α m) * (G2 α m c z) ^ 2 - 2 * (c z * G2 α m c z)) z := by
    intro z hz
    have h := radFar_hasDerivAt_mul_sq (A := G2 α m c) (s := radP α m) (d := fun w => -(c w))
      hderiv0 z hz
    refine h.congr_deriv ?_
    ring_nf
  have hcont0 : ContinuousOn (G2 α m c) (Set.Ioi (0 : ℝ)) := fun z hz =>
    (hderiv0 z hz).continuousAt.continuousWithinAt
  intro y hy
  have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
  have hIcc : Set.Icc (1 : ℝ) y ⊆ Set.Ioi (0 : ℝ) := by
    intro z hz
    show (0 : ℝ) < z
    linarith [hz.1]
  have hcontG : ContinuousOn (G2 α m c) (Set.Icc (1 : ℝ) y) := hcont0.mono hIcc
  have hcontc : ContinuousOn c (Set.Icc (1 : ℝ) y) := hc.mono hIcc
  have hint_sq : IntervalIntegrable (fun z : ℝ => (G2 α m c z) ^ 2) volume (1 : ℝ) y :=
    (hcontG.pow 2).intervalIntegrable_of_Icc hy.le
  have hint_cG : IntervalIntegrable (fun z : ℝ => c z * G2 α m c z) volume (1 : ℝ) y :=
    (hcontc.mul hcontG).intervalIntegrable_of_Icc hy.le
  have hint_csq : IntervalIntegrable (fun z : ℝ => (c z) ^ 2) volume (1 : ℝ) y :=
    (hcontc.pow 2).intervalIntegrable_of_Icc hy.le
  have hcontD : ContinuousOn (fun z : ℝ => (1 + 2 * radP α m) * (G2 α m c z) ^ 2
      - 2 * (c z * G2 α m c z)) (Set.Icc (1 : ℝ) y) :=
    ((hcontG.pow 2).const_mul _).sub ((hcontc.mul hcontG).const_mul 2)
  have hintD : IntervalIntegrable (fun z : ℝ => (1 + 2 * radP α m) * (G2 α m c z) ^ 2
      - 2 * (c z * G2 α m c z)) volume (1 : ℝ) y :=
    hcontD.intervalIntegrable_of_Icc hy.le
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (1 : ℝ)) (b := y)
    (f := fun t : ℝ => t * (G2 α m c t) ^ 2)
    (f' := fun z : ℝ => (1 + 2 * radP α m) * (G2 α m c z) ^ 2 - 2 * (c z * G2 α m c z))
    (fun z hz => by
      rw [Set.uIcc_of_le hy.le] at hz
      exact henergy z (lt_of_lt_of_le zero_lt_one hz.1))
    hintD
  rw [intervalIntegral.integral_sub (hint_sq.const_mul _) (hint_cG.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, one_mul] at hFTC
  have habs : (∫ z in (1 : ℝ)..y, c z * G2 α m c z)
      ≤ ∫ z in (1 : ℝ)..y, |c z * G2 α m c z| :=
    intervalIntegral.integral_mono_on hy.le hint_cG hint_cG.abs (fun z _ => le_abs_self _)
  have hint_abs : IntervalIntegrable (fun z : ℝ => |c z * G2 α m c z|) volume (1 : ℝ) y :=
    hint_cG.abs
  have hamgm : 2 * (∫ z in (1 : ℝ)..y, |c z * G2 α m c z|)
      ≤ ((1 + 2 * radP α m) / 2) * (∫ z in (1 : ℝ)..y, (G2 α m c z) ^ 2)
        + (2 / (1 + 2 * radP α m)) * (∫ z in (1 : ℝ)..y, (c z) ^ 2) := by
    have hlm : ((1 + 2 * radP α m) / 2) * (2 / (1 + 2 * radP α m)) = 1 := by
      rw [div_mul_div_comm, mul_comm (1 + 2 * radP α m) 2]
      exact div_self (by positivity)
    have hpt : ∀ z ∈ Set.Icc (1 : ℝ) y,
        2 * |c z * G2 α m c z|
          ≤ ((1 + 2 * radP α m) / 2) * (G2 α m c z) ^ 2
            + (2 / (1 + 2 * radP α m)) * (c z) ^ 2 := by
      intro z _
      have h := radFar_amgm (l := (1 + 2 * radP α m) / 2) (m := 2 / (1 + 2 * radP α m))
        (by linarith) (div_pos (by norm_num) hp1) hlm (X := G2 α m c z) (Y := c z)
      have h2 : 2 * |(G2 α m c z) * (c z)| = 2 * |c z * G2 α m c z| := by
        rw [mul_comm (G2 α m c z) (c z)]
      rwa [h2] at h
    have hint_lhs : IntervalIntegrable (fun z : ℝ => 2 * |c z * G2 α m c z|) volume (1 : ℝ) y :=
      hint_abs.const_mul 2
    have hint_rhs : IntervalIntegrable (fun z : ℝ =>
        ((1 + 2 * radP α m) / 2) * (G2 α m c z) ^ 2
          + (2 / (1 + 2 * radP α m)) * (c z) ^ 2) volume (1 : ℝ) y :=
      (hint_sq.const_mul _).add (hint_csq.const_mul _)
    have hmono := intervalIntegral.integral_mono_on hy.le hint_lhs hint_rhs hpt
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
      (hint_sq.const_mul _) (hint_csq.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
    exact hmono
  have hcsq_le : (∫ z in (1 : ℝ)..y, (c z) ^ 2) ≤ ∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2 := by
    rw [intervalIntegral.integral_of_le hy.le]
    exact MeasureTheory.setIntegral_mono_set hfar (ae_of_all _ fun t => sq_nonneg (c t))
      (ae_of_all _ fun t ht => ht.1)
  have hY : y * (G2 α m c y) ^ 2 ≤ (1 / radP α m) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2) :=
    G2_tail_bound hα hm hc hfar y hy
  set P : ℝ := ∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2 with hPdef
  set I : ℝ := ∫ z in (1 : ℝ)..y, (G2 α m c z) ^ 2 with hIdef
  set J : ℝ := ∫ z in (1 : ℝ)..y, c z * G2 α m c z with hJdef
  set K : ℝ := ∫ z in (1 : ℝ)..y, |c z * G2 α m c z| with hKdef
  set Q : ℝ := ∫ z in (1 : ℝ)..y, (c z) ^ 2 with hQdef
  set Y : ℝ := y * (G2 α m c y) ^ 2 with hYdef
  set C1 : ℝ := (G2 α m c 1) ^ 2 with hC1def
  have hC1nn : 0 ≤ C1 := by rw [hC1def]; exact sq_nonneg _
  have hkey : (1 + 2 * radP α m) * I
      ≤ (1 / radP α m) * P + ((1 + 2 * radP α m) / 2) * I
        + (2 / (1 + 2 * radP α m)) * P := by
    have h1 : (1 + 2 * radP α m) * I = Y - C1 + 2 * J := by
      rw [hIdef, hYdef, hC1def, hJdef]
      linarith [hFTC]
    have h2 : Y ≤ (1 / radP α m) * P := by rw [hYdef, hPdef]; exact hY
    have h4 : 2 * J ≤ 2 * K := by rw [hJdef, hKdef]; linarith [habs]
    have h5 : 2 * K ≤ ((1 + 2 * radP α m) / 2) * I + (2 / (1 + 2 * radP α m)) * Q := by
      rw [hKdef, hIdef, hQdef]; exact hamgm
    have h6 : (2 / (1 + 2 * radP α m)) * Q ≤ (2 / (1 + 2 * radP α m)) * P := by
      rw [hQdef, hPdef]
      exact mul_le_mul_of_nonneg_left hcsq_le (le_of_lt (div_pos (by norm_num) hp1))
    linarith [h1, h2, hC1nn, h4, h5, h6]
  have hfinal : I ≤ 2 / (1 + 2 * radP α m) * ((1 / radP α m) * P
      + (2 / (1 + 2 * radP α m)) * P) := by
    have hstep : ((1 + 2 * radP α m) / 2) * I
        ≤ (1 / radP α m) * P + (2 / (1 + 2 * radP α m)) * P := by
      linarith [hkey]
    have hmul : 2 * (((1 + 2 * radP α m) / 2) * I)
        ≤ 2 * ((1 / radP α m) * P + (2 / (1 + 2 * radP α m)) * P) :=
      mul_le_mul_of_nonneg_left hstep (by norm_num)
    have heq : 2 * (((1 + 2 * radP α m) / 2) * I) = (1 + 2 * radP α m) * I := by ring
    rw [heq] at hmul
    rw [show 2 / (1 + 2 * radP α m)
          * ((1 / radP α m) * P + (2 / (1 + 2 * radP α m)) * P)
        = 2 * ((1 / radP α m) * P + (2 / (1 + 2 * radP α m)) * P) / (1 + 2 * radP α m)
        from by ring,
      le_div_iff₀ hp1]
    linarith [hmul]
  rw [hIdef, hPdef] at hfinal
  exact hfinal

/-- **Far-field weighted `L²`-integrability of `G2`.** -/
theorem G2_sq_w_sq_integrableOn_far {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : ContinuousOn c (Set.Ioi 0))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (G2 α m c z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 1) := by
  have hp : 0 < radP α m := by
    rw [radP]
    exact div_pos (by positivity) hα
  have hp1 : 0 < 1 + 2 * radP α m := by linarith
  have hc1 : ContinuousOn c (Set.Ioi 1) :=
    hc.mono (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  have hinf : MeasureTheory.IntegrableOn (fun t : ℝ => |c t| * t ^ (-(radP α m) - 1))
      (Set.Ioi 1) :=
    integrableOn_abs_mul_rpow_of_sq (p := radP α m) (by linarith) hc1 hfar
  have hcont0 : ContinuousOn (G2 α m c) (Set.Ioi (0 : ℝ)) := fun z hz =>
    ((G2_hasDerivAt_pos hα hα4 hm hc hinf z hz)).continuousAt.continuousWithinAt
  have hb := G2_far_interval_bound hα hα4 hm hc hfar
  have hT : 0 ≤ 2 / (1 + 2 * radP α m)
      * ((1 / radP α m) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)
        + (2 / (1 + 2 * radP α m)) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)) := by
    have hPnn : 0 ≤ ∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2 :=
      setIntegral_nonneg measurableSet_Ioi (fun t _ => sq_nonneg _)
    have h1 : 0 ≤ 1 / radP α m := le_of_lt (div_pos (by norm_num) hp)
    have h2 : 0 ≤ 2 / (1 + 2 * radP α m) := le_of_lt (div_pos (by norm_num) hp1)
    exact mul_nonneg h2 (add_nonneg (mul_nonneg h1 hPnn) (mul_nonneg h2 hPnn))
  have hsq : MeasureTheory.IntegrableOn (fun z : ℝ => (G2 α m c z) ^ 2) (Set.Ioi 1) :=
    radFar_integrableOn_Ioi_one_of_sq_interval_bound hT
      (T := 2 / (1 + 2 * radP α m)
        * ((1 / radP α m) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)
          + (2 / (1 + 2 * radP α m)) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)))
      (fun z => sq_nonneg _) (hcont0.pow 2) hb
  exact radFar_integrableOn_mul_w_sq hsq

end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.RadGreenFarG1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.PhiStar.Honesty

open Work.FTS.EllExist.Honesty (G1 G1f)
open Work.FTS.PhiStar.RadialWAux (radQ)

/-- **The `G1` interval estimate** (in the case where `G1f` is integrable on `(0,1)`, so that `G1`
is differentiable and `G1(1)` is an honest number): for every `y > 1`,
`∫_1^y G1² ≤ (2/(2q-1))·(G1(1)² + (2/(2q-1))·P)`, `q = (2m+5)/α`, `P = ∫_1^∞ c²`. -/
private theorem G1_far_interval_bound {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : ContinuousOn c (Set.Ioi 0))
    (hInt : MeasureTheory.IntegrableOn (G1f α m c) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∀ y : ℝ, 1 < y → (∫ z in (1 : ℝ)..y, (G1 α m c z) ^ 2)
      ≤ 2 / (2 * radQ α m - 1)
        * ((G1 α m c 1) ^ 2
          + (2 / (2 * radQ α m - 1)) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)) := by
  have hq28 : 28 ≤ radQ α m := by
    rw [radQ, le_div_iff₀ hα]
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith
  have hq1 : 0 < 2 * radQ α m - 1 := by linarith
  have hq21 : 0 < (2 * radQ α m - 1) / 2 := by linarith
  have hqm : 0 < 2 / (2 * radQ α m - 1) := div_pos (by norm_num) hq1
  have hderiv0 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (G1 α m c) (((-radQ α m) * G1 α m c z + c z) / z) z :=
    Work.FTS.EllExist.Honesty.G1_hasDerivAt_of_intervalIntegrable hc hInt
  have henergy : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun y : ℝ => y * (G1 α m c y) ^ 2)
      ((1 - 2 * radQ α m) * (G1 α m c z) ^ 2 + 2 * (c z * G1 α m c z)) z := by
    intro z hz
    have h := radFar_hasDerivAt_mul_sq (A := G1 α m c) (s := -radQ α m) (d := c) hderiv0 z hz
    refine h.congr_deriv ?_
    ring_nf
  have hcont0 : ContinuousOn (G1 α m c) (Set.Ioi (0 : ℝ)) := fun z hz =>
    (hderiv0 z hz).continuousAt.continuousWithinAt
  intro y hy
  have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
  have hIcc : Set.Icc (1 : ℝ) y ⊆ Set.Ioi (0 : ℝ) := by
    intro z hz
    show (0 : ℝ) < z
    linarith [hz.1]
  have hcontG : ContinuousOn (G1 α m c) (Set.Icc (1 : ℝ) y) := hcont0.mono hIcc
  have hcontc : ContinuousOn c (Set.Icc (1 : ℝ) y) := hc.mono hIcc
  have hint_sq : IntervalIntegrable (fun z : ℝ => (G1 α m c z) ^ 2) volume (1 : ℝ) y :=
    (hcontG.pow 2).intervalIntegrable_of_Icc hy.le
  have hint_cG : IntervalIntegrable (fun z : ℝ => c z * G1 α m c z) volume (1 : ℝ) y :=
    (hcontc.mul hcontG).intervalIntegrable_of_Icc hy.le
  have hint_csq : IntervalIntegrable (fun z : ℝ => (c z) ^ 2) volume (1 : ℝ) y :=
    (hcontc.pow 2).intervalIntegrable_of_Icc hy.le
  have hcontD : ContinuousOn (fun z : ℝ => (1 - 2 * radQ α m) * (G1 α m c z) ^ 2
      + 2 * (c z * G1 α m c z)) (Set.Icc (1 : ℝ) y) :=
    ((hcontG.pow 2).const_mul _).add ((hcontc.mul hcontG).const_mul 2)
  have hintD : IntervalIntegrable (fun z : ℝ => (1 - 2 * radQ α m) * (G1 α m c z) ^ 2
      + 2 * (c z * G1 α m c z)) volume (1 : ℝ) y :=
    hcontD.intervalIntegrable_of_Icc hy.le
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (1 : ℝ)) (b := y)
    (f := fun t : ℝ => t * (G1 α m c t) ^ 2)
    (f' := fun z : ℝ => (1 - 2 * radQ α m) * (G1 α m c z) ^ 2 + 2 * (c z * G1 α m c z))
    (fun z hz => by
      rw [Set.uIcc_of_le hy.le] at hz
      exact henergy z (lt_of_lt_of_le zero_lt_one hz.1))
    hintD
  rw [intervalIntegral.integral_add (hint_sq.const_mul _) (hint_cG.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, one_mul] at hFTC
  have habs : (∫ z in (1 : ℝ)..y, c z * G1 α m c z)
      ≤ ∫ z in (1 : ℝ)..y, |c z * G1 α m c z| :=
    intervalIntegral.integral_mono_on hy.le hint_cG hint_cG.abs (fun z _ => le_abs_self _)
  have hint_abs : IntervalIntegrable (fun z : ℝ => |c z * G1 α m c z|) volume (1 : ℝ) y :=
    hint_cG.abs
  have hamgm : 2 * (∫ z in (1 : ℝ)..y, |c z * G1 α m c z|)
      ≤ ((2 * radQ α m - 1) / 2) * (∫ z in (1 : ℝ)..y, (G1 α m c z) ^ 2)
        + (2 / (2 * radQ α m - 1)) * (∫ z in (1 : ℝ)..y, (c z) ^ 2) := by
    have hlm : ((2 * radQ α m - 1) / 2) * (2 / (2 * radQ α m - 1)) = 1 := by
      rw [div_mul_div_comm, mul_comm (2 * radQ α m - 1) 2]
      exact div_self (mul_ne_zero (by norm_num) (ne_of_gt hq1))
    have hpt : ∀ z ∈ Set.Icc (1 : ℝ) y,
        2 * |c z * G1 α m c z|
          ≤ ((2 * radQ α m - 1) / 2) * (G1 α m c z) ^ 2
            + (2 / (2 * radQ α m - 1)) * (c z) ^ 2 := by
      intro z _
      have h := radFar_amgm (l := (2 * radQ α m - 1) / 2) (m := 2 / (2 * radQ α m - 1))
        hq21 hqm hlm (X := G1 α m c z) (Y := c z)
      have h2 : 2 * |(G1 α m c z) * (c z)| = 2 * |c z * G1 α m c z| := by
        rw [mul_comm (G1 α m c z) (c z)]
      rwa [h2] at h
    have hint_lhs : IntervalIntegrable (fun z : ℝ => 2 * |c z * G1 α m c z|) volume (1 : ℝ) y :=
      hint_abs.const_mul 2
    have hint_rhs : IntervalIntegrable (fun z : ℝ =>
        ((2 * radQ α m - 1) / 2) * (G1 α m c z) ^ 2
          + (2 / (2 * radQ α m - 1)) * (c z) ^ 2) volume (1 : ℝ) y :=
      (hint_sq.const_mul _).add (hint_csq.const_mul _)
    have hmono := intervalIntegral.integral_mono_on hy.le hint_lhs hint_rhs hpt
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
      (hint_sq.const_mul _) (hint_csq.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
    exact hmono
  have hcsq_le : (∫ z in (1 : ℝ)..y, (c z) ^ 2) ≤ ∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2 := by
    rw [intervalIntegral.integral_of_le hy.le]
    exact MeasureTheory.setIntegral_mono_set hfar (ae_of_all _ fun t => sq_nonneg (c t))
      (ae_of_all _ fun t ht => ht.1)
  set P : ℝ := ∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2 with hPdef
  set I : ℝ := ∫ z in (1 : ℝ)..y, (G1 α m c z) ^ 2 with hIdef
  set J : ℝ := ∫ z in (1 : ℝ)..y, c z * G1 α m c z with hJdef
  set K : ℝ := ∫ z in (1 : ℝ)..y, |c z * G1 α m c z| with hKdef
  set Q : ℝ := ∫ z in (1 : ℝ)..y, (c z) ^ 2 with hQdef
  set Y : ℝ := y * (G1 α m c y) ^ 2 with hYdef
  set C1 : ℝ := (G1 α m c 1) ^ 2 with hC1def
  have hYnn : 0 ≤ Y := by
    rw [hYdef]
    exact mul_nonneg hy0.le (sq_nonneg _)
  have hkey : (2 * radQ α m - 1) * I
      ≤ C1 + ((2 * radQ α m - 1) / 2) * I + (2 / (2 * radQ α m - 1)) * P := by
    have h1 : (2 * radQ α m - 1) * I = C1 - Y + 2 * J := by
      rw [hIdef, hC1def, hYdef, hJdef]
      linarith [hFTC]
    have h4 : 2 * J ≤ 2 * K := by rw [hJdef, hKdef]; linarith [habs]
    have h5 : 2 * K ≤ ((2 * radQ α m - 1) / 2) * I + (2 / (2 * radQ α m - 1)) * Q := by
      rw [hKdef, hIdef, hQdef]; exact hamgm
    have h6 : (2 / (2 * radQ α m - 1)) * Q ≤ (2 / (2 * radQ α m - 1)) * P := by
      rw [hQdef, hPdef]
      exact mul_le_mul_of_nonneg_left hcsq_le (le_of_lt hqm)
    linarith [h1, hYnn, h4, h5, h6]
  have hfinal : I ≤ 2 / (2 * radQ α m - 1) * (C1 + (2 / (2 * radQ α m - 1)) * P) := by
    have hstep : ((2 * radQ α m - 1) / 2) * I ≤ C1 + (2 / (2 * radQ α m - 1)) * P := by
      linarith [hkey]
    have hmul := mul_le_mul_of_nonneg_left hstep (le_of_lt hqm)
    have hcoef : (2 / (2 * radQ α m - 1)) * ((2 * radQ α m - 1) / 2) = 1 := by
      rw [div_mul_div_comm, mul_comm 2 (2 * radQ α m - 1)]
      exact div_self (mul_ne_zero (ne_of_gt hq1) (by norm_num))
    have hfirst : (2 / (2 * radQ α m - 1) * ((2 * radQ α m - 1) / 2)) * I = I := by
      rw [hcoef, one_mul]
    calc I = (2 / (2 * radQ α m - 1) * ((2 * radQ α m - 1) / 2)) * I := hfirst.symm
      _ = (2 / (2 * radQ α m - 1)) * (((2 * radQ α m - 1) / 2) * I) := by ring
      _ ≤ (2 / (2 * radQ α m - 1)) * (C1 + (2 / (2 * radQ α m - 1)) * P) := hmul
  rw [hIdef, hC1def, hPdef] at hfinal
  exact hfinal

/-- **Far-field weighted `L²`-integrability of `G1`.** -/
theorem G1_sq_w_sq_integrableOn_far {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : ContinuousOn c (Set.Ioi 0))
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (G1 α m c z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 1) := by
  by_cases hgood : MeasureTheory.IntegrableOn (G1f α m c) (Set.Ioc (0 : ℝ) 1)
  · have hInt : MeasureTheory.IntegrableOn (G1f α m c) (Set.Ioo 0 1) :=
      hgood.mono_set (fun z hz => ⟨hz.1, le_of_lt hz.2⟩)
    have hderiv0 : ∀ z ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (G1 α m c) (((-radQ α m) * G1 α m c z + c z) / z) z :=
      Work.FTS.EllExist.Honesty.G1_hasDerivAt_of_intervalIntegrable hc hInt
    have hcont0 : ContinuousOn (G1 α m c) (Set.Ioi (0 : ℝ)) := fun z hz =>
      (hderiv0 z hz).continuousAt.continuousWithinAt
    have hb := G1_far_interval_bound hα hα4 hm hc hInt hfar
    have hq28 : 28 ≤ radQ α m := by
      rw [radQ, le_div_iff₀ hα]
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      nlinarith
    have hq1 : 0 < 2 * radQ α m - 1 := by linarith
    have hT : 0 ≤ 2 / (2 * radQ α m - 1)
        * ((G1 α m c 1) ^ 2
          + (2 / (2 * radQ α m - 1)) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)) := by
      have hPnn : 0 ≤ ∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2 :=
        setIntegral_nonneg measurableSet_Ioi (fun t _ => sq_nonneg _)
      have h2 : 0 ≤ 2 / (2 * radQ α m - 1) :=
        le_of_lt (div_pos (by norm_num) hq1)
      exact mul_nonneg h2 (add_nonneg (sq_nonneg _) (mul_nonneg h2 hPnn))
    have hsq : MeasureTheory.IntegrableOn (fun z : ℝ => (G1 α m c z) ^ 2) (Set.Ioi 1) :=
      radFar_integrableOn_Ioi_one_of_sq_interval_bound hT
        (T := 2 / (2 * radQ α m - 1)
          * ((G1 α m c 1) ^ 2
            + (2 / (2 * radQ α m - 1)) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)))
        (fun z => sq_nonneg _) (hcont0.pow 2) hb
    exact radFar_integrableOn_mul_w_sq hsq
  · have hzero : ∀ z ∈ Set.Ioi (1 : ℝ),
        (fun z : ℝ => (0 : ℝ)) z = (G1 α m c z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
      intro z hz
      show (0 : ℝ) = (G1 α m c z) ^ 2 * (Work.Spaces.w z) ^ 2
      rw [Work.FTS.EllExist.Honesty.G1_eq_zero_of_not_integrableOn m hgood hz]
      ring
    exact IntegrableOn.congr_fun
      (integrableOn_zero : MeasureTheory.IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Set.Ioi 1))
      hzero measurableSet_Ioi

end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.T4Honest.T4Leaf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C.T4Honest

open Work.FTS.StrongPersist.N6Trans.T1Hon

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- **The leaf-sum bound for the `D_θ`-transport pairing with a `D`-sup coefficient.** -/
theorem T4LeafSumBound : ∃ Cb : ℝ, 0 < Cb ∧
    ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.VocabO.WDMem 4 f →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      Work.Spaces.DecayAll 4 g →
      Work.FTS.TransportS.leafSum α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g
        ≤ Cb * Work.FTS.VocabO.WDp 4 f * Work.Spaces.HkSq α 4 g := by
  obtain ⟨C, hCpos, hC⟩ := T4SlotBound
  refine ⟨75 * C, by linarith, ?_⟩
  intro α f g hα hα1 hf hwf hg hmg hdg
  set u : ℝ → ℝ → ℝ := fun z θ => f z θ * Work.Spaces.Dth g z θ with hu
  set K : ℝ := C * Work.FTS.VocabO.WDp 4 f * Work.Spaces.HkSq α 4 g with hKdef
  have hK : 0 ≤ K := by
    rw [hKdef]
    exact mul_nonneg (mul_nonneg (le_of_lt hCpos)
      (Work.FTS.OpenPkg.WDp_nonneg 4 f)) (Work.Spaces.HkSq_nonneg α 4 g)
  have e1 : t1W Work.Spaces.eta = Work.FTS.TransportS.leafEta := rfl
  have e2 : t1W 0 = Work.FTS.TransportS.leafOne := by
    funext z θ
    simp only [t1W, Work.FTS.TransportS.leafOne, neg_zero, Real.rpow_zero, mul_one]
  have e3 : t1W (Work.Spaces.gam α) = Work.FTS.TransportS.leafGam α := rfl
  have key : ∀ a b : ℕ, a + b ≤ 4 →
      |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafEta a b u g|
          + |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafOne a b u g|
          + (if 1 ≤ a then
              |Work.FTS.TransportS.slotPairing (Work.FTS.TransportS.leafGam α) a b u g|
             else 0)
        ≤ 3 * K := by
    intro a b hab
    have h1 : |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafEta a b u g| ≤ K := by
      have ht := hC α f g hα hα1 hf hwf hg hmg hdg a b hab Work.Spaces.eta
        (fun _ => Or.inr rfl) (fun _ => Or.inr (Or.inl rfl))
      rw [← hKdef] at ht
      rw [e1] at ht
      exact ht
    have h2 : |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafOne a b u g| ≤ K := by
      have ht := hC α f g hα hα1 hf hwf hg hmg hdg a b hab 0
        (fun _ => Or.inl rfl) (fun _ => Or.inl rfl)
      rw [← hKdef] at ht
      rw [e2] at ht
      exact ht
    by_cases ha : 1 ≤ a
    · have h3 : |Work.FTS.TransportS.slotPairing (Work.FTS.TransportS.leafGam α) a b u g|
          ≤ K := by
        have ht := hC α f g hα hα1 hf hwf hg hmg hdg a b hab (Work.Spaces.gam α)
          (fun h => absurd h (by omega)) (fun _ => Or.inr (Or.inr rfl))
        rw [← hKdef] at ht
        rw [e3] at ht
        exact ht
      rw [if_pos ha]
      linarith
    · rw [if_neg ha]
      linarith
  have hsum : (∑ a ∈ Finset.range 5, ∑ b ∈ Finset.range 5,
        (if a + b ≤ 4 then
          |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafEta a b u g|
            + |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafOne a b u g|
            + (if 1 ≤ a then
                |Work.FTS.TransportS.slotPairing (Work.FTS.TransportS.leafGam α) a b u g|
              else 0)
        else 0))
      ≤ ∑ a ∈ Finset.range 5, ∑ b ∈ Finset.range 5, (3 * K) := by
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
    by_cases hab : a + b ≤ 4
    · rw [if_pos hab]; exact key a b hab
    · rw [if_neg hab]; linarith
  rw [Work.FTS.TransportS.leafSum]
  calc (∑ a ∈ Finset.range 5, ∑ b ∈ Finset.range 5,
        (if a + b ≤ 4 then
          |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafEta a b u g|
            + |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafOne a b u g|
            + (if 1 ≤ a then
                |Work.FTS.TransportS.slotPairing (Work.FTS.TransportS.leafGam α) a b u g|
              else 0)
        else 0))
      ≤ ∑ a ∈ Finset.range 5, ∑ b ∈ Finset.range 5, (3 * K) := hsum
    _ = 75 * K := by
        simp only [Finset.sum_const, Finset.card_range]
        ring
    _ = 75 * C * Work.FTS.VocabO.WDp 4 f * Work.Spaces.HkSq α 4 g := by
        rw [hKdef]; ring

end Work.FTS.StrongEps.E4R3.N4C.T4Honest
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.rows.rowsN3b =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.N4C.rows

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **Row 18 in the honest class**: `|(N₃^{*g}, g)| ≤ K α^{3/2} X²`. -/
theorem rowN3sg_honest (IP : ℝ → Fn → Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      |IP α (Work.FTS.Nonlin.N3sg α Φs g) g|
        ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g ^ 2) := by
  have hCt : 0 < Ct := hE.pos.1
  refine ⟨4 * Ct * max Cs 1 + 1, by positivity, ?_⟩
  intro α g Φs Φg hC
  have hα : 0 < α := hC.hα
  have hα1 : α ≤ 1 := hC.hα1
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hC.hαα₂⟩
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hA0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hCs1 : 0 ≤ max Cs 1 := le_of_lt (lt_of_lt_of_le zero_lt_one (le_max_right Cs 1))
  -- the star package and the coefficient `f = V(Φ̃_*)`
  have hs2 : Work.FTS.VocabO2.StarPkgo2 α Cs Φs := hC.hs
  have hs : Work.FTS.VocabO.StarPkgo α Cs Φs := hs2.toStarPkgo
  have hfsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) :=
    Work.FTS.NonlinRows.smoothOpen_Vop
      (Work.FTS.NonlinRows.smoothOpen_PhiTs hα hα1 hs)
  have hfWmem : Work.Spaces.WlInfMem α 4
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) := hs2.VW.1
  have hfWle : Work.Spaces.WlInf α 4
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) ≤ max Cs 1 * α :=
    le_trans hs2.VW.2 (mul_le_mul_of_nonneg_right (le_max_left Cs 1) hα.le)
  have hfΔmem : Work.FTS.VocabO.CoefThMem 3
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) := hs.Vth.1
  have hfΔle : Work.FTS.VocabO.CoefTh 3
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) ≤ max Cs 1 * α :=
    le_trans hs.Vth.2 (mul_le_mul_of_nonneg_right (le_max_left Cs 1) hα.le)
  -- the `g`-side data
  have hreg4 : Work.FTS.VocabO.HQo α 4 g := hC.hqo4
  have hmem5 : Work.Spaces.HkMem α 5 g := hC.hkMem5
  have hDzMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz g) := hC.hkMemDz
  have hDzSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz g) := hC.hSmoothOpen.Dz
  -- the product `V(Φ̃_*)·D_z g` is in `ℋ⁴` (also the honesty of the first argument of `IP`)
  have hprod : Work.Spaces.HkMem α 4
      (fun z θ => Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ
        * Work.Spaces.Dz g z θ) :=
    (hN.wprod α hIoc (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) (Work.Spaces.Dz g)
      hfsm hfWmem ⟨hDzSm, hDzMem⟩).1
  have hprodQ : Work.FTS.VocabO.HQo α 4
      (fun z θ => Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ
        * Work.Spaces.Dz g z θ) :=
    ⟨hfsm.mul hDzSm, hprod⟩
  -- `N₃^{*g}` is `-2α` times that product
  have hN3 : Work.FTS.Nonlin.N3sg α Φs g
      = fun z θ => (-2 * α) * (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ
          * Work.Spaces.Dz g z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N3sg]
    ring
  have hIPeq : IP α (Work.FTS.Nonlin.N3sg α Φs g) g
      = (-2 * α) * IP α (fun z θ => Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ
          * Work.Spaces.Dz g z θ) g := by
    rw [hN3]
    exact hE.smul α hIoc (-2 * α) _ g hprodQ hreg4
  rw [hIPeq]
  have habs : |(-2 : ℝ) * α| = 2 * α := by
    rw [abs_of_neg (by linarith : (-2 : ℝ) * α < 0)]
    ring
  rw [abs_mul, habs]
  -- the `D_z`-transport estimate for the coefficient `V(Φ̃_*)`
  have ht3 := hE.t3 α hIoc (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) g
    hfsm hfWmem hfΔmem hC.hSmoothOpen hC.hkMem4 hmem5 hC.hdecay
  refine (mul_le_mul_of_nonneg_left ht3 (by linarith : (0 : ℝ) ≤ 2 * α)).trans ?_
  -- the weighted sum of the two coefficient norms is `≤ 2 Cs α`
  have hWsum : Work.Spaces.WlInf α 4
        (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))
      + Work.FTS.VocabO.CoefTh 3 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))
      ≤ 2 * (max Cs 1 * α) := by
    linarith
  have hstep : Ct * α ^ (-(1 / 2 : ℝ))
        * (Work.Spaces.WlInf α 4 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))
          + Work.FTS.VocabO.CoefTh 3 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)))
        * Work.FTS.Nonlin.Xn α g ^ 2
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * (2 * (max Cs 1 * α)) * Work.FTS.Nonlin.Xn α g ^ 2 := by
    have hpre : (0 : ℝ) ≤ Ct * α ^ (-(1 / 2 : ℝ)) := mul_nonneg hCt.le hA0
    have hX2 : 0 ≤ Work.FTS.Nonlin.Xn α g ^ 2 := pow_nonneg hX0 2
    calc Ct * α ^ (-(1 / 2 : ℝ))
          * (Work.Spaces.WlInf α 4 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))
            + Work.FTS.VocabO.CoefTh 3 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)))
          * Work.FTS.Nonlin.Xn α g ^ 2
        = (Ct * α ^ (-(1 / 2 : ℝ))
            * (Work.Spaces.WlInf α 4 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))
              + Work.FTS.VocabO.CoefTh 3
                  (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))))
          * Work.FTS.Nonlin.Xn α g ^ 2 := by ring
      _ ≤ (Ct * α ^ (-(1 / 2 : ℝ)) * (2 * (max Cs 1 * α))) * Work.FTS.Nonlin.Xn α g ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWsum hpre) hX2
      _ = Ct * α ^ (-(1 / 2 : ℝ)) * (2 * (max Cs 1 * α)) * Work.FTS.Nonlin.Xn α g ^ 2 := by
          ring
  refine (mul_le_mul_of_nonneg_left hstep (by linarith : (0 : ℝ) ≤ 2 * α)).trans ?_
  -- `α · α^{-1/2} · α = α^{3/2}`
  have hpow : α * α ^ (-(1 / 2 : ℝ)) * α = α ^ (3 / 2 : ℝ) := by
    have h1 := Real.rpow_add hα (1 : ℝ) (1 / 2 : ℝ)
    rw [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num, Real.rpow_one] at h1
    have h2 := Real.rpow_add hα (1 : ℝ) (-(1 / 2 : ℝ))
    rw [show (1 : ℝ) + -(1 / 2) = 1 / 2 by norm_num, Real.rpow_one] at h2
    rw [h1, h2]
    ring
  have harith : 2 * α * (Ct * α ^ (-(1 / 2 : ℝ)) * (2 * (max Cs 1 * α))
        * Work.FTS.Nonlin.Xn α g ^ 2)
      = 4 * Ct * max Cs 1 * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g ^ 2) := by
    rw [← hpow]
    ring
  rw [harith]
  have h32 : 0 ≤ α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g ^ 2 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (pow_nonneg hX0 2)
  have hcs : 0 ≤ 4 * Ct * max Cs 1 := by positivity
  nlinarith [mul_nonneg hcs h32]

/-- **Row 19 in the honest class**: `‖N₃^{**}‖_{ℋ⁴} ≤ K α³` (from `N3ssPriced`, whose hypotheses
are exactly `0 < α ≤ 1` and `StarPkgo2 α Cs Φs`). -/
theorem rowN3ss_honest (Cs : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {Φs : Fn},
      0 < α → α ≤ 1 → Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3ss α Φs) ≤ K * α ^ 3 := by
  obtain ⟨C19, hC19pos, hC19⟩ := Work.FTS.StrongPersist.L3Rhs.N3ssPriced
  refine ⟨C19 * (1 + |Cs|) + 1, ?_, fun {α Φs} hα hα1 hs => ?_⟩
  · have h1 : (0 : ℝ) ≤ 1 + |Cs| := by positivity
    have h2 : 0 < C19 * (1 + |Cs|) := mul_pos hC19pos (by have := abs_nonneg Cs; linarith)
    linarith
  · have h := (hC19 α ⟨hα, hα1⟩ Cs Φs hs).2
    have h3 : (0 : ℝ) ≤ α ^ 3 := by positivity
    have h4 : C19 * (1 + |Cs|) * α ^ 3 ≤ (C19 * (1 + |Cs|) + 1) * α ^ 3 :=
      mul_le_mul_of_nonneg_right (by linarith) h3
    linarith

theorem rowsN3b (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      |IP α (Work.FTS.Nonlin.N3sg α Φs g) g|
          ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g ^ 2) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3ss α Φs) ≤ K * α ^ 3 := by
  obtain ⟨K18, hK18pos, h18⟩ := rowN3sg_honest IP hN hE
  obtain ⟨K19, hK19pos, h19⟩ := rowN3ss_honest Cs
  refine ⟨max K18 K19, lt_max_iff.mpr (Or.inl hK18pos), ?_⟩
  intro α g Φs Φg hC
  constructor
  · exact le_trans (h18 hC)
      (mul_le_mul_of_nonneg_right (le_max_left K18 K19)
        (mul_nonneg (Real.rpow_nonneg hC.hα.le _)
          (pow_nonneg (Work.Spaces.HkNorm_nonneg α 4 g) 2)))
  · exact le_trans (h19 hC.hα hC.hα1 hC.hs)
      (mul_le_mul_of_nonneg_right (le_max_right K18 K19) (pow_nonneg hC.hα.le 3))

end Work.FTS.StrongEps.E4R3.N4C.rows
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.JepsMulSinCos2Integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

/-- The open-quadrant smoothness of `W` in the raw `∀ n`-form used by the `J_ε`-API
(`SmoothOpen` is definitionally `ContDiffOn ℝ smoothOrder (uncurry ·) Q0`). -/
theorem smoothOpen_forall_of_smoothOpen {W : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen W) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry W)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall W).mp hsm n

/-- **Integrability of the `sin θ cos²θ`-moment of the mollified slice.**

`J_ε W` is `C^∞` on the open quadrant and, being a mollification of an `ℋ^1`-profile, is
honestly `ℋ^0`; the level-`0` honesty alone controls the angular endpoints (its weight
`sin(2θ)^{-η/2}` with `η = 99/100 < 1` forces `|W| ≲ sin(2θ)^{-a}` with `a < 1/200`), so the
bounded multiplier `sinCos2` is integrable against the slice. -/
theorem integrableOn_Jeps_mul_sinCos2 {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {W : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen W) (hmem : Work.Spaces.HkMem α 1 W) :
    ∀ r : ℝ, 0 < r → MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.FTS.StrongEps.Jeps ρ ε W r θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := by
  intro r hr
  -- the raw `∀ n`-form of the smoothness of `W`, and the descent `ℋ¹ ⟹ ℋ⁰`
  have hsmW := smoothOpen_forall_of_smoothOpen hsm
  have hmem0W : Work.Spaces.HkMem α 0 W :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := 0) (l := 1)
      (by norm_num) hsmW hmem
  -- `J_ε W` is again `ℋ⁰` and `C^∞` on the open quadrant
  have hmem0J : Work.Spaces.HkMem α 0 (Work.FTS.StrongEps.Jeps ρ ε W) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε hsmW hmem0W
  have hsmJ : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε W) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε hsmW
  -- the level-`0` absorption `|g·sinCos2| ≤ (g·w/sin^{η/2})² + 1` on the slice
  have hcont : ContinuousOn (Function.uncurry (Work.FTS.StrongEps.Jeps ρ ε W))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hsmJ.continuousOn
  have hmain : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.FTS.StrongEps.Jeps ρ ε W r θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Cores.integrableOn_slice_mul_sinCos2 hcont hmem0J hr
  exact hmain

theorem JepsMulSinCos2Integrable {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {W : Work.FTS.Galerkin.Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen W) (hmem : Work.Spaces.HkMem α 1 W) :
    ∀ r : ℝ, 0 < r → MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.FTS.StrongEps.Jeps ρ ε W r θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ :=
  integrableOn_Jeps_mul_sinCos2 hρ hε hα hsm hmem

end Work.FTS.StrongEps.EpsE4Thr
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_le_HkSq_ClassC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsSqTools

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary `rpow` bookkeeping on `Iθ` -/

/-- `sin (2θ) ≥ 0` on `Iθ = [0,π/2]`. -/
theorem sin_two_nonneg_Iθ_eps {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `((sin 2θ)^a)^2 = (sin 2θ)^(2a)` on `Iθ`. -/
theorem sin_rpow_sq {θ a : ℝ} (hs : 0 ≤ Real.sin (2 * θ)) :
    ((Real.sin (2 * θ)) ^ a) ^ 2 = (Real.sin (2 * θ)) ^ (2 * a) := by
  calc ((Real.sin (2 * θ)) ^ a) ^ (2 : ℕ)
      = ((Real.sin (2 * θ)) ^ a) ^ ((2 : ℕ) : ℝ) := by norm_num
    _ = (Real.sin (2 * θ)) ^ (a * ((2 : ℕ) : ℝ)) := by rw [← Real.rpow_mul hs]
    _ = (Real.sin (2 * θ)) ^ (2 * a) := by congr 1; ring

/-- **The square of the weight of the `ε`-scheme** is the `γ`-weighted square on `Iθ`:
`(epsW α z θ)² = w(z)² sin(2θ)^{-γ}`. -/
theorem epsW_sq_eq {α z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.FTS.StrongEps.epsW α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs := sin_two_nonneg_Iθ_eps hθ
  have hpow : ((Real.sin (2 * θ)) ^ (Work.Spaces.gam α / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ (Work.Spaces.gam α) := by
    rw [sin_rpow_sq hs]
    congr 1
    ring
  rw [Work.FTS.StrongEps.epsW, div_pow, hpow, div_eq_mul_inv, ← Real.rpow_neg hs]

/-- **The square of the mixed weight** is the `γ`-weighted square on `Iθ`:
`(Wt α z θ)² = w(z)² sin(2θ)^{-γ}` (the `Iθ`-version of `Work.FTS.H2.Wt_sq`). -/
theorem Wt_sq_eq_eps {α z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs := sin_two_nonneg_Iθ_eps hθ
  have hpow : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [sin_rpow_sq hs]
    congr 1
    ring
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, hpow]

/-! ## The two slice identities -/

/-- **The `EpsSq`-slice is `w²` times the `γ`-weighted `L²` of the slice.** -/
theorem epsSq_slice_eq (α z : ℝ) (f : ℝ → ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
      = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
          (f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun
    (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) ?_
  intro θ hθ
  simp only []
  have h1 : (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2
      = (f z θ) ^ 2
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
    rw [mul_pow, epsW_sq_eq hθ]
  rw [h1]
  ring

/-- **The `(0,1)`-slot of the `ℋ⁴`-integrand is `w²` times the `2-γ`-weighted square of the
unguarded angular derivative.**  Uses `sin(2θ)^{2-γ}(∂_θ u)² = sin(2θ)^{-γ}(D_θ u)²`
(`Work.FTS.H2.pth_sq_mul_sin_eq`). -/
theorem slot_slice_eq {α z : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z θ) ^ 2 := by
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun
    (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) ?_
  intro θ hθ
  simp only []
  have hcomm : (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z θ) ^ 2
      = (Work.Spaces.pth f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by ring
  have h1 : (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2
        * ((Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z θ) ^ 2) := by
    rw [mul_pow, Wt_sq_eq_eps hθ, Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero]
    rw [hcomm, Work.FTS.H2.pth_sq_mul_sin_eq α hα0 hα1 f z θ hθ]
    ring
  rw [h1]

/-- **The `pth`-form of the Hardy hypothesis at a fixed `z`**, converted from the
`(0,1)`-slot integrability. -/
theorem pth_slice_integrable {α z : ℝ} {f : ℝ → ℝ → ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hz : 0 < z)
    (hslot : MeasureTheory.Integrable
      (fun θ => (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (fun θ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z θ) ^ 2)
      Work.Spaces.Iθ := by
  have hw : Work.Spaces.w z ≠ 0 := by
    have h1 : (0 : ℝ) < (1 + z) ^ 2 := by positivity
    have h2 : (0 : ℝ) < z ^ 2 := by positivity
    rw [Work.Spaces.w]
    exact div_ne_zero (ne_of_gt h1) (ne_of_gt h2)
  refine ((hslot.const_mul ((Work.Spaces.w z) ^ 2)⁻¹)).congr ?_
  refine MeasureTheory.ae_restrict_of_forall_mem
    (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) fun θ hθ => ?_
  have h1 : (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2
        * ((Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z θ) ^ 2) := by
    rw [mul_pow, Wt_sq_eq_eps hθ, Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero]
    rw [show (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z θ) ^ 2
        = (Work.Spaces.pth f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) by ring,
      Work.FTS.H2.pth_sq_mul_sin_eq α hα0 hα1 f z θ hθ]
    ring
  calc (Work.Spaces.w z ^ 2)⁻¹ * (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z ^ 2)⁻¹
        * ((Work.Spaces.w z) ^ 2
          * ((Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z θ) ^ 2)) := by
          rw [h1]
    _ = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z θ) ^ 2 := by
          rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hw), one_mul]

/-! ## The `(0,1)`-slot of `ℋ⁴` -/

/-- **The `(0,1)`-slot of the `ℋ⁴`-integrand is integrable in `z` and bounded by `HkSq α 4`**
(in the order `∫_z ∫_θ`). -/
theorem slot01_le_HkSq4 {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 4 f) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iz ∧
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      ≤ Work.Spaces.HkSq α 4 f := by
  have hprod : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.mixed 0 1 f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.FTS.EllipticEst.AeSlotOneAe.Interp.integrable_uncurry_slot_mixed hso hm 0 1
      (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · simpa only [Function.uncurry, MeasureTheory.IntegrableOn]
      using hprod.integral_prod_left
  · rw [Work.Spaces.HkSq]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ => sq_nonneg _)
      hm.2 ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _) (hm.1 z hz) ?_
    filter_upwards with θ
    exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ 1 0 (by norm_num) (by norm_num)

/-- **The `(0,1)`-slot is `θ`-integrable for almost every `z`** (from the product integrability). -/
theorem slot01_ae_integrable {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 4 f) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable
        (fun θ => (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  (Work.FTS.EllipticEst.AeSlotOneAe.Interp.integrable_uncurry_slot_mixed hso hm 0 1
    (by norm_num) (by norm_num)).prod_right_ae

/-- **Almost every `z` of `Iz` is positive** (`Iz = [0,∞)` and `{0}` is null). -/
theorem ae_pos_Iz : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
  have h1 : Set.Ioi (0 : ℝ) =ᵐ[volume] Set.Ici 0 := Ioi_ae_eq_Ici
  rw [Work.Spaces.Iz, ← Measure.restrict_congr_set h1]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioi

/-- **Continuity of the weight of the `ε`-scheme on the open quadrant.** -/
theorem continuousOn_epsW (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.StrongEps.epsW α p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hWt : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.H2.continuousOn_Wt_Qd α
  refine hWt.congr fun p hp => ?_
  obtain ⟨hz, hθ1, hθ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact epsW_eq_Wt_of_mem_Iθ ⟨hθ1.le, hθ2.le⟩

theorem EpsSq_le_HkSq_ClassC : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
    ∀ f : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α f →
      Work.FTS.StrongEps.EpsMem α f ∧
      Work.FTS.StrongEps.EpsSq α f
        ≤ C / (Work.Spaces.gam α - 1) ^ 8 * Work.Spaces.HkSq α 4 f := by
  obtain ⟨CH, hCHpos, hCH⟩ := hardySinGam_weak
  refine ⟨max 1 (CH / 1000000), by positivity, ?_⟩
  intro α hα f hf
  obtain ⟨hα0, hα1⟩ := hα
  have hγ1 : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα0
  have hγ32 : Work.Spaces.gam α ≤ 3 / 2 := by rw [Work.Spaces.gam]; linarith
  have hγpos : 0 < Work.Spaces.gam α - 1 := by linarith
  have hγδ : (Work.Spaces.gam α - 1) ^ 6 ≤ 1 / 1000000 := by
    have hle : Work.Spaces.gam α - 1 ≤ 1 / 10 := by rw [Work.Spaces.gam]; linarith
    have h0 : (0 : ℝ) ≤ Work.Spaces.gam α - 1 := by linarith
    calc (Work.Spaces.gam α - 1) ^ 6 ≤ (1 / 10 : ℝ) ^ 6 := pow_le_pow_left₀ h0 hle 6
      _ = 1 / 1000000 := by norm_num
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hf.reg 4 (by norm_num) hf.mem8
  obtain ⟨hEint, hEle⟩ := slot01_le_HkSq4 hf.reg hmem4
  have hslot_ae := slot01_ae_integrable hf.reg hmem4
  have hae_pos := ae_pos_Iz
  -- the a.e.-in-`z` slice Hardy bound, together with the θ-integrability of the slice
  have hpoint : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
          ≤ CH / (Work.Spaces.gam α - 1) ^ 2 *
            (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) ∧
      MeasureTheory.Integrable
        (fun θ => (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [hslot_ae, hae_pos] with z hslot hz
    have hcd : ContDiffOn ℝ 1 (fun θ => f z θ) (Set.Ioo 0 (Real.pi / 2)) :=
      (hf.reg.curry_θ hz).of_le
        (show (1 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder from by
          simp [Work.Stability.smoothOrder])
    have htrace := (hf.tr 0 0 (by norm_num)).2 z (Set.mem_Ioi.mpr hz)
    have ht1 : Filter.Tendsto (fun θ => f z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      Work.FTS.H2.HQ.tendsto_nhdsGT_zero_of_traces α hα0
        (by simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using htrace.1)
    have ht2 : Filter.Tendsto (fun θ => f z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
      Work.FTS.H2.HQ.tendsto_nhdsLT_zero_of_traces α hα0
        (by simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using htrace.2)
    have hint := pth_slice_integrable (α := α) (z := z) (f := f) hα0 hα1 hz hslot
    obtain ⟨hL1, hL2⟩ := hCH (Work.Spaces.gam α) (fun θ => f z θ) hγ1 hγ32 hcd ht1 ht2 hint
    have hcomm : (∫ θ in Work.Spaces.Iθ,
          (f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        = (∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (f z θ) ^ 2) :=
      MeasureTheory.setIntegral_congr_fun
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) (fun θ _ => by ring)
    have hbound : (∫ θ in Work.Spaces.Iθ, (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
        ≤ CH / (Work.Spaces.gam α - 1) ^ 2 *
          (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
      calc (∫ θ in Work.Spaces.Iθ, (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
          = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
              (f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
            epsSq_slice_eq α z f
        _ = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
              (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (f z θ) ^ 2 := by rw [hcomm]
        _ ≤ (Work.Spaces.w z) ^ 2 * (CH / (Work.Spaces.gam α - 1) ^ 2 *
              ∫ θ in Work.Spaces.Iθ,
                (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z θ) ^ 2) :=
            mul_le_mul_of_nonneg_left hL2 (sq_nonneg _)
        _ = CH / (Work.Spaces.gam α - 1) ^ 2 * ((Work.Spaces.w z) ^ 2 *
              ∫ θ in Work.Spaces.Iθ,
                (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z θ) ^ 2) := by
            ring
        _ = CH / (Work.Spaces.gam α - 1) ^ 2 *
              (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
            rw [slot_slice_eq (α := α) (z := z) hα0 hα1 f]
    refine ⟨hbound, ?_⟩
    refine (hL1.const_mul ((Work.Spaces.w z) ^ 2)).congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) fun θ hθ => ?_
    have h1 : (Work.FTS.StrongEps.epsW α z θ) ^ 2
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
      epsW_sq_eq hθ
    simp only []
    rw [mul_pow, h1]
    ring
  -- the outer `z`-integral
  have hEint' : MeasureTheory.Integrable
      (fun z : ℝ => CH / (Work.Spaces.gam α - 1) ^ 2 *
        (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hEint.const_mul _
  have hmain : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
      ≤ CH / (Work.Spaces.gam α - 1) ^ 2 * Work.Spaces.HkSq α 4 f := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hEle (div_nonneg hCHpos.le (sq_nonneg _)))
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z =>
        MeasureTheory.integral_nonneg fun θ => sq_nonneg _) hEint' ?_
    filter_upwards [hpoint] with z hz using hz.1
  -- the arithmetic of the constant
  have hconst : CH / (Work.Spaces.gam α - 1) ^ 2
      ≤ max 1 (CH / 1000000) / (Work.Spaces.gam α - 1) ^ 8 := by
    have h1 : CH * (Work.Spaces.gam α - 1) ^ 6 ≤ CH / 1000000 := by
      calc CH * (Work.Spaces.gam α - 1) ^ 6 ≤ CH * (1 / 1000000) :=
            mul_le_mul_of_nonneg_left hγδ hCHpos.le
        _ = CH / 1000000 := by ring
    have h2 : CH / 1000000 ≤ max 1 (CH / 1000000) := le_max_right _ _
    have h3 : CH * (Work.Spaces.gam α - 1) ^ 6 / (Work.Spaces.gam α - 1) ^ 8
        ≤ max 1 (CH / 1000000) / (Work.Spaces.gam α - 1) ^ 8 :=
      div_le_div_of_nonneg_right (le_trans h1 h2) (by positivity)
    have h4 : CH / (Work.Spaces.gam α - 1) ^ 2
        = CH * (Work.Spaces.gam α - 1) ^ 6 / (Work.Spaces.gam α - 1) ^ 8 := by
      rw [div_eq_div_iff (by positivity) (by positivity)]
      ring
    rw [h4]
    exact h3
  refine ⟨?_, ?_⟩
  · -- `EpsMem α f`
    have hAESM : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => (f p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd _
        (ContinuousOn.pow
          (ContinuousOn.mul (hf.reg.forall 0).continuousOn (continuousOn_epsW α)) 2)
    have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        MeasureTheory.HasFiniteIntegral
          (fun θ => (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      filter_upwards [hpoint] with z hz using hz.2.2
    have hzInt : MeasureTheory.HasFiniteIntegral
        (fun z : ℝ => ∫ θ, ‖(f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2‖
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      have haesm : MeasureTheory.AEStronglyMeasurable
          (fun z : ℝ => ∫ θ, ‖(f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2‖
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
        hAESM.norm.integral_prod_right'
      have hbdd : (fun z : ℝ => ‖∫ θ, ‖(f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2‖
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)‖)
          ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
          (fun z : ℝ => CH / (Work.Spaces.gam α - 1) ^ 2 *
            (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)) := by
        filter_upwards [hpoint] with z hz
        rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ => norm_nonneg _)]
        refine le_trans (le_of_eq ?_) hz.1
        exact MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun θ => Real.norm_of_nonneg (sq_nonneg _))
      exact (MeasureTheory.Integrable.mono' hEint' haesm hbdd).2
    have hmeas : (MeasureTheory.volume : Measure (ℝ × ℝ)).restrict
          (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
        = (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      rw [MeasureTheory.Measure.volume_eq_prod, Measure.prod_restrict]
    rw [Work.FTS.StrongEps.EpsMem, MeasureTheory.IntegrableOn, hmeas]
    exact ⟨hAESM, (MeasureTheory.hasFiniteIntegral_prod_iff' hAESM).mpr ⟨hslice, hzInt⟩⟩
  · calc Work.FTS.StrongEps.EpsSq α f
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2 := rfl
      _ ≤ CH / (Work.Spaces.gam α - 1) ^ 2 * Work.Spaces.HkSq α 4 f := hmain
      _ ≤ max 1 (CH / 1000000) / (Work.Spaces.gam α - 1) ^ 8 * Work.Spaces.HkSq α 4 f :=
          mul_le_mul_of_nonneg_right hconst (Work.Spaces.HkSq_nonneg α 4 f)


end Work.FTS.StrongEps.EpsSqTools
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_mul_le_of_sup =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsSqTools

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The open quadrant inside the closed one -/

/-- The open quadrant `Quad = (0,∞) × (0,π/2)` sits inside `Iz ×ˢ Iθ = [0,∞) × [0,π/2]`. -/
theorem quad_subset_quadrant :
    Work.FTS.StrongEps.Quad ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ := by
  rintro ⟨z, θ⟩ hp
  show 0 ≤ z ∧ 0 ≤ θ ∧ θ ≤ π / 2
  exact ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩

/-- The open quadrant is measurable. -/
theorem measurableSet_quad : MeasurableSet Work.FTS.StrongEps.Quad :=
  measurableSet_Ioi.prod measurableSet_Ioo

/-- **The two restricted measures agree**: `volume ∣_{Iz ×ˢ Iθ} = volume ∣_{Quad}`.  Indeed the
closed quadrant is the union of the open quadrant and the three boundary lines `z = 0`, `θ = 0`,
`θ = π/2`, which are null for the product measure, and the open quadrant is conull in the closed
one. -/
theorem restrict_prod_eq_restrict_quad :
    (volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      = (volume : Measure (ℝ × ℝ)).restrict Work.FTS.StrongEps.Quad := by
  have hP : (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)
      = (volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod ℝ ℝ]
  have hQ : (volume : Measure (ℝ × ℝ)).restrict Work.FTS.StrongEps.Quad
      = ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)).restrict
          Work.FTS.StrongEps.Quad :=
    (Measure.restrict_restrict_of_subset quad_subset_quadrant).symm
  rw [hQ, ← hP]
  exact (Measure.restrict_eq_self_of_ae_mem ae_mem_quad).symm

/-! ## The pointwise domination -/


/-! ## The target -/


end Work.FTS.StrongEps.EpsSqTools
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsSqTools.L12_sub_EpsSq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory

namespace Work.FTS.StrongEps.EpsSqTools

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The angular factor `sin(2θ)^{γ/2}` of the `ε`-weight -/

/-- `Swe α θ = sin(2θ)^{γ/2}` with `γ = gam α`: the angular factor of `epsW α z θ = w z / Swe α θ`. -/
def Swe (α θ : ℝ) : ℝ := Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2)

/-- `BKe α = √(∫_θ (K(θ)·Swe α θ)² dθ)`: the angular `L²`-norm of the profile `K·Swe`. -/
def BKe (α : ℝ) : ℝ :=
  Real.sqrt (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ * Swe α θ) ^ 2)

/-- `W2e = ∫_{(0,∞)} Wlam²`: the finite `L²`-mass of the radial weight `Wlam s = s/(1+s)²`. -/
def W2e : ℝ := ∫ s in Set.Ioi (0 : ℝ), Work.FTS.GalBasis.cc.Wlam s ^ 2

lemma Swe_nonneg_of_mem_Iθ {α θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Swe α θ := by
  rw [Swe]
  exact Real.rpow_nonneg (Work.FTS.GalBasis.cc.sin_two_nonneg_of_mem_Iθ hθ) _


lemma Swe_le_one {α θ : ℝ} (hα : 0 ≤ Work.Spaces.gam α / 2) (hθ : θ ∈ Work.Spaces.Iθ) :
    Swe α θ ≤ 1 := by
  rw [Swe]
  exact Real.rpow_le_one (Work.FTS.GalBasis.cc.sin_two_nonneg_of_mem_Iθ hθ) (Real.sin_le_one _) hα

lemma continuous_Swe {α : ℝ} (hα : 0 ≤ Work.Spaces.gam α / 2) : Continuous (Swe α) := by
  change Continuous (fun θ : ℝ => Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2))
  exact (Real.continuous_rpow_const hα).comp
    (Real.continuous_sin.comp (continuous_const.mul continuous_id))

lemma continuous_K : Continuous Work.Spaces.K := by
  change Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
  fun_prop

/-- Where `Swe` vanishes on `Iθ`, so does `K`. -/
lemma Swe_eq_zero_imp_K_eq_zero {α θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (h : Swe α θ = 0) :
    Work.Spaces.K θ = 0 := by
  rw [Swe] at h
  have hsin := Work.FTS.GalBasis.cc.sin_two_nonneg_of_mem_Iθ hθ
  have hzero : Real.sin (2 * θ) = 0 := ((Real.rpow_eq_zero_iff_of_nonneg hsin).mp h).1
  rw [Real.sin_two_mul] at hzero
  have : Real.sin θ = 0 ∨ Real.cos θ = 0 := by
    rcases mul_eq_zero.mp hzero with h' | h'
    · exact Or.inl (by linarith [h'])
    · exact Or.inr h'
  rw [Work.Spaces.K]
  rcases this with h' | h' <;> simp [h']

/-! ## The pointwise factorisation of the `L₁₂`-density integrand -/

/-- For `s > 0` and `θ ∈ Iθ` the density integrand factorises as the radial weight `Wlam s`
times the pairing of the angular profile `K·Swe` with the `ε`-weighted datum `h·epsW`. -/
lemma K_mul_h_div_s_eq_eps (α : ℝ) (h : ℝ → ℝ → ℝ) {s : ℝ} (hs : 0 < s) :
    ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.K θ * h s θ / s
        = Work.FTS.GalBasis.cc.Wlam s
            * (Work.Spaces.K θ * Swe α θ * (h s θ * epsW α s θ)) := by
  intro θ hθ
  by_cases hS : Swe α θ = 0
  · have hK : Work.Spaces.K θ = 0 := Swe_eq_zero_imp_K_eq_zero hθ hS
    rw [hS, hK]
    simp
  · have hstep : Swe α θ * (h s θ * epsW α s θ) = h s θ * Work.Spaces.w s := by
      have he : epsW α s θ = Work.Spaces.w s / Swe α θ := rfl
      rw [he]
      rw [show Swe α θ * (h s θ * (Work.Spaces.w s / Swe α θ))
            = h s θ * (Swe α θ * (Work.Spaces.w s / Swe α θ)) from by ring]
      rw [mul_div_cancel₀ _ hS]
    exact (calc Work.FTS.GalBasis.cc.Wlam s * (Work.Spaces.K θ * Swe α θ * (h s θ * epsW α s θ))
        = Work.Spaces.K θ
            * (Work.FTS.GalBasis.cc.Wlam s * (Swe α θ * (h s θ * epsW α s θ))) := by ring
      _ = Work.Spaces.K θ
            * (Work.FTS.GalBasis.cc.Wlam s * (h s θ * Work.Spaces.w s)) := by rw [hstep]
      _ = Work.Spaces.K θ
            * (h s θ * (Work.Spaces.w s * Work.FTS.GalBasis.cc.Wlam s)) := by ring
      _ = Work.Spaces.K θ * (h s θ * (1 / s)) := by
            rw [Work.FTS.GalBasis.cc.w_mul_Wlam hs]
      _ = Work.Spaces.K θ * h s θ / s := by ring).symm

/-! ## The angular Cauchy–Schwarz step -/

lemma BKe_nonneg (α : ℝ) : 0 ≤ BKe α := Real.sqrt_nonneg _

/-- **Angular Cauchy–Schwarz against the `ε`-weighted datum.**  If the `θ`-slice of the
`ε`-integrand is integrable, then the pairing `∫_θ K θ · Swe α θ · (h s θ · epsW α s θ)` is
dominated by the product of the angular profile norm `BKe α` and the square root of the slice
energy. -/
theorem abs_integral_K_Swe_eps_le {α : ℝ} (hα : 0 ≤ Work.Spaces.gam α / 2)
    (h : ℝ → ℝ → ℝ) {s : ℝ}
    (hint : IntegrableOn (fun θ => (h s θ * epsW α s θ) ^ 2) Work.Spaces.Iθ) :
    |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Swe α θ * (h s θ * epsW α s θ)|
      ≤ BKe α * Real.sqrt (∫ θ in Work.Spaces.Iθ, (h s θ * epsW α s θ) ^ 2) := by
  set u : ℝ → ℝ := fun θ => Work.Spaces.K θ * Swe α θ with hu
  set v : ℝ → ℝ := fun θ => h s θ * epsW α s θ with hv
  set w : ℝ → ℝ := fun θ => Real.sqrt ((h s θ * epsW α s θ) ^ 2) with hw
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hw_nn : ∀ θ : ℝ, 0 ≤ w θ := fun θ => Real.sqrt_nonneg _
  have hvw : ∀ θ : ℝ, |v θ| ≤ w θ := by
    intro θ
    show |h s θ * epsW α s θ| ≤ Real.sqrt ((h s θ * epsW α s θ) ^ 2)
    rw [Real.sqrt_sq_eq_abs]
  have hcont_u : Continuous u := by
    rw [hu]
    exact continuous_K.mul (continuous_Swe hα)
  have hw_aesm : AEStronglyMeasurable w (volume.restrict Work.Spaces.Iθ) := by
    rw [hw]
    exact (hint.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  have hu2_int : IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ :=
    (hcont_u.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hw2_int : IntegrableOn (fun θ => (w θ) ^ 2) Work.Spaces.Iθ := by
    refine hint.congr_fun (fun θ _ => ?_) hIθ
    rw [hw]
    exact (Real.sq_sqrt (sq_nonneg _)).symm
  have huw_int : IntegrableOn (fun θ => |u θ| * w θ) Work.Spaces.Iθ := by
    have hmaj : IntegrableOn (fun θ => ((u θ) ^ 2 + (w θ) ^ 2) / 2) Work.Spaces.Iθ :=
      (hu2_int.add hw2_int).div_const 2
    refine hmaj.mono' ((hcont_u.abs.aestronglyMeasurable).mul hw_aesm) ?_
    filter_upwards with θ
    have h1 : 0 ≤ |u θ| := abs_nonneg _
    have h2 : 0 ≤ w θ := hw_nn θ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2, abs_of_nonneg h1]
    have key : |u θ| * w θ ≤ (|u θ| ^ 2 + (w θ) ^ 2) / 2 := by
      nlinarith [sq_nonneg (|u θ| - w θ), sq_nonneg (|u θ| + w θ)]
    rw [sq_abs (u θ)] at key
    exact key
  have hMemLp_u : MemLp (fun θ => |u θ|) 2 (volume.restrict Work.Spaces.Iθ) :=
    (memLp_two_iff_integrable_sq (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun θ => |u θ|) hcont_u.abs.aestronglyMeasurable).mpr
      (hu2_int.congr (Filter.Eventually.of_forall fun θ => (sq_abs (u θ)).symm))
  have hMemLp_w : MemLp w 2 (volume.restrict Work.Spaces.Iθ) :=
    (memLp_two_iff_integrable_sq (μ := volume.restrict Work.Spaces.Iθ) hw_aesm).mpr hw2_int
  have hcs := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt (u := fun θ => |u θ|)
    (v := w) hMemLp_u hMemLp_w
  have hsqrt_u : Real.sqrt (∫ θ in Work.Spaces.Iθ, |u θ| ^ 2) = BKe α := by
    rw [BKe]
    congr 1
    rw [hu]
    exact integral_congr_ae (Filter.Eventually.of_forall fun θ => sq_abs (Work.Spaces.K θ * Swe α θ))
  have hsqrt_w : Real.sqrt (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2)
      = Real.sqrt (∫ θ in Work.Spaces.Iθ, (h s θ * epsW α s θ) ^ 2) := by
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    rw [hw]
    exact Real.sq_sqrt (sq_nonneg _)
  have h1 : |∫ θ in Work.Spaces.Iθ, u θ * v θ|
      ≤ ∫ θ in Work.Spaces.Iθ, |u θ * v θ| := by
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict Work.Spaces.Iθ)
        (f := fun θ => u θ * v θ))
  have h2 : ∫ θ in Work.Spaces.Iθ, |u θ * v θ| ≤ ∫ θ in Work.Spaces.Iθ, |u θ| * w θ := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun θ => abs_nonneg _) huw_int
      (Filter.Eventually.of_forall fun θ => ?_)
    show |u θ * v θ| ≤ |u θ| * w θ
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hvw θ) (abs_nonneg _)
  have h3 : ∫ θ in Work.Spaces.Iθ, |u θ| * w θ
      = |∫ θ in Work.Spaces.Iθ, |u θ| * w θ| := by
    rw [abs_of_nonneg]
    exact integral_nonneg fun θ => mul_nonneg (abs_nonneg _) (hw_nn θ)
  calc |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Swe α θ * (h s θ * epsW α s θ)|
      = |∫ θ in Work.Spaces.Iθ, u θ * v θ| := by simp only [hu, hv]
    _ ≤ ∫ θ in Work.Spaces.Iθ, |u θ * v θ| := h1
    _ ≤ ∫ θ in Work.Spaces.Iθ, |u θ| * w θ := h2
    _ = |∫ θ in Work.Spaces.Iθ, |u θ| * w θ| := h3
    _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, |u θ| ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2) := hcs
    _ = BKe α * Real.sqrt (∫ θ in Work.Spaces.Iθ, (h s θ * epsW α s θ) ^ 2) := by
        rw [hsqrt_u, hsqrt_w]

/-- **The `z`- and `α`-free bound `BKe α ≤ 5`** for `α ∈ (0,1]`: on `Iθ` one has `K ≤ 3` and
`Swe ≤ 1`, so the integrand is at most `9` and the angular interval has measure `π/2 < 2`. -/
lemma BKe_le_five {α : ℝ} (hα : α ∈ Set.Ioc 0 1) : BKe α ≤ 5 := by
  have hgam : 0 ≤ Work.Spaces.gam α / 2 := by rw [Work.Spaces.gam]; linarith [hα.1]
  have hbd : ∀ θ ∈ Work.Spaces.Iθ, (Work.Spaces.K θ * Swe α θ) ^ 2 ≤ 9 := by
    intro θ hθ
    have hK := Work.FTS.GalBasis.cc.K_le_three_of_mem_Iθ hθ
    have hK0 := Work.FTS.GalBasis.cc.K_nonneg_of_mem_Iθ hθ
    have hSw := Swe_le_one hgam hθ
    have hSw0 := Swe_nonneg_of_mem_Iθ (α := α) hθ
    have hspan : 0 ≤ Work.Spaces.K θ * Swe α θ := mul_nonneg hK0 hSw0
    have hprod : Work.Spaces.K θ * Swe α θ ≤ 3 := by
      nlinarith [mul_le_mul hK hSw hSw0 (by norm_num : (0 : ℝ) ≤ 3)]
    have hsq := mul_self_le_mul_self hspan hprod
    nlinarith [hsq]
  have h9int : IntegrableOn (fun _ : ℝ => (9 : ℝ)) Work.Spaces.Iθ :=
    integrableOn_const (by rw [Work.Spaces.Iθ, Real.volume_Icc]; simp)
  have hle : ∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ * Swe α θ) ^ 2
      ≤ ∫ θ in Work.Spaces.Iθ, (9 : ℝ) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _) h9int
      (ae_restrict_of_forall_mem (by simp [Work.Spaces.Iθ]) (fun θ hθ => hbd θ hθ))
  have h9 : ∫ θ in Work.Spaces.Iθ, (9 : ℝ) = 9 * (π / 2) := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Work.Spaces.Iθ,
      Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  have hfin : ∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ * Swe α θ) ^ 2 ≤ 25 := by
    rw [h9] at hle
    nlinarith [Real.pi_lt_four]
  rw [BKe]
  calc Real.sqrt (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ * Swe α θ) ^ 2)
      ≤ Real.sqrt 25 := Real.sqrt_le_sqrt hfin
    _ = 5 := by norm_num

/-! ## The pointwise bound on the density -/

/-- **The `L₁₂`-density bound in the `ε`-weight.**  If the `θ`-slice of the `ε`-integrand is
integrable, then for `s > 0`

`|L₁₂dens h s| ≤ BKe α · Wlam s · √(∫_θ (h s θ · epsW α s θ)²)`. -/
theorem abs_L12dens_le_eps {α : ℝ} (hα : 0 ≤ Work.Spaces.gam α / 2)
    (h : ℝ → ℝ → ℝ) {s : ℝ} (hs : 0 < s)
    (hint : IntegrableOn (fun θ => (h s θ * epsW α s θ) ^ 2) Work.Spaces.Iθ) :
    |Work.Construction.L12dens h s|
      ≤ BKe α * (Work.FTS.GalBasis.cc.Wlam s
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (h s θ * epsW α s θ) ^ 2)) := by
  have hId : Work.Construction.L12dens h s
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * h s θ / s := rfl
  have hcongr : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * h s θ / s)
      = ∫ θ in Work.Spaces.Iθ, Work.FTS.GalBasis.cc.Wlam s
          * (Work.Spaces.K θ * Swe α θ * (h s θ * epsW α s θ)) :=
    MeasureTheory.setIntegral_congr_fun (by simp [Work.Spaces.Iθ])
      (fun θ hθ => K_mul_h_div_s_eq_eps α h hs θ hθ)
  rw [hId, hcongr, integral_const_mul, abs_mul,
    abs_of_nonneg (Work.FTS.GalBasis.cc.Wlam_nonneg hs.le)]
  calc Work.FTS.GalBasis.cc.Wlam s
        * |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Swe α θ * (h s θ * epsW α s θ)|
      ≤ Work.FTS.GalBasis.cc.Wlam s
          * (BKe α * Real.sqrt (∫ θ in Work.Spaces.Iθ, (h s θ * epsW α s θ) ^ 2)) :=
        mul_le_mul_of_nonneg_left (abs_integral_K_Swe_eps_le hα h hint)
          (Work.FTS.GalBasis.cc.Wlam_nonneg hs.le)
    _ = BKe α * (Work.FTS.GalBasis.cc.Wlam s
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (h s θ * epsW α s θ) ^ 2)) := by ring

/-! ## The radial Cauchy–Schwarz data -/

/-- The radial weight `Wlam` is square-integrable on `(0,∞)` (it equals `s/(1+s)²`). -/
lemma Wlam_sq_integrableOn_Ioi0 :
    IntegrableOn (fun s : ℝ => Work.FTS.GalBasis.cc.Wlam s ^ 2) (Set.Ioi (0 : ℝ)) := by
  simpa only [Work.FTS.GalBasis.cc.Wlam] using Work.Elliptic.psi_sq_integrable_aux

lemma Wlam_aesm_restrict {z : ℝ} (hz : 0 ≤ z) :
    AEStronglyMeasurable Work.FTS.GalBasis.cc.Wlam (volume.restrict (Set.Ioi z)) := by
  have h0 : AEStronglyMeasurable Work.FTS.GalBasis.cc.Wlam
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    change AEStronglyMeasurable (fun s : ℝ => s / (1 + s) ^ 2) (volume.restrict (Set.Ioi 0))
    refine ContinuousOn.aestronglyMeasurable (μ := volume)
      (continuousOn_id.div ((continuousOn_const.add continuousOn_id).pow 2) ?_) measurableSet_Ioi
    intro s hs
    have hne : (1 : ℝ) + s ≠ 0 := by
      simp only [Set.mem_Ioi] at hs
      linarith
    exact pow_ne_zero 2 hne
  exact h0.mono_measure (MeasureTheory.Measure.restrict_mono_set volume (fun x hx => by
    simp only [Set.mem_Ioi] at hx ⊢
    linarith))

/-! ## The main estimate for a single datum -/

/-- **`|L₁₂ h z| ≤ C √(EpsSq α h)` uniformly in `α ∈ (0,1]` and `z ∈ [0,∞)`**, from the sole
hypothesis `EpsMem α h` (level-`0` `ε`-integrability of `h`). -/
theorem L12_le_sqrt_EpsSq : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
    ∀ h : Work.FTS.Galerkin.Fn, EpsMem α h → ∀ z ∈ Work.Spaces.Iz,
      |Work.Construction.L12 h z| ≤ C * Real.sqrt (EpsSq α h) := by
  refine ⟨5 * Real.sqrt W2e + 1, by have := Real.sqrt_nonneg W2e; linarith, ?_⟩
  intro α hα h hmem z hz
  have hz0 : (0 : ℝ) ≤ z := hz
  have hgam : 0 ≤ Work.Spaces.gam α / 2 := by rw [Work.Spaces.gam]; linarith [hα.1]
  -- the angular marginal of the `ε`-integrand, its square root, and the radial data
  set F : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ, (h s θ * epsW α s θ) ^ 2 with hF
  set A : ℝ → ℝ := fun s => Real.sqrt (F s) with hA
  have hFnn : ∀ s : ℝ, 0 ≤ F s := fun s => integral_nonneg fun θ => sq_nonneg _
  have hAnn : ∀ s : ℝ, 0 ≤ A s := fun s => Real.sqrt_nonneg _
  have hA2 : ∀ s : ℝ, A s ^ 2 = F s := fun s => Real.sq_sqrt (hFnn s)
  have hFdef : ∀ s : ℝ, F s = ∫ θ in Work.Spaces.Iθ, (h s θ * epsW α s θ) ^ 2 := fun _ => rfl
  -- Fubini: the marginal `F` is integrable on `Iz`, and its slices are a.e. integrable
  have hsub : Set.Ioi z ⊆ Work.Spaces.Iz := by
    intro x hx
    simp only [Set.mem_Ioi] at hx
    simp only [Work.Spaces.Iz, Set.mem_Ici]
    linarith
  have hEprod_Iz : Integrable (fun p : ℝ × ℝ => (h p.1 p.2 * epsW α p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact hmem
  have hFint_Iz : IntegrableOn F Work.Spaces.Iz := hEprod_Iz.integral_prod_left
  have hEprod : Integrable (fun p : ℝ × ℝ => (h p.1 p.2 * epsW α p.1 p.2) ^ 2)
      ((volume.restrict (Set.Ioi z)).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact hmem.mono_set (Set.prod_mono hsub subset_rfl)
  have hFint : IntegrableOn F (Set.Ioi z) := hEprod.integral_prod_left
  have hslice : ∀ᵐ s ∂(volume.restrict (Set.Ioi z)),
      IntegrableOn (fun θ => (h s θ * epsW α s θ) ^ 2) Work.Spaces.Iθ := hEprod.prod_right_ae
  have hEpsSq : EpsSq α h = ∫ s in Work.Spaces.Iz, F s := by
    rw [hF]
    rfl
  -- `A² = F` is integrable on `(z,∞)`, and `A` is `L²` there
  have hA2int : IntegrableOn (fun s => A s ^ 2) (Set.Ioi z) :=
    hFint.congr_fun (fun s _ => (hA2 s).symm) measurableSet_Ioi
  have hA_aesm : AEStronglyMeasurable A (volume.restrict (Set.Ioi z)) := by
    rw [hA]
    exact (hFint.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  have hA_memLp : MemLp A 2 (volume.restrict (Set.Ioi z)) :=
    (memLp_two_iff_integrable_sq hA_aesm).mpr hA2int
  -- the radial weight `Wlam` is `L²((z,∞))`
  have hsub0 : Set.Ioi z ⊆ Set.Ioi (0 : ℝ) := fun x hx => by
    simp only [Set.mem_Ioi] at hx ⊢
    linarith
  have hWlam_sq_int : IntegrableOn (fun s => Work.FTS.GalBasis.cc.Wlam s ^ 2) (Set.Ioi z) :=
    Wlam_sq_integrableOn_Ioi0.mono_set hsub0
  have hWlam_sq_le : ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s ^ 2 ≤ W2e :=
    MeasureTheory.setIntegral_mono_set Wlam_sq_integrableOn_Ioi0
      (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (Filter.Eventually.of_forall fun x hx => hsub0 hx)
  have hWlam_memLp : MemLp Work.FTS.GalBasis.cc.Wlam 2 (volume.restrict (Set.Ioi z)) :=
    (memLp_two_iff_integrable_sq (Wlam_aesm_restrict hz0)).mpr hWlam_sq_int
  -- radial Cauchy–Schwarz
  have hFle : ∫ s in Set.Ioi z, F s ≤ EpsSq α h := by
    rw [hEpsSq]
    exact MeasureTheory.setIntegral_mono_set hFint_Iz
      (Filter.Eventually.of_forall fun x => hFnn x)
      (Filter.Eventually.of_forall fun x hx => by
        simp only [Set.mem_Ioi] at hx
        simp only [Work.Spaces.Iz, Set.mem_Ici]
        linarith)
  have hCS : ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s
      ≤ Real.sqrt W2e * Real.sqrt (EpsSq α h) := by
    have hcs := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt
      (u := Work.FTS.GalBasis.cc.Wlam) (v := A) (s := Set.Ioi z) hWlam_memLp hA_memLp
    have hA2eq : (∫ s in Set.Ioi z, A s ^ 2) = ∫ s in Set.Ioi z, F s :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s _ => hA2 s)
    have hnn : 0 ≤ ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s := by
      refine MeasureTheory.integral_nonneg_of_ae ?_
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
      have hzs : z < s := Set.mem_Ioi.mp hs
      exact mul_nonneg
        (Work.FTS.GalBasis.cc.Wlam_nonneg (le_of_lt (lt_of_le_of_lt hz0 hzs))) (hAnn s)
    have hWle : Real.sqrt (∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s ^ 2)
        ≤ Real.sqrt W2e := Real.sqrt_le_sqrt hWlam_sq_le
    have hAle : Real.sqrt (∫ s in Set.Ioi z, A s ^ 2) ≤ Real.sqrt (EpsSq α h) := by
      rw [hA2eq]
      exact Real.sqrt_le_sqrt hFle
    calc ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s
        = |∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s| := (abs_of_nonneg hnn).symm
      _ ≤ Real.sqrt (∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s ^ 2)
            * Real.sqrt (∫ s in Set.Ioi z, A s ^ 2) := hcs
      _ ≤ Real.sqrt W2e * Real.sqrt (EpsSq α h) :=
          mul_le_mul hWle hAle (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- the a.e. density bound and the integrability of the majorant
  have hbd : ∀ᵐ s ∂(volume.restrict (Set.Ioi z)), |Work.Construction.L12dens h s|
      ≤ BKe α * (Work.FTS.GalBasis.cc.Wlam s * A s) := by
    filter_upwards [hslice, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hsl hs
    have hzs : z < s := Set.mem_Ioi.mp hs
    have h := abs_L12dens_le_eps hgam h (by linarith) hsl
    simpa only [hA, hFdef] using h
  have hAMGM : ∀ s ∈ Set.Ioi z,
      Work.FTS.GalBasis.cc.Wlam s * A s ≤ Work.FTS.GalBasis.cc.Wlam s ^ 2 + A s ^ 2 :=
    fun s _ => by nlinarith [sq_nonneg (Work.FTS.GalBasis.cc.Wlam s - A s)]
  have hsum_int : IntegrableOn
      (fun s => Work.FTS.GalBasis.cc.Wlam s ^ 2 + A s ^ 2) (Set.Ioi z) :=
    hWlam_sq_int.add hA2int
  have hmax_int : IntegrableOn
      (fun s => BKe α * (Work.FTS.GalBasis.cc.Wlam s * A s)) (Set.Ioi z) := by
    refine MeasureTheory.Integrable.mono' (hsum_int.const_mul (BKe α))
      (((Wlam_aesm_restrict hz0).mul hA_aesm).const_mul (BKe α)) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    have hzs : z < s := Set.mem_Ioi.mp hs
    have hnn : 0 ≤ BKe α * (Work.FTS.GalBasis.cc.Wlam s * A s) :=
      mul_nonneg (BKe_nonneg α)
        (mul_nonneg (Work.FTS.GalBasis.cc.Wlam_nonneg (le_of_lt (lt_of_le_of_lt hz0 hzs)))
          (hAnn s))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_left (hAMGM s hs) (BKe_nonneg α)
  -- assembly
  have h1 : |Work.Construction.L12 h z|
      ≤ ∫ s in Set.Ioi z, |Work.Construction.L12dens h s| := by
    have hL : Work.Construction.L12 h z
        = ∫ s in Set.Ioi z, Work.Construction.L12dens h s := rfl
    rw [hL]
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioi z))
        (f := fun s => Work.Construction.L12dens h s))
  have h2 : ∫ s in Set.Ioi z, |Work.Construction.L12dens h s|
      ≤ ∫ s in Set.Ioi z, BKe α * (Work.FTS.GalBasis.cc.Wlam s * A s) :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun s => abs_nonneg _) hmax_int hbd
  have h3 : ∫ s in Set.Ioi z, BKe α * (Work.FTS.GalBasis.cc.Wlam s * A s)
      = BKe α * ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s :=
    MeasureTheory.integral_const_mul _ _
  calc |Work.Construction.L12 h z|
      ≤ ∫ s in Set.Ioi z, |Work.Construction.L12dens h s| := h1
    _ ≤ ∫ s in Set.Ioi z, BKe α * (Work.FTS.GalBasis.cc.Wlam s * A s) := h2
    _ = BKe α * ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s := h3
    _ ≤ BKe α * (Real.sqrt W2e * Real.sqrt (EpsSq α h)) :=
        mul_le_mul_of_nonneg_left hCS (BKe_nonneg α)
    _ ≤ 5 * (Real.sqrt W2e * Real.sqrt (EpsSq α h)) :=
        mul_le_mul_of_nonneg_right (BKe_le_five hα)
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ = (5 * Real.sqrt W2e) * Real.sqrt (EpsSq α h) := by ring
    _ ≤ (5 * Real.sqrt W2e + 1) * Real.sqrt (EpsSq α h) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)

/-! ## The requested theorem -/

theorem L12_sub_EpsSq_le : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
    ∀ f g : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.EllipticEst.SmoothOpen g →
      Work.Spaces.HkMem α 4 f → Work.Spaces.HkMem α 4 g →
      Work.FTS.StrongEps.EpsMem α (fun z θ => f z θ - g z θ) →
      ∀ z ∈ Work.Spaces.Iz,
        |Work.Construction.L12 f z - Work.Construction.L12 g z|
          ≤ C * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ - g z θ)) := by
  obtain ⟨C, hC, hCbound⟩ := L12_le_sqrt_EpsSq
  refine ⟨C, hC, ?_⟩
  intro α hα f g hfs hgs hmf hmg he z hz
  rw [← Work.FTS.StrongEps.EComparison.L12_sub_HkMem hfs hgs hmf hmg z hz]
  exact hCbound α hα (fun z θ => f z θ - g z θ) he z hz

end Work.FTS.StrongEps.EpsSqTools
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.Jeps_absCompactBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set

namespace Work.FTS.StrongEps


end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.h6pair_mod =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.StrongPersist.H6Pair6Aux.h6pair_mod` — the modulation bound `|muDyn| ≤ K α^{-10}(1+M)^4`

`muDyn α Φ g τ = Construction.mufunS α (N0 α F f) (N α F Φ) f` with `f = slice g τ`,
`Φ = slice Φ τ`, `F = F_* + f` (`Ftau`), and

  `mufunS α N0v Nv g = (1/(2α))·(L₁₂(N0v)(0) + L₁₂(Nv)(0)) + (1/(2α))·L₁₂(3 D_θg/(1+z))(0)`

(`Construction/Defs.lean:205`, `Construction/MufunS.lean:65`).  Hence `muDyn` is bounded by
`(1/(2α))` times the *three zero-mode estimates* of the paper's Proposition `muestimate`
(tex 1508–1526), evaluated at the slice `f` and the elliptic solution `Ψ = slice Φ τ`:

* the transport zero mode `|L₁₂(3 D_θ f/(1+z))(0)| ≤ C |f|_{ℋ⁴}`, which is
  `StrongPersist.L3Aux.Transport_L12_zero_le`, *already proved* in this area (a ∂_θ-integration
  by parts plus weighted Cauchy–Schwarz; no elliptic input);
* the `N₀` zero mode `|L₁₂(N₀ α (F_*+f) f)(0)| ≤ K α^{-9}(1+M)⁴` (`h6pair_N0_zero`, the
  level-six analogue of the *proved* level-four row `Nonlinear.Pieces.rl0_bound`; `N₀` involves
  `F_*` and `f` only);
* the `N` zero mode `|L₁₂(N α (F_*+f) Ψ)(0)| ≤ K α^{-9}(1+M)⁴` (`h6pair_N_zero`), which is the
  half carrying the elliptic residual `PhiTil α F Ψ`.

The assembly below (`h6pair_mod_of_pieces`) is pure bookkeeping: the triangle inequality, the
`Xn α f ≤ M` datum of `L6Ctx`, and the arithmetic
`(1/(2α))·(CA·M + (KN0+KN)·α^{-9}(1+M)⁴) ≤ K α^{-10}(1+M)⁴` (using `M α^9 ≤ (1+M)⁴` for
`M ≥ 0`, `α ≤ 1`).

See `H6Pair6Aux/NOTES_H6Pair6Aux_route.md` for the route, the level-four analogues and the exact
interface input that the `N`-half consumes.
-/

namespace Work.FTS.StrongPersist.H6Pair6Aux

open Work.FTS.Galerkin (Fn Fam slice muDyn)

noncomputable section

/-- The transport zero mode `|L₁₂(3 D_θf/(1+z))(0)| ≤ C|f|_{ℋ⁴}` in the exact spelling of the
`muDyn` decomposition: this is `L3Aux.Transport_L12_zero_le` with
`Coercivity.Transport f = 3 D_θf/(1+z)` and `Coercivity.L12f = Construction.L12` unfolded. -/
theorem transport_zero_le' : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : Fn),
    0 < α → α ≤ 1 → Work.Spaces.HkMem α 4 f →
    |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth f z θ / (1 + z)) 0|
      ≤ C * Work.FTS.Nonlin.Xn α f := by
  obtain ⟨C, hC, h⟩ := Work.FTS.StrongPersist.L3Aux.Transport_L12_zero_le
  refine ⟨C, hC, fun α f hα hα1 hm => ?_⟩
  have := h α f hα hα1 hm
  simpa only [Work.Coercivity.Transport, Work.Coercivity.L12f, Work.Construction.L12,
    Work.FM.L12, Work.FM.L12dens, Work.Elliptic.L12, Work.Elliptic.L12dens] using this



end

end Work.FTS.StrongPersist.H6Pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Row6Gam.b1gInner =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Row6

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section
/-! ## The pointwise-in-`z` bound on the angular integral -/

theorem b1gInner : ∀ (α : ℝ) (A f : ℝ → ℝ → ℝ) (M : ℝ), α ∈ Set.Ioc 0 1 →
    Work.FTS.EllipticEst.SmoothOpen A → Work.FTS.EllipticEst.SmoothOpen f →
    Work.Spaces.HkMem α 6 A → Work.Spaces.HkMem α 6 f → Work.FTS.Nonlin.Xn α f ≤ M →
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ, |b1gF α A f (z, θ)| ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ≤ Real.sqrt 3 * M * ((Work.Spaces.w z
              * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z))
            * (Work.Spaces.w z
              * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z))) := by
  intro α A f M hα hA hf h6A h6f hXnM
  obtain ⟨hα0, hα1⟩ := hα
  have hMnn : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hXnM
  have h4f : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hf 4 (by norm_num) h6f
  have hgam1 : Work.Spaces.gam α - 1 = α / 10 :=
    Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.hgam_const
  have hgam_pos : 0 < Work.Spaces.gam α - 1 := by rw [hgam1]; linarith
  have hMXnn : ∀ z : ℝ, 0 ≤ Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z := by
    intro z
    rw [Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX_apply]
    refine add_nonneg (mul_nonneg (by positivity)
        (MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)))
      (mul_nonneg (div_nonneg (by norm_num) hgam_pos.le)
        (MeasureTheory.setIntegral_nonneg measurableSet_Icc
          (fun θ hθ => mul_nonneg
            (Real.rpow_nonneg
              (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.sin_two_nonneg_of_Iθ' hθ) _)
            (sq_nonneg _))))
  have hQznn : ∀ z : ℝ, 0 ≤ Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z := by
    intro z
    rw [Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz_apply]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg
        (Real.rpow_nonneg
          (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.sin_two_nonneg_of_Iθ' hθ) _) (sq_nonneg _))
  have hXpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter 5 A z θ) ^ 2
        ≤ Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z := by
    intro z θ hz hθ0 hθ1
    rw [Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX_apply]
    exact Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.xSliceAgmon5 α A hα0 hα1 hA h6A
      z θ hz hθ0 hθ1
  have hPz_le : ∀ z : ℝ, 0 < z → b1gPz α f z ≤ 3 * M ^ 2 := by
    intro z hz
    have h1 : b1gPz α f z ≤ 3 * Work.Spaces.HkSq α 4 f := by
      rw [b1gPz_apply]
      exact Work.FTS.StrongPersist.H6Row6Gam.gamSliceSup11 α f hα0 hα1 hf h4f z hz
    have h2 : Work.Spaces.HkSq α 4 f = (Work.Spaces.HkNorm α 4 f) ^ 2 := by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 f)]
    have h3 : (Work.Spaces.HkNorm α 4 f) ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 f) hXnM 2
    linarith [h1, h2.le, h2.ge, h3]
  have hCSθ : ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (|Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|))
        ≤ Real.sqrt (b1gPz α f z)
          * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z) := by
    intro z hz
    have h := Work.FTS.StrongPersist.H6Row6Gam.gamSliceCS11 α f hα0 hα1 hf h6f z hz
    simpa only [mul_assoc, b1gPz_apply,
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz_apply] using h
  have hAMall : ∀ z : ℝ,
      (Work.Spaces.w z * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z))
        * (Work.Spaces.w z
          * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z))
      ≤ ((Work.Spaces.w z) ^ 2 * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z
          + (Work.Spaces.w z) ^ 2
            * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z) / 2 := by
    intro z
    have ha : (Work.Spaces.w z
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)) ^ 2
        = (Work.Spaces.w z) ^ 2
          * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z := by
      rw [mul_pow, Real.sq_sqrt (hMXnn z)]
    have hb : (Work.Spaces.w z
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z)) ^ 2
        = (Work.Spaces.w z) ^ 2
          * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z := by
      rw [mul_pow, Real.sq_sqrt (hQznn z)]
    nlinarith [sq_nonneg (Work.Spaces.w z
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
      - Work.Spaces.w z * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z))]
  have hIz : (Work.Spaces.Iz : Set ℝ) =ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
  rw [MeasureTheory.Measure.restrict_congr_set hIz]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
  have hpt : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |b1gF α A f (z, θ)| ≤ (Work.Spaces.w z) ^ 2
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
        * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (|Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|)) := by
    refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ hθ0 hθ1 => ?_)
    have hθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    have hσnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
      Real.rpow_nonneg (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.sin_two_nonneg_of_Iθ' hθ) _
    have hX2 : |Work.Spaces.DzIter 5 A z θ|
        ≤ Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (hXpt z θ hz hθ0 hθ1)
    have habsF : |b1gF α A f (z, θ)| = (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * |Work.Spaces.DzIter 5 A z θ|
          * (|Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|) := by
      simp only [b1gF_apply, Work.FTS.TransportS.leafGam, Work.Spaces.mixed_zero_right]
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (mul_nonneg (sq_nonneg _) hσnn)]
      ring
    rw [habsF]
    have h1 : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * |Work.Spaces.DzIter 5 A z θ|
          * (|Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|)
        ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
          * (|Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|) := by
      refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      exact mul_le_mul_of_nonneg_left hX2 (mul_nonneg (sq_nonneg _) hσnn)
    refine h1.trans_eq ?_
    ring
  have hInt_eq : (∫ θ, (Work.Spaces.w z) ^ 2
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
        * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (|Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|))
      ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      = (Work.Spaces.w z) ^ 2
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
        * (∫ θ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (|Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    MeasureTheory.integral_const_mul _ _
  have hWint := Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.integrableOn_gamMixed_slice
    (b := 1) (a := 1) hα0 hf h6f le_rfl (by norm_num) hz
  have hZint := Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.integrableOn_gamMixed_slice
    (b := 5) (a := 1) hα0 hf h6f le_rfl (by norm_num) hz
  have hmaj : MeasureTheory.Integrable (fun θ => (Work.Spaces.w z) ^ 2
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
        * (((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 1 1 f z θ) ^ 2
          + (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 5 1 f z θ) ^ 2) / 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (((hWint.add hZint)).div_const 2).const_mul
      ((Work.Spaces.w z) ^ 2
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z))
  have hint1 : MeasureTheory.Integrable (fun θ => (Work.Spaces.w z) ^ 2
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
        * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (|Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
    · exact (Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
          * (|Work.Spaces.mixed 1 1 f p.1 p.2| * |Work.Spaces.mixed 5 1 f p.1 p.2|))
        (contOn_sig_abs11 hf) hz).const_mul
        ((Work.Spaces.w z) ^ 2
          * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z))
    · refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ hθ0 hθ1 => ?_)
      have hθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
      have hσnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        Real.rpow_nonneg (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.sin_two_nonneg_of_Iθ' hθ) _
      have hc : 0 ≤ (Work.Spaces.w z) ^ 2
          * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z) :=
        mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
      rw [Real.norm_of_nonneg (mul_nonneg hc
        (mul_nonneg hσnn (mul_nonneg (abs_nonneg _) (abs_nonneg _))))]
      have habs : |Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|
          ≤ ((Work.Spaces.mixed 1 1 f z θ) ^ 2
              + (Work.Spaces.mixed 5 1 f z θ) ^ 2) / 2 := by
        nlinarith [sq_nonneg (|Work.Spaces.mixed 1 1 f z θ| - |Work.Spaces.mixed 5 1 f z θ|),
          sq_abs (Work.Spaces.mixed 1 1 f z θ), sq_abs (Work.Spaces.mixed 5 1 f z θ)]
      have hAM2 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (|Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|)
          ≤ ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed 1 1 f z θ) ^ 2
              + (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed 5 1 f z θ) ^ 2) / 2 := by
        have h := mul_le_mul_of_nonneg_left habs hσnn
        calc (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (|Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|)
            ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (((Work.Spaces.mixed 1 1 f z θ) ^ 2
                  + (Work.Spaces.mixed 5 1 f z θ) ^ 2) / 2) := h
          _ = ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                  * (Work.Spaces.mixed 1 1 f z θ) ^ 2
                + (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                  * (Work.Spaces.mixed 5 1 f z θ) ^ 2) / 2 := by ring
      exact mul_le_mul_of_nonneg_left hAM2 hc
  calc (∫ θ, |b1gF α A f (z, θ)| ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      ≤ ∫ θ, (Work.Spaces.w z) ^ 2
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
        * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (|Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|))
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        MeasureTheory.integral_mono_ae (b1gSliceInt α A f hα0 hα1 hA hf h6A h6f z hz)
          hint1 hpt
    _ = (Work.Spaces.w z) ^ 2
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
        * (∫ θ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (|Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := hInt_eq
    _ ≤ (Work.Spaces.w z) ^ 2
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
        * (Real.sqrt (b1gPz α f z)
          * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z)) :=
        mul_le_mul_of_nonneg_left (hCSθ z hz) (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))
    _ ≤ Real.sqrt 3 * M
        * ((Work.Spaces.w z
            * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z))
          * (Work.Spaces.w z
            * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z))) := by
        have h2 : Real.sqrt (b1gPz α f z) ≤ Real.sqrt 3 * M := by
          calc Real.sqrt (b1gPz α f z) ≤ Real.sqrt (3 * M ^ 2) :=
                Real.sqrt_le_sqrt (hPz_le z hz)
            _ = Real.sqrt 3 * M := by
                rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_sq_eq_abs,
                  abs_of_nonneg hMnn]
        have h3 : 0 ≤ (Work.Spaces.w z) ^ 2
            * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z) :=
          mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
        calc (Work.Spaces.w z) ^ 2
              * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
              * (Real.sqrt (b1gPz α f z)
                * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z))
            ≤ (Work.Spaces.w z) ^ 2
              * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
              * ((Real.sqrt 3 * M)
                * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z)) := by
              refine mul_le_mul_of_nonneg_left ?_ h3
              exact mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
          _ = Real.sqrt 3 * M
              * ((Work.Spaces.w z
                  * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z))
                * (Work.Spaces.w z
                  * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z))) := by
              ring
end

end Work.FTS.StrongPersist.H6Row6
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.coefData_pertSharp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `coefData_pertSharp` — the `CoefData` of the perturbed residual, sharp pointwise price

`T6Coef.coefData_pert` prices the three perturbed residual fields `Rop(Φ̃_f)`,
`Uop(Φ̃_f)/sin 2θ`, `Vop(Φ̃_f)` pointwise by the *inflated* constant
`K (1+|Ce|)³ α^{-10} (1+M)³` (the losses `(1+|Ce|)³(1+M)³ ≥ |Ce| M` and `α^{-10} ≥ α^{-1/2}`
are conveniences of that lemma).  Here the pointwise slot is kept at its sharp value
`K α^{-1/2} |Ce| M`: the open-quadrant Agmon bound `SupOpenH2` gives
`|A z θ| ≤ C α^{-1/2} HkNorm α 2 A`, and the two monotonicities
`HkNorm α 2 A ≤ HkNorm α 4 A = Xn α A ≤ Ce · Xn α f ≤ |Ce| M` finish it, while the `ℋ⁶`-pricing
of `EllPkgK α 6` is transported verbatim (`HkNorm α 6 A ≤ Ce HkNorm α 6 f ≤ |Ce| HkNorm α 6 f`).
No hypothesis is used beyond what is stated.
-/

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

theorem coefData_pertSharp : ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (Ce M : ℝ) (f Φg : Work.FTS.Galerkin.Fn),
      Work.FTS.VocabO.HQo α 4 f → Work.FTS.Nonlin.Xn α f ≤ M →
      Work.FTS.VocabO.EllPkgGo α Ce f Φg → Work.FTS.StrongPersist.EllPkgK α 6 Ce f Φg →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α
          (Work.Construction.Rop α (Work.Construction.PhiTil α f Φg))
          (K * α ^ (-(1 / 2 : ℝ)) * |Ce| * M) (|Ce| * M)
          (|Ce| * Work.Spaces.HkNorm α 6 f) ∧
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α
          (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f Φg) z θ
            / Work.Construction.s2 θ)
          (K * α ^ (-(1 / 2 : ℝ)) * |Ce| * M) (|Ce| * M)
          (|Ce| * Work.Spaces.HkNorm α 6 f) ∧
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α
          (Work.Construction.Vop (Work.Construction.PhiTil α f Φg))
          (K * α ^ (-(1 / 2 : ℝ)) * |Ce| * M) (|Ce| * M)
          (|Ce| * Work.Spaces.HkNorm α 6 f) := by
  obtain ⟨C, hCpos, hsup⟩ := Work.FTS.StrongPersist.SupOpenH2
  refine ⟨C + 1, by linarith, ?_⟩
  intro α hαI Ce M f Φg hHQ hXM hGo hK
  have hα : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  have hMnn : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hXM
  have hr : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hCeabs : 0 ≤ |Ce| := abs_nonneg Ce
  have hrCeM : 0 ≤ α ^ (-(1 / 2 : ℝ)) * |Ce| * M :=
    mul_nonneg (mul_nonneg hr hCeabs) hMnn
  -- the pointwise (Agmon) pricing of any level-four field whose `Xn` is `≤ |Ce| M`
  have keyval : ∀ (g : Work.FTS.Galerkin.Fn), Work.FTS.VocabO.HQo α 4 g →
      Work.FTS.Nonlin.Xn α g ≤ |Ce| * M →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |g z θ| ≤ (C + 1) * α ^ (-(1 / 2 : ℝ)) * |Ce| * M := by
    intro g hQ4 hbd z θ hz hθ0 hθ1
    obtain ⟨hsm, hm4⟩ := hQ4
    have hm2 : Work.Spaces.HkMem α 2 g :=
      Work.FTS.OpenPkg.HkMem_mono_open hsm 2 (by norm_num) hm4
    have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩
    have hs := hsup α hα hα1 g ⟨hsm, hm2⟩ z θ hmem
    have hmono : Work.Spaces.HkNorm α 2 g ≤ Work.Spaces.HkNorm α 4 g :=
      Work.FTS.StrongLWP.HkNorm_mono_of_mem (by norm_num) hm4
    have hCf : 0 ≤ C * α ^ (-(1 / 2 : ℝ)) := mul_nonneg hCpos.le hr
    have h1 : C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 2 g
        ≤ C * α ^ (-(1 / 2 : ℝ)) * (|Ce| * M) :=
      mul_le_mul_of_nonneg_left (le_trans hmono hbd) hCf
    have h2 : C * α ^ (-(1 / 2 : ℝ)) * (|Ce| * M)
        ≤ (C + 1) * α ^ (-(1 / 2 : ℝ)) * |Ce| * M := by
      have hstep : C * (α ^ (-(1 / 2 : ℝ)) * |Ce| * M)
          ≤ (C + 1) * (α ^ (-(1 / 2 : ℝ)) * |Ce| * M) :=
        mul_le_mul_of_nonneg_right (by linarith) hrCeM
      calc C * α ^ (-(1 / 2 : ℝ)) * (|Ce| * M)
          = C * (α ^ (-(1 / 2 : ℝ)) * |Ce| * M) := by ring
        _ ≤ (C + 1) * (α ^ (-(1 / 2 : ℝ)) * |Ce| * M) := hstep
        _ = (C + 1) * α ^ (-(1 / 2 : ℝ)) * |Ce| * M := by ring
    linarith [hs, h1, h2]
  -- the level-four pricing `Xn α A ≤ |Ce| M`, from `EllPkgGo`
  have hXnR : Work.FTS.Nonlin.Xn α (Work.Construction.Rop α (Work.Construction.PhiTil α f Φg))
      ≤ |Ce| * M := by
    have hXfnn : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
    calc Work.FTS.Nonlin.Xn α (Work.Construction.Rop α (Work.Construction.PhiTil α f Φg))
        ≤ Ce * Work.FTS.Nonlin.Xn α f := hGo.R.2
      _ ≤ |Ce| * Work.FTS.Nonlin.Xn α f :=
            mul_le_mul_of_nonneg_right (le_abs_self Ce) hXfnn
      _ ≤ |Ce| * M := mul_le_mul_of_nonneg_left hXM hCeabs
  have hXnU : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f Φg) z θ
        / Work.Construction.s2 θ) ≤ |Ce| * M := by
    have hXfnn : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
    calc Work.FTS.Nonlin.Xn α
          (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f Φg) z θ
            / Work.Construction.s2 θ)
        ≤ Ce * Work.FTS.Nonlin.Xn α f := hGo.U.2
      _ ≤ |Ce| * Work.FTS.Nonlin.Xn α f :=
            mul_le_mul_of_nonneg_right (le_abs_self Ce) hXfnn
      _ ≤ |Ce| * M := mul_le_mul_of_nonneg_left hXM hCeabs
  have hXnV : Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.Construction.PhiTil α f Φg))
      ≤ |Ce| * M := by
    have hXfnn : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
    calc Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.Construction.PhiTil α f Φg))
        ≤ Ce * Work.FTS.Nonlin.Xn α f := hGo.V.2
      _ ≤ |Ce| * Work.FTS.Nonlin.Xn α f :=
            mul_le_mul_of_nonneg_right (le_abs_self Ce) hXfnn
      _ ≤ |Ce| * M := mul_le_mul_of_nonneg_left hXM hCeabs
  -- the level-six pricing `HkNorm α 6 A ≤ |Ce| HkNorm α 6 f`, from `EllPkgK`
  have hN6R : Work.Spaces.HkNorm α 6 (Work.Construction.Rop α (Work.Construction.PhiTil α f Φg))
      ≤ |Ce| * Work.Spaces.HkNorm α 6 f := by
    have h6nn : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
    calc Work.Spaces.HkNorm α 6 (Work.Construction.Rop α (Work.Construction.PhiTil α f Φg))
        ≤ Ce * Work.Spaces.HkNorm α 6 f := hK.R.2
      _ ≤ |Ce| * Work.Spaces.HkNorm α 6 f :=
            mul_le_mul_of_nonneg_right (le_abs_self Ce) h6nn
  have hN6U : Work.Spaces.HkNorm α 6
      (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f Φg) z θ
        / Work.Construction.s2 θ) ≤ |Ce| * Work.Spaces.HkNorm α 6 f := by
    have h6nn : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
    calc Work.Spaces.HkNorm α 6
          (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f Φg) z θ
            / Work.Construction.s2 θ)
        ≤ Ce * Work.Spaces.HkNorm α 6 f := hK.U.2
      _ ≤ |Ce| * Work.Spaces.HkNorm α 6 f :=
            mul_le_mul_of_nonneg_right (le_abs_self Ce) h6nn
  have hN6V : Work.Spaces.HkNorm α 6 (Work.Construction.Vop (Work.Construction.PhiTil α f Φg))
      ≤ |Ce| * Work.Spaces.HkNorm α 6 f := by
    have h6nn : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
    calc Work.Spaces.HkNorm α 6 (Work.Construction.Vop (Work.Construction.PhiTil α f Φg))
        ≤ Ce * Work.Spaces.HkNorm α 6 f := hK.V.2
      _ ≤ |Ce| * Work.Spaces.HkNorm α 6 f :=
            mul_le_mul_of_nonneg_right (le_abs_self Ce) h6nn
  exact
    ⟨⟨hGo.R.1.1, hGo.R.1.2, hK.R.1.2, keyval _ hGo.R.1 hXnR, hXnR, hN6R⟩,
     ⟨hGo.U.1.1, hGo.U.1.2, hK.U.1.2, keyval _ hGo.U.1 hXnU, hXnU, hN6U⟩,
     ⟨hGo.V.1.1, hGo.V.1.2, hK.V.1.2, keyval _ hGo.V.1 hXnV, hXnV, hN6V⟩⟩

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6SplitIP6 =====
section

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

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **`H6Split` for the concrete pairing `IP6 1 … 1`.**  From the finite-order honesty (`C⁶` on
the open quadrant) and the `ℋ⁶`-membership of the two summands `linPart α f`, `rhs` and of `f`
itself, the pairing splits across the sum. -/
theorem H6Split_IP6 {α : ℝ} {f rhs : Fn} (hα : 0 < α)
    (hl : ContDiffOn ℝ 6 (Function.uncurry (linPart α f)) Work.FTS.EllipticEst.Q0)
    (hr : ContDiffOn ℝ 6 (Function.uncurry rhs) Work.FTS.EllipticEst.Q0)
    (hf : ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hml : Work.Spaces.HkMem α 6 (linPart α f))
    (hmr : Work.Spaces.HkMem α 6 rhs) (hmf : Work.Spaces.HkMem α 6 f) :
    H6Split (IP6 1 1 1 1 1 1 1 1 1 1) α f rhs :=
  IP6AddFin hα hl hr hf hml hmr hmf

/-- **`hsplit` discharged for an `H6Adm` slice.**  In the strong route the slice `f` is in
`H6Adm α` (so it is `C⁶` and `ℋ⁶`), the right-hand side `rhs = dynRHS α Φ g τ` is `HQo α 6`
(hence `C⁶` and `ℋ⁶`), and `linPart α f` is `ℋ⁶` by `H6LinMem6` and `C⁶` on the open quadrant by
the (finite-order) regularity of the solution.  Under those hypotheses the `hsplit` field of
`L6Ctx` holds for the concrete pairing — so `L6Ctx` needs no `SmoothOpen` of `𝓛_Γ^T f` (which is
false, see `NOTES_L3_lin_FALSE.md`). -/
theorem H6Split_IP6_of_adm {α : ℝ} {f rhs : Fn} (hα : 0 < α)
    (hf : H6Adm α f) (hr : Work.FTS.VocabO.HQo α 6 rhs) (hlc : ContDiffOn ℝ 6 (Function.uncurry (linPart α f))
      Work.FTS.EllipticEst.Q0)
    (hml : Work.Spaces.HkMem α 6 (linPart α f)) :
    H6Split (IP6 1 1 1 1 1 1 1 1 1 1) α f rhs :=
  H6Split_IP6 hα hlc (hr.1.forall 6) (hf.reg.1.forall 6) hml hr.2 hf.reg.2

end Work.FTS.StrongPersist
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.SP6.FieldHints =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.SP6


end Work.FTS.StrongPersist.SP6
end
-- ===== merged: Submission.Work.FTS.StrongPersist.StarPkg6Assembly =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

set_option autoImplicit false
set_option linter.unusedVariables false

theorem StarPkg6OfPieces
    (hWl : ∃ CW : ℝ, 0 < CW ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (K : ℝ),
      0 < α → α ≤ 1 → (∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → f z θ = 0) →
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.VocabO2.FlatW 6 f K →
      Work.Spaces.WlInfMem α 6 f ∧ Work.Spaces.WlInf α 6 f ≤ CW * K)
    (hDz : ∃ CD : ℝ, 0 < CD ∧ ∀ (K : ℝ) (Y : ℝ → ℝ → ℝ),
      0 ≤ K → Work.FTS.EllipticEst.SmoothOpen Y → Work.FTS.VocabO2.FlatW 7 Y K →
      Work.FTS.PhiStar.F0 6 (CD * K) (Work.FTS.PhiStar.Yblk Y))
    (hF : ∃ CF : ℝ, 0 < CF ∧ ∀ (α K KY KD : ℝ) (Y : ℝ → ℝ → ℝ),
      0 ≤ α → 0 ≤ K → 0 ≤ KY → 0 ≤ KD → Work.FTS.EllipticEst.SmoothOpen Y →
      Work.FTS.VocabO2.FlatW 7 Y K → Work.FTS.PhiStar.Fb 6 KY Y →
      Work.FTS.PhiStar.F0 6 KD (Work.FTS.PhiStar.Yblk Y) →
      Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EH α Y) (CF * (α + 1) * (K + KY + KD)) ∧
      Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EVz Y) (CF * (α + 1) * (K + KY + KD)) ∧
      Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EV Y) (CF * (α + 1) * (K + KY + KD)) ∧
      Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EUz α Y) (CF * (α + 1) * (K + KY + KD)) ∧
      Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EU α Y) (CF * (α + 1) * (K + KY + KD))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α Cs : ℝ) (Φs : Work.FTS.Galerkin.Fn),
      0 < α → α ≤ 1 / 4 → 0 < Cs → Work.FTS.VocabO2.StarCore α Cs Φs →
      StarPkg6 α (C * Cs) Φs := by
  obtain ⟨CW, hCW, hWl⟩ := hWl
  obtain ⟨CD, hCD, hDz⟩ := hDz
  obtain ⟨CF, hCF, hF⟩ := hF
  obtain ⟨CB, hCB, hFb⟩ := Work.FTS.PhiStar.CoreAux.Fb_of_FlatW
  obtain ⟨C1, hC1, hStar⟩ := Work.FTS.PhiStar.StarPkgo2OfCore
  -- the master constants
  set CBal : ℝ := CW * CF * (5 / 4) * (1 + CB + CD) with hCBal
  have hCBal0 : 0 ≤ CBal := by rw [hCBal]; positivity
  set Cfin : ℝ := max C1 CBal + 1 with hCfin
  have hCfin0 : 0 < Cfin := by
    rw [hCfin]
    linarith [le_max_left C1 CBal, le_max_right C1 CBal]
  have hC1le : C1 ≤ Cfin := by
    rw [hCfin]; linarith [le_max_left C1 CBal]
  have hCBle : CBal ≤ Cfin := by
    rw [hCfin]; linarith [le_max_right C1 CBal]
  refine ⟨Cfin, hCfin0, ?_⟩
  intro α Cs Φs hα hα4 hCs hcore
  have hα0 : (0 : ℝ) ≤ α := le_of_lt hα
  have hα1 : α ≤ 1 := by linarith
  have hα54 : α + 1 ≤ 5 / 4 := by linarith
  have hK0 : 0 ≤ Cs * α := mul_nonneg (le_of_lt hCs) hα0
  have hCB0 : 0 ≤ CB := le_of_lt hCB
  have hCD0 : 0 ≤ CD := le_of_lt hCD
  -- the star datum
  have hsmY : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.VocabO2.Ycheck α Φs) :=
    (Work.FTS.PhiStar.CoreAux.smoothOpen_PhiTs hα hα1 hcore.smooth).2.2
  have hY7 : Work.FTS.VocabO2.FlatW 7 (Work.FTS.VocabO2.Ycheck α Φs) (Cs * α) := hcore.core
  have hFbY : Work.FTS.PhiStar.Fb 6 (CB * (Cs * α)) (Work.FTS.VocabO2.Ycheck α Φs) :=
    hFb (Cs * α) _ hK0 hsmY hY7
  have hDzY : Work.FTS.PhiStar.F0 6 (CD * (Cs * α)) (Work.FTS.PhiStar.Yblk (Work.FTS.VocabO2.Ycheck α Φs)) :=
    hDz (Cs * α) _ hK0 hsmY hY7
  obtain ⟨hFeh, hFevz, hFev, hFeuz, hFeu⟩ :=
    hF α (Cs * α) (CB * (Cs * α)) (CD * (Cs * α)) (Work.FTS.VocabO2.Ycheck α Φs)
      hα0 hK0 (by positivity) (by positivity) hsmY hY7 hFbY hDzY
  -- the identities, smoothness and vanishing of the five fields
  obtain ⟨hidH, hidV, hidVz, hidU, hidUz, _hidPU⟩ :=
    Work.FTS.PhiStar.CoreAux.fields_ident hα hα1 hcore.smooth
  obtain ⟨hvH, hvV, hvVz, hvU, hvUz, -, -, -, -, -⟩ :=
    Work.FTS.PhiStar.CoreAux.fields_vanish hα hcore
  obtain ⟨-, hsmH, hsmV, hsmVz, hsmU, hsmUz, -⟩ :=
    Work.FTS.PhiStar.CoreAux.fields_smooth hα hα1 hcore.smooth
  -- the five order-six `WlInf`-bounds, at the intermediate constant
  set Km : ℝ := CF * (α + 1) * (Cs * α + CB * (Cs * α) + CD * (Cs * α)) with hKm
  have hH := hWl α
    (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ)
    Km hα hα1 (zeroOff_of_vanish_Q0 hvH) hsmH
    (FlatW_congr (fun z θ hz hθ hθ' => hidH z θ hz hθ hθ') hFeh)
  have hV := hWl α (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs))
    Km hα hα1 (zeroOff_of_vanish_Q0 hvV) hsmV
    (FlatW_congr (fun z θ hz hθ hθ' => hidV z θ hz hθ hθ') hFev)
  have hVz := hWl α
    (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ)
    Km hα hα1 (zeroOff_of_vanish_Q0 hvVz) hsmVz
    (FlatW_congr (fun z θ hz hθ hθ' => hidVz z θ hz hθ hθ') hFevz)
  have hU := hWl α
    (fun z θ => Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ)
    Km hα hα1 (zeroOff_of_vanish_Q0 hvU) hsmU
    (FlatW_congr (fun z θ hz hθ hθ' => hidU z θ hz hθ hθ') hFeu)
  have hUz := hWl α
    (fun z θ => (z + 1) / z * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ))
    Km hα hα1 (zeroOff_of_vanish_Q0 hvUz) hsmUz
    (FlatW_congr (fun z θ hz hθ hθ' => hidUz z θ hz hθ hθ') hFeuz)
  -- the constant comparison: `CW * Km ≤ CBal * (Cs * α)`
  have hKm_le : CW * Km ≤ CBal * (Cs * α) := by
    have hx : 0 ≤ Cs * α + CB * (Cs * α) + CD * (Cs * α) :=
      add_nonneg (add_nonneg hK0 (mul_nonneg hCB0 hK0)) (mul_nonneg hCD0 hK0)
    have hcc : 0 ≤ CW * CF := mul_nonneg (le_of_lt hCW) (le_of_lt hCF)
    have h1 : CW * CF * (α + 1) ≤ CW * CF * (5 / 4) :=
      mul_le_mul_of_nonneg_left hα54 hcc
    rw [hKm, hCBal]
    calc CW * (CF * (α + 1) * (Cs * α + CB * (Cs * α) + CD * (Cs * α)))
        = (CW * CF * (α + 1)) * (Cs * α + CB * (Cs * α) + CD * (Cs * α)) := by ring
      _ ≤ (CW * CF * (5 / 4)) * (Cs * α + CB * (Cs * α) + CD * (Cs * α)) :=
          mul_le_mul_of_nonneg_right h1 hx
      _ = CW * CF * (5 / 4) * (1 + CB + CD) * (Cs * α) := by ring
  have hbound : ∀ f : ℝ → ℝ → ℝ, Work.Spaces.WlInf α 6 f ≤ CW * Km → Work.Spaces.WlInf α 6 f ≤ Cfin * Cs * α := by
    intro f hf
    have h2 : CBal * (Cs * α) ≤ Cfin * (Cs * α) := mul_le_mul_of_nonneg_right hCBle hK0
    have h3 : Cfin * (Cs * α) = Cfin * Cs * α := by ring
    linarith [hKm_le]
  refine
    { toStarPkgo2 := StarPkgo2_raise_Cs hα0
        (mul_le_mul_of_nonneg_right hC1le (le_of_lt hCs))
        (hStar α Cs Φs hα hα4 hCs hcore)
      RW6 := ⟨hH.1, hbound _ hH.2⟩
      VW6 := ⟨hV.1, hbound _ hV.2⟩
      VzW6 := ⟨hVz.1, hbound _ hVz.2⟩
      UsW6 := ⟨hU.1, hbound _ hU.2⟩
      UszW6 := ⟨hUz.1, hbound _ hUz.2⟩ }

end Work.FTS.StrongPersist
end
end
