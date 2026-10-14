import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.H2W.AngBW.Step3.HkMemGradU
import Submission.Work.FTS.EllipticEst.Honest.HonSliceSigmaLower
import Submission.Work.FTS.EllipticEst.Honest.I4UpperHonest
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.remov.SrdFork.EllWeakPos_DzIter_one_shift_fork
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.integral_sin_two_rpow_neg
import Submission.Work.FTS.LocDataExt.LocG5
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6.HkN_sepF_le
import Submission.Work.FTS.StrongPersist.N6.Slots
import Submission.Work.FTS.StrongPersist.QangSq6Full
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H2.WPQ.Dth_DzIter_comm_smoothQuad
import Submission.Work.H2.WPQ.hardy_slice_Aang
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.H2W.momentChainAe
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.WProductRule
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.aesm_thEta_zSchur_pth_sq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open scoped Real Topology
open MeasureTheory Set Filter

-- the hypotheses `0 < δ` and `0 < z` of the statement are not needed for measurability
set_option linter.unusedVariables false

/-- **Joint continuity of the Schur integrand.**  For a datum `C^∞` on the open quadrant, the
function

  `(s, t) ↦ sKerd δ (log z - t) · ∂_θG(e^t, s)`

is continuous on `(0, π/2) × ℝ`: the kernel factor is a continuous function of `t`, while the
point `(e^t, s)` lies in the open quadrant, where `∂_θG` is continuous (and the map
`(s,t) ↦ (e^t, s)` is continuous). -/
theorem continuousOn_sKerd_pth_joint {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.SmoothOpen G) (δ z : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - p.2)
        * Work.Spaces.pth G (Real.exp p.2) p.1)
      (Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ (Set.univ : Set ℝ)) := by
  have hpth : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth G (Real.exp p.2) p.1)
      (Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ (Set.univ : Set ℝ)) := by
    have hbase : ContinuousOn (Function.uncurry (Work.Spaces.pth G)) Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.EllipticEst.SmoothOpen.pth hG).continuousOn
    have hφ : Continuous (fun p : ℝ × ℝ => (Real.exp p.2, p.1)) :=
      (Real.continuous_exp.comp continuous_snd).prodMk continuous_fst
    have hmap : MapsTo (fun p : ℝ × ℝ => (Real.exp p.2, p.1))
        (Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ (Set.univ : Set ℝ)) Work.FTS.EllipticEst.Q0 := by
      intro p hp
      rw [Set.mem_prod] at hp
      show (Real.exp p.2, p.1) ∈ Work.FTS.EllipticEst.Q0
      rw [Work.FTS.EllipticEst.mem_Q0]
      exact ⟨Real.exp_pos p.2, hp.1.1, hp.1.2⟩
    exact (hbase.comp hφ.continuousOn hmap).congr (fun p _ => rfl)
  have hK : ContinuousOn
      (fun p : ℝ × ℝ => Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - p.2))
      (Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ (Set.univ : Set ℝ)) :=
    ((Work.FTS.EllSol.EllPkgAux.MollDzAux.continuous_sKerd δ).comp
      (continuous_const.sub continuous_snd)).continuousOn
  exact hK.mul hpth

/-- **A.e. strong measurability of the weighted square of the Schur transform of an angular
derivative.**  For fixed `δ ≥ 0` and `z`, the function

  `s ↦ sin(2s)^{-η} · (zSchur δ (fun w => ∂_θG(w,s)) z)²`

is a.e. strongly measurable on the angular interval `Iθ = [0, π/2]`.

The proof unwinds `zSchur` as the `t`-integral of the jointly continuous density
`(s,t) ↦ sKerd δ (log z - t) · ∂_θG(e^t, s)` (`continuousOn_sKerd_pth_joint`); Fubini's
measurability theorem `MeasureTheory.AEStronglyMeasurable.integral_prod_right'` then gives the
a.e. strong measurability of the marginal in `s`, and `sin(2s)^{-η}` is everywhere continuous. -/
theorem aesm_thEta_zSchur_pth_sq (G : ℝ → ℝ → ℝ)
    (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G) (δ : ℝ) (hδ : 0 < δ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => Work.FTS.EllipticEst.thEta s
        * (Work.FTS.EllSol.EllPkgAux.MollDom.zSchur δ (fun w => Work.Spaces.pth G w s) z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hG : Work.FTS.EllipticEst.SmoothOpen G := hT.1
  -- the (measurable) set on which the joint integrand is continuous
  have hmeasU : MeasurableSet (Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ (Set.univ : Set ℝ)) :=
    measurableSet_Ioo.prod MeasurableSet.univ
  have hjoint : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - p.2)
        * Work.Spaces.pth G (Real.exp p.2) p.1)
      ((MeasureTheory.volume.prod MeasureTheory.volume).restrict
        (Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ (Set.univ : Set ℝ))) :=
    (continuousOn_sKerd_pth_joint hG δ z).aestronglyMeasurable hmeasU
  -- rewrite the restricted product measure as the product of the restricted measure
  rw [← MeasureTheory.Measure.restrict_prod_eq_prod_univ] at hjoint
  -- Fubini: the marginal in `s` is a.e. strongly measurable
  have hzschur : MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => zSchur δ (fun w => Work.Spaces.pth G w s) z)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    simpa only [zSchur] using hjoint.integral_prod_right'
  have hsq : MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => (zSchur δ (fun w => Work.Spaces.pth G w s) z) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hzschur.pow 2
  have hfull : MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => Work.FTS.EllipticEst.thEta s
        * (zSchur δ (fun w => Work.Spaces.pth G w s) z) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (measurable_thEta.aestronglyMeasurable (μ :=
      MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))).mul hsq
  -- transfer from the open interval to `Iθ = [0, π/2]` (the two endpoints are null)
  have hIθ : (MeasureTheory.volume.restrict Work.Spaces.Iθ : MeasureTheory.Measure ℝ)
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl]
    exact (MeasureTheory.restrict_Ioo_eq_restrict_Icc (μ := MeasureTheory.volume)
      (a := (0 : ℝ)) (b := Real.pi / 2)).symm
  rw [hIθ]
  exact hfull

end Work.FTS.EllSol.EllPkgAux.MollDom
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeS1.aeSliceConds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeS1

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Slice tools for the level-`0` a.e. class -/

/-- Almost every point of `Iθ = [0,π/2]` lies in the open interval `(0,π/2)`. -/
theorem ae_mem_Ioo_Iθ_fts :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have h : (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) : Measure ℝ)
      = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  rw [← h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- The unweighted angular square of a level-`0` honest function is integrable on `Iθ`: divide
the radial weight `(w z)²` out of the `w²`-weighted slice integrability supplied by `HkMem`. -/
theorem slice_sq_of_HkMem_fts {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 0 f) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2) Work.Spaces.Iθ :=
  Work.FTS.EllipticEst.AngAWeak.integrableOn_slice_sgU hmem hz

/-- **`AM–GM` for slice products**: the product of two functions whose angular squares are
integrable is integrable, provided it is a.e. strongly measurable on `Iθ`. -/
theorem slice_mul_of_sq_fts {f g : ℝ → ℝ}
    (hf : MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2) Work.Spaces.Iθ)
    (hg : MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2) Work.Spaces.Iθ)
    (hm : MeasureTheory.AEStronglyMeasurable (fun θ => f θ * g θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (fun θ => f θ * g θ) Work.Spaces.Iθ := by
  refine MeasureTheory.Integrable.mono' ((hf.add hg).const_mul (1 / 2)) hm ?_
  filter_upwards with θ
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|f θ| - |g θ|), sq_abs (f θ), sq_abs (g θ)]

/-- A function continuous on the **open** quadrant has an a.e. strongly measurable angular slice
at every `z > 0` (the two endpoints of `Iθ` are a null set). -/
theorem aesm_slice_of_cont_fts {f : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hf : ContinuousOn (Function.uncurry f) Work.FTS.EllipticEst.AngAWeak.Qd) :
    MeasureTheory.AEStronglyMeasurable (fun θ => f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  Work.FTS.EllipticEst.AngAWeak.aestronglyMeasurable_of_continuousOn_Ioo <|
    hf.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hθ => Work.FTS.EllipticEst.AngAWeak.mem_Qd.mpr ⟨hz, hθ.1, hθ.2⟩)

/-- **The six a.e. slice-integrability conditions of the truncated level-0 energy identity** for a
datum of the almost-everywhere class `H2W.Ae.AeData`: for almost every `z > 0`, the angular fibres
`θ ↦ bslOp α u z θ · u z θ`, `θ ↦ Lzero u z θ · u z θ`, `θ ↦ ∂_z²u z θ · u z θ`,
`θ ↦ ∂_zu z θ · u z θ`, `θ ↦ (z ∂_zu z θ)²` and `θ ↦ u z θ²` are integrable on `Iθ = [0,π/2]`.
This is the hypothesis `hslice` consumed by `H2W.AeW.aeTruncWHon` (the truncated energy identity)
and by `AngAWeak.CutEnergy.aeCutEnergyIneq` (the truncated energy inequality). -/
theorem aeSliceConds (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hC : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => u z θ) (Set.Icc 0 (Real.pi / 2))) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.bslOp α u z θ * u z θ)
            Work.Spaces.Iθ
      ∧ MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.Lzero u z θ * u z θ)
            Work.Spaces.Iθ
      ∧ MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pzIter 2 u z θ * u z θ)
            Work.Spaces.Iθ
      ∧ MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pz u z θ * u z θ)
            Work.Spaces.Iθ
      ∧ MeasureTheory.IntegrableOn (fun θ => (z * Work.Spaces.pz u z θ) ^ 2)
            Work.Spaces.Iθ
      ∧ MeasureTheory.IntegrableOn (fun θ => (u z θ) ^ 2) Work.Spaces.Iθ := by
  -- in fact all six conditions hold for *every* `z > 0` (`hC` is not needed).
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
  -- joint continuity of the angular slices on the open quadrant
  have hu_cont : ContinuousOn (Function.uncurry u) Work.FTS.EllipticEst.AngAWeak.Qd :=
    (h.smooth 0).continuousOn_zero
  have hpz_cont : ContinuousOn (Function.uncurry (Work.Spaces.pz u))
      Work.FTS.EllipticEst.AngAWeak.Qd :=
    (Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ
      (U := Work.FTS.EllipticEst.AngAWeak.Qd)
      Work.FTS.EllipticEst.AngAWeak.isOpen_Qd (n := 0)
      (by simpa only [Work.FTS.EllipticEst.AngAWeak.Qd] using h.smooth 1)).continuousOn_zero
  have hpz2_cont : ContinuousOn (Function.uncurry (Work.Spaces.pzIter 2 u))
      Work.FTS.EllipticEst.AngAWeak.Qd :=
    Work.FTS.EllipticEst.AngAWeak.continuousOn_uncurry_pzIter_two
      (fun n => by simpa only [Work.FTS.EllipticEst.AngAWeak.Qd] using h.smooth n)
  -- the degrees of freedom `u` and `z ∂_z u` are honest
  have hu_mem : Work.Spaces.HkMem α 0 u := Work.FTS.EllipticEst.Dispatch.hkMem_uM α u G h
  have hg_mem : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) :=
    Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G h
  -- the angular squares
  have hU2 : MeasureTheory.IntegrableOn (fun θ => (u z θ) ^ 2) Work.Spaces.Iθ :=
    slice_sq_of_HkMem_fts hu_mem hz
  have hG2 : MeasureTheory.IntegrableOn (fun θ => (G z θ) ^ 2) Work.Spaces.Iθ :=
    slice_sq_of_HkMem_fts h.memG hz
  have hB2 : MeasureTheory.IntegrableOn (fun θ => (z * Work.Spaces.pz u z θ) ^ 2)
      Work.Spaces.Iθ := by
    simpa only [Work.FTS.EllipticEst.H2W.Ae.grad] using slice_sq_of_HkMem_fts hg_mem hz
  have hR2 : MeasureTheory.IntegrableOn
      (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2) Work.Spaces.Iθ :=
    slice_sq_of_HkMem_fts h.memRad2 hz
  have hP2 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pz u z θ) ^ 2)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.AngAWeak.integrableOn_slice_sq_of_mul_const (c := z ^ 2)
      (pow_ne_zero 2 (ne_of_gt hz))
      (hB2.congr_fun (fun θ _ => by ring) measurableSet_Icc)
  have hP22 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pzIter 2 u z θ) ^ 2)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.AngAWeak.integrableOn_slice_sq_of_mul_const (c := (z ^ 2) ^ 2)
      (pow_ne_zero 2 (pow_ne_zero 2 (ne_of_gt hz)))
      (hR2.congr_fun (fun θ _ => by ring) measurableSet_Icc)
  -- the products of two square-integrable slices
  have hGu : MeasureTheory.IntegrableOn (fun θ => G z θ * u z θ) Work.Spaces.Iθ :=
    slice_mul_of_sq_fts hG2 hU2
      ((Work.FTS.EllipticEst.AngAWeak.aesm_slice_G h hz).mul (aesm_slice_of_cont_fts hz hu_cont))
  have hPu : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pz u z θ * u z θ)
      Work.Spaces.Iθ :=
    slice_mul_of_sq_fts hP2 hU2
      ((aesm_slice_of_cont_fts hz hpz_cont).mul (aesm_slice_of_cont_fts hz hu_cont))
  have hP2u : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pzIter 2 u z θ * u z θ)
      Work.Spaces.Iθ :=
    slice_mul_of_sq_fts hP22 hU2
      ((aesm_slice_of_cont_fts hz hpz2_cont).mul (aesm_slice_of_cont_fts hz hu_cont))
  -- `Lzero u · u` through the equation `Lzero u = G + α²z²∂_zzu + α(5+α)z∂_zu` on the quadrant
  have hLuu : MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.Lzero u z θ * u z θ)
      Work.Spaces.Iθ := by
    have hsum : MeasureTheory.IntegrableOn (fun θ => G z θ * u z θ
        + ((α ^ 2 * z ^ 2) * (Work.Spaces.pzIter 2 u z θ * u z θ)
          + (α * (5 + α) * z) * (Work.Spaces.pz u z θ * u z θ))) Work.Spaces.Iθ :=
      hGu.add ((hP2u.const_mul _).add (hPu.const_mul _))
    refine hsum.congr ?_
    filter_upwards [ae_mem_Ioo_Iθ_fts] with θ hθ
    have hbsl : Work.Elliptic.bslOp α u z θ = G z θ := h.eq z hz θ hθ.1 hθ.2
    have hkey : Work.Elliptic.Lzero u z θ = G z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
        + (α * (5 + α) * z) * Work.Spaces.pz u z θ := by
      rw [← hbsl, Work.Elliptic.bslOp_apply]; ring
    rw [hkey]; ring
  -- `bslOp α u · u = G · u` on *all* of `Iθ` (both products vanish at the two endpoints)
  have hBuu : MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.bslOp α u z θ * u z θ)
      Work.Spaces.Iθ := by
    refine hGu.congr_fun (fun θ hθ => ?_) measurableSet_Icc
    show G z θ * u z θ = Work.Elliptic.bslOp α u z θ * u z θ
    by_cases h0 : θ = 0
    · rw [h0, Work.FTS.EllipticEst.H2W.Ae.AeData.dirZero h z]; ring
    · by_cases hpi : θ = Real.pi / 2
      · rw [hpi, Work.FTS.EllipticEst.H2W.Ae.AeData.dirPi h z]; ring
      · rw [h.eq z hz θ (lt_of_le_of_ne hθ.1 (Ne.symm h0)) (lt_of_le_of_ne hθ.2 hpi)]
  exact ⟨hBuu, hLuu, hP2u, hPu, hB2, hU2⟩

end

end Work.FTS.EllipticEst.AeS1
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeS1.unwAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeS1

set_option autoImplicit false

local notation "sEta" => Work.FTS.EllipticEst.sEta

/-! ## Small facts about the weights -/

theorem one_le_w_of_pos {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, one_le_div (by positivity : (0 : ℝ) < z ^ 2)]
  exact pow_le_pow_left₀ (le_of_lt hz) (by linarith) 2

theorem w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  positivity

theorem w_zero : Work.Spaces.w 0 = 0 := by
  rw [Work.Spaces.w]; norm_num

theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem one_le_sEta_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ sEta θ := by
  have h0 : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθ
  have hle1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h := Real.rpow_le_rpow_of_exponent_ge h0 hle1
    (show -(Work.Spaces.eta) ≤ (0 : ℝ) by have := Work.Spaces.eta_pos; linarith)
  simpa [Work.FTS.EllipticEst.sEta, Real.rpow_zero] using h

/-- The open interval `(0, π/2)` is conull inside `Iθ`. -/
theorem ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have h : MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
    Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  rw [← h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- The measure of the angular interval is finite. -/
theorem volume_Iθ_ne_top : MeasureTheory.volume Work.Spaces.Iθ ≠ ⊤ := by
  rw [Work.Spaces.Iθ, Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

/-! ## The level-`0` `H`-integrand and the plain weighted square -/

theorem HkIntegrand_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

theorem sq_mul_w_sq_le_HkIntegrand (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (f z θ * Work.Spaces.w z) ^ 2 ≤ Work.Spaces.HkIntegrand α 0 f z θ := by
  have h0 : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθ
  have hs1 : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one (le_of_lt h0) (Real.sin_le_one _)
      (by have := Work.Spaces.eta_pos; linarith)
  have hs0 : 0 < Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos h0 _
  have hw := w_nonneg z
  have hquot : Work.Spaces.w z ≤ Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := by
    rw [le_div_iff₀ hs0]
    calc Work.Spaces.w z * Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
        ≤ Work.Spaces.w z * 1 := mul_le_mul_of_nonneg_left hs1 hw
      _ = Work.Spaces.w z := mul_one _
  rw [HkIntegrand_zero_eq]
  have habs : |f z θ * Work.Spaces.w z|
      ≤ |f z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hw,
      abs_of_nonneg (div_nonneg hw (le_of_lt hs0))]
    exact mul_le_mul_of_nonneg_left hquot (abs_nonneg _)
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (f z θ * Work.Spaces.w z)) habs 2

/-! ## Almost-everywhere strong measurability of the angular slices -/

theorem aesm_slice_of_continuousOn_Ioo {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable g (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have h : MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
    Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  rw [← h]
  exact hg.aestronglyMeasurable measurableSet_Ioo

theorem continuousOn_pz_slice {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ : ℝ => Work.Spaces.pz u z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hU : ContinuousOn (Function.uncurry (Work.Spaces.pz u))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((Work.FTS.EllipticEst.smoothOpen_of_forall hu).pz).continuousOn
  have h1 : ContinuousOn (fun θ : ℝ => Function.uncurry (Work.Spaces.pz u) (z, θ))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hU.comp (by fun_prop) (fun θ hθ => ⟨hz, hθ⟩)
  exact h1

theorem continuousOn_pth_slice {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ : ℝ => Work.Spaces.pth u z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hU : ContinuousOn (Function.uncurry (Work.Spaces.pth u))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((Work.FTS.EllipticEst.smoothOpen_of_forall hu).pth).continuousOn
  have h1 : ContinuousOn (fun θ : ℝ => Function.uncurry (Work.Spaces.pth u) (z, θ))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hU.comp (by fun_prop) (fun θ hθ => ⟨hz, hθ⟩)
  exact h1

theorem aesm_slice_gradW_sq {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ : ℝ => (z * Work.Spaces.pz u z θ * Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have h := aesm_slice_of_continuousOn_Ioo (continuousOn_pz_slice hu hz)
  exact ((h.const_mul z).mul_const (Work.Spaces.w z)).pow 2

theorem aesm_slice_pthW_sq {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ : ℝ => (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have h := aesm_slice_of_continuousOn_Ioo (continuousOn_pth_slice hu hz)
  exact (h.mul_const (Work.Spaces.w z)).pow 2

theorem continuousOn_w_fst :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := rfl
  rw [hfun]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2) (continuousOn_fst.pow 2)
    (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))

theorem continuousOn_pz_uncurry {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  ((Work.FTS.EllipticEst.smoothOpen_of_forall hu).pz).continuousOn

theorem continuousOn_pth_uncurry {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  ((Work.FTS.EllipticEst.smoothOpen_of_forall hu).pth).continuousOn

theorem aesm_prod_gradW_sq {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => (p.1 * Work.Spaces.pz u p.1 p.2 * Work.Spaces.w p.1) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _
    (((continuousOn_fst.mul (continuousOn_pz_uncurry hu)).mul continuousOn_w_fst).pow 2)

theorem aesm_prod_pthW_sq {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.pth u p.1 p.2 * Work.Spaces.w p.1) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _
    (((continuousOn_pth_uncurry hu).mul continuousOn_w_fst).pow 2)

/-! ## The per-fibre integrability of the two weighted squares -/

theorem integrableOn_gradW_sq {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (z * Work.Spaces.pz u z θ * Work.Spaces.w z) ^ 2) Work.Spaces.Iθ := by
  intro z hz
  have hI := (Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G h).1 z hz
  have hbound : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖(z * Work.Spaces.pz u z θ * Work.Spaces.w z) ^ 2‖
        ≤ Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ := by
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · subst hz0
      refine Filter.Eventually.of_forall fun θ => ?_
      simp only [w_zero, HkIntegrand_zero_eq, mul_zero, zero_mul, zero_div, zero_pow,
        ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, norm_zero, le_refl]
    · filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact sq_mul_w_sq_le_HkIntegrand α (Work.FTS.EllipticEst.H2W.Ae.grad u) hθ
  have haesm : AEStronglyMeasurable
      (fun θ : ℝ => (z * Work.Spaces.pz u z θ * Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · subst hz0
      have hzero : (fun θ : ℝ => (0 * Work.Spaces.pz u 0 θ * Work.Spaces.w 0) ^ 2)
          = fun _ : ℝ => (0 : ℝ) := by
        funext θ; rw [w_zero]; ring
      rw [hzero]
      exact aestronglyMeasurable_const
    · exact aesm_slice_gradW_sq h.smooth hzpos
  exact hI.mono' haesm hbound

theorem integrableOn_pthW_sq {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2) Work.Spaces.Iθ := by
  intro z hz
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · subst hz0
    have hzero : (fun θ : ℝ => (Work.Spaces.pth u 0 θ * Work.Spaces.w 0) ^ 2)
        = fun _ : ℝ => (0 : ℝ) := by
      funext θ; rw [w_zero]; ring
    rw [hzero]
    exact integrableOn_zero
  · obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB h.smooth h.memAng2 hzpos
    have hbound : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        ‖(Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2‖ ≤ (C * Work.Spaces.w z) ^ 2 := by
      filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
      have hb : |Work.Spaces.pth u z θ| ≤ C := by
        simpa only [Work.Spaces.pth] using (hC θ hθ).2
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      calc (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2
          = (Work.Spaces.pth u z θ) ^ 2 * (Work.Spaces.w z) ^ 2 := by ring
        _ ≤ C ^ 2 * (Work.Spaces.w z) ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) hb 2
        _ = (C * Work.Spaces.w z) ^ 2 := by ring
    exact (MeasureTheory.integrableOn_const (μ := MeasureTheory.volume)
      (s := Work.Spaces.Iθ) (C := (C * Work.Spaces.w z) ^ 2) volume_Iθ_ne_top).mono'
      (aesm_slice_pthW_sq h.smooth hzpos) hbound

theorem ae_integrableOn_pth_sq {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.pth u z θ) ^ 2) Work.Spaces.Iθ := by
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB h.smooth h.memAng2 hz
  have hbound : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖(Work.Spaces.pth u z θ) ^ 2‖ ≤ C ^ 2 := by
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    have hb : |Work.Spaces.pth u z θ| ≤ C := by
      simpa only [Work.Spaces.pth] using (hC θ hθ).2
    rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  exact (MeasureTheory.integrableOn_const (μ := MeasureTheory.volume)
    (s := Work.Spaces.Iθ) (C := C ^ 2) volume_Iθ_ne_top).mono'
    ((aesm_slice_of_continuousOn_Ioo (continuousOn_pth_slice h.smooth hz)).pow 2) hbound


theorem continuousOn_u_slice {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ : ℝ => u z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hU : ContinuousOn (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_of_forall hu).continuousOn
  have h1 : ContinuousOn (fun θ : ℝ => Function.uncurry u (z, θ))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hU.comp (by fun_prop) (fun θ hθ => ⟨hz, hθ⟩)
  exact h1

theorem ae_integrableOn_u_sq {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ : ℝ => (u z θ) ^ 2) Work.Spaces.Iθ := by
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB h.smooth h.memAng2 hz
  have hbound : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖(u z θ) ^ 2‖ ≤ C ^ 2 := by
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    have hb : |u z θ| ≤ C := (hC θ hθ).1
    rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  exact (MeasureTheory.integrableOn_const (μ := MeasureTheory.volume)
    (s := Work.Spaces.Iθ) (C := C ^ 2) volume_Iθ_ne_top).mono'
    ((aesm_slice_of_continuousOn_Ioo (continuousOn_u_slice h.smooth hz)).pow 2) hbound

/-! ## Finiteness of the `∫⁻`-norm from the weighted `H^0`-honesty -/

theorem lintegral_ne_top_of_HkMem {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.HkMem α 0 f) :
    (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
      * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((f z θ) ^ 2))) ≠ ⊤ := by
  have hkey1 : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((f z θ) ^ 2)))
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((f z θ * Work.Spaces.w z) ^ 2) := by
    refine lintegral_congr fun z => ?_
    rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal ((Work.Spaces.w z) ^ 2))
      (fun θ => ENNReal.ofReal ((f z θ) ^ 2)) ENNReal.ofReal_ne_top]
    refine lintegral_congr fun θ => ?_
    rw [← ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z))]
    congr 1
    ring
  have hkey2 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((f z θ * Work.Spaces.w z) ^ 2))
      ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 f z θ) := by
    refine lintegral_mono fun z => ?_
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    exact ENNReal.ofReal_le_ofReal (sq_mul_w_sq_le_HkIntegrand α f hθ)
  have hkey3 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 f z θ))
      = ∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ) := by
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hf.1 z hz)
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 f z θ)).symm
  have hkey4 : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ))
      = ENNReal.ofReal (∫ z in Work.Spaces.Iz,
          ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf.2
      (Filter.Eventually.of_forall fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 0 f z θ)).symm
  have hle : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((f z θ) ^ 2)))
      ≤ ENNReal.ofReal (∫ z in Work.Spaces.Iz,
          ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ) := by
    rw [hkey1]
    exact hkey2.trans (hkey3.trans hkey4).le
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

end Work.FTS.EllipticEst.AeS1
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.Pieces.TopSlotRhsDom =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.Pieces

open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000




/-! ## Measurability of the top angular slot, and a general integration helper -/







/-- Pointwise bound for the source slot of `B = D_zΨ`, via its second angular derivative. -/
theorem srcB_pointwise (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (B : ℝ → ℝ → ℝ), 0 < α →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pthIter 2 B))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter k B z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
          ≤ C * Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.pthIter 2 B) z θ := by
  obtain ⟨C0, hC0pos, hC0⟩ :=
    Work.FTS.EllipticEst.remov.selfdth.slot_pointwise_HkIntegrand (k - 2) (by omega)
  refine ⟨C0, hC0pos, fun α B hα hsmW z hz => ?_⟩
  have hkB : Work.Spaces.pthIter k B
      = Work.Spaces.pthIter (k - 2) (Work.Spaces.pthIter 2 B) := by
    conv_lhs => rw [show k = (k - 2) + 2 from by omega]
    exact Work.FTS.EllipticEst.remov.pthIter_add_local (k - 2) 2 B
  have h2 := hC0 α (Work.Spaces.pthIter 2 B) (k - 1) (by omega) hα hsmW z hz
  have h1 : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter k B z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
        ≤ (Work.Spaces.w z) ^ 2 *
            ((Work.Spaces.pthIter (k - 2) (Work.Spaces.pthIter 2 B) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (((k - 2 : ℕ)) : ℝ) - Work.Spaces.gam α)) := by
    refine Work.FTS.EllipticEst.remov.selfdth.ae_mem_Ioo_of_Iθ.mono (fun θ hθ => ?_)
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hexp : 2 * (((k - 2 : ℕ)) : ℝ) - Work.Spaces.gam α
        ≤ 2 * (k : ℝ) - Work.Spaces.gam α := by
      have hcast : (((k - 2 : ℕ)) : ℝ) = (k : ℝ) - 2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ k)]; push_cast; ring
      rw [hcast]; linarith
    have hwle : (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)
        ≤ (Real.sin (2 * θ)) ^ (2 * (((k - 2 : ℕ)) : ℝ) - Work.Spaces.gam α) :=
      Real.rpow_le_rpow_of_exponent_ge hs hs1 hexp
    rw [hkB]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwle (sq_nonneg _)) (sq_nonneg _)
  filter_upwards [h1, h2] with θ h1θ h2θ
  exact le_trans h1θ h2θ

/-- Hypothesis (1) of the target, with parameter `D`. -/
def H1 (D : ℝ) (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : Prop :=
  α ^ 2 * Work.Spaces.HkNorm α (k - 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
    ≤ D * Work.Spaces.HkNorm α k F

/-- Hypothesis (2) of the target, with parameter `D`. -/
def H2 (D : ℝ) (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : Prop :=
  α ^ 2 * Work.Spaces.HkNorm α (k - 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
      + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
    ≤ D * Work.Spaces.HkNorm α k F





/- **Domination of the right-hand side of `TopSlotTwoD` by `C·|F|²_{ℋ^k}`.**
Intended namespace: `Work.FTS.EllipticEst.Cores.Pieces`.

Hypotheses (1) and (2) are the two level-`(k-1)` norm bounds of the target, with the *parameter* `D`:

(1) `α²|z²∂_z²Ψ|_{k-1} + |∂_θθΨ|_{k-1} ≤ D|F|_k`,
(2) `α²|z²∂_z²(D_zΨ)|_{k-1} + |∂_θθ(D_zΨ)|_{k-1} ≤ D|F|_k`,

where `|f|_m = Work.Spaces.HkNorm α m f` and `D_z = z∂_z`.

The five groups to bound, with `γ = gam α`, `σ = sin(2θ)`, `sEta θ = σ^{-η}`:

* the top source slot `∫∫ (∂_θ^k(Gsrc α F Ψ))²σ^{2k-γ}w²`, `Gsrc α F Ψ = F + α²z²∂_z²Ψ + α(5+α)D_zΨ`:
  convert the plain slot into `D_θ`-slots of `F`, of `z²∂_z²Ψ` and of `D_zΨ`; the first are slots of
  `HkSq α k F`, the second come from (1) for levels `≤ k-1` and from the PROVED
  `Work.FTS.EllipticEst.remov.A_top_slot_bound` at level `k`, and the third from (2) (the plain
  `∂_θ^k` of `D_zΨ` is `∂_θ^{k-2}` of `∂_θθ(D_zΨ)`, a level `≤ k-1` slot, its weight `σ^{2k-γ}` being
  dominated by `σ^{2(k-2)-γ}`);
* the `u`-family `Σ_{i∈Icc 3 (k+1)} ∫∫(∂_θ^iΨ)²σ^{2i-4-γ}w²`: each is a plain level-`(i-2)` slot of
  `∂_θθΨ`, i.e. a slot of `HkSq α (k-1)(∂_θθΨ) ≤ D²|F|_k²` by (1);
* the `η`-term `∫∫(∂_θθΨ)²sEta w²`: the pure level-`0` slot of `HkSq α (k-1)(∂_θθΨ) ≤ D²|F|_k²`;
* `∫∫(∂_θΨ)²w²` and `∫∫Ψ²w²`: for a.e. `z` the slice `θ ↦ Ψ z θ` is continuous on `[0, π/2]`
  (the proved `Work.FTS.EllipticEst.remov.weakSliceRegular`) and vanishes at both endpoints, so the
  proved `Work.FTS.EllipticEst.Mine.SlicePoincare.SlicePoincare` gives
  `∫(∂_θΨ)² ≤ K∫(∂_θθΨ)²sEta` and `∫Ψ² ≤ K∫(∂_θθΨ)²sEta`; then `∫(∂_θθΨ)² ≤ ∫(∂_θθΨ)²sEta` because
  `sEta ≥ 1`.  (No smoothness beyond continuity at the endpoints is needed.)

The conversion "plain slot ↦ `D_θ`-slots" is the sharp forward expansion
`σ^{2m}(∂_θ^m f)² ≤ C Σ_{q∈Icc 1 m}(D_θ^q f)²`, in which the `q = 0` term is *absent* (the
coefficient of `∂_θ^0` in `D_θ^m` vanishes because `D_θ(const) = 0`).  The existing
`Work.FTS.EllipticEst.Cores.Pieces.pthIter_sq_mul_sin_pow_le` is the weaker version of this with a
`q = 0` term, hence not sufficient; `Work.FTS.EllipticEst.remov.sliceTopCore.sin_pow_le_dth1Iter`
and `Work.FTS.EllipticEst.dthCoef_self`/`DthCoef_sin_pow_bound` are the available ingredients. -/

end Work.FTS.EllipticEst.Cores.Pieces
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.Pieces.ae_hksq_le_of_energy =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.Pieces





end Work.FTS.EllipticEst.Cores.Pieces
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Frontier.aeSigmaSliceLowerFts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Frontier

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# `aeSigmaSliceLowerFts` — the slicewise `σ`-coercivity of `Lzero1` in the `AeData` class

For data in the almost-everywhere class `Work.FTS.EllipticEst.H2W.Ae.AeData`, the `θ`-fibre
`f = θ ↦ u z θ` has, for almost every `z > 0`:

* `f` is `C²` on the open interval `(0, π/2)` (`AeData.smooth`) and `f → 0` at `0⁺`
  (`H2W.AeLeftClean.sliceLeftTendstoClean`) and at `(π/2)⁻` (`H2W.Ae.AeSliceRightTendsto`);
* the `σ`-weighted integrands `f² σ`, `(f')² σ`, `(f'')² σ` are honest on `Iθ`, where
  `σ = sin(2θ)^{-η}` (`H2W.AeProof.AeSigma.aeSliceSigmaInt` together with
  `integrableOn_sq_mul_sEtaR_of_HkMem` applied to `AeData.memAng2`).

Hence `Work.EllipticEst.Core.thetaInterpEndpoints` supplies the one-sided limits of `f'`, and
`Honest.PthCore.contDiffOnOneExtension` produces a `C¹`-extension `g` of `f` to `[0, π/2]`
with `g 0 = g (π/2) = 0` and `g = f`, `g' = f'` on the open interval.  The proved slicewise
coercivity `Honest.HonSliceSigmaLower` applied to `g` gives

  `((1-η)/(1+η)) ∫_θ (g')² σ ≤ ∫_θ (Lzero1 g) g σ + K ∫_θ g² σ`,

and dropping the nonnegative left hand side and transferring the integrals back to `f`
(the two functions agree off the null set `{0, π/2}`) yields the claim.
-/

theorem aeSigmaSliceLowerFts : ∃ K : ℝ, 0 < K ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        -K * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          ≤ ∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.Lzero1 (fun θ => u z θ) θ * u z θ
                * Work.FTS.EllipticEst.sEta θ := by
  have hη0 : 0 ≤ Work.Spaces.eta := by norm_num [Work.Spaces.eta]
  have hη1 : Work.Spaces.eta < 1 := by norm_num [Work.Spaces.eta]
  obtain ⟨K, hKpos, hK⟩ :=
    Work.FTS.EllipticEst.Honest.HonSliceSigmaLower Work.Spaces.eta hη0 hη1
  refine ⟨K, hKpos, ?_⟩
  intro α u G h
  have hl := Work.FTS.EllipticEst.H2W.AeLeftClean.sliceLeftTendstoClean α u G h
  filter_upwards [hl, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hlz hz
  -- ## the regularity and the a.e. endpoint limits of the fibre
  have hcd : ContDiffOn ℝ 2 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip h.smooth hz 2
  have hr : Tendsto (fun θ => u z θ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds 0) :=
    Work.FTS.EllipticEst.H2W.Ae.AeSliceRightTendsto α u G h z hz
  -- ## the `σ`-weighted integrability of the fibre
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    Work.FTS.EllipticEst.H2W.AeProof.AeSigma.aeSliceSigmaInt α u G h z hz
  have hu2 : IntegrableOn (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := h1
  have hdu : IntegrableOn
      (fun θ => (deriv (fun θ' => u z θ') θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    simpa only [Work.Spaces.pth] using h2
  have hddu : IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun θ' => u z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    have h0 := Work.FTS.EllipticEst.H2W.AeProof.AeSigma.integrableOn_sq_mul_sEtaR_of_HkMem
      (g := Work.Spaces.pthIter 2 u) h.memAng2 hz
    refine h0.congr (Filter.Eventually.of_forall (fun θ => ?_))
    show Work.Spaces.pthIter 2 u z θ ^ 2 * Work.FTS.EllipticEst.sEta θ
      = (deriv (fun t => deriv (fun θ' => u z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ
    rw [show Work.Spaces.pthIter 2 u z θ
      = deriv (fun t => deriv (fun θ' => u z θ') t) θ from rfl]
  -- ## the one-sided limits of the derivative, and the `C¹`-extension
  obtain ⟨_, _, L₀, L₁, _, _, _, _, hL0, hL1, _, _⟩ :=
    Work.EllipticEst.Core.thetaInterpEndpoints (fun θ => u z θ) hcd hu2 hdu hddu
  obtain ⟨g, hg1, hg0, hgπ, hgEq⟩ :=
    Work.FTS.EllipticEst.Honest.PthCore.contDiffOnOneExtension
      (hcd.of_le (by norm_num)) hlz hr ⟨L₀, hL0⟩ ⟨L₁, hL1⟩
  -- ## congruence facts between `g` and the fibre
  have hg2 : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)) :=
    hcd.congr (fun θ hθ => (hgEq θ hθ).1)
  have hLzero_eq : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 g θ
        = Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ := by
    intro θ hθ
    have e1 : deriv (fun t => deriv g t) θ
        = deriv (fun t => deriv (fun θ' => u z θ') t) θ := by
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
      exact (hgEq t ht).2
    have e2 : deriv (fun t => Real.tan t * g t) θ
        = deriv (fun t => Real.tan t * u z t) θ := by
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
      show Real.tan t * g t = Real.tan t * u z t
      rw [(hgEq t ht).1]
    simp only [Work.FTS.EllipticEst.Lzero1, e1, e2, (hgEq θ hθ).1]
  have hdderiv_eq : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv (deriv g) θ = deriv (deriv (fun θ' => u z θ')) θ := by
    intro θ hθ
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
    exact (hgEq t ht).2
  -- ## the four integrability hypotheses for `g`
  have hgdu : IntegrableOn
      (fun θ => (deriv g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine (hdu.mono_set Ioo_subset_Icc_self).congr_fun ?_ measurableSet_Ioo
    intro θ hθ
    show (deriv (fun θ' => u z θ') θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      = (deriv g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    simp only [(hgEq θ hθ).2]
  have hgddu : IntegrableOn
      (fun θ => (deriv (deriv g) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine (hddu.mono_set Ioo_subset_Icc_self).congr_fun ?_ measurableSet_Ioo
    intro θ hθ
    show (deriv (fun t => deriv (fun θ' => u z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ
      = (deriv (deriv g) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    rw [hdderiv_eq θ hθ]
  have hgu : IntegrableOn (fun θ => (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine (hu2.mono_set Ioo_subset_Icc_self).congr_fun ?_ measurableSet_Ioo
    intro θ hθ
    show (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      = (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    simp only [(hgEq θ hθ).1]
  have hglz : IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 g θ * g θ * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    refine h5.congr (Work.FTS.EllipticEst.Honest.eventually_ae_Iθ_of_Ioo ?_)
    intro θ hθ
    show Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ * u z θ
        * Work.FTS.EllipticEst.sEta θ
      = Work.FTS.EllipticEst.Lzero1 g θ * g θ * Work.FTS.EllipticEst.sEta θ
    rw [← hLzero_eq θ hθ, ← (hgEq θ hθ).1]
  -- ## the coercivity for the extension
  have hconc := hK g hg2 hg1 hg0 hgπ hgdu hgddu hgu hglz
  have hduN : 0 ≤ ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
      * (∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) := by
    refine mul_nonneg (div_nonneg (by linarith) (by linarith)) ?_
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.H2W.AeProof.AeSigma.sEtaR_nonneg hθ)
  have hmain : -K * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      ≤ ∫ θ in Work.Spaces.Iθ,
          Work.FTS.EllipticEst.Lzero1 g θ * g θ * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
    rw [neg_mul]
    linarith [hconc, hduN]
  have hsEta : ∀ θ : ℝ, (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
      = Work.FTS.EllipticEst.sEta θ := fun _ => rfl
  -- ## transfer back to the fibre
  have hsq : (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      = ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
    refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc
      ((MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp ?_)
    refine Work.FTS.EllipticEst.Honest.eventually_ae_Iθ_of_Ioo ?_
    intro θ hθ
    show (g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
      = (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    rw [(hgEq θ hθ).1, hsEta θ]
  have hlz : (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.Lzero1 g θ * g θ * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      = ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ * u z θ
          * Work.FTS.EllipticEst.sEta θ := by
    refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc
      ((MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp ?_)
    refine Work.FTS.EllipticEst.Honest.eventually_ae_Iθ_of_Ioo ?_
    intro θ hθ
    show Work.FTS.EllipticEst.Lzero1 g θ * g θ * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
      = Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ * u z θ
        * Work.FTS.EllipticEst.sEta θ
    rw [hLzero_eq θ hθ, (hgEq θ hθ).1, hsEta θ]
  rw [hsq, hlz] at hmain
  exact hmain

end Work.FTS.EllipticEst.Frontier
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.AeI1.aeDzTraceHk =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `θ`-trace of `z ∂_z u` vanishes at both endpoints, a.e. in `z`

For a datum `AeData α u G` of the almost-everywhere class of the level-`0` elliptic estimate,
with the two extra `ℋ⁰`-honesties `HkMem α 0 (z ∂_zu)` and `HkMem α 0 (∂_θ(z∂_zu))`, the
angular slice `θ ↦ z ∂_zu(z,θ)` tends to `0` at `0⁺` and at `(π/2)⁻` for almost every `z > 0`.

The route is the one recorded in `H2W/InterpOpenAux/NOTES_trace_DzV_zero_FALSE.md` §3–5, with
`V = u`:

* `sliceBoundaryLimit` applied to the slice `f z := θ ↦ z ∂_zu(z,θ)` (whose derivative is
  `z ∂_θ∂_zu = Dz (∂_θu)` by Clairaut) gives both one-sided limits `c₀(z)`, `c₁(z)` and the
  quadratic bounds `(f z θ - c₀ z)² ≤ 2θ^{1+η}·Φ(z)` resp. `≤ 2(π/2-θ)^{1+η}·Φ(z)`, where `Φ` is
  the `σ`-weighted slice energy of `Dz (∂_θu)`; `HkMem α 0 (∂_θ(z∂_zu))` makes `Φ` honest;
* the `z`-FTC, `u(z+h,θ)-u(z,θ) = ∫_{(z,z+h)}∂_zu(s,θ)ds`, is passed to the limit `θ → 0⁺`
  resp. `θ → (π/2)⁻` by dominated convergence (the domination comes from the FTC in `θ` and
  `∫w²Φ < ∞`); the left/right traces of `u` itself vanish a.e. in `z` / for every `z`
  (`H2W.AeLeftClean.sliceLeftTendstoClean`, `H2W.AeProof.AeSliceRightTendsto`);
* hence `∫_{(z,z+h)}c₀(s)/s ds = 0` for a.e. `(z,h)` (left) and for all `z,h>0` (right), i.e. the
  primitives of `c₀/s` resp. `c₁/s` are (a.e.) locally constant;
* the Lebesgue differentiation theorem (`LocallyIntegrable.ae_hasDerivAt_integral`) then gives
  `c₀ = 0` and `c₁ = 0` almost everywhere.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT.AeI1

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz

/-! ## 1. The `σ`-weighted slice energy of `z ∂_z u` -/

/-- `Φ u z = ∫_θ (∂_θ(z ∂_z u)(z,θ))² σ(θ) dθ`, the `σ`-weighted angular energy of the slice
`θ ↦ z ∂_zu(z,θ)` (`σ θ = sin(2θ)^{-η}`). -/
def sliceEnergy (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Iθ, (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ

theorem sliceEnergy_nonneg (u : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ sliceEnergy u z :=
  setIntegral_nonneg measurableSet_Icc fun θ hθ =>
    mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)

theorem sliceEnergy_eq_Ioo (u : ℝ → ℝ → ℝ) (z : ℝ) :
    sliceEnergy u z = ∫ θ in Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
  MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume)).symm

/-- The `k = 0` weighted integrand is `(f · w · sin(2θ)^{-η/2})² = f² w² σ`. -/
theorem HkIntegrand_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Iθ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  rw [show Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 from by
    simp [Work.Spaces.HkIntegrand]]
  have hs : 0 ≤ Real.sin (2 * θ) := by
    have h1 : 0 ≤ 2 * θ := by have := hθ.1; linarith
    have h2 : 2 * θ ≤ Real.pi := by have := hθ.2; linarith [Real.pi_pos]
    exact Real.sin_nonneg_of_nonneg_of_le_pi h1 h2
  rw [Work.FTS.EllipticEst.sEta]
  rcases eq_or_lt_of_le hs with h0 | hpos
  · rw [← h0, Real.zero_rpow (by norm_num [Work.Spaces.eta] : Work.Spaces.eta / 2 ≠ 0),
      Real.zero_rpow (by norm_num [Work.Spaces.eta] : -(Work.Spaces.eta) ≠ 0)]
    simp
  · have hsq : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
        = Real.sin (2 * θ) ^ Work.Spaces.eta := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hpos)]
      congr 1
      ring
    rw [mul_pow, div_pow, hsq, div_eq_mul_inv, Real.rpow_neg (le_of_lt hpos)]
    ring

theorem w_eq_zero_at_zero : Work.Spaces.w 0 = 0 := by
  rw [Work.Spaces.w]; norm_num

theorem w_pos_of_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]
  exact div_pos (sq_pos_of_pos (by linarith)) (sq_pos_of_pos hz)


/-- Clairaut in the `σ`-weighted square: on the domain, `z ∂_θ∂_zu` and `∂_θ(z∂_zu)` have the
same weighted square. -/
theorem clairaut_sq {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u) {z θ : ℝ}
    (hz : z ∈ Iz) (hθ : θ ∈ Iθ) :
    (z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      = (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  by_cases hsin : Real.sin (2 * θ) = 0
  · rw [Work.FTS.EllipticEst.sEta, hsin,
      Real.zero_rpow (by norm_num [Work.Spaces.eta] : -(Work.Spaces.eta) ≠ 0)]
    ring
  · by_cases hz0 : z = 0
    · subst hz0
      simp [Work.Spaces.Dz]
    · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
      have hne0 : θ ≠ 0 := by intro hh; exact hsin (by subst hh; norm_num)
      have hne1 : θ ≠ Real.pi / 2 := by
        intro hh
        exact hsin (by rw [hh]; rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi])
      have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) :=
        ⟨lt_of_le_of_ne hθ.1 (Ne.symm hne0), lt_of_le_of_ne hθ.2 hne1⟩
      have hcd : ContDiffAt ℝ 2 (Function.uncurry u) (z, θ) :=
        (hS.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hzpos, hθ'.1, hθ'.2⟩))
      have hcl := Work.Spaces.pz_pth_comm (f := u) hcd
      simp only [Work.Spaces.Dz]
      rw [hcl]

/-- Clairaut in the `σ`-weighted square, with the radial weight kept. -/
theorem clairaut_sq_w {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u) {z θ : ℝ}
    (hz : z ∈ Iz) (hθ : θ ∈ Iθ) :
    (z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.sEta θ
      = (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.sEta θ := by
  rw [show (z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.sEta θ
      = ((z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        * (Work.Spaces.w z) ^ 2 from by ring,
    clairaut_sq hS hz hθ]
  ring

/-- The per-slice `σ`-honesty of the slice energy, from `HkMem` of `z ∂_θ∂_zu`. -/
theorem integrableOn_sliceEnergy_energy {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hMix : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ)) :
    ∀ z ∈ Iz, MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Iθ := by
  intro z hz
  set F₁ : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ with hF₁
  have h0 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 0 F₁ z θ) Iθ := hMix.1 z hz
  have hA : (fun θ => Work.Spaces.HkIntegrand α 0 F₁ z θ)
      =ᵐ[volume.restrict Iθ]
      (fun θ => (F₁ z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact HkIntegrand_zero_eq α F₁ hθ
  have h1 := h0.congr hA
  have hB : (fun θ => (F₁ z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      =ᵐ[volume.restrict Iθ]
      (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.sEta θ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    simp only [hF₁]
    exact clairaut_sq_w hS hz hθ
  have h2 := h1.congr hB
  by_cases hz0 : z = 0
  · subst hz0
    refine (MeasureTheory.integrable_zero ℝ ℝ (volume.restrict Iθ)).congr ?_
    filter_upwards with θ
    simp [Work.Spaces.Dz]
  · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
    have hw : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (w_pos_of_pos hzpos))
    refine MeasureTheory.Integrable.congr (h2.const_mul ((Work.Spaces.w z) ^ 2)⁻¹) ?_
    filter_upwards with θ
    rw [show (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.sEta θ
        = (Work.Spaces.w z) ^ 2
          * ((Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        from by ring]
    exact inv_mul_cancel_left₀ hw _

/-- The outer `z`-integrability of `w² · Φ`, straight from `HkMem` of `z ∂_θ∂_zu`. -/
theorem integrableOn_w2_sliceEnergy {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hMix : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ)) :
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * sliceEnergy u z) Iz := by
  set F₁ : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ with hF₁
  have h0 : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Iθ, Work.Spaces.HkIntegrand α 0 F₁ z θ) Iz := hMix.2
  refine MeasureTheory.Integrable.congr h0 ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
  have h1 : (∫ θ in Iθ, Work.Spaces.HkIntegrand α 0 F₁ z θ)
      = ∫ θ in Iθ, (F₁ z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun θ hθ => HkIntegrand_zero_eq α F₁ hθ)
  have h2 : (∫ θ in Iθ, (F₁ z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      = (Work.Spaces.w z) ^ 2 * ∫ θ in Iθ, (F₁ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
    rw [show (∫ θ in Iθ, (F₁ z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        = ∫ θ in Iθ, (Work.Spaces.w z) ^ 2 * ((F₁ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
    rw [MeasureTheory.integral_const_mul]
  have h3 : (∫ θ in Iθ, (F₁ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      = ∫ θ in Iθ, (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun θ hθ => by simp only [hF₁]; exact clairaut_sq hS hz hθ)
  rw [h1, h2, h3]
  rfl

/-- Continuity of the radial weight on `(a,b)` with `0 ≤ a`. -/
theorem continuousOn_w {a b : ℝ} (ha : 0 ≤ a) :
    ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioo a b) := by
  rw [show (fun z : ℝ => Work.Spaces.w z) = fun z => (1 + z) ^ 2 / z ^ 2 from rfl]
  refine ContinuousOn.div ?_ ?_ ?_
  · exact (continuousOn_const.add continuousOn_id).pow 2
  · exact continuousOn_id.pow 2
  · intro z hz
    exact pow_ne_zero 2 (ne_of_gt (lt_of_le_of_lt ha hz.1))

/-- A.e.-measurability of `Φ` on subintervals of `(0,∞)`. -/
theorem aemeasurable_sliceEnergy_Ioo {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hMix : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    AEMeasurable (sliceEnergy u) (volume.restrict (Set.Ioo a b)) := by
  have hsub : Set.Ioo a b ⊆ Iz := fun x hx => le_of_lt (lt_of_le_of_lt ha hx.1)
  have h1 : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * sliceEnergy u z)
      (Set.Ioo a b) := (integrableOn_w2_sliceEnergy hS hMix).mono_set hsub
  have h1m : AEMeasurable (fun z => (Work.Spaces.w z) ^ 2 * sliceEnergy u z)
      (volume.restrict (Set.Ioo a b)) := h1.aemeasurable
  have hwm : AEMeasurable (fun z => ((Work.Spaces.w z) ^ 2)⁻¹)
      (volume.restrict (Set.Ioo a b)) := by
    refine ContinuousOn.aemeasurable ?_ measurableSet_Ioo
    exact ((continuousOn_w ha).pow 2).inv₀
      (fun z hz => pow_ne_zero 2 (ne_of_gt (w_pos_of_pos (lt_of_le_of_lt ha hz.1))))
  refine (hwm.mul h1m).congr ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with z hz
  have hw : (Work.Spaces.w z) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (ne_of_gt (w_pos_of_pos (lt_of_le_of_lt ha hz.1)))
  exact inv_mul_cancel_left₀ hw _


/-- `Φ/s⁴` is locally integrable on `(0,∞)` (dominated by `w²Φ`). -/
theorem integrableOn_sliceEnergy_div_pow_four {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hMix : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ))
    {b : ℝ} (hb : 0 < b) :
    MeasureTheory.IntegrableOn (fun s => sliceEnergy u s / s ^ 4) (Set.Ioo 0 b) := by
  have h1 : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * sliceEnergy u z)
      (Set.Ioo 0 b) :=
    (integrableOn_w2_sliceEnergy hS hMix).mono_set (fun x hx => le_of_lt hx.1)
  have hΦm : AEMeasurable (sliceEnergy u) (volume.restrict (Set.Ioo 0 b)) :=
    aemeasurable_sliceEnergy_Ioo hS hMix le_rfl hb
  have h4inv : AEMeasurable (fun s : ℝ => (s ^ 4)⁻¹) (volume.restrict (Set.Ioo 0 b)) := by
    refine ContinuousOn.aemeasurable ?_ measurableSet_Ioo
    exact (continuousOn_id.pow 4).inv₀ (fun z hz => pow_ne_zero 4 (ne_of_gt hz.1))
  refine MeasureTheory.Integrable.mono' h1.abs ?_ ?_
  · refine ((hΦm.mul h4inv).aestronglyMeasurable).congr ?_
    filter_upwards with s
    simp only [Pi.mul_apply, div_eq_mul_inv]
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with z hz
    have hzpos : 0 < z := hz.1
    have hΦ := sliceEnergy_nonneg u z
    have hw4 : (1:ℝ) / z ^ 4 ≤ (Work.Spaces.w z) ^ 2 := by
      have h1z : (1:ℝ) ≤ (1 + z) ^ 4 := one_le_pow₀ (by linarith)
      have hz4 : (0:ℝ) ≤ z ^ 4 := by positivity
      have hkey : (1:ℝ) * z ^ 4 ≤ (1 + z) ^ 4 * z ^ 4 :=
        mul_le_mul_of_nonneg_right h1z hz4
      rw [Work.Spaces.w]
      simp only [div_pow]
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < z ^ 4)
        (by positivity : (0:ℝ) < (z ^ 2) ^ 2)]
      calc (1:ℝ) * (z ^ 2) ^ 2 = 1 * z ^ 4 := by ring
        _ ≤ (1 + z) ^ 4 * z ^ 4 := hkey
        _ = ((1 + z) ^ 2) ^ 2 * z ^ 4 := by ring
    have hdiff : sliceEnergy u z / z ^ 4 ≤ (Work.Spaces.w z) ^ 2 * sliceEnergy u z := by
      calc sliceEnergy u z / z ^ 4 = (1 / z ^ 4) * sliceEnergy u z := by ring
        _ ≤ (Work.Spaces.w z) ^ 2 * sliceEnergy u z := mul_le_mul_of_nonneg_right hw4 hΦ
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hΦ (by positivity)),
      abs_of_nonneg (mul_nonneg (sq_nonneg _) hΦ)]
    exact hdiff

/-- AM–GM for the square root. -/
theorem sqrt_mul_le_add_div_two {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ (a + b) / 2 := by
  have h1 : Real.sqrt (a * b) ^ 2 = a * b := Real.sq_sqrt (mul_nonneg ha hb)
  have h2 : ((a + b) / 2) ^ 2 = (a + b) ^ 2 / 4 := by ring
  have hs : 0 ≤ Real.sqrt (a * b) := Real.sqrt_nonneg _
  have ht : 0 ≤ (a + b) / 2 := by linarith
  nlinarith [h1, h2, sq_nonneg (a - b), hs, ht]

/-- `√Φ/s` is locally integrable near `0`, by AM–GM applied to `Φ/s⁴` and `s²`. -/
theorem integrableOn_sqrt_sliceEnergy_div {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hMix : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ))
    {b : ℝ} (hb : 0 < b) :
    MeasureTheory.IntegrableOn (fun s => Real.sqrt (sliceEnergy u s) / s) (Set.Ioo 0 b) := by
  have h1 : MeasureTheory.IntegrableOn (fun s => sliceEnergy u s / s ^ 4) (Set.Ioo 0 b) :=
    integrableOn_sliceEnergy_div_pow_four hS hMix hb
  have h2 : MeasureTheory.IntegrableOn (fun s : ℝ => s ^ 2) (Set.Ioo 0 b) :=
    (continuous_id.pow 2).integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self
  have hdom : MeasureTheory.IntegrableOn
      (fun s => (sliceEnergy u s / s ^ 4 + s ^ 2) / 2) (Set.Ioo 0 b) := by
    refine MeasureTheory.Integrable.congr ((h1.add h2).const_mul (1/2)) ?_
    filter_upwards with s
    show (1/2 : ℝ) * (sliceEnergy u s / s ^ 4 + s ^ 2) = (sliceEnergy u s / s ^ 4 + s ^ 2) / 2
    ring
  refine MeasureTheory.Integrable.mono' hdom ?_ ?_
  · have hΦm : AEMeasurable (sliceEnergy u) (volume.restrict (Set.Ioo 0 b)) :=
      aemeasurable_sliceEnergy_Ioo hS hMix le_rfl hb
    have hsqrt : AEMeasurable (fun s => Real.sqrt (sliceEnergy u s))
        (volume.restrict (Set.Ioo 0 b)) :=
      (Real.continuous_sqrt.measurable).comp_aemeasurable hΦm
    have hinv : AEMeasurable (fun s : ℝ => s⁻¹) (volume.restrict (Set.Ioo 0 b)) := by
      refine ContinuousOn.aemeasurable ?_ measurableSet_Ioo
      exact continuousOn_id.inv₀ (fun z hz => ne_of_gt hz.1)
    refine ((hsqrt.mul hinv).aestronglyMeasurable).congr ?_
    filter_upwards with s
    simp only [Pi.mul_apply, div_eq_mul_inv]
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with s hs
    have hspos : 0 < s := hs.1
    have hΦ := sliceEnergy_nonneg u s
    have hkey : Real.sqrt (sliceEnergy u s) / s = Real.sqrt (sliceEnergy u s / s ^ 2) := by
      rw [Real.sqrt_div hΦ, Real.sqrt_sq (le_of_lt hspos)]
    have hsplit : sliceEnergy u s / s ^ 2 = (sliceEnergy u s / s ^ 4) * s ^ 2 := by
      field_simp
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (le_of_lt hspos)),
      hkey, hsplit]
    exact sqrt_mul_le_add_div_two (div_nonneg hΦ (by positivity)) (sq_nonneg s)

/-! ## 2. Two generic real-analysis lemmas -/


/-- **Dominated convergence for the `θ`-slices of `∂_zu`**, in the `z`-integrated form. -/
theorem tendsto_setIntegral_pz {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u)
    {l : Filter ℝ} [l.IsCountablyGenerated] {c g : ℝ → ℝ} {z h : ℝ}
    (hz : 0 < z) (hh : 0 < h)
    (hθl : ∀ᶠ θ in l, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hlim : ∀ s, 0 < s → Filter.Tendsto (fun θ => Work.Spaces.pz u s θ) l (nhds (c s)))
    (hbound : ∀ᶠ θ in l, ∀ s ∈ Set.Ioo z (z + h), ‖Work.Spaces.pz u s θ‖ ≤ g s)
    (hgi : MeasureTheory.IntegrableOn g (Set.Ioo z (z + h))) :
    Filter.Tendsto (fun θ => ∫ s in Set.Ioo z (z + h), Work.Spaces.pz u s θ) l
      (nhds (∫ s in Set.Ioo z (z + h), c s)) := by
  have hmain : Filter.Tendsto
      (fun θ => ∫ s, Work.Spaces.pz u s θ ∂(volume.restrict (Set.Ioo z (z + h)))) l
      (nhds (∫ s, c s ∂(volume.restrict (Set.Ioo z (z + h))))) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence g ?_ ?_ hgi ?_
    · filter_upwards [hθl] with θ hθ
      have hslice : ContDiffOn ℝ Work.Stability.smoothOrder
          (fun s : ℝ => Work.Spaces.pz u s θ) (Set.Ioo z (z + h)) :=
        (Work.FTS.LocData.contDiffOn_slice_z (G := Work.Spaces.pz u) (s := Set.Ioi 0)
          (t := Set.Ioo 0 (Real.pi / 2)) (hS.pz) hθ).mono
            (fun s hs => lt_trans hz hs.1)
      exact (hslice.continuousOn.aemeasurable measurableSet_Ioo).aestronglyMeasurable
    · filter_upwards [hbound] with θ hθ
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with s hs
      exact hθ s hs
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with s hs
      exact hlim s (lt_trans hz hs.1)
  exact hmain

/-! ## 3. The two endpoint traces as `limsup`-defined functions -/

/-- The left trace of the slice `θ ↦ ∂_z u(·,θ)` at `0⁺`, taken along the diagonal sequence
`θ_n = 1/(n+1)`; it is `a.e.`-measurable by construction and agrees with the honest limit
whenever the latter exists (see `dzTrace0_eq_of_tendsto`). -/
def dzTrace0 (u : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => limsup (fun n : ℕ => Work.Spaces.pz u z (1 / ((n : ℝ) + 1))) atTop

/-- The right trace of the slice `θ ↦ ∂_z u(·,θ)` at `(π/2)⁻`. -/
def dzTrace1 (u : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => limsup (fun n : ℕ => Work.Spaces.pz u z (Real.pi / 2 - 1 / ((n : ℝ) + 1))) atTop

/-- The diagonal sequence `θ_n = 1/(n+1)` lies in `(0,π/2)` and tends to `0` within `(0,∞)`. -/
theorem tendsto_theta0 : Tendsto (fun n : ℕ => (1:ℝ) / ((n : ℝ) + 1)) atTop
    (nhdsWithin (0:ℝ) (Set.Ioi 0)) := by
  rw [nhdsWithin, tendsto_inf, tendsto_principal]
  refine ⟨?_, ?_⟩
  · simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  · filter_upwards with n
    exact one_div_pos.mpr (by positivity : (0:ℝ) < (n : ℝ) + 1)

/-- The diagonal sequence `θ_n = π/2 - 1/(n+1)` tends to `π/2` within `(0,π/2)`. -/
theorem tendsto_theta1 : Tendsto (fun n : ℕ => Real.pi / 2 - 1 / ((n : ℝ) + 1)) atTop
    (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) := by
  rw [nhdsWithin, tendsto_inf, tendsto_principal]
  refine ⟨?_, ?_⟩
  · have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hc : Tendsto (fun _ : ℕ => Real.pi / 2) atTop (nhds (Real.pi / 2)) := tendsto_const_nhds
    have h1 : Tendsto (fun n : ℕ => Real.pi / 2 - (1:ℝ) / ((n : ℝ) + 1)) atTop
        (nhds (Real.pi / 2 - 0)) := hc.sub h0
    simpa using h1
  · filter_upwards with n
    have : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact sub_lt_self _ this

theorem theta0_mem {n : ℕ} : (1:ℝ) / ((n : ℝ) + 1) ∈ Set.Ioo 0 (Real.pi / 2) := by
  constructor
  · exact div_pos one_pos (by positivity)
  · have h1 : (1:ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; norm_num
    have h2 : (1:ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
    linarith

theorem theta1_mem {n : ℕ} : Real.pi / 2 - 1 / ((n : ℝ) + 1) ∈ Set.Ioo 0 (Real.pi / 2) := by
  constructor
  · have h : (1:ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; norm_num
    have h2 : (1:ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
    linarith
  · exact sub_lt_self _ (by positivity)

/-- The `z`-slice of `∂_zu` at a fixed interior angle is a.e. strongly measurable. -/
theorem aeStronglyMeasurable_zslice {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    AEStronglyMeasurable (fun z => Work.Spaces.pz u z θ) (volume.restrict (Set.Ioi 0)) := by
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => Work.Spaces.pz u z θ)
      (Set.Ioi 0) :=
    Work.FTS.LocData.contDiffOn_slice_z (G := Work.Spaces.pz u) (s := Set.Ioi 0)
      (t := Set.Ioo 0 (Real.pi / 2)) (hS.pz) hθ
  exact (hslice.continuousOn.aemeasurable measurableSet_Ioi).aestronglyMeasurable

theorem aemeasurable_dzTrace0 {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u) :
    AEMeasurable (dzTrace0 u) (volume.restrict (Set.Ioi 0)) := by
  refine AEMeasurable.limsup (fun n => ?_)
  exact (aeStronglyMeasurable_zslice hS theta0_mem).aemeasurable

theorem aemeasurable_dzTrace1 {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u) :
    AEMeasurable (dzTrace1 u) (volume.restrict (Set.Ioi 0)) := by
  refine AEMeasurable.limsup (fun n => ?_)
  exact (aeStronglyMeasurable_zslice hS theta1_mem).aemeasurable

theorem dzTrace0_eq_of_tendsto {u : ℝ → ℝ → ℝ} {c : ℝ → ℝ} {z : ℝ}
    (h : Tendsto (fun θ => Work.Spaces.pz u z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (c z))) :
    dzTrace0 u z = c z := by
  exact (h.comp tendsto_theta0).limsup_eq

theorem dzTrace1_eq_of_tendsto {u : ℝ → ℝ → ℝ} {c : ℝ → ℝ} {z : ℝ}
    (h : Tendsto (fun θ => Work.Spaces.pz u z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (c z))) :
    dzTrace1 u z = c z := by
  exact (h.comp tendsto_theta1).limsup_eq

/-- **Localized Lebesgue-differentiation lemma.**  If `∫_z^{z+t} F = 0` for a.e. `z ∈ A` and a.e.
`t > 0`, then `F = 0` a.e. on `A` (for `F` locally integrable). -/
theorem aeZeroOn_of_intervalIntegralZero {F : ℝ → ℝ} {A : Set ℝ}
    (hF : MeasureTheory.LocallyIntegrable F volume)
    (hint : ∀ᵐ z ∂(volume.restrict A),
      ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)), (∫ x in z..(z + t), F x) = 0) :
    ∀ᵐ z ∂(volume.restrict A), F z = 0 := by
  have hLDT : ∀ᵐ z ∂volume, ∀ c, HasDerivAt (fun x => ∫ t in c..x, F t) (F z) z :=
    LocallyIntegrable.ae_hasDerivAt_integral hF
  filter_upwards [MeasureTheory.ae_restrict_of_ae hLDT, hint] with z hder hh
  set K' : ℝ → ℝ := fun x => ∫ t in z..x, F t with hK'
  have hderz : HasDerivAt K' (F z) z := by rw [hK']; exact hder z
  have hnull : ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)), t⁻¹ * (K' (z + t) - K' z) = 0 := by
    filter_upwards [hh] with t ht
    have hval : K' (z + t) - K' z = ∫ x in z..(z + t), F x := by
      rw [hK']
      simp [intervalIntegral.integral_same]
    rw [hval, ht, mul_zero]
  have hsetnull : volume {t : ℝ | 0 < t ∧ t⁻¹ * (K' (z + t) - K' z) ≠ 0} = 0 := by
    have h2 := MeasureTheory.ae_iff.mp hnull
    have h3 : (volume.restrict (Set.Ioi 0))
        {t : ℝ | 0 < t ∧ t⁻¹ * (K' (z + t) - K' z) ≠ 0} = 0 :=
      MeasureTheory.measure_mono_null (fun t ht => ht.2) h2
    rwa [MeasureTheory.Measure.restrict_eq_self volume (fun t ht => ht.1)] at h3
  have hseq : ∀ n : ℕ, ∃ t : ℝ, t ∈ Set.Ioo 0 (1 / ((n : ℝ) + 1)) ∧
      t⁻¹ * (K' (z + t) - K' z) = 0 := by
    intro n
    by_contra hcon
    push_neg at hcon
    have hsub : Set.Ioo 0 (1 / ((n : ℝ) + 1)) ⊆
        {t : ℝ | 0 < t ∧ t⁻¹ * (K' (z + t) - K' z) ≠ 0} :=
      fun t ht => ⟨ht.1, hcon t ht⟩
    have hle : volume (Set.Ioo 0 (1 / ((n : ℝ) + 1))) ≤
        volume {t : ℝ | 0 < t ∧ t⁻¹ * (K' (z + t) - K' z) ≠ 0} :=
      MeasureTheory.measure_mono hsub
    rw [hsetnull, le_zero_iff, Real.volume_Ioo] at hle
    have hle0 : (1 / ((n : ℝ) + 1)) ≤ 0 := by simpa using ENNReal.ofReal_eq_zero.mp hle
    have hpos : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  choose t ht using hseq
  have htend0 : Tendsto t atTop (nhds (0:ℝ)) := by
    have hdiv : Tendsto (fun n : ℕ => (1:ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiv
      (fun n => le_of_lt (ht n).1.1) (fun n => le_of_lt (ht n).1.2)
  have htend : Tendsto t atTop (nhdsWithin (0:ℝ) (Set.Ioi 0)) := by
    rw [nhdsWithin, tendsto_inf, tendsto_principal]
    exact ⟨htend0, Eventually.of_forall fun n => (ht n).1.1⟩
  have hcomp := hderz.tendsto_slope_zero_right.comp htend
  have hzero : Tendsto (fun n => (t n)⁻¹ * (K' (z + t n) - K' z)) atTop (nhds (0:ℝ)) := by
    have : (fun n => (t n)⁻¹ * (K' (z + t n) - K' z)) = fun _ => (0:ℝ) :=
      funext fun n => (ht n).2
    rw [this]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hcomp hzero

/-- **Cut-off local integrability.**  A function which vanishes below `ε > 0` and is integrable on
every compact subinterval of `(ε,∞)` is locally integrable. -/
theorem locallyIntegrable_indicator_Ioi {F : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ a b : ℝ, ε ≤ a → a < b → MeasureTheory.IntegrableOn F (Set.Ioo a b)) :
    MeasureTheory.LocallyIntegrable (Set.indicator (Set.Ioi ε) F) volume := by
  have hInt : ∀ a b : ℝ, a < b → MeasureTheory.IntegrableOn
      (Set.indicator (Set.Ioi ε) F) (Set.Ioo a b) := by
    intro a b hab
    rcases le_or_gt b ε with hb | hb
    · refine MeasureTheory.IntegrableOn.congr_fun
        (MeasureTheory.integrable_zero ℝ ℝ _) ?_ measurableSet_Ioo
      intro s hs
      have hmem : s ∉ Set.Ioi ε := not_lt.mpr (le_trans (le_of_lt hs.2) hb)
      exact (Set.indicator_of_notMem hmem F).symm
    · have hbase : MeasureTheory.IntegrableOn F (Set.Ioo (max a ε) b) := by
        rcases lt_or_ge (max a ε) b with hlt | hge
        · exact h (max a ε) b (le_max_right _ _) hlt
        · rw [show Set.Ioo (max a ε) b = ∅ from
            Set.eq_empty_iff_forall_notMem.mpr
              (fun s hs => absurd hs.1 (not_lt.mpr (le_trans (le_of_lt hs.2) hge)))]
          exact MeasureTheory.integrableOn_empty
      have h2 : MeasureTheory.IntegrableOn (Set.indicator (Set.Ioi ε) F)
          (Set.Ioo a b ∩ Set.Ioi ε) :=
        MeasureTheory.IntegrableOn.congr_fun
          (hbase.mono_set (fun s hs => ⟨max_lt hs.1.1 hs.2, hs.1.2⟩))
          (fun s hs => (Set.indicator_of_mem hs.2 F).symm)
          (measurableSet_Ioo.inter measurableSet_Ioi)
      have h3 : MeasureTheory.IntegrableOn (Set.indicator (Set.Ioi ε) F)
          (Set.Ioo a b \ Set.Ioi ε) :=
        MeasureTheory.IntegrableOn.congr_fun
          (MeasureTheory.integrable_zero ℝ ℝ _)
          (fun s hs => (Set.indicator_of_notMem hs.2 F).symm)
          (measurableSet_Ioo.diff measurableSet_Ioi)
      refine (h2.union h3).mono_set ?_
      intro s hs
      by_cases hmem : ε < s
      · exact Set.mem_union_left _ ⟨hs, hmem⟩
      · exact Set.mem_union_right _ ⟨hs, hmem⟩
  intro x
  rcases le_or_gt x (ε / 2) with hx | hx
  · exact ⟨Set.Ioo (x - 1) (ε / 2 + 1),
      IsOpen.mem_nhds isOpen_Ioo ⟨by linarith, by linarith⟩, hInt _ _ (by linarith)⟩
  · exact ⟨Set.Ioo (ε / 2) (x + 1),
      IsOpen.mem_nhds isOpen_Ioo ⟨by linarith, by linarith⟩, hInt _ _ (by linarith)⟩

theorem aeDzTraceHk (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ))
    (hMix : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ)) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => z * Work.Spaces.pz u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds 0) ∧
      Filter.Tendsto (fun θ => z * Work.Spaces.pz u z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  classical
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hpi4 : (0:ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hpi4mem : (Real.pi / 4) ∈ Set.Ioo (0:ℝ) (Real.pi / 2) :=
    ⟨hpi4, by linarith [Real.pi_pos]⟩
  have heta1 : (0:ℝ) < 1 + Work.Spaces.eta := by
    have := Work.Spaces.eta_nonneg; linarith
  -- (A) the derivative of the slice
  have hslice_deriv : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) →
      deriv (fun θ' => Work.Spaces.Dz u z θ') θ = Work.Spaces.Dz (Work.Spaces.pth u) z θ := by
    intro z θ hz hθ
    have hcd : ContDiffAt ℝ 2 (Function.uncurry u) (z, θ) :=
      (hS.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩))
    have hcl := Work.Spaces.pz_pth_comm (f := u) hcd
    have h1 : deriv (fun θ' => Work.Spaces.Dz u z θ') θ
        = z * Work.Spaces.pth (Work.Spaces.pz u) z θ := by
      simp only [Work.Spaces.Dz, Work.Spaces.pth, deriv_const_mul_field]
    rw [h1]
    show z * Work.Spaces.pth (Work.Spaces.pz u) z θ
      = z * Work.Spaces.pz (Work.Spaces.pth u) z θ
    exact congrArg (fun t => z * t) hcl.symm
  have hthEta : ∀ θ : ℝ, Work.FTS.EllipticEst.thEta θ = Work.FTS.EllipticEst.sEta θ :=
    fun θ => rfl
  -- (B) integrability of the weighted derivative
  have hslice_int : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ' => Work.Spaces.Dz u z θ') θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) (Set.Ioo (0:ℝ) (Real.pi / 2)) := by
    intro z hz
    have hbase : MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Iθ :=
      integrableOn_sliceEnergy_energy hS hMix z (le_of_lt hz)
    refine ((hbase.mono_set Set.Ioo_subset_Icc_self)).congr ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
    simpa only [hslice_deriv z θ hz hθ, hthEta θ]
  -- (C) the two endpoint parameters
  obtain ⟨K, hKpos, hSBL⟩ := Work.EllipticEst.Core.sliceBoundaryLimit
  have hsliceC1 : ∀ z : ℝ, 0 < z → ContDiffOn ℝ 1
      (fun θ => Work.Spaces.Dz u z θ) (Set.Ioo (0:ℝ) (Real.pi / 2)) := by
    intro z hz
    refine (hS.Dz.curry_θ hz).of_le ?_
    rw [Work.Stability.smoothOrder]
    exact WithTop.coe_le_coe.mpr le_top
  have hleft : ∀ z : ℝ, ∃ c : ℝ, 0 < z →
      Filter.Tendsto (fun θ => Work.Spaces.Dz u z θ) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds c) ∧
      (∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), (Work.Spaces.Dz u z θ - c) ^ 2
        ≤ K * θ ^ (1 + Work.Spaces.eta) * sliceEnergy u z) := by
    intro z
    by_cases hz : 0 < z
    · obtain ⟨c, hlim, hbd⟩ := (hSBL (fun θ => Work.Spaces.Dz u z θ) (hsliceC1 z hz)
        (hslice_int z hz)).1
      refine ⟨c, fun _ => ⟨hlim, fun θ hθ => ?_⟩⟩
      have hA : MeasureTheory.IntegrableOn
          (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) (Set.Ioo (0:ℝ) (Real.pi / 2)) :=
        (integrableOn_sliceEnergy_energy hS hMix z (le_of_lt hz)).mono_set
          Set.Ioo_subset_Icc_self
      have hEq1 : (∫ t in Set.Ioo 0 θ, (deriv (fun θ' => Work.Spaces.Dz u z θ') t) ^ 2
            * Work.FTS.EllipticEst.thEta t)
          = ∫ t in Set.Ioo 0 θ, (Work.Spaces.Dz (Work.Spaces.pth u) z t) ^ 2
            * Work.FTS.EllipticEst.sEta t :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
          (fun t ht => by
            simpa only [hslice_deriv z t hz ⟨ht.1, lt_trans ht.2 hθ.2⟩, hthEta t])
      have hEq2 : (∫ t in Set.Ioo 0 (Real.pi / 2), (Work.Spaces.Dz (Work.Spaces.pth u) z t) ^ 2
            * Work.FTS.EllipticEst.sEta t) = sliceEnergy u z :=
        (sliceEnergy_eq_Ioo u z).symm
      have hmono : (∫ t in Set.Ioo 0 θ, (deriv (fun θ' => Work.Spaces.Dz u z θ') t) ^ 2
          * Work.FTS.EllipticEst.thEta t) ≤ sliceEnergy u z := by
        rw [hEq1, ← hEq2]
        exact MeasureTheory.setIntegral_mono_set hA
          (by
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
            exact mul_nonneg (sq_nonneg _)
              (Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt ht.1, le_of_lt ht.2⟩))
          (by
            filter_upwards with t ht
            exact ⟨ht.1, lt_trans ht.2 hθ.2⟩)
      exact le_trans (hbd θ hθ)
        (mul_le_mul_of_nonneg_left hmono (mul_nonneg hKpos.le (Real.rpow_nonneg hθ.1.le _)))
    · exact ⟨0, fun hz' => absurd hz' hz⟩
  have hright : ∀ z : ℝ, ∃ c : ℝ, 0 < z →
      Filter.Tendsto (fun θ => Work.Spaces.Dz u z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c) ∧
      (∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), (Work.Spaces.Dz u z θ - c) ^ 2
        ≤ K * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) * sliceEnergy u z) := by
    intro z
    by_cases hz : 0 < z
    · obtain ⟨c, hlim, hbd⟩ := (hSBL (fun θ => Work.Spaces.Dz u z θ) (hsliceC1 z hz)
        (hslice_int z hz)).2
      refine ⟨c, fun _ => ⟨hlim, fun θ hθ => ?_⟩⟩
      have hA : MeasureTheory.IntegrableOn
          (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) (Set.Ioo (0:ℝ) (Real.pi / 2)) :=
        (integrableOn_sliceEnergy_energy hS hMix z (le_of_lt hz)).mono_set
          Set.Ioo_subset_Icc_self
      have hEq1 : (∫ t in Set.Ioo θ (Real.pi / 2),
            (deriv (fun θ' => Work.Spaces.Dz u z θ') t) ^ 2 * Work.FTS.EllipticEst.thEta t)
          = ∫ t in Set.Ioo θ (Real.pi / 2), (Work.Spaces.Dz (Work.Spaces.pth u) z t) ^ 2
            * Work.FTS.EllipticEst.sEta t :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
          (fun t ht => by
            simpa only [hslice_deriv z t hz ⟨lt_trans hθ.1 ht.1, ht.2⟩, hthEta t])
      have hEq2 : (∫ t in Set.Ioo 0 (Real.pi / 2), (Work.Spaces.Dz (Work.Spaces.pth u) z t) ^ 2
            * Work.FTS.EllipticEst.sEta t) = sliceEnergy u z :=
        (sliceEnergy_eq_Ioo u z).symm
      have hmono : (∫ t in Set.Ioo θ (Real.pi / 2),
          (deriv (fun θ' => Work.Spaces.Dz u z θ') t) ^ 2 * Work.FTS.EllipticEst.thEta t)
          ≤ sliceEnergy u z := by
        rw [hEq1, ← hEq2]
        exact MeasureTheory.setIntegral_mono_set hA
          (by
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
            exact mul_nonneg (sq_nonneg _)
              (Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt ht.1, le_of_lt ht.2⟩))
          (by
            filter_upwards with t ht
            exact ⟨lt_trans hθ.1 ht.1, ht.2⟩)
      exact le_trans (hbd θ hθ)
        (mul_le_mul_of_nonneg_left hmono
          (mul_nonneg hKpos.le (Real.rpow_nonneg (by linarith [hθ.2]) _)))
    · exact ⟨0, fun hz' => absurd hz' hz⟩
  choose c0 hc0 using hleft
  choose c1 hc1 using hright
  -- (D) the traces
  have hlim0 : ∀ s : ℝ, 0 < s → Filter.Tendsto (fun θ => Work.Spaces.pz u s θ)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (c0 s / s)) := by
    intro s hs
    have h1 : Filter.Tendsto (fun θ => s * Work.Spaces.pz u s θ)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (c0 s)) := by
      simpa only [Work.Spaces.Dz] using (hc0 s hs).1
    have h3 : (fun θ => s * Work.Spaces.pz u s θ / s) = fun θ => Work.Spaces.pz u s θ := by
      funext θ
      exact mul_div_cancel_left₀ _ (ne_of_gt hs)
    rw [← h3]
    exact h1.div_const s
  have hlim1 : ∀ s : ℝ, 0 < s → Filter.Tendsto (fun θ => Work.Spaces.pz u s θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (c1 s / s)) := by
    intro s hs
    have h1 : Filter.Tendsto (fun θ => s * Work.Spaces.pz u s θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (c1 s)) := by
      simpa only [Work.Spaces.Dz] using (hc1 s hs).1
    have h3 : (fun θ => s * Work.Spaces.pz u s θ / s) = fun θ => Work.Spaces.pz u s θ := by
      funext θ
      exact mul_div_cancel_left₀ _ (ne_of_gt hs)
    rw [← h3]
    exact h1.div_const s
  have htr0 : ∀ z : ℝ, 0 < z → dzTrace0 u z = c0 z / z := by
    intro z hz
    exact dzTrace0_eq_of_tendsto (hlim0 z hz)
  have htr1 : ∀ z : ℝ, 0 < z → dzTrace1 u z = c1 z / z := by
    intro z hz
    exact dzTrace1_eq_of_tendsto (hlim1 z hz)
  -- (E) the pointwise bounds
  have hc0bd : ∀ z : ℝ, 0 < z → |c0 z| ≤ |Work.Spaces.Dz u z (Real.pi / 4)|
      + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)) * Real.sqrt (sliceEnergy u z) := by
    intro z hz
    have hb := (hc0 z hz).2 (Real.pi / 4) hpi4mem
    have h1 : |c0 z - Work.Spaces.Dz u z (Real.pi / 4)|
        ≤ Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)) * Real.sqrt (sliceEnergy u z) := by
      rw [← Real.sqrt_sq_eq_abs]
      rw [show (c0 z - Work.Spaces.Dz u z (Real.pi / 4)) ^ 2
          = (Work.Spaces.Dz u z (Real.pi / 4) - c0 z) ^ 2 from by ring]
      calc Real.sqrt ((Work.Spaces.Dz u z (Real.pi / 4) - c0 z) ^ 2)
          ≤ Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta) * sliceEnergy u z) :=
            Real.sqrt_le_sqrt hb
        _ = Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
              * Real.sqrt (sliceEnergy u z) :=
            Real.sqrt_mul (mul_nonneg hKpos.le (Real.rpow_nonneg hpi4.le _)) _
    have h2 : |c0 z| = |Work.Spaces.Dz u z (Real.pi / 4)
        - (Work.Spaces.Dz u z (Real.pi / 4) - c0 z)| := by
      congr 1
      ring
    rw [h2]
    calc |Work.Spaces.Dz u z (Real.pi / 4) - (Work.Spaces.Dz u z (Real.pi / 4) - c0 z)|
        ≤ |Work.Spaces.Dz u z (Real.pi / 4)| + |Work.Spaces.Dz u z (Real.pi / 4) - c0 z| :=
          abs_sub _ _
      _ = |Work.Spaces.Dz u z (Real.pi / 4)| + |c0 z - Work.Spaces.Dz u z (Real.pi / 4)| := by
          rw [abs_sub_comm]
      _ ≤ |Work.Spaces.Dz u z (Real.pi / 4)|
            + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
              * Real.sqrt (sliceEnergy u z) := by
          linarith [h1]
  have hc1bd : ∀ z : ℝ, 0 < z → |c1 z| ≤ |Work.Spaces.Dz u z (Real.pi / 4)|
      + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)) * Real.sqrt (sliceEnergy u z) := by
    intro z hz
    have hb := (hc1 z hz).2 (Real.pi / 4) hpi4mem
    have hb' : (Work.Spaces.Dz u z (Real.pi / 4) - c1 z) ^ 2
        ≤ K * (Real.pi / 4) ^ (1 + Work.Spaces.eta) * sliceEnergy u z := by
      have hpi : Real.pi / 2 - Real.pi / 4 = Real.pi / 4 := by ring
      simpa only [hpi] using hb
    have h1 : |c1 z - Work.Spaces.Dz u z (Real.pi / 4)|
        ≤ Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)) * Real.sqrt (sliceEnergy u z) := by
      rw [← Real.sqrt_sq_eq_abs]
      rw [show (c1 z - Work.Spaces.Dz u z (Real.pi / 4)) ^ 2
          = (Work.Spaces.Dz u z (Real.pi / 4) - c1 z) ^ 2 from by ring]
      calc Real.sqrt ((Work.Spaces.Dz u z (Real.pi / 4) - c1 z) ^ 2)
          ≤ Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta) * sliceEnergy u z) :=
            Real.sqrt_le_sqrt hb'
        _ = Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
              * Real.sqrt (sliceEnergy u z) :=
            Real.sqrt_mul (mul_nonneg hKpos.le (Real.rpow_nonneg hpi4.le _)) _
    have h2 : |c1 z| = |Work.Spaces.Dz u z (Real.pi / 4)
        - (Work.Spaces.Dz u z (Real.pi / 4) - c1 z)| := by
      congr 1
      ring
    rw [h2]
    calc |Work.Spaces.Dz u z (Real.pi / 4) - (Work.Spaces.Dz u z (Real.pi / 4) - c1 z)|
        ≤ |Work.Spaces.Dz u z (Real.pi / 4)| + |Work.Spaces.Dz u z (Real.pi / 4) - c1 z| :=
          abs_sub _ _
      _ = |Work.Spaces.Dz u z (Real.pi / 4)| + |c1 z - Work.Spaces.Dz u z (Real.pi / 4)| := by
          rw [abs_sub_comm]
      _ ≤ |Work.Spaces.Dz u z (Real.pi / 4)|
            + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
              * Real.sqrt (sliceEnergy u z) := by
          linarith [h1]
  have hslicebd : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) →
      |Work.Spaces.Dz u z θ| ≤ |Work.Spaces.Dz u z (Real.pi / 4)|
        + (Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
            + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)))
          * Real.sqrt (sliceEnergy u z) := by
    intro z θ hz hθ
    have hb := (hc0 z hz).2 θ hθ
    have h1 : |Work.Spaces.Dz u z θ - c0 z|
        ≤ Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
          * Real.sqrt (sliceEnergy u z) := by
      rw [← Real.sqrt_sq_eq_abs]
      calc Real.sqrt ((Work.Spaces.Dz u z θ - c0 z) ^ 2)
          ≤ Real.sqrt (K * θ ^ (1 + Work.Spaces.eta) * sliceEnergy u z) := Real.sqrt_le_sqrt hb
        _ = Real.sqrt (K * θ ^ (1 + Work.Spaces.eta)) * Real.sqrt (sliceEnergy u z) :=
            Real.sqrt_mul (mul_nonneg hKpos.le (Real.rpow_nonneg hθ.1.le _)) _
        _ ≤ Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
              * Real.sqrt (sliceEnergy u z) := by
            refine mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow hθ.1.le hθ.2.le heta1.le) hKpos.le
    have h2 : |Work.Spaces.Dz u z θ| ≤ |Work.Spaces.Dz u z θ - c0 z| + |c0 z| := by
      have h3 : |Work.Spaces.Dz u z θ| = |(Work.Spaces.Dz u z θ - c0 z) + c0 z| := by
        congr 1
        ring
      rw [h3]
      exact abs_add_le _ _
    have h4 := hc0bd z hz
    calc |Work.Spaces.Dz u z θ|
        ≤ |Work.Spaces.Dz u z θ - c0 z| + |c0 z| := h2
      _ ≤ Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)) * Real.sqrt (sliceEnergy u z)
            + (|Work.Spaces.Dz u z (Real.pi / 4)|
              + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
                * Real.sqrt (sliceEnergy u z)) := by linarith [h1, h4]
      _ = |Work.Spaces.Dz u z (Real.pi / 4)|
            + (Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
              + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)))
              * Real.sqrt (sliceEnergy u z) := by ring
  -- (F) the FTC in `z`
  have hftc : ∀ z t θ : ℝ, 0 < z → 0 < t → θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) →
      (∫ s in Set.Ioo z (z + t), Work.Spaces.pz u s θ) = u (z + t) θ - u z θ := by
    intro z t θ hz ht hθ
    have hderiv : ∀ x ∈ Set.uIcc z (z + t), HasDerivAt (fun s : ℝ => u s θ)
        (Work.Spaces.pz u x θ) x := by
      intro x hx
      have hx' := Set.mem_uIcc.mp hx
      rcases hx' with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hS.hasDerivAt_slice hθ (lt_of_lt_of_le hz h1)
      · exact hS.hasDerivAt_slice hθ (lt_of_lt_of_le (by linarith : (0:ℝ) < z + t) h1)
    have hcont : ContinuousOn (fun s : ℝ => Work.Spaces.pz u s θ) (Set.uIcc z (z + t)) :=
      ((Work.FTS.LocData.contDiffOn_slice_z (G := Work.Spaces.pz u) (s := Set.Ioi 0)
        (t := Set.Ioo (0:ℝ) (Real.pi / 2)) (hS.pz) hθ).continuousOn).mono
          (fun s hs => by
            have hs' := Set.mem_uIcc.mp hs
            rcases hs' with ⟨h1, _⟩ | ⟨h1, _⟩
            · exact lt_of_lt_of_le hz h1
            · exact lt_of_lt_of_le (by linarith : (0:ℝ) < z + t) h1)
    have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
    rw [← hmain, intervalIntegral.integral_of_le (by linarith : z ≤ z + t),
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  -- (G) the good set for the left trace
  set S : Set ℝ := {z : ℝ | Filter.Tendsto (fun θ => u z θ)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0)} ∪ {z : ℝ | z ≤ 0} with hSdef
  have hScomp : Sᶜ ⊆ Set.Ioi (0:ℝ) := by
    intro z hz
    by_contra hcon
    have hlt : ¬ (0:ℝ) < z := fun h => hcon (by simpa using h)
    exact hz (Or.inr (not_lt.mp hlt))
  have hSnull : volume Sᶜ = 0 := by
    have h1 : (volume.restrict (Set.Ioi 0)) Sᶜ = 0 := by
      refine MeasureTheory.ae_iff.mp ?_
      filter_upwards [Work.FTS.EllipticEst.H2W.AeLeftClean.sliceLeftTendstoClean α u G h]
        with z hz
      exact Or.inl hz
    rwa [MeasureTheory.Measure.restrict_eq_self volume hScomp] at h1
  have hStrace : ∀ z ∈ S, 0 < z →
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
    intro z hz hzpos
    rcases hz with h | h
    · exact h
    · exact absurd h (not_le.mpr hzpos)
  have hSaet : ∀ z : ℝ, ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)), z + t ∈ S := by
    intro z
    have hnull : volume ((fun t : ℝ => z + t) ⁻¹' Sᶜ) = 0 := by
      rw [MeasureTheory.measure_preimage_add]
      exact hSnull
    rw [MeasureTheory.ae_iff]
    rw [MeasureTheory.Measure.restrict_apply_eq_zero' measurableSet_Ioi]
    refine MeasureTheory.measure_mono_null ?_ hnull
    intro t ht
    exact ht.1
  -- (H) the limit filters
  have hθl0 : ∀ᶠ θ in nhdsWithin (0:ℝ) (Set.Ioi 0), θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) := by
    have h2 : Set.Ioo (-1:ℝ) (Real.pi / 2) ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
      Filter.mem_inf_of_left
        (Ioo_mem_nhds (by norm_num : (-1:ℝ) < 0)
          (by linarith [Real.pi_pos] : (0:ℝ) < Real.pi / 2))
    refine Filter.mem_of_superset
      (Filter.inter_mem
        (self_mem_nhdsWithin : Set.Ioi (0:ℝ) ∈ nhdsWithin (0:ℝ) (Set.Ioi 0)) h2) ?_
    intro x hx
    exact ⟨hx.1, hx.2.2⟩
  have hθl1 : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) := by
    have h2 : Set.Ioi (0:ℝ) ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) :=
      Filter.mem_inf_of_left
        (Ioi_mem_nhds (by linarith [Real.pi_pos] : (0:ℝ) < Real.pi / 2))
    refine Filter.mem_of_superset
      (Filter.inter_mem h2
        (self_mem_nhdsWithin : Set.Iio (Real.pi / 2) ∈
          nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))) ?_
    intro x hx
    exact ⟨hx.1, hx.2⟩
  -- (I) the a.e. vanishing of the interval integrals, left endpoint
  have hdct0 : ∀ z t : ℝ, 0 < z → 0 < t → z ∈ S → z + t ∈ S →
      (∫ x in z..(z + t), Set.indicator (Set.Ioi 0) (dzTrace0 u) x) = 0 := by
    intro z t hz ht hzS hztS
    have htrz : Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) :=
      hStrace z hzS hz
    have htrzt : Filter.Tendsto (fun θ => u (z + t) θ) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) :=
      hStrace (z + t) hztS (by linarith)
    have hGint : MeasureTheory.IntegrableOn
        (fun s => |Work.Spaces.pz u s (Real.pi / 4)|
          + (Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
              + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)))
            * (Real.sqrt (sliceEnergy u s) / s)) (Set.Ioo z (z + t)) := by
      have h1 : MeasureTheory.IntegrableOn (fun s : ℝ => |Work.Spaces.pz u s (Real.pi / 4)|)
          (Set.Ioo z (z + t)) := by
        have hcont : ContinuousOn (fun s : ℝ => Work.Spaces.pz u s (Real.pi / 4))
            (Set.Icc z (z + t)) :=
          ((Work.FTS.LocData.contDiffOn_slice_z (G := Work.Spaces.pz u) (s := Set.Ioi 0)
            (t := Set.Ioo (0:ℝ) (Real.pi / 2)) (hS.pz) hpi4mem).continuousOn).mono
              (fun s hs => lt_of_lt_of_le hz (Set.mem_Icc.mp hs).1)
        exact ((hcont.abs).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
      have h2 : MeasureTheory.IntegrableOn (fun s => Real.sqrt (sliceEnergy u s) / s)
          (Set.Ioo z (z + t)) :=
        (integrableOn_sqrt_sliceEnergy_div hS hMix (by linarith : 0 < z + t)).mono_set
          (fun s hs => ⟨lt_trans hz hs.1, hs.2⟩)
      have h3 : MeasureTheory.IntegrableOn
          (fun s => (Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
              + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)))
            * (Real.sqrt (sliceEnergy u s) / s)) (Set.Ioo z (z + t)) :=
        h2.const_mul _
      exact h1.add h3
    have hDCT := tendsto_setIntegral_pz hS (l := nhdsWithin (0:ℝ) (Set.Ioi 0))
      (c := dzTrace0 u)
      (g := fun s => |Work.Spaces.pz u s (Real.pi / 4)|
        + (Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
            + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)))
          * (Real.sqrt (sliceEnergy u s) / s)) hz ht hθl0
      (fun s hs => by rw [htr0 s hs]; exact hlim0 s hs) ?_ hGint
    · have heq : (fun θ => u (z + t) θ - u z θ)
          =ᶠ[nhdsWithin (0:ℝ) (Set.Ioi 0)]
          (fun θ => ∫ s in Set.Ioo z (z + t), Work.Spaces.pz u s θ) := by
        filter_upwards [hθl0] with θ hθ
        exact (hftc z t θ hz ht hθ).symm
      have htr : Filter.Tendsto (fun θ => u (z + t) θ - u z θ)
          (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
        simpa using htrzt.sub htrz
      have htr' : Filter.Tendsto (fun θ => ∫ s in Set.Ioo z (z + t), Work.Spaces.pz u s θ)
          (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) :=
        Filter.Tendsto.congr' heq htr
      have huniq := tendsto_nhds_unique hDCT htr'
      have h2 : (∫ x in Set.Ioo z (z + t), Set.indicator (Set.Ioi 0) (dzTrace0 u) x)
          = ∫ x in Set.Ioo z (z + t), dzTrace0 u x :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
          (fun x hx => Set.indicator_of_mem (lt_trans hz hx.1) _)
      rw [intervalIntegral.integral_of_le (by linarith : z ≤ z + t),
        MeasureTheory.integral_Ioc_eq_integral_Ioo, h2]
      exact huniq
    · filter_upwards [hθl0] with θ hθ
      intro s hs
      have hs0 : 0 < s := lt_trans hz hs.1
      have hb := hslicebd s θ hs0 hθ
      have hpz : |Work.Spaces.pz u s θ| = |Work.Spaces.Dz u s θ| / s := by
        rw [Work.Spaces.Dz, abs_mul, abs_of_pos hs0, mul_div_cancel_left₀ _ (ne_of_gt hs0)]
      have hDz : |Work.Spaces.Dz u s (Real.pi / 4)| / s
          = |Work.Spaces.pz u s (Real.pi / 4)| := by
        rw [Work.Spaces.Dz, abs_mul, abs_of_pos hs0, mul_div_cancel_left₀ _ (ne_of_gt hs0)]
      rw [Real.norm_eq_abs, hpz]
      calc |Work.Spaces.Dz u s θ| / s
          ≤ (|Work.Spaces.Dz u s (Real.pi / 4)|
              + (Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
                + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)))
                * Real.sqrt (sliceEnergy u s)) / s :=
            div_le_div_of_nonneg_right hb (le_of_lt hs0)
        _ = |Work.Spaces.pz u s (Real.pi / 4)|
              + (Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
                + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)))
                * (Real.sqrt (sliceEnergy u s) / s) := by
            rw [add_div, hDz, mul_div_assoc]
  -- (J) the right endpoint: the interval integrals for all `z, t`
  have hdct1 : ∀ z t : ℝ, 0 < z → 0 < t →
      (∫ x in z..(z + t), Set.indicator (Set.Ioi 0) (dzTrace1 u) x) = 0 := by
    intro z t hz ht
    have htrz : Filter.Tendsto (fun θ => u z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
      (Work.FTS.EllipticEst.H2W.AeProof.AeSliceRightTendsto α u G h z hz).1
    have htrzt : Filter.Tendsto (fun θ => u (z + t) θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
      (Work.FTS.EllipticEst.H2W.AeProof.AeSliceRightTendsto α u G h (z + t)
        (by linarith)).1
    have hGint : MeasureTheory.IntegrableOn
        (fun s => |Work.Spaces.pz u s (Real.pi / 4)|
          + (Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
              + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)))
            * (Real.sqrt (sliceEnergy u s) / s)) (Set.Ioo z (z + t)) := by
      have h1 : MeasureTheory.IntegrableOn (fun s : ℝ => |Work.Spaces.pz u s (Real.pi / 4)|)
          (Set.Ioo z (z + t)) := by
        have hcont : ContinuousOn (fun s : ℝ => Work.Spaces.pz u s (Real.pi / 4))
            (Set.Icc z (z + t)) :=
          ((Work.FTS.LocData.contDiffOn_slice_z (G := Work.Spaces.pz u) (s := Set.Ioi 0)
            (t := Set.Ioo (0:ℝ) (Real.pi / 2)) (hS.pz) hpi4mem).continuousOn).mono
              (fun s hs => lt_of_lt_of_le hz (Set.mem_Icc.mp hs).1)
        exact ((hcont.abs).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
      have h2 : MeasureTheory.IntegrableOn (fun s => Real.sqrt (sliceEnergy u s) / s)
          (Set.Ioo z (z + t)) :=
        (integrableOn_sqrt_sliceEnergy_div hS hMix (by linarith : 0 < z + t)).mono_set
          (fun s hs => ⟨lt_trans hz hs.1, hs.2⟩)
      have h3 : MeasureTheory.IntegrableOn
          (fun s => (Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
              + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)))
            * (Real.sqrt (sliceEnergy u s) / s)) (Set.Ioo z (z + t)) :=
        h2.const_mul _
      exact h1.add h3
    have hDCT := tendsto_setIntegral_pz hS
      (l := nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (c := dzTrace1 u)
      (g := fun s => |Work.Spaces.pz u s (Real.pi / 4)|
        + (Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
            + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)))
          * (Real.sqrt (sliceEnergy u s) / s)) hz ht hθl1
      (fun s hs => by rw [htr1 s hs]; exact hlim1 s hs) ?_ hGint
    · have heq : (fun θ => u (z + t) θ - u z θ)
          =ᶠ[nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))]
          (fun θ => ∫ s in Set.Ioo z (z + t), Work.Spaces.pz u s θ) := by
        filter_upwards [hθl1] with θ hθ
        exact (hftc z t θ hz ht hθ).symm
      have htr : Filter.Tendsto (fun θ => u (z + t) θ - u z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
        simpa using htrzt.sub htrz
      have htr' : Filter.Tendsto (fun θ => ∫ s in Set.Ioo z (z + t), Work.Spaces.pz u s θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
        Filter.Tendsto.congr' heq htr
      have huniq := tendsto_nhds_unique hDCT htr'
      have h2 : (∫ x in Set.Ioo z (z + t), Set.indicator (Set.Ioi 0) (dzTrace1 u) x)
          = ∫ x in Set.Ioo z (z + t), dzTrace1 u x :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
          (fun x hx => Set.indicator_of_mem (lt_trans hz hx.1) _)
      rw [intervalIntegral.integral_of_le (by linarith : z ≤ z + t),
        MeasureTheory.integral_Ioc_eq_integral_Ioo, h2]
      exact huniq
    · filter_upwards [hθl1] with θ hθ
      intro s hs
      have hs0 : 0 < s := lt_trans hz hs.1
      have hb := hslicebd s θ hs0 hθ
      have hpz : |Work.Spaces.pz u s θ| = |Work.Spaces.Dz u s θ| / s := by
        rw [Work.Spaces.Dz, abs_mul, abs_of_pos hs0, mul_div_cancel_left₀ _ (ne_of_gt hs0)]
      have hDz : |Work.Spaces.Dz u s (Real.pi / 4)| / s
          = |Work.Spaces.pz u s (Real.pi / 4)| := by
        rw [Work.Spaces.Dz, abs_mul, abs_of_pos hs0, mul_div_cancel_left₀ _ (ne_of_gt hs0)]
      rw [Real.norm_eq_abs, hpz]
      calc |Work.Spaces.Dz u s θ| / s
          ≤ (|Work.Spaces.Dz u s (Real.pi / 4)|
              + (Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
                + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)))
                * Real.sqrt (sliceEnergy u s)) / s :=
            div_le_div_of_nonneg_right hb (le_of_lt hs0)
        _ = |Work.Spaces.pz u s (Real.pi / 4)|
              + (Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
                + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)))
                * (Real.sqrt (sliceEnergy u s) / s) := by
            rw [add_div, hDz, mul_div_assoc]
  -- (K) the trace functions are locally integrable on `(0,∞)`
  have htrbd : ∀ s : ℝ, 0 < s → |dzTrace0 u s| ≤ |Work.Spaces.pz u s (Real.pi / 4)|
      + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
        * (Real.sqrt (sliceEnergy u s) / s) := by
    intro s hs
    have hDz : |Work.Spaces.Dz u s (Real.pi / 4)| / s
        = |Work.Spaces.pz u s (Real.pi / 4)| := by
      rw [Work.Spaces.Dz, abs_mul, abs_of_pos hs, mul_div_cancel_left₀ _ (ne_of_gt hs)]
    rw [htr0 s hs, abs_div, abs_of_pos hs]
    calc |c0 s| / s ≤ (|Work.Spaces.Dz u s (Real.pi / 4)|
          + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
            * Real.sqrt (sliceEnergy u s)) / s :=
        div_le_div_of_nonneg_right (hc0bd s hs) (le_of_lt hs)
      _ = |Work.Spaces.pz u s (Real.pi / 4)|
          + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
            * (Real.sqrt (sliceEnergy u s) / s) := by
        rw [add_div, hDz, mul_div_assoc]
  have htr1bd : ∀ s : ℝ, 0 < s → |dzTrace1 u s| ≤ |Work.Spaces.pz u s (Real.pi / 4)|
      + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
        * (Real.sqrt (sliceEnergy u s) / s) := by
    intro s hs
    have hDz : |Work.Spaces.Dz u s (Real.pi / 4)| / s
        = |Work.Spaces.pz u s (Real.pi / 4)| := by
      rw [Work.Spaces.Dz, abs_mul, abs_of_pos hs, mul_div_cancel_left₀ _ (ne_of_gt hs)]
    rw [htr1 s hs, abs_div, abs_of_pos hs]
    calc |c1 s| / s ≤ (|Work.Spaces.Dz u s (Real.pi / 4)|
          + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
            * Real.sqrt (sliceEnergy u s)) / s :=
        div_le_div_of_nonneg_right (hc1bd s hs) (le_of_lt hs)
      _ = |Work.Spaces.pz u s (Real.pi / 4)|
          + Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
            * (Real.sqrt (sliceEnergy u s) / s) := by
        rw [add_div, hDz, mul_div_assoc]
  have hTrInt : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (dzTrace0 u) (Set.Ioo a b) := by
    intro a b ha hab
    have h1 : MeasureTheory.IntegrableOn (fun s : ℝ => |Work.Spaces.pz u s (Real.pi / 4)|)
        (Set.Ioo a b) := by
      have hcont : ContinuousOn (fun s : ℝ => Work.Spaces.pz u s (Real.pi / 4))
          (Set.Icc a b) :=
        ((Work.FTS.LocData.contDiffOn_slice_z (G := Work.Spaces.pz u) (s := Set.Ioi 0)
          (t := Set.Ioo (0:ℝ) (Real.pi / 2)) (hS.pz) hpi4mem).continuousOn).mono
            (fun s hs => lt_of_lt_of_le ha (Set.mem_Icc.mp hs).1)
      exact ((hcont.abs).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    have h2 : MeasureTheory.IntegrableOn (fun s : ℝ =>
        Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
          * (Real.sqrt (sliceEnergy u s) / s)) (Set.Ioo a b) :=
      ((integrableOn_sqrt_sliceEnergy_div hS hMix (lt_trans ha hab)).mono_set
        (fun s hs => ⟨lt_trans ha hs.1, hs.2⟩)).const_mul _
    refine MeasureTheory.Integrable.mono' (h1.add h2) ?_ ?_
    · have hle : volume.restrict (Set.Ioo a b) ≤ volume.restrict (Set.Ioi (0:ℝ)) :=
        MeasureTheory.Measure.restrict_mono_set volume (fun s hs => lt_trans ha hs.1)
      exact ((aemeasurable_dzTrace0 (u := u) hS).aestronglyMeasurable).mono_measure hle
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with s hs
      rw [Real.norm_eq_abs]
      exact htrbd s (lt_trans ha hs.1)
  have hTr1Int : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (dzTrace1 u) (Set.Ioo a b) := by
    intro a b ha hab
    have h1 : MeasureTheory.IntegrableOn (fun s : ℝ => |Work.Spaces.pz u s (Real.pi / 4)|)
        (Set.Ioo a b) := by
      have hcont : ContinuousOn (fun s : ℝ => Work.Spaces.pz u s (Real.pi / 4))
          (Set.Icc a b) :=
        ((Work.FTS.LocData.contDiffOn_slice_z (G := Work.Spaces.pz u) (s := Set.Ioi 0)
          (t := Set.Ioo (0:ℝ) (Real.pi / 2)) (hS.pz) hpi4mem).continuousOn).mono
            (fun s hs => lt_of_lt_of_le ha (Set.mem_Icc.mp hs).1)
      exact ((hcont.abs).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    have h2 : MeasureTheory.IntegrableOn (fun s : ℝ =>
        Real.sqrt (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
          * (Real.sqrt (sliceEnergy u s) / s)) (Set.Ioo a b) :=
      ((integrableOn_sqrt_sliceEnergy_div hS hMix (lt_trans ha hab)).mono_set
        (fun s hs => ⟨lt_trans ha hs.1, hs.2⟩)).const_mul _
    refine MeasureTheory.Integrable.mono' (h1.add h2) ?_ ?_
    · have hle : volume.restrict (Set.Ioo a b) ≤ volume.restrict (Set.Ioi (0:ℝ)) :=
        MeasureTheory.Measure.restrict_mono_set volume (fun s hs => lt_trans ha hs.1)
      exact ((aemeasurable_dzTrace1 (u := u) hS).aestronglyMeasurable).mono_measure hle
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with s hs
      rw [Real.norm_eq_abs]
      exact htr1bd s (lt_trans ha hs.1)
  -- (L) the cut-off functions have vanishing interval integrals
  have hcut0 : ∀ (ε : ℝ), 0 < ε → ∀ z t : ℝ, 0 < z → 0 < t → ε < z → z ∈ S → z + t ∈ S →
      (∫ x in z..(z + t), Set.indicator (Set.Ioi ε) (dzTrace0 u) x) = 0 := by
    intro ε hε z t hz ht hεz hzS hztS
    have hII : (∫ x in z..(z + t), Set.indicator (Set.Ioi ε) (dzTrace0 u) x)
        = ∫ x in Set.Ioo z (z + t), Set.indicator (Set.Ioi ε) (dzTrace0 u) x := by
      rw [intervalIntegral.integral_of_le (by linarith : z ≤ z + t),
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
    have hII2 : (∫ x in Set.Ioo z (z + t), Set.indicator (Set.Ioi 0) (dzTrace0 u) x)
        = ∫ x in z..(z + t), Set.indicator (Set.Ioi 0) (dzTrace0 u) x := by
      rw [intervalIntegral.integral_of_le (by linarith : z ≤ z + t),
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
    have hmid : (∫ x in Set.Ioo z (z + t), Set.indicator (Set.Ioi ε) (dzTrace0 u) x)
        = ∫ x in Set.Ioo z (z + t), Set.indicator (Set.Ioi 0) (dzTrace0 u) x :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
        (fun x hx => by
          have h1 : Set.indicator (Set.Ioi ε) (dzTrace0 u) x = dzTrace0 u x :=
            Set.indicator_of_mem (lt_trans hεz hx.1) (dzTrace0 u)
          have h2 : Set.indicator (Set.Ioi 0) (dzTrace0 u) x = dzTrace0 u x :=
            Set.indicator_of_mem (lt_trans hε (lt_trans hεz hx.1)) (dzTrace0 u)
          rw [h1, h2])
    rw [hII, hmid, hII2]
    exact hdct0 z t hz ht hzS hztS
  have hcut1 : ∀ (ε : ℝ), 0 < ε → ∀ z t : ℝ, 0 < z → 0 < t → ε < z →
      (∫ x in z..(z + t), Set.indicator (Set.Ioi ε) (dzTrace1 u) x) = 0 := by
    intro ε hε z t hz ht hεz
    have hII : (∫ x in z..(z + t), Set.indicator (Set.Ioi ε) (dzTrace1 u) x)
        = ∫ x in Set.Ioo z (z + t), Set.indicator (Set.Ioi ε) (dzTrace1 u) x := by
      rw [intervalIntegral.integral_of_le (by linarith : z ≤ z + t),
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
    have hII2 : (∫ x in Set.Ioo z (z + t), Set.indicator (Set.Ioi 0) (dzTrace1 u) x)
        = ∫ x in z..(z + t), Set.indicator (Set.Ioi 0) (dzTrace1 u) x := by
      rw [intervalIntegral.integral_of_le (by linarith : z ≤ z + t),
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
    have hmid : (∫ x in Set.Ioo z (z + t), Set.indicator (Set.Ioi ε) (dzTrace1 u) x)
        = ∫ x in Set.Ioo z (z + t), Set.indicator (Set.Ioi 0) (dzTrace1 u) x :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
        (fun x hx => by
          have h1 : Set.indicator (Set.Ioi ε) (dzTrace1 u) x = dzTrace1 u x :=
            Set.indicator_of_mem (lt_trans hεz hx.1) (dzTrace1 u)
          have h2 : Set.indicator (Set.Ioi 0) (dzTrace1 u) x = dzTrace1 u x :=
            Set.indicator_of_mem (lt_trans hε (lt_trans hεz hx.1)) (dzTrace1 u)
          rw [h1, h2])
    rw [hII, hmid, hII2]
    exact hdct1 z t hz ht
  -- (M) measurable full-measure good set and the two `D2` applications
  obtain ⟨N, hSN, hNmeas, hNnull⟩ := MeasureTheory.exists_measurable_superset_of_null hSnull
  have hS1meas : MeasurableSet Nᶜ := hNmeas.compl
  have hS1sub : Nᶜ ⊆ S := fun z hz => by
    by_contra hzs
    exact hz (hSN hzs)
  have hS1null : volume (Nᶜ)ᶜ = 0 := by simpa using hNnull
  have hS1trace : ∀ z ∈ Nᶜ, 0 < z →
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) :=
    fun z hz hzpos => hStrace z (hS1sub hz) hzpos
  have hS1aet : ∀ z : ℝ, ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)), z + t ∈ Nᶜ := by
    intro z
    have hnull : volume ((fun t : ℝ => z + t) ⁻¹' (Nᶜ)ᶜ) = 0 := by
      rw [MeasureTheory.measure_preimage_add]
      exact hS1null
    rw [MeasureTheory.ae_iff]
    rw [MeasureTheory.Measure.restrict_apply_eq_zero' measurableSet_Ioi]
    refine MeasureTheory.measure_mono_null ?_ hnull
    intro t ht
    exact ht.1
  have hper0 : ∀ n : ℕ, ∀ᵐ z ∂(volume.restrict (Set.Ioi (1/((n:ℝ)+1)))),
      dzTrace0 u z = 0 := by
    intro n
    set ε : ℝ := 1 / ((n:ℝ) + 1) with hεdef
    have hεpos : 0 < ε := by positivity
    have hloc : MeasureTheory.LocallyIntegrable (Set.indicator (Set.Ioi ε) (dzTrace0 u)) volume :=
      locallyIntegrable_indicator_Ioi hεpos
        (fun a b ha hab => hTrInt a b (lt_of_lt_of_le hεpos ha) hab)
    have hint : ∀ᵐ z ∂(volume.restrict (Set.Ioi ε ∩ Nᶜ)),
        ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)),
          (∫ x in z..(z + t), Set.indicator (Set.Ioi ε) (dzTrace0 u) x) = 0 := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict (measurableSet_Ioi.inter hS1meas)]
        with z hz
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi, hS1aet z]
        with t ht hN
      exact hcut0 ε hεpos z t (lt_trans hεpos hz.1) ht hz.1
        (hS1sub hz.2) (hS1sub hN)
    have hmain := aeZeroOn_of_intervalIntegralZero hloc hint
    have hae : Set.Ioi ε ∩ Nᶜ =ᵐ[volume] Set.Ioi ε := by
      refine MeasureTheory.ae_eq_set.mpr ⟨?_, ?_⟩
      · rw [show (Set.Ioi ε ∩ Nᶜ) \ Set.Ioi ε = ∅ from Set.diff_eq_empty.mpr Set.inter_subset_left]
        simp
      · refine MeasureTheory.measure_mono_null ?_ hNnull
        intro z hz
        by_contra hzN
        exact hz.2 ⟨hz.1, hzN⟩
    rw [MeasureTheory.Measure.restrict_congr_set hae] at hmain
    filter_upwards [hmain,
      MeasureTheory.ae_restrict_mem (μ := volume) (s := Set.Ioi ε) measurableSet_Ioi]
      with z hz hzε
    rwa [Set.indicator_of_mem hzε (dzTrace0 u)] at hz
  have hper1 : ∀ n : ℕ, ∀ᵐ z ∂(volume.restrict (Set.Ioi (1/((n:ℝ)+1)))),
      dzTrace1 u z = 0 := by
    intro n
    set ε : ℝ := 1 / ((n:ℝ) + 1) with hεdef
    have hεpos : 0 < ε := by positivity
    have hloc : MeasureTheory.LocallyIntegrable (Set.indicator (Set.Ioi ε) (dzTrace1 u)) volume :=
      locallyIntegrable_indicator_Ioi hεpos
        (fun a b ha hab => hTr1Int a b (lt_of_lt_of_le hεpos ha) hab)
    have hint : ∀ᵐ z ∂(volume.restrict (Set.Ioi ε)),
        ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)),
          (∫ x in z..(z + t), Set.indicator (Set.Ioi ε) (dzTrace1 u) x) = 0 := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact hcut1 ε hεpos z t (lt_trans hεpos hz) ht hz
    have hmain := aeZeroOn_of_intervalIntegralZero hloc hint
    filter_upwards [hmain,
      MeasureTheory.ae_restrict_mem (μ := volume) (s := Set.Ioi ε) measurableSet_Ioi]
      with z hz hzε
    rwa [Set.indicator_of_mem hzε (dzTrace1 u)] at hz
  have hzero0 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), dzTrace0 u z = 0 := by
    rw [MeasureTheory.ae_iff]
    rw [MeasureTheory.Measure.restrict_apply_eq_zero' measurableSet_Ioi]
    have hcov : {z : ℝ | ¬ dzTrace0 u z = 0} ∩ Set.Ioi (0:ℝ) ⊆
        ⋃ n : ℕ, ({z : ℝ | ¬ dzTrace0 u z = 0} ∩ Set.Ioi (1/((n:ℝ)+1))) := by
      intro z hz
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0:ℝ) < z by simpa using hz.2)
      exact Set.mem_iUnion.mpr ⟨n, ⟨hz.1, hn⟩⟩
    refine MeasureTheory.measure_mono_null hcov ?_
    refine MeasureTheory.measure_iUnion_null ?_
    intro n
    exact MeasureTheory.Measure.measure_inter_eq_zero_of_restrict
      (MeasureTheory.ae_iff.mp (hper0 n))
  have hzero1 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), dzTrace1 u z = 0 := by
    rw [MeasureTheory.ae_iff]
    rw [MeasureTheory.Measure.restrict_apply_eq_zero' measurableSet_Ioi]
    have hcov : {z : ℝ | ¬ dzTrace1 u z = 0} ∩ Set.Ioi (0:ℝ) ⊆
        ⋃ n : ℕ, ({z : ℝ | ¬ dzTrace1 u z = 0} ∩ Set.Ioi (1/((n:ℝ)+1))) := by
      intro z hz
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0:ℝ) < z by simpa using hz.2)
      exact Set.mem_iUnion.mpr ⟨n, ⟨hz.1, hn⟩⟩
    refine MeasureTheory.measure_mono_null hcov ?_
    refine MeasureTheory.measure_iUnion_null ?_
    intro n
    exact MeasureTheory.Measure.measure_inter_eq_zero_of_restrict
      (MeasureTheory.ae_iff.mp (hper1 n))
  -- (N) conclusion
  have hconv0 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => z * Work.Spaces.pz u z θ)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
    filter_upwards [hzero0, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz hzpos
    have h1 : Filter.Tendsto (fun θ => Work.Spaces.pz u z θ)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
      have h := hlim0 z hzpos
      rw [← htr0 z hzpos, hz] at h
      exact h
    simpa using h1.const_mul z
  have hconv1 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => z * Work.Spaces.pz u z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    filter_upwards [hzero1, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz hzpos
    have h1 : Filter.Tendsto (fun θ => Work.Spaces.pz u z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have h := hlim1 z hzpos
      rw [← htr1 z hzpos, hz] at h
      exact h
    simpa using h1.const_mul z
  filter_upwards [hconv0, hconv1] with z h0 h1
  exact ⟨h0, h1⟩
end Work.FTS.EllipticEst.TT.AeI1
end
end
-- ===== merged: Submission.Work.FTS.OpenPkg.WProdWin.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg.WProdWin

open Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- The angular factor surviving the mixed slots of the `𝒲^{4,∞}`-priced product rule:
`(α + sin 2θ)² sin(2θ)^{2α/5 - γ}`, the product of the squared `f`-side factor
`(α + sin 2θ) sin(2θ)^{α/5}` with the `g`-side weight `sin(2θ)^{-γ}`. -/
def TW (α θ : ℝ) : ℝ :=
  (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)

/-- `HgInt α g z = ∫_θ HkIntegrand α 4 g z θ`, the angular integral of the `ℋ⁴`-integrand of `g`
at fixed radius.  (Its `z`-integral is `HkSq α 4 g` by definition.) -/
def HgInt (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Iθ, HkIntegrand α 4 g z θ

/-- **The pointwise majorant of the `𝒲^{4,∞}`-priced product rule.**

It is the `ℋ⁴`-integrand of `g` plus the angular contribution of the mean-term bound for the
radial slots of `g` (`HgInt`, the mean term) and of the angular `L²`-norms `Aang` of the mixed
slots of `g`, together with the surviving angular factor `TW`. -/
def GmajW (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  HkIntegrand α 4 g z θ
    + (HgInt α g z + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 4, Work.FTS.H2.WPQ.Aang α g d z)
      * TW α θ

/-! ## Elementary properties of `TW` -/

theorem TW_nonneg {α θ : ℝ} (hα : 0 ≤ α) (hθ : θ ∈ Iθ) : 0 ≤ TW α θ :=
  mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg' hθ) _)

/-- On the open quadrant, `TW` splits as `(α+sin2θ)² sin(2θ)^{2α/5} · sin(2θ)^{-γ}`. -/
theorem TW_eq_mul {α θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    TW α θ = ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
      * (Real.sin (2 * θ)) ^ (-(gam α)) := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  rw [TW, mul_assoc, ← Real.rpow_add hs, sub_eq_add_neg]

theorem TW_integrable {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) : IntegrableOn (TW α) Iθ :=
  Work.Spaces.integrableOn_angular_weight hα hα1

theorem TW_integral_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (∫ θ in Iθ, TW α θ) ≤ 700 :=
  Work.Spaces.angular_weight_integral_bound hα hα1

/-! ## Elementary properties of `HgInt` and `GmajW` -/

theorem HgInt_nonneg (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ HgInt α g z :=
  integral_nonneg fun θ => HkIntegrand_nonneg α 4 g z θ

theorem GmajW_nonneg {α : ℝ} (hα : 0 < α) (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Iθ) :
    0 ≤ GmajW α g z θ := by
  have hγ1 : (0 : ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
  refine add_nonneg (HkIntegrand_nonneg α 4 g z θ) (mul_nonneg (add_nonneg (HgInt_nonneg α g z)
    (mul_nonneg (inv_nonneg.mpr hγ1.le) (Work.FTS.H2.WPQ.sum_Aang_nonneg α g z)))
    (TW_nonneg hα.le hθ))

/-- The `ℋ⁴`-integrand of `g` is dominated by the majorant. -/
theorem HkIntegrand_le_GmajW {α : ℝ} (hα : 0 < α) (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Iθ) :
    HkIntegrand α 4 g z θ ≤ GmajW α g z θ := by
  have hγ1 : (0 : ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
  refine le_add_of_nonneg_right (mul_nonneg (add_nonneg (HgInt_nonneg α g z)
    (mul_nonneg (inv_nonneg.mpr hγ1.le) (Work.FTS.H2.WPQ.sum_Aang_nonneg α g z)))
    (TW_nonneg hα.le hθ))

/-- The sum of the angular `L²`-norms of the mixed slots of `g` is dominated by the mean term. -/
theorem sum_Aang_le_HgInt {α : ℝ} {g : ℝ → ℝ → ℝ} (hgm : HkMem α 4 g) {z : ℝ} (hz : z ∈ Iz) :
    ∑ d ∈ Finset.range 4, Work.FTS.H2.WPQ.Aang α g d z ≤ 4 * HgInt α g z :=
  Work.FTS.H2.WPQ.sum_Aang_le α hgm hz

/-- `HgInt` integrates to `HkSq α 4 g` (definitional). -/
theorem HgInt_z_integral (α : ℝ) (g : ℝ → ℝ → ℝ) :
    (∫ z in Iz, HgInt α g z) = HkSq α 4 g := rfl

/-- **The mean term controls the radial slots of `g`**: `w(z)² ∫_σ (D_z^d g(z,σ))² ≤ HgInt z`.

The weight `w/sin(2σ)^{η/2}` is `≥ w ≥ 1` on the open quadrant, so the left-hand side is
pointwise dominated by the `(d,0)`-slot of `HkIntegrand α 4 g`. -/
theorem w_sq_mul_slice_le_HgInt {α : ℝ} {g : ℝ → ℝ → ℝ} (hgm : HkMem α 4 g)
    {d : ℕ} (hd : d ≤ 4) {z : ℝ} (hz : 0 < z) :
    (w z) ^ 2 * (∫ σ in Iθ, (DzIter d g z σ) ^ 2) ≤ HgInt α g z := by
  have hzI : z ∈ Iz := le_of_lt hz
  have hdiv : (w z) ^ 2 * (∫ σ in Iθ, (DzIter d g z σ) ^ 2)
      = ∫ σ in Iθ, (w z) ^ 2 * (DzIter d g z σ) ^ 2 := by
    rw [MeasureTheory.integral_const_mul]
  rw [hdiv]
  refine integral_mono_of_nonneg (Eventually.of_forall fun σ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (hgm.1 z hzI) ?_
  filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ hσ
  have hs : 0 < Real.sin (2 * σ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1]) (by linarith [hσ.2, Real.pi_pos])
  have hspos : 0 < (Real.sin (2 * σ)) ^ (eta / 2) := Real.rpow_pos_of_pos hs _
  have hkey : DzIter d g z σ * (w z / (Real.sin (2 * σ)) ^ (eta / 2))
        * (Real.sin (2 * σ)) ^ (eta / 2) = DzIter d g z σ * w z := by
    rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt hspos)]
  have hsq : ((Real.sin (2 * σ)) ^ (eta / 2)) ^ (2 : ℕ) = (Real.sin (2 * σ)) ^ eta := by
    rw [pow_two, ← Real.rpow_add hs]
    congr 1
    rw [eta]; ring
  calc (w z) ^ 2 * (DzIter d g z σ) ^ 2
      = (DzIter d g z σ * w z) ^ 2 := by ring
    _ = (DzIter d g z σ * (w z / (Real.sin (2 * σ)) ^ (eta / 2))
          * (Real.sin (2 * σ)) ^ (eta / 2)) ^ 2 := by rw [hkey]
    _ = (DzIter d g z σ * (w z / (Real.sin (2 * σ)) ^ (eta / 2))) ^ 2
          * (Real.sin (2 * σ)) ^ eta := by
        rw [mul_pow, hsq]
    _ ≤ (DzIter d g z σ * (w z / (Real.sin (2 * σ)) ^ (eta / 2))) ^ 2 * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        exact Real.rpow_le_one hs.le (Real.sin_le_one _) (by norm_num [eta])
    _ ≤ HkIntegrand α 4 g z σ := by
        rw [mul_one]
        exact sq_le_HkIntegrand_z α 4 g z σ d hd

/-- The angular slice of the majorant is integrable, for every `z ∈ Iz`. -/
theorem GmajW_integrableOn_theta {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hgm : HkMem α 4 g) {z : ℝ} (hz : z ∈ Iz) :
    IntegrableOn (fun θ => GmajW α g z θ) Iθ := by
  have h2 : IntegrableOn (fun θ => (HgInt α g z
      + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 4, Work.FTS.H2.WPQ.Aang α g d z) * TW α θ) Iθ :=
    (TW_integrable hα hα1).const_mul _
  refine Integrable.congr ((hgm.1 z hz).add h2) ?_
  filter_upwards with θ
  simp only [Pi.add_apply, GmajW]

/-- The angular integral of the majorant at a fixed radius, dominated by the mean term. -/
theorem GmajW_theta_integral_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hgm : HkMem α 4 g) {z : ℝ} (hz : z ∈ Iz) :
    (∫ θ in Iθ, GmajW α g z θ) ≤ (1 + 700 * (1 + 4 * (gam α - 1)⁻¹)) * HgInt α g z := by
  have hγ1 : (0 : ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
  have hγinv : 0 ≤ (gam α - 1)⁻¹ := inv_nonneg.mpr hγ1.le
  have hhg : IntegrableOn (fun θ => HkIntegrand α 4 g z θ) Iθ := hgm.1 z hz
  have hsum : ∑ d ∈ Finset.range 4, Work.FTS.H2.WPQ.Aang α g d z ≤ 4 * HgInt α g z :=
    sum_Aang_le_HgInt hgm hz
  have h2 : IntegrableOn (fun θ => (HgInt α g z
      + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 4, Work.FTS.H2.WPQ.Aang α g d z) * TW α θ) Iθ :=
    (TW_integrable hα hα1).const_mul _
  have hsplit : (∫ θ in Iθ, GmajW α g z θ)
      = HgInt α g z + (HgInt α g z
          + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 4, Work.FTS.H2.WPQ.Aang α g d z)
            * (∫ θ in Iθ, TW α θ) := by
    have hfun : (fun θ : ℝ => GmajW α g z θ)
        = fun θ : ℝ => HkIntegrand α 4 g z θ
            + (HgInt α g z + (gam α - 1)⁻¹
                * ∑ d ∈ Finset.range 4, Work.FTS.H2.WPQ.Aang α g d z) * TW α θ := by
      funext θ; rw [GmajW]
    rw [hfun, MeasureTheory.integral_add hhg h2, MeasureTheory.integral_const_mul]
    rfl
  rw [hsplit]
  have hT := TW_integral_le hα hα1
  have hTnn : 0 ≤ ∫ θ in Iθ, TW α θ :=
    setIntegral_nonneg measurableSet_Icc (fun θ hθ => TW_nonneg hα.le hθ)
  have hbr : HgInt α g z + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 4, Work.FTS.H2.WPQ.Aang α g d z
      ≤ HgInt α g z + (gam α - 1)⁻¹ * (4 * HgInt α g z) :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum hγinv)
  have hmain : (HgInt α g z + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 4,
        Work.FTS.H2.WPQ.Aang α g d z) * (∫ θ in Iθ, TW α θ)
      ≤ (HgInt α g z + (gam α - 1)⁻¹ * (4 * HgInt α g z)) * 700 :=
    mul_le_mul hbr hT hTnn
      (add_nonneg (HgInt_nonneg α g z) (mul_nonneg hγinv (mul_nonneg (by norm_num)
        (HgInt_nonneg α g z))))
  calc HgInt α g z + (HgInt α g z + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 4,
        Work.FTS.H2.WPQ.Aang α g d z) * (∫ θ in Iθ, TW α θ)
      ≤ HgInt α g z + (HgInt α g z + (gam α - 1)⁻¹ * (4 * HgInt α g z)) * 700 :=
        add_le_add le_rfl hmain
    _ = (1 + 700 * (1 + 4 * (gam α - 1)⁻¹)) * HgInt α g z := by ring


end Work.FTS.OpenPkg.WProdWin
end
end
-- ===== merged: Submission.Work.H2.T1Q.SlotPtQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.H2.T1Q

set_option autoImplicit false
set_option maxHeartbeats 800000

open Work.FTS.H2

/-- **The `D_z`-slot summand with a low-order `f`-factor.** -/
theorem xD_Kf_pt (α : ℝ) (hα : 0 < α) (f g : ℝ → ℝ → ℝ) (Kf : ℝ) (hKf0 : 0 ≤ Kf)
    (hKf : ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a f z θ| ≤ Kf)
    (i b : ℕ) (hi : i ≤ 4) (hbi : b ≤ i) (hib : i - b ≤ 3) (hb2 : b ≤ 2) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |xD f g i b z θ| ≤ (i.choose b : ℝ) * Kf *
        ((|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
          * (|Work.Spaces.DzIter i g z θ| * Whz z θ)) := by
  intro z θ hz hθ0 hθ1
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hF : |Work.Spaces.DzIter b f z θ| ≤ Kf := by
    have h := hKf b 0 (by omega) z θ hz hθ0 hθ1
    rwa [Work.Spaces.mixed_zero_right] at h
  have hWmnn : 0 ≤ Wm α z θ := Wm_nonneg α hθI
  have hWhznn : 0 ≤ Whz z θ := Whz_nonneg hθI
  have hch : 0 ≤ (i.choose b : ℝ) := by positivity
  have hkey : Whz z θ ^ 2 ≤ Wm α z θ * Whz z θ := Whz_sq_le_Wm_mul α hα hθI
  have hG1 : 0 ≤ |Work.Spaces.mixed (i - b) 1 g z θ| := abs_nonneg _
  have hG2 : 0 ≤ |Work.Spaces.DzIter i g z θ| := abs_nonneg _
  have hfacnn : 0 ≤ (|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
      * (|Work.Spaces.DzIter i g z θ| * Whz z θ) :=
    mul_nonneg (mul_nonneg hG1 hWmnn) (mul_nonneg hG2 hWhznn)
  have hstep : |Work.Spaces.DzIter b f z θ| * |Work.Spaces.mixed (i - b) 1 g z θ|
      * |Work.Spaces.DzIter i g z θ| * Whz z θ ^ 2
      ≤ Kf * ((|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
        * (|Work.Spaces.DzIter i g z θ| * Whz z θ)) := by
    have h1 : |Work.Spaces.DzIter b f z θ| * |Work.Spaces.mixed (i - b) 1 g z θ|
        * |Work.Spaces.DzIter i g z θ| * Whz z θ ^ 2
        ≤ |Work.Spaces.DzIter b f z θ| * |Work.Spaces.mixed (i - b) 1 g z θ|
          * |Work.Spaces.DzIter i g z θ| * (Wm α z θ * Whz z θ) :=
      mul_le_mul_of_nonneg_left hkey (by positivity)
    have h2 : |Work.Spaces.DzIter b f z θ|
          * (|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
          * (|Work.Spaces.DzIter i g z θ| * Whz z θ)
        = |Work.Spaces.DzIter b f z θ| * |Work.Spaces.mixed (i - b) 1 g z θ|
          * |Work.Spaces.DzIter i g z θ| * (Wm α z θ * Whz z θ) := by ring
    have h3 : |Work.Spaces.DzIter b f z θ|
          * (|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
          * (|Work.Spaces.DzIter i g z θ| * Whz z θ)
        ≤ Kf * ((|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
          * (|Work.Spaces.DzIter i g z θ| * Whz z θ)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right hF hfacnn
    calc |Work.Spaces.DzIter b f z θ| * |Work.Spaces.mixed (i - b) 1 g z θ|
          * |Work.Spaces.DzIter i g z θ| * Whz z θ ^ 2
        ≤ |Work.Spaces.DzIter b f z θ| * |Work.Spaces.mixed (i - b) 1 g z θ|
          * |Work.Spaces.DzIter i g z θ| * (Wm α z θ * Whz z θ) := h1
      _ = |Work.Spaces.DzIter b f z θ|
          * (|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
          * (|Work.Spaces.DzIter i g z θ| * Whz z θ) := h2.symm
      _ ≤ Kf * ((|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
          * (|Work.Spaces.DzIter i g z θ| * Whz z θ)) := h3
  calc |xD f g i b z θ|
      = (i.choose b : ℝ) * (|Work.Spaces.DzIter b f z θ|
          * |Work.Spaces.mixed (i - b) 1 g z θ| * |Work.Spaces.DzIter i g z θ|
          * Whz z θ ^ 2) := by
        simp only [xD, abs_mul, abs_of_nonneg hch, abs_of_nonneg (sq_nonneg (Whz z θ))] <;> ring
    _ ≤ (i.choose b : ℝ) * (Kf * ((|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
          * (|Work.Spaces.DzIter i g z θ| * Whz z θ))) :=
        mul_le_mul_of_nonneg_left hstep hch
    _ = (i.choose b : ℝ) * Kf *
        ((|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
          * (|Work.Spaces.DzIter i g z θ| * Whz z θ)) := by ring

/-- **The `D_z`-slot summand with a low-order `g`-factor.** -/
theorem xD_Kg_pt (α : ℝ) (hα : 0 < α) (f g : ℝ → ℝ → ℝ) (Kg : ℝ) (hKg0 : 0 ≤ Kg)
    (hKg : ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a g z θ| ≤ Kg)
    (i b : ℕ) (hi : i ≤ 4) (hbi : b ≤ i) (hb3 : 3 ≤ b) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |xD f g i b z θ| ≤ (i.choose b : ℝ) * Kg *
        ((|Work.Spaces.DzIter b f z θ| * Whz z θ)
          * (|Work.Spaces.DzIter i g z θ| * Whz z θ)) := by
  intro z θ hz hθ0 hθ1
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hG : |Work.Spaces.mixed (i - b) 1 g z θ| ≤ Kg :=
    hKg (i - b) 1 (by omega) z θ hz hθ0 hθ1
  have hWhznn : 0 ≤ Whz z θ := Whz_nonneg hθI
  have hch : 0 ≤ (i.choose b : ℝ) := by positivity
  have hG1 : 0 ≤ |Work.Spaces.DzIter b f z θ| := abs_nonneg _
  have hG2 : 0 ≤ |Work.Spaces.DzIter i g z θ| := abs_nonneg _
  have hfacnn : 0 ≤ (|Work.Spaces.DzIter b f z θ| * Whz z θ)
      * (|Work.Spaces.DzIter i g z θ| * Whz z θ) :=
    mul_nonneg (mul_nonneg hG1 hWhznn) (mul_nonneg hG2 hWhznn)
  have hstep : |Work.Spaces.DzIter b f z θ| * |Work.Spaces.mixed (i - b) 1 g z θ|
      * |Work.Spaces.DzIter i g z θ| * Whz z θ ^ 2
      ≤ Kg * ((|Work.Spaces.DzIter b f z θ| * Whz z θ)
        * (|Work.Spaces.DzIter i g z θ| * Whz z θ)) := by
    have h1 : |Work.Spaces.DzIter b f z θ| * |Work.Spaces.mixed (i - b) 1 g z θ|
        * |Work.Spaces.DzIter i g z θ| * Whz z θ ^ 2
        ≤ |Work.Spaces.DzIter b f z θ| * Kg
          * |Work.Spaces.DzIter i g z θ| * (Whz z θ * Whz z θ) := by
      have hmul : |Work.Spaces.DzIter b f z θ| * |Work.Spaces.mixed (i - b) 1 g z θ|
          * |Work.Spaces.DzIter i g z θ|
          ≤ |Work.Spaces.DzIter b f z θ| * Kg * |Work.Spaces.DzIter i g z θ| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG hG1) hG2
      calc |Work.Spaces.DzIter b f z θ| * |Work.Spaces.mixed (i - b) 1 g z θ|
            * |Work.Spaces.DzIter i g z θ| * Whz z θ ^ 2
          = (|Work.Spaces.DzIter b f z θ| * |Work.Spaces.mixed (i - b) 1 g z θ|
            * |Work.Spaces.DzIter i g z θ|) * (Whz z θ * Whz z θ) := by ring
        _ ≤ (|Work.Spaces.DzIter b f z θ| * Kg * |Work.Spaces.DzIter i g z θ|)
            * (Whz z θ * Whz z θ) :=
            mul_le_mul_of_nonneg_right hmul (mul_nonneg hWhznn hWhznn)
        _ = |Work.Spaces.DzIter b f z θ| * Kg
            * |Work.Spaces.DzIter i g z θ| * (Whz z θ * Whz z θ) := by ring
    have h2 : |Work.Spaces.DzIter b f z θ| * Kg * |Work.Spaces.DzIter i g z θ|
          * (Whz z θ * Whz z θ)
        = Kg * ((|Work.Spaces.DzIter b f z θ| * Whz z θ)
          * (|Work.Spaces.DzIter i g z θ| * Whz z θ)) := by ring
    rw [h2] at h1
    exact h1
  calc |xD f g i b z θ|
      = (i.choose b : ℝ) * (|Work.Spaces.DzIter b f z θ|
          * |Work.Spaces.mixed (i - b) 1 g z θ| * |Work.Spaces.DzIter i g z θ|
          * Whz z θ ^ 2) := by
        simp only [xD, abs_mul, abs_of_nonneg hch, abs_of_nonneg (sq_nonneg (Whz z θ))] <;> ring
    _ ≤ (i.choose b : ℝ) * (Kg * ((|Work.Spaces.DzIter b f z θ| * Whz z θ)
          * (|Work.Spaces.DzIter i g z θ| * Whz z θ))) :=
        mul_le_mul_of_nonneg_left hstep hch
    _ = (i.choose b : ℝ) * Kg *
        ((|Work.Spaces.DzIter b f z θ| * Whz z θ)
          * (|Work.Spaces.DzIter i g z θ| * Whz z θ)) := by ring

/-- **The mixed summand with a low-order `f`-factor.** -/
theorem yM_Kf_pt (α : ℝ) (f g : ℝ → ℝ → ℝ) (Kf : ℝ) (hKf0 : 0 ≤ Kf)
    (hKf : ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a f z θ| ≤ Kf)
    (i j a b : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) (hai : a ≤ i) (hbj : b ≤ j)
    (hab : a + b ≤ 2) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |yM α f g i j a b z θ| ≤ (i.choose a : ℝ) * (j.choose b : ℝ) * Kf *
        ((|Work.Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ)
          * (|Work.Spaces.mixed j i g z θ| * Wm α z θ)) := by
  intro z θ hz hθ0 hθ1
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hF : |Work.Spaces.mixed b a f z θ| ≤ Kf := hKf b a hab z θ hz hθ0 hθ1
  have hWmnn : 0 ≤ Wm α z θ := Wm_nonneg α hθI
  have hch : 0 ≤ (i.choose a : ℝ) * (j.choose b : ℝ) := by positivity
  have hG1 : 0 ≤ |Work.Spaces.mixed (j - b) (i - a + 1) g z θ| := abs_nonneg _
  have hG2 : 0 ≤ |Work.Spaces.mixed j i g z θ| := abs_nonneg _
  have hfacnn : 0 ≤ (|Work.Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ)
      * (|Work.Spaces.mixed j i g z θ| * Wm α z θ) :=
    mul_nonneg (mul_nonneg hG1 hWmnn) (mul_nonneg hG2 hWmnn)
  have hstep : |Work.Spaces.mixed b a f z θ| * |Work.Spaces.mixed (j - b) (i - a + 1) g z θ|
      * |Work.Spaces.mixed j i g z θ| * Wm α z θ ^ 2
      ≤ Kf * ((|Work.Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ)
        * (|Work.Spaces.mixed j i g z θ| * Wm α z θ)) := by
    have h1 : |Work.Spaces.mixed b a f z θ| * |Work.Spaces.mixed (j - b) (i - a + 1) g z θ|
        * |Work.Spaces.mixed j i g z θ| * Wm α z θ ^ 2
        = |Work.Spaces.mixed b a f z θ| * (|Work.Spaces.mixed (j - b) (i - a + 1) g z θ|
          * Wm α z θ) * (|Work.Spaces.mixed j i g z θ| * Wm α z θ) := by ring
    rw [h1, mul_assoc]
    exact mul_le_mul_of_nonneg_right hF hfacnn
  calc |yM α f g i j a b z θ|
      = ((i.choose a : ℝ) * (j.choose b : ℝ)) * (|Work.Spaces.mixed b a f z θ|
          * |Work.Spaces.mixed (j - b) (i - a + 1) g z θ|
          * |Work.Spaces.mixed j i g z θ| * Wm α z θ ^ 2) := by
        simp only [yM, abs_mul, abs_of_nonneg hch, abs_of_nonneg (sq_nonneg (Wm α z θ))] <;> ring
    _ ≤ ((i.choose a : ℝ) * (j.choose b : ℝ))
          * (Kf * ((|Work.Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ)
            * (|Work.Spaces.mixed j i g z θ| * Wm α z θ))) :=
        mul_le_mul_of_nonneg_left hstep hch
    _ = (i.choose a : ℝ) * (j.choose b : ℝ) * Kf *
        ((|Work.Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ)
          * (|Work.Spaces.mixed j i g z θ| * Wm α z θ)) := by ring

/-- **The mixed summand with a low-order `g`-factor and a mixed `f`-factor.** -/
theorem yM_Kg_mixed_pt (α : ℝ) (f g : ℝ → ℝ → ℝ) (Kg : ℝ) (hKg0 : 0 ≤ Kg)
    (hKg : ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a g z θ| ≤ Kg)
    (i j a b : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) (hai : a ≤ i) (hbj : b ≤ j)
    (ha1 : 1 ≤ a) (hab : 3 ≤ a + b) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |yM α f g i j a b z θ| ≤ (i.choose a : ℝ) * (j.choose b : ℝ) * Kg *
        ((|Work.Spaces.mixed b a f z θ| * Wm α z θ)
          * (|Work.Spaces.mixed j i g z θ| * Wm α z θ)) := by
  intro z θ hz hθ0 hθ1
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hG : |Work.Spaces.mixed (j - b) (i - a + 1) g z θ| ≤ Kg :=
    hKg (j - b) (i - a + 1) (by omega) z θ hz hθ0 hθ1
  have hWmnn : 0 ≤ Wm α z θ := Wm_nonneg α hθI
  have hch : 0 ≤ (i.choose a : ℝ) * (j.choose b : ℝ) := by positivity
  have hG1 : 0 ≤ |Work.Spaces.mixed b a f z θ| := abs_nonneg _
  have hG2 : 0 ≤ |Work.Spaces.mixed j i g z θ| := abs_nonneg _
  have hfacnn : 0 ≤ (|Work.Spaces.mixed b a f z θ| * Wm α z θ)
      * (|Work.Spaces.mixed j i g z θ| * Wm α z θ) :=
    mul_nonneg (mul_nonneg hG1 hWmnn) (mul_nonneg hG2 hWmnn)
  have hstep : |Work.Spaces.mixed b a f z θ| * |Work.Spaces.mixed (j - b) (i - a + 1) g z θ|
      * |Work.Spaces.mixed j i g z θ| * Wm α z θ ^ 2
      ≤ Kg * ((|Work.Spaces.mixed b a f z θ| * Wm α z θ)
        * (|Work.Spaces.mixed j i g z θ| * Wm α z θ)) := by
    have hmul : |Work.Spaces.mixed b a f z θ| * |Work.Spaces.mixed (j - b) (i - a + 1) g z θ|
        * |Work.Spaces.mixed j i g z θ| ≤ |Work.Spaces.mixed b a f z θ| * Kg
        * |Work.Spaces.mixed j i g z θ| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG hG1) hG2
    have h1 : |Work.Spaces.mixed b a f z θ| * |Work.Spaces.mixed (j - b) (i - a + 1) g z θ|
        * |Work.Spaces.mixed j i g z θ| * Wm α z θ ^ 2
        ≤ |Work.Spaces.mixed b a f z θ| * Kg * |Work.Spaces.mixed j i g z θ|
          * (Wm α z θ * Wm α z θ) := by
      calc |Work.Spaces.mixed b a f z θ| * |Work.Spaces.mixed (j - b) (i - a + 1) g z θ|
            * |Work.Spaces.mixed j i g z θ| * Wm α z θ ^ 2
          = (|Work.Spaces.mixed b a f z θ| * |Work.Spaces.mixed (j - b) (i - a + 1) g z θ|
            * |Work.Spaces.mixed j i g z θ|) * (Wm α z θ * Wm α z θ) := by ring
        _ ≤ (|Work.Spaces.mixed b a f z θ| * Kg * |Work.Spaces.mixed j i g z θ|)
            * (Wm α z θ * Wm α z θ) :=
            mul_le_mul_of_nonneg_right hmul (mul_nonneg hWmnn hWmnn)
        _ = |Work.Spaces.mixed b a f z θ| * Kg * |Work.Spaces.mixed j i g z θ|
            * (Wm α z θ * Wm α z θ) := by ring
    have h2 : |Work.Spaces.mixed b a f z θ| * Kg * |Work.Spaces.mixed j i g z θ|
          * (Wm α z θ * Wm α z θ)
        = Kg * ((|Work.Spaces.mixed b a f z θ| * Wm α z θ)
          * (|Work.Spaces.mixed j i g z θ| * Wm α z θ)) := by ring
    rw [h2] at h1
    exact h1
  calc |yM α f g i j a b z θ|
      = ((i.choose a : ℝ) * (j.choose b : ℝ)) * (|Work.Spaces.mixed b a f z θ|
          * |Work.Spaces.mixed (j - b) (i - a + 1) g z θ|
          * |Work.Spaces.mixed j i g z θ| * Wm α z θ ^ 2) := by
        simp only [yM, abs_mul, abs_of_nonneg hch, abs_of_nonneg (sq_nonneg (Wm α z θ))] <;> ring
    _ ≤ ((i.choose a : ℝ) * (j.choose b : ℝ))
          * (Kg * ((|Work.Spaces.mixed b a f z θ| * Wm α z θ)
            * (|Work.Spaces.mixed j i g z θ| * Wm α z θ))) :=
        mul_le_mul_of_nonneg_left hstep hch
    _ = (i.choose a : ℝ) * (j.choose b : ℝ) * Kg *
        ((|Work.Spaces.mixed b a f z θ| * Wm α z θ)
          * (|Work.Spaces.mixed j i g z θ| * Wm α z θ)) := by ring


/-! ## Boundedness of the `θ`-slice of `D_z³f` -/

/-- Almost every `θ ∈ Iθ` lies in the open interval `(0, π/2)`. -/
theorem ae_Iθ_mem_Ioo' : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (π / 2) := by
  have h : ∀ᵐ θ ∂(volume.restrict (Set.Icc (0 : ℝ) (π / 2))), θ ∈ Set.Ioo 0 (π / 2) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ (Set.Finite.measure_zero
      (by simp : ({0, π / 2} : Set ℝ).Finite) volume)
    intro θ hθ
    simp only [Set.mem_setOf_eq, not_imp, Set.mem_Icc] at hθ
    obtain ⟨hθI, hnot⟩ := hθ
    simp only [Set.mem_Ioo, Set.mem_insert_iff, Set.mem_singleton_iff] at hnot ⊢
    by_cases h0 : 0 < θ
    · right
      by_contra h2
      exact hnot ⟨h0, lt_of_le_of_ne hθI.2 h2⟩
    · left
      exact le_antisymm (not_lt.mp h0) hθI.1
  exact h



end Work.H2.T1Q
end
end
