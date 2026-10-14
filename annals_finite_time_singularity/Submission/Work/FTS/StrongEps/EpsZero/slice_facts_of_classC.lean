import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Tactic.MinImports
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.H2W.Ae.TruncIdentAe
import Submission.Work.FTS.EllipticEst.H2W.PsiSlices.PsiBox
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.Honest.I4UpperHonest
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.SliceAux
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.LocDataExt.Defs
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongPersist.N6.Swap6
import Submission.Work.FTS.Vocab
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2W.momentChainAe
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.SolutionDelivery.Slices
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.Cutoff
import Submission.Work.StabilityFar.Decay.KernelDefs
-- ===== merged: Submission.Work.Blocks.DzV_amgm_clean =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.EllipticEst
open Work.FTS.EllipticEst.Blocks
open Work.FTS.EllipticEst.DzAmgm

namespace Work.Blocks

namespace DzVamgm

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false

/-! ## The cut-off `logChi n`, extended by `0` on `(-∞,0]` -/

/-- `Work.FTS.EllipticEst.TT.logChi n`, extended by `0` on `(-∞,0]`.  This extension has
compact support in `(0,∞)`, which is the support hypothesis required by
`Work.FTS.EllipticEst.Blocks.AgmonIBP`; on `(0,∞)` it agrees with `logChi n`. -/
def logChiPos (n : ℕ) : ℝ → ℝ :=
  fun z => if 0 < z then Work.FTS.EllipticEst.TT.logChi n z else 0

theorem logChiPos_of_pos {n : ℕ} {z : ℝ} (hz : 0 < z) :
    logChiPos n z = Work.FTS.EllipticEst.TT.logChi n z := by
  simp only [logChiPos, if_pos hz]

theorem logChiPos_nonneg (n : ℕ) (z : ℝ) : 0 ≤ logChiPos n z := by
  by_cases hz : 0 < z
  · rw [logChiPos_of_pos hz]
    exact (Work.FTS.EllipticEst.TT.logChi_mem_Icc n z).1
  · simp only [logChiPos, if_neg hz, le_refl]

theorem logChiPos_le_one (n : ℕ) (z : ℝ) : logChiPos n z ≤ 1 := by
  by_cases hz : 0 < z
  · rw [logChiPos_of_pos hz]
    exact (Work.FTS.EllipticEst.TT.logChi_mem_Icc n z).2
  · simp only [logChiPos, if_neg hz]
    norm_num

theorem logChiPos_contDiffOn (n : ℕ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (logChiPos n) (Set.Ioi (0 : ℝ)) := by
  refine (contDiffOn_congr ?_).mpr (Work.FTS.EllipticEst.TT.logChi_contDiffOn n)
  intro z hz
  exact logChiPos_of_pos hz

/-- `logChiPos n` is supported in `[1/((n:ℝ)+2)², ((n:ℝ)+2)²] ⊆ (0,∞)`. -/
theorem logChiPos_eq_zero_off (n : ℕ) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ z : ℝ, z ∉ Set.Icc a b → logChiPos n z = 0 := by
  refine ⟨1 / ((n : ℝ) + 2) ^ 2, ((n : ℝ) + 2) ^ 2, ?_, ?_, ?_⟩
  · positivity
  · have h2 : (2 : ℝ) ≤ (n : ℝ) + 2 := Work.FTS.EllipticEst.TT.two_le_two_add_natCast n
    have h4 : (4 : ℝ) ≤ ((n : ℝ) + 2) ^ 2 := by nlinarith
    have hpos : (0 : ℝ) < ((n : ℝ) + 2) ^ 2 := by linarith
    rw [div_le_iff₀ hpos]
    nlinarith
  · intro z hz
    simp only [Set.mem_Icc, not_and_or, not_le] at hz
    rcases hz with h | h
    · by_cases hz0 : 0 < z
      · rw [logChiPos_of_pos hz0]
        exact Work.FTS.EllipticEst.TT.logChi_eq_zero_of_le hz0 (le_of_lt h)
      · simp only [logChiPos, if_neg hz0]
    · have hz0 : 0 < z := by
        have hb : (0 : ℝ) < ((n : ℝ) + 2) ^ 2 := by positivity
        linarith
      rw [logChiPos_of_pos hz0]
      exact Work.FTS.EllipticEst.TT.logChi_eq_zero_of_ge (le_of_lt h)

theorem deriv_logChiPos_eq {n : ℕ} {z : ℝ} (hz : 0 < z) :
    deriv (logChiPos n) z = deriv (Work.FTS.EllipticEst.TT.logChi n) z := by
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
  exact logChiPos_of_pos hy

theorem deriv_deriv_logChiPos_eq {n : ℕ} {z : ℝ} (hz : 0 < z) :
    deriv (deriv (logChiPos n)) z
      = deriv (deriv (Work.FTS.EllipticEst.TT.logChi n)) z := by
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
  exact deriv_logChiPos_eq hy

/-! ## The main assembly -/

/-- **The one-dimensional weighted Agmon--Nirenberg inequality for `C^∞` data, unconditional
`lintegral` form.**  This is `Work.EllipticEst.DzAgmonSmooth` (proved from the three pieces
above), used by `Work.EllipticEst.DzV_amgm_Hk`. -/
theorem DzAgmon1D_clean : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (h : ℝ → ℝ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ Work.Stability.smoothOrder h (Set.Ioi (0 : ℝ)) →
      ENNReal.ofReal (α ^ 2) *
          MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
            (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2))
        ≤ ENNReal.ofReal (C ^ 2) *
            (ENNReal.ofReal (α ^ 4) *
                MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                  (fun z => ENNReal.ofReal
                    ((Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2))
              + MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                  (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (h z) ^ 2))) := by
  refine ⟨100, by norm_num, ?_⟩
  intro α h hα hα1 hcd
  -- abbreviations, matching the goal syntactically
  set F : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2 with hF
  set H : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 * (h z) ^ 2 with hH
  set G : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2 with hG
  -- the two trivial cases
  by_cases hHtop : (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal (H z)) = ⊤
  · rw [hHtop, add_top, ENNReal.mul_top]
    · exact le_top
    · exact ne_of_gt (ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 100 ^ 2))
  by_cases hGtop : (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal (G z)) = ⊤
  · rw [hGtop, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hα 4))), top_add,
      ENNReal.mul_top]
    · exact le_top
    · exact ne_of_gt (ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 100 ^ 2))
  -- ### continuity of the data integrands
  have hw2cont : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) := by
    have h : (fun z : ℝ => (Work.Spaces.w z) ^ 2) = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by
      funext z; simp only [Work.Spaces.w]
    rw [h]
    refine ContinuousOn.pow (ContinuousOn.div ?_ ?_ ?_) 2
    · exact (continuousOn_const.add continuousOn_id).pow 2
    · exact continuousOn_id.pow 2
    · intro z hz; exact pow_ne_zero 2 (ne_of_gt hz)
  have hdh_smooth : ContDiffOn ℝ Work.Stability.smoothOrder (deriv h) (Set.Ioi (0 : ℝ)) :=
    hcd.deriv_of_isOpen isOpen_Ioi (by simp [Work.Stability.smoothOrder])
  have hdhcont : ContinuousOn (deriv h) (Set.Ioi (0 : ℝ)) := hdh_smooth.continuousOn
  have hd2h_smooth : ContDiffOn ℝ Work.Stability.smoothOrder (deriv (deriv h))
      (Set.Ioi (0 : ℝ)) :=
    hdh_smooth.deriv_of_isOpen isOpen_Ioi (by simp [Work.Stability.smoothOrder])
  have hd2hcont : ContinuousOn (deriv (deriv h)) (Set.Ioi (0 : ℝ)) := hd2h_smooth.continuousOn
  have hHcont : ContinuousOn H (Set.Ioi (0 : ℝ)) := by
    rw [hH]
    exact hw2cont.mul (hcd.continuousOn.pow 2)
  have hGcont : ContinuousOn G (Set.Ioi (0 : ℝ)) := by
    rw [hG]
    exact hw2cont.mul (((continuousOn_id.pow 2).mul hd2hcont).pow 2)
  have hFcont : ContinuousOn F (Set.Ioi (0 : ℝ)) := by
    rw [hF]
    exact hw2cont.mul ((continuousOn_id.mul hdhcont).pow 2)
  -- ### integrability of the data
  have hHmeas : AEStronglyMeasurable H (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    hHcont.aestronglyMeasurable measurableSet_Ioi
  have hGmeas : AEStronglyMeasurable G (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    hGcont.aestronglyMeasurable measurableSet_Ioi
  have hFmeas : AEMeasurable F (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    hFcont.aemeasurable measurableSet_Ioi
  have hHnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))] H :=
    Filter.Eventually.of_forall fun z => by
      rw [hH]; exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hGnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))] G :=
    Filter.Eventually.of_forall fun z => by
      rw [hG]; exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hFnn : ∀ z : ℝ, 0 ≤ F z := fun z => by
    rw [hF]; exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hHint : IntegrableOn H (Set.Ioi (0 : ℝ)) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hHmeas hHnn).mp hHtop
  have hGint : IntegrableOn G (Set.Ioi (0 : ℝ)) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hGmeas hGnn).mp hGtop
  -- the `ofReal` bridges
  have hbridgeH : (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal (H z))
      = ENNReal.ofReal (∫ z in Set.Ioi (0 : ℝ), H z) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hHint hHnn).symm
  have hbridgeG : (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal (G z))
      = ENNReal.ofReal (∫ z in Set.Ioi (0 : ℝ), G z) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hGint hGnn).symm
  have hpnn : (0 : ℝ) ≤ ∫ z in Set.Ioi (0 : ℝ), H z :=
    integral_nonneg fun z => by rw [hH]; exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hqnn : (0 : ℝ) ≤ ∫ z in Set.Ioi (0 : ℝ), G z :=
    integral_nonneg fun z => by rw [hG]; exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  -- ### integrability of `F · logChi n²`
  obtain ⟨Kw, hKw0, -, hKw, -, -⟩ := Work.FTS.EllipticEst.Blocks.logChiFamily
  have hFint : ∀ n : ℕ, IntegrableOn
      (fun z : ℝ => F z * (Work.FTS.EllipticEst.TT.logChi n z) ^ 2) (Set.Ioi (0 : ℝ)) := by
    intro n
    obtain ⟨a, b, ha, hab, hsupp⟩ := logChiPos_eq_zero_off n
    set g : ℝ → ℝ := fun z => h z * logChiPos n z with hg
    have hgcd : ContDiffOn ℝ Work.Stability.smoothOrder g (Set.Ioi (0 : ℝ)) := by
      rw [hg]
      exact hcd.mul (logChiPos_contDiffOn n)
    have hgsupp : ∀ z : ℝ, z ∉ Set.Icc a b → g z = 0 := by
      intro z hz
      rw [hg]
      simp only [hsupp z hz, mul_zero]
    obtain ⟨hgd_left, hgd_right, -, -⟩ :=
      Work.FTS.EllipticEst.Blocks.AgmonDerivVanishing hgsupp
    have hsub : ∀ z ∈ Set.Icc a b, (0 : ℝ) < z := fun z hz => lt_of_lt_of_le ha hz.1
    have hdom_int : IntegrableOn
        (fun z : ℝ => 2 * ((Work.Spaces.w z) ^ 2 * (z * deriv g z) ^ 2)
          + 2 * Kw ^ 2 * H z) (Set.Ioi (0 : ℝ)) := by
      refine IntegrableOn.add ?_ (hHint.const_mul _)
      refine Work.FTS.EllipticEst.Blocks.integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off
        (a := a) (b := b) ?_ ?_
      · refine ContinuousOn.mul continuousOn_const ?_
        have hgd_smooth : ContDiffOn ℝ Work.Stability.smoothOrder (deriv g) (Set.Ioi (0 : ℝ)) :=
          hgcd.deriv_of_isOpen isOpen_Ioi (by simp [Work.Stability.smoothOrder])
        have hgd_cont : ContinuousOn (deriv g) (Set.Icc a b) :=
          hgd_smooth.continuousOn.mono (fun z hz => hsub z hz)
        have hw2_cont : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Icc a b) :=
          hw2cont.mono (fun z hz => hsub z hz)
        exact ContinuousOn.mul hw2_cont
          (ContinuousOn.pow (ContinuousOn.mul continuousOn_id hgd_cont) 2)
      · intro z hz
        rcases (by
          simpa only [Set.mem_Icc, not_and_or, not_le] using hz : z < a ∨ b < z) with h' | h'
        · rw [hgd_left z h']; ring
        · rw [hgd_right z h']; ring
    have hpt : ∀ z ∈ Set.Ioi (0 : ℝ),
        ‖F z * (Work.FTS.EllipticEst.TT.logChi n z) ^ 2‖
          ≤ 2 * ((Work.Spaces.w z) ^ 2 * (z * deriv g z) ^ 2) + 2 * Kw ^ 2 * H z := by
      intro z hz
      have hχ : Work.FTS.EllipticEst.TT.logChi n z = logChiPos n z :=
        (logChiPos_of_pos hz).symm
      have hdh : DifferentiableAt ℝ h z :=
        (hcd.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hz)
      have hdχ : DifferentiableAt ℝ (logChiPos n) z :=
        ((logChiPos_contDiffOn n).differentiableOn (by simp)).differentiableAt
          (isOpen_Ioi.mem_nhds hz)
      have hgderiv : deriv g z
          = deriv h z * logChiPos n z + h z * deriv (logChiPos n) z := by
        rw [hg]
        exact deriv_mul hdh hdχ
      have hkey : z * deriv h z * logChiPos n z
          = z * deriv g z - z * h z * deriv (logChiPos n) z := by
        rw [hgderiv]; ring
      have hb2 : (z * deriv (logChiPos n) z) ^ 2 ≤ Kw ^ 2 := by
        have h := hKw n z hz
        rw [← deriv_logChiPos_eq hz] at h
        calc (z * deriv (logChiPos n) z) ^ 2 = |z * deriv (logChiPos n) z| ^ 2 :=
              (sq_abs _).symm
          _ ≤ Kw ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      have hsq : (z * deriv h z * logChiPos n z) ^ 2
          ≤ 2 * (z * deriv g z) ^ 2 + 2 * Kw ^ 2 * (h z) ^ 2 := by
        have h2 : (z * h z * deriv (logChiPos n) z) ^ 2 ≤ Kw ^ 2 * (h z) ^ 2 := by
          have h3 : (z * h z * deriv (logChiPos n) z) ^ 2
              = (h z) ^ 2 * (z * deriv (logChiPos n) z) ^ 2 := by ring
          rw [h3]
          nlinarith [hb2, sq_nonneg (h z)]
        have h1 : ∀ u v : ℝ, (u - v) ^ 2 ≤ 2 * u ^ 2 + 2 * v ^ 2 := by
          intro u v; nlinarith [sq_nonneg (u + v)]
        calc (z * deriv h z * logChiPos n z) ^ 2
            = (z * deriv g z - z * h z * deriv (logChiPos n) z) ^ 2 := by rw [hkey]
          _ ≤ 2 * (z * deriv g z) ^ 2 + 2 * (z * h z * deriv (logChiPos n) z) ^ 2 := h1 _ _
          _ ≤ 2 * (z * deriv g z) ^ 2 + 2 * (Kw ^ 2 * (h z) ^ 2) := by linarith
          _ = 2 * (z * deriv g z) ^ 2 + 2 * Kw ^ 2 * (h z) ^ 2 := by ring
      rw [Real.norm_eq_abs, hχ, hF, hH]
      rw [abs_of_nonneg (by
        refine mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))]
      have hw2 : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      have h4 : (z * deriv h z * logChiPos n z) ^ 2
          = (z * deriv h z) ^ 2 * (logChiPos n z) ^ 2 := by ring
      nlinarith [hsq, hw2, sq_nonneg (Work.Spaces.w z), sq_nonneg (z * deriv h z),
        sq_nonneg (logChiPos n z)]
    refine Integrable.mono' hdom_int
      ((hFcont.mul ((Work.FTS.EllipticEst.TT.logChi_contDiffOn n).continuousOn.pow 2))
        |>.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
    exact hpt z hz
  -- ### the estimate, for `n` large
  obtain ⟨N₁, hN₁⟩ := Work.FTS.EllipticEst.Blocks.AgmonSmallness
  obtain ⟨K₂, hK₂pos, hK₂⟩ := Work.EllipticEst.logChi_second_deriv_le
  have hlogtop : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_mono (fun n : ℕ => by
      have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith) tendsto_natCast_atTop_atTop)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hlogtop.eventually_ge_atTop K₂)
  set N₀ : ℕ := max N₁ N₂ with hN₀
  have hest : ∀ n : ℕ, N₀ ≤ n → α ^ 2 *
      (∫ z in Set.Ioi (0 : ℝ), F z * (Work.FTS.EllipticEst.TT.logChi n z) ^ 2)
      ≤ 100 * ((∫ z in Set.Ioi (0 : ℝ), H z)
          + α ^ 4 * (∫ z in Set.Ioi (0 : ℝ), G z)) := by
    intro n hn
    have hn₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
    have hn₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
    have hder1 : ∀ z : ℝ, 0 < z → |z * deriv (logChiPos n) z| ≤ 1 / 8 := by
      intro z hz
      rw [deriv_logChiPos_eq hz]
      exact hN₁ n hn₁ z hz
    have hder2 : ∀ z : ℝ, 0 < z → |z ^ 2 * deriv (deriv (logChiPos n)) z| ≤ 1 := by
      intro z hz
      have hle : |z ^ 2 * deriv (deriv (Work.FTS.EllipticEst.TT.logChi n)) z|
          ≤ K₂ / Real.log ((n : ℝ) + 2) := hK₂ n z hz
      rw [deriv_deriv_logChiPos_eq hz]
      have hlog : K₂ ≤ Real.log ((n : ℝ) + 2) := hN₂ n hn₂
      have hpos : 0 < Real.log ((n : ℝ) + 2) :=
        Work.FTS.EllipticEst.TT.log_two_add_natCast_pos n
      have hle1 : K₂ / Real.log ((n : ℝ) + 2) ≤ 1 := by
        rw [div_le_one hpos]
        exact hlog
      exact le_trans hle hle1
    have hag := Work.EllipticEst.agmon_cutoff_estimate (logChiPos n) 1 (by norm_num) (by norm_num)
      (logChiPos_contDiffOn n) (logChiPos_nonneg n) (logChiPos_le_one n) hder1 hder2
      (logChiPos_eq_zero_off n) α hα hα1 h hcd hHint hGint
    -- replace `logChiPos` by `logChi` inside the integral (they agree on `(0,∞)`)
    have hcongr : (∫ z in Set.Ioi (0 : ℝ),
          Work.FTS.EllipticEst.Blocks.W2 z * (z * deriv h z) ^ 2 * (logChiPos n z) ^ 2)
        = ∫ z in Set.Ioi (0 : ℝ),
            F z * (Work.FTS.EllipticEst.TT.logChi n z) ^ 2 := by
      refine integral_congr_ae ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
      rw [logChiPos_of_pos hz]
      simp only [hF, Work.FTS.EllipticEst.Blocks.W2]
    rw [hcongr] at hag
    have hpH : (∫ z in Set.Ioi (0 : ℝ), Work.FTS.EllipticEst.Blocks.W2 z * h z ^ 2)
        = ∫ z in Set.Ioi (0 : ℝ), H z := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [hH, Work.FTS.EllipticEst.Blocks.W2]
    have hqG : (∫ z in Set.Ioi (0 : ℝ),
          Work.FTS.EllipticEst.Blocks.W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2)
        = ∫ z in Set.Ioi (0 : ℝ), G z := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [hG, Work.FTS.EllipticEst.Blocks.W2]
    rwa [hpH, hqG] at hag
  -- ### monotonicity in `n`
  have hmono : Monotone fun n : ℕ =>
      ∫ z in Set.Ioi (0 : ℝ), F z * (Work.FTS.EllipticEst.TT.logChi n z) ^ 2 := by
    intro m n hmn
    refine MeasureTheory.integral_mono_ae (hFint m) (hFint n) ?_
    filter_upwards with z
    have hle : Work.FTS.EllipticEst.TT.logChi m z ≤ Work.FTS.EllipticEst.TT.logChi n z :=
      monotone_nat_of_le_succ (fun k => Work.FTS.EllipticEst.Blocks.logChi_mono_succ k z) hmn
    have h0 : 0 ≤ Work.FTS.EllipticEst.TT.logChi m z :=
      (Work.FTS.EllipticEst.TT.logChi_mem_Icc m z).1
    have h1 : 0 ≤ Work.FTS.EllipticEst.TT.logChi n z :=
      (Work.FTS.EllipticEst.TT.logChi_mem_Icc n z).1
    have hsq : (Work.FTS.EllipticEst.TT.logChi m z) ^ 2
        ≤ (Work.FTS.EllipticEst.TT.logChi n z) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left hsq (hFnn z)
  -- ### monotone convergence and conclusion
  have hmct := Work.EllipticEst.logChi_iSup_lintegral F hFnn hFmeas hFint
  rw [hmct, ENNReal.mul_iSup]
  refine iSup_le fun n => ?_
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ α ^ 2)]
  have hbound : α ^ 2 * (∫ z in Set.Ioi (0 : ℝ),
      F z * (Work.FTS.EllipticEst.TT.logChi n z) ^ 2)
      ≤ 100 * ((∫ z in Set.Ioi (0 : ℝ), H z) + α ^ 4 * (∫ z in Set.Ioi (0 : ℝ), G z)) := by
    by_cases hn : n < N₀
    · exact le_trans (mul_le_mul_of_nonneg_left (hmono (le_of_lt hn)) (by positivity))
        (hest N₀ le_rfl)
    · exact hest n (not_lt.mp hn)
  refine le_trans (ENNReal.ofReal_le_ofReal hbound) ?_
  rw [hbridgeG, hbridgeH]
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ α ^ 4),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 100 ^ 2)]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [hpnn, hqnn, (by positivity : (0 : ℝ) ≤ α ^ 4)]

end

end DzVamgm

namespace DzVamgm

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.EllipticEst.DzAmgm

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The angular weights as squares -/

theorem angZ_sq {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : (angZ θ) ^ 2 = sEta θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  rw [angZ, sEta, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hs]
  norm_num

theorem angM_sq (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : (angM α θ) ^ 2 = sGam α θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  rw [angM, sGam, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hs]
  norm_num

/-! ## The termwise Agmon estimate (adapted from `DzAmgm.Scratch`) -/

/-- **Termwise AM–GM, pure summands.**  Applying `TermAMGMLintegral` with `V = D_z^m f`,
`wth = angZ` and rewriting `D_z (D_z^m f) = D_z^{m+1} f`,
`z²∂_z²(D_z^m f) = D_z^m (z²∂_z²f)` (`ZsqPz2Comm`) gives the termwise estimate for `TZ`. -/
theorem TZ_termwise (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2)))) :
    ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (f : ℝ → ℝ → ℝ), SmoothOpen f → ∀ (m : ℕ),
      ENNReal.ofReal (α ^ 2) * TZ f (m + 1)
        ≤ ENNReal.ofReal (C1 ^ 2) *
            (ENNReal.ofReal (α ^ 4) * TZ (zsqPz2 f) m + TZ f m) := by
  intro α hα hα1 f hf m
  have hang : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ angZ θ := fun θ hθ =>
    angZ_nonneg_of_mem (by rw [Work.Spaces.Iθ]; exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have h := hgen α hα hα1 (Work.Spaces.DzIter m f) angZ (hf.DzIter m) hang
  -- the first factor of the left-hand integrand
  have hL : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.Dz (Work.Spaces.DzIter m f) z θ * Work.Spaces.w z
          * angZ θ) ^ 2))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.DzIter (m + 1) f z θ * Work.Spaces.w z * angZ θ) ^ 2) := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    rw [Work.Spaces.DzIter_succ]
  -- the second-derivative factor of the right-hand side
  have hR2 : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z θ
          * Work.Spaces.w z * angZ θ) ^ 2))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.DzIter m (zsqPz2 f) z θ * Work.Spaces.w z * angZ θ) ^ 2) := by
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have hcomm := AgmonSlice.zsq_pzIter2_mixed_open f ((smoothOpen_iff_forall f).mp hf) m 0 hz hθ
    have h1 : z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z θ
        = Work.Spaces.DzIter m (zsqPz2 f) z θ := hcomm
    rw [h1]
  rw [hL, hR2] at h
  rw [lintegral_open_eq_prod] at h
  rw [lintegral_open_eq_prod] at h
  rw [lintegral_open_eq_prod] at h
  exact h

/-- **Termwise AM–GM, mixed summands.**  Applying `TermAMGMLintegral` with
`V = D_z^j D_θ^i f`, `wth = angM α` and rewriting `D_z (D_z^j D_θ^i f) = D_z^{j+1} D_θ^i f`,
`z²∂_z²(D_z^j D_θ^i f) = D_z^j D_θ^i (z²∂_z²f)` (`ZsqPz2Comm`) gives the termwise estimate. -/
theorem TM_termwise (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2)))) :
    ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (f : ℝ → ℝ → ℝ), SmoothOpen f → ∀ (i j : ℕ),
      ENNReal.ofReal (α ^ 2) * TM α f i (j + 1)
        ≤ ENNReal.ofReal (C1 ^ 2) *
            (ENNReal.ofReal (α ^ 4) * TM α (zsqPz2 f) i j + TM α f i j) := by
  intro α hα hα1 f hf i j
  have hang : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ angM α θ := fun θ hθ =>
    angM_nonneg_of_mem (by rw [Work.Spaces.Iθ]; exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have h := hgen α hα hα1 (Work.Spaces.mixed j i f) (angM α) (hf.mixed j i) hang
  have hL : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.Dz (Work.Spaces.mixed j i f) z θ * Work.Spaces.w z
          * angM α θ) ^ 2))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.mixed (j + 1) i f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    have hdz : Work.Spaces.Dz (Work.Spaces.mixed j i f)
        = Work.Spaces.mixed (j + 1) i f := by
      simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ]
    rw [hdz]
    exact mixed_ofReal_eq α f i (j + 1) z θ
  have hR2 : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.mixed j i f) z θ
          * Work.Spaces.w z * angM α θ) ^ 2))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.mixed j i (zsqPz2 f) z θ * Work.Spaces.Wt α z θ) ^ 2) := by
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have hcomm := AgmonSlice.zsq_pzIter2_mixed_open f ((smoothOpen_iff_forall f).mp hf) j i hz hθ
    have h1 : z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.mixed j i f) z θ
        = Work.Spaces.mixed j i (zsqPz2 f) z θ := hcomm
    rw [h1, mixed_ofReal_eq α (zsqPz2 f) i j z θ]
  have hR3 : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.mixed j i f z θ * Work.Spaces.w z * angM α θ) ^ 2))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact mixed_ofReal_eq α f i j z θ
  rw [hL, hR2, hR3] at h
  rw [lintegral_open_eq_prod] at h
  rw [lintegral_open_eq_prod] at h
  rw [lintegral_open_eq_prod] at h
  exact h



/-! ## The `LkSq` inequality -/

/-- **The `θ`-integrated radial interpolation for `D_z f`, at the level of the honest
`lintegral`s.** -/
theorem LkSq_Dz_le (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2)))) :
    ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (k : ℕ) (f : ℝ → ℝ → ℝ),
      (∀ (a : ℕ) (z θ : ℝ), (z, θ) ∈ Q0 →
        Work.Spaces.DthIter a (Work.Spaces.Dz f) z θ
          = Work.Spaces.Dz (Work.Spaces.DthIter a f) z θ) →
      SmoothOpen f →
      ENNReal.ofReal (α ^ 2) * LkSq α k (Work.Spaces.Dz f)
        ≤ ENNReal.ofReal (C1 ^ 2) *
            (ENNReal.ofReal (α ^ 4) * LkSq α k (zsqPz2 f) + LkSq α k f) := by
  intro α hα hα1 k f hcomm hf
  have hDz : SmoothOpen (Work.Spaces.Dz f) := hf.Dz
  have hQ : SmoothOpen (zsqPz2 f) := SmoothOpen_zsqPz2 f hf
  have hdec : LkSq α k (Work.Spaces.Dz f)
      = (∑ i ∈ Finset.range (k + 1), TZ f (i + 1))
        + ∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α f p.1 (p.2 + 1) else 0) := by
    rw [LkSq_eq_sum α k (Work.Spaces.Dz f) hDz]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => TZ_Dz f i
    · refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
      · rw [if_pos hc, if_pos hc, TM_Dz_of_comm α f hcomm p.1 p.2]
      · rw [if_neg hc, if_neg hc]
  have hdecQ : LkSq α k (zsqPz2 f)
      = (∑ i ∈ Finset.range (k + 1), TZ (zsqPz2 f) i)
        + ∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α (zsqPz2 f) p.1 p.2 else 0) :=
    LkSq_eq_sum α k (zsqPz2 f) hQ
  have hdecf : LkSq α k f
      = (∑ i ∈ Finset.range (k + 1), TZ f i)
        + ∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α f p.1 p.2 else 0) :=
    LkSq_eq_sum α k f hf
  -- the termwise bounds
  have hT : ∀ i ∈ Finset.range (k + 1), ENNReal.ofReal (α ^ 2) * TZ f (i + 1)
      ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * TZ (zsqPz2 f) i + TZ f i) :=
    fun i _ => TZ_termwise C1 hC1 hgen α hα hα1 f hf i
  have hM : ∀ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
      (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then ENNReal.ofReal (α ^ 2) * TM α f p.1 (p.2 + 1) else 0)
        ≤ ENNReal.ofReal (C1 ^ 2) *
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then
              ENNReal.ofReal (α ^ 4) * TM α (zsqPz2 f) p.1 p.2 + TM α f p.1 p.2 else 0) := by
    intro p _
    by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
    · rw [if_pos hc, if_pos hc]
      exact TM_termwise C1 hC1 hgen α hα hα1 f hf p.1 p.2
    · rw [if_neg hc, if_neg hc, mul_zero]
  -- the two sums
  have hS1le : ENNReal.ofReal (α ^ 2) * (∑ i ∈ Finset.range (k + 1), TZ f (i + 1))
      ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∑ i ∈ Finset.range (k + 1), TZ (zsqPz2 f) i)
            + (∑ i ∈ Finset.range (k + 1), TZ f i)) := by
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum hT) (le_of_eq ?_)
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.mul_sum]
  have hS2le : ENNReal.ofReal (α ^ 2)
        * (∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α f p.1 (p.2 + 1) else 0))
      ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4)
              * (∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
                  (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α (zsqPz2 f) p.1 p.2 else 0))
            + (∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
                  (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α f p.1 p.2 else 0))) := by
    rw [Finset.mul_sum]
    have hstep : (∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
          ENNReal.ofReal (α ^ 2) *
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α f p.1 (p.2 + 1) else 0))
        = ∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
              then ENNReal.ofReal (α ^ 2) * TM α f p.1 (p.2 + 1) else 0) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
      · rw [if_pos hc, if_pos hc]
      · rw [if_neg hc, if_neg hc, mul_zero]
    rw [hstep]
    refine le_trans (Finset.sum_le_sum hM) (le_of_eq ?_)
    have hflat : ∀ p : ℕ × ℕ,
        ENNReal.ofReal (C1 ^ 2) * (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then
            ENNReal.ofReal (α ^ 4) * TM α (zsqPz2 f) p.1 p.2 + TM α f p.1 p.2 else 0)
          = (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then ENNReal.ofReal (C1 ^ 2) *
                (ENNReal.ofReal (α ^ 4) * TM α (zsqPz2 f) p.1 p.2 + TM α f p.1 p.2)
              else 0) := by
      intro p; by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ k <;> simp [hc]
    rw [Finset.sum_congr rfl (fun p _ => hflat p)]
    rw [sum_ite_mul_split (k := k) (ENNReal.ofReal (C1 ^ 2)) (ENNReal.ofReal (α ^ 4))
      (fun p => TM α (zsqPz2 f) p.1 p.2) (fun p => TM α f p.1 p.2)]
    rw [mul_add]
    ring
  -- combine
  rw [hdec, mul_add]
  refine le_trans (add_le_add hS1le hS2le) (le_of_eq ?_)
  rw [hdecQ, hdecf]
  ring

/-- Finiteness of `LkSq (D_z f)` from the `LkSq` inequality. -/
theorem LkSq_Dz_lt_top (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2))))
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f)
    (hmf : Work.Spaces.HkMem α k f) (hmQ : Work.Spaces.HkMem α k (zsqPz2 f)) :
    LkSq α k (Work.Spaces.Dz f) < ⊤ := by
  have hQfin : LkSq α k (zsqPz2 f) < ⊤ := LkSq_lt_top α k _ (SmoothOpen_zsqPz2 f hf) hmQ
  have hffin : LkSq α k f < ⊤ := LkSq_lt_top α k f hf hmf
  have h := LkSq_Dz_le C1 hC1 hgen α hα hα1 k f (comm_hyp f hf) hf
  have hfin : ENNReal.ofReal (C1 ^ 2) *
      (ENNReal.ofReal (α ^ 4) * LkSq α k (zsqPz2 f) + LkSq α k f) < ⊤ := by
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hQfin, hffin⟩
  have hlt : ENNReal.ofReal (α ^ 2) * LkSq α k (Work.Spaces.Dz f) < ⊤ := lt_of_le_of_lt h hfin
  have hpos : ENNReal.ofReal (α ^ 2) ≠ 0 := by
    simpa using (ENNReal.ofReal_pos.mpr (by positivity : (0 : ℝ) < α ^ 2)).ne'
  rcases ENNReal.mul_lt_top_iff.mp hlt with ⟨-, h2⟩ | h0 | h0
  · exact h2
  · exact absurd h0 hpos
  · exact lt_top_iff_ne_top.mpr (by simp [h0])

/-- **The norm inequality**, given the honesty of `D_z f`. -/
theorem HkNorm_Dz_le_of (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2))))
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f)
    (hmf : Work.Spaces.HkMem α k f) (hmQ : Work.Spaces.HkMem α k (zsqPz2 f))
    (hmDz : Work.Spaces.HkMem α k (Work.Spaces.Dz f)) :
    α * Work.Spaces.HkNorm α k (Work.Spaces.Dz f)
      ≤ C1 * (Work.Spaces.HkNorm α k f + α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f)) := by
  have hDzSm : SmoothOpen (Work.Spaces.Dz f) := hf.Dz
  have hQSm : SmoothOpen (zsqPz2 f) := SmoothOpen_zsqPz2 f hf
  have hDzfin := LkSq_Dz_lt_top C1 hC1 hgen α hα hα1 k f hf hmf hmQ
  have hQfin : LkSq α k (zsqPz2 f) < ⊤ := LkSq_lt_top α k _ hQSm hmQ
  have hffin : LkSq α k f < ⊤ := LkSq_lt_top α k f hf hmf
  -- (★) in terms of `HkSq`
  have h := LkSq_Dz_le C1 hC1 hgen α hα hα1 k f (comm_hyp f hf) hf
  rw [LkSq_eq_ofReal_HkSq α k (Work.Spaces.Dz f) hDzSm hmDz,
    LkSq_eq_ofReal_HkSq α k (zsqPz2 f) hQSm hmQ,
    LkSq_eq_ofReal_HkSq α k f hf hmf] at h
  have hnn : 0 ≤ Work.Spaces.HkSq α k (Work.Spaces.Dz f) :=
    Work.Spaces.HkSq_nonneg α k _
  have hnnQ : 0 ≤ Work.Spaces.HkSq α k (zsqPz2 f) := Work.Spaces.HkSq_nonneg α k _
  have hnnf : 0 ≤ Work.Spaces.HkSq α k f := Work.Spaces.HkSq_nonneg α k f
  have hL : ENNReal.ofReal (α ^ 2) * ENNReal.ofReal (Work.Spaces.HkSq α k (Work.Spaces.Dz f))
      = ENNReal.ofReal (α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz f)) := by
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ α ^ 2)]
  have hR : ENNReal.ofReal (C1 ^ 2) * (ENNReal.ofReal (α ^ 4) *
        ENNReal.ofReal (Work.Spaces.HkSq α k (zsqPz2 f)) + ENNReal.ofReal (Work.Spaces.HkSq α k f))
      = ENNReal.ofReal (C1 ^ 2 * (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f)
          + Work.Spaces.HkSq α k f)) := by
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ C1 ^ 2),
      ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f)) hnnf,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ α ^ 4)]
  rw [hL, hR] at h
  have hsq : α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz f)
      ≤ C1 ^ 2 * (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  -- take square roots
  have hsqrt : α * Real.sqrt (Work.Spaces.HkSq α k (Work.Spaces.Dz f))
      ≤ C1 * Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f) := by
    have h1 : α * Real.sqrt (Work.Spaces.HkSq α k (Work.Spaces.Dz f))
        = Real.sqrt (α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz f)) := by
      rw [Real.sqrt_mul (sq_nonneg α), Real.sqrt_sq hα.le]
    have h2 : C1 * Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f)
        = Real.sqrt (C1 ^ 2 * (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f)
            + Work.Spaces.HkSq α k f)) := by
      rw [Real.sqrt_mul (sq_nonneg C1), Real.sqrt_sq hC1.le]
    rw [h1, h2]
    exact Real.sqrt_le_sqrt hsq
  have hf1 : Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f))
      = α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ α ^ 4), Work.Spaces.HkNorm,
      show Real.sqrt (α ^ 4) = α ^ 2 by
        rw [show α ^ 4 = (α ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity : (0 : ℝ) ≤ α ^ 2)]]
  have hadd : Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f)
      ≤ α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f) + Work.Spaces.HkNorm α k f := by
    calc Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f)
        ≤ Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f))
          + Real.sqrt (Work.Spaces.HkSq α k f) :=
          sqrt_add_le_sqrt _ _ (by positivity) (Work.Spaces.HkSq_nonneg α k f)
      _ = α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f) + Work.Spaces.HkNorm α k f := by
          rw [hf1]
          rfl
  calc α * Real.sqrt (Work.Spaces.HkSq α k (Work.Spaces.Dz f))
      ≤ C1 * Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f) := hsqrt
    _ ≤ C1 * (α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f) + Work.Spaces.HkNorm α k f) :=
        mul_le_mul_of_nonneg_left hadd (le_of_lt hC1)
    _ = C1 * (Work.Spaces.HkNorm α k f + α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f)) := by ring


/-! ## The honesty certificate `HkMem α k (D_z f)` -/

section Cert

/-- `D_z` commutes with the iterates `D_z^m` on the left: `D_z^m (D_z f) = D_z (D_z^m f)`. -/
theorem DzIter_Dz_eq (m : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter m (Work.Spaces.Dz f) = Work.Spaces.Dz (Work.Spaces.DzIter m f) := by
  have h1 : Work.Spaces.Dz f = Work.Spaces.DzIter 1 f := rfl
  rw [h1, ← Work.Spaces.DzIter_add_right m 1 f,
    show m + 1 = 1 + m from by omega, Work.Spaces.DzIter_add_right 1 m f]
  rfl

theorem angw_zero (α : ℝ) (θ : ℝ) : angw α 0 θ = sEta θ := by simp [angw]

theorem angw_pos (α : ℝ) {i : ℕ} (hi : 1 ≤ i) (θ : ℝ) : angw α i θ = sGam α θ := by
  simp only [angw]
  rw [if_neg (by omega)]

theorem measurable_angZ : Measurable angZ := by
  have h : angZ = fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) := rfl
  rw [h]; fun_prop

theorem measurable_angM (α : ℝ) : Measurable (angM α) := by
  have h : angM α = fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := rfl
  rw [h]; fun_prop

/-- A single block of the `ℋ^k`-integrand is dominated by the whole integrand. -/
theorem hblk_le_HkIntegrand (α : ℝ) (k : ℕ) (φ : ℝ → ℝ → ℝ) (i m : ℕ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : hblk α k φ (i, m) z θ ≤ Work.Spaces.HkIntegrand α k φ z θ := by
  by_cases h : i + m ≤ k
  · rw [HkIntegrand_eq_hblk α k φ hθ]
    refine le_trans (Finset.single_le_sum (s := Finset.range (k + 1))
      (f := fun m' => hblk α k φ (i, m') z θ)
      (fun m' _ => hblk_nonneg α k φ (i, m') z θ hθ) (a := m)
      (Finset.mem_range.mpr (by omega))) ?_
    exact Finset.single_le_sum (s := Finset.range (k + 1))
      (f := fun i' => ∑ m' ∈ Finset.range (k + 1), hblk α k φ (i', m') z θ)
      (fun i' _ => Finset.sum_nonneg (fun m' _ => hblk_nonneg α k φ (i', m') z θ hθ)) (a := i)
      (Finset.mem_range.mpr (by omega))
  · rw [hblk_eq_zero α k φ (i, m) z θ h]
    exact Work.Spaces.HkIntegrand_nonneg α k φ z θ

/-- The `θ`-slice integral of a single block of the `ℋ^k`-integrand is finite, as soon as the
integrand is honest. -/
theorem hblk_Iθ_lt_top (α : ℝ) (k : ℕ) (φ : ℝ → ℝ → ℝ) (hφ : SmoothOpen φ)
    (hm : Work.Spaces.HkMem α k φ) (i m : ℕ) {z : ℝ} (hz : 0 < z) :
    ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (hblk α k φ (i, m) z θ) < ⊤ := by
  have hInt : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k φ z θ) Work.Spaces.Iθ :=
    hm.1 z (le_of_lt hz)
  have haesm : AEStronglyMeasurable (fun θ => Work.Spaces.HkIntegrand α k φ z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd _ (hφ.continuousOn_HkIntegrand α k) hz
  have hbnd : ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k φ z θ) < ⊤ :=
    lt_top_iff_ne_top.mpr ((MeasureTheory.lintegral_ofReal_ne_top_iff_integrable haesm
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k φ z θ)).mpr hInt)
  exact lt_of_le_of_lt (lintegral_mono_ae (by
    filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from
      measurableSet_Icc)] with θ hθ
    exact ENNReal.ofReal_le_ofReal (hblk_le_HkIntegrand α k φ i m hθ))) hbnd

/-- **The `z`-slice of `D_z V`, against a general angular weight, is finite.**  This is the
`D_z`-form of the slice lemma `SliceZDeriv_finite`. -/
theorem sliceDz_lintegral_lt_top (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ)
    (hwth : ∀ θ, 0 ≤ wth θ) (hwthmeas : Measurable wth)
    (hsm : ContDiffOn ℝ 2 (Function.uncurry V) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hG : ∀ z ∈ Set.Ioi (0 : ℝ),
      ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ENNReal.ofReal ((V z θ * wth θ) ^ 2) < ⊤)
    (hB : ∀ z ∈ Set.Ioi (0 : ℝ), ∃ δ : ℝ, 0 < δ ∧
      ∫⁻ z' in Set.Ioo z (z + δ), ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal ((Work.Spaces.pzIter 2 V z' θ * wth θ) ^ 2) < ⊤)
    {z : ℝ} (hz : 0 < z) :
    ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2) < ⊤ := by
  have h1 := SliceZDeriv_finite V wth hwth hwthmeas hsm hG hB hz
  rw [lintegral_Iθ_eq_Ioo]
  have hEq : ∀ θ : ℝ, ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2)
      = ENNReal.ofReal ((z * Work.Spaces.w z) ^ 2)
        * ENNReal.ofReal ((Work.Spaces.pz V z θ * wth θ) ^ 2) := by
    intro θ
    have hpt : (Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2
        = (z * Work.Spaces.w z) ^ 2 * (Work.Spaces.pz V z θ * wth θ) ^ 2 := by
      simp only [Work.Spaces.Dz]
      ring
    rw [hpt, ENNReal.ofReal_mul (by positivity)]
  rw [lintegral_congr_ae (Filter.Eventually.of_forall hEq)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h1

/-- The raw shape of the open-quadrant smoothness hypothesis. -/
theorem smooth_raw {φ : ℝ → ℝ → ℝ} (h : SmoothOpen φ) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  fun n => (smoothOpen_iff_forall φ).mp h n

/-- The second radial derivative of `f`, as a `SmoothOpen` function. -/
theorem smooth_zsqPz2 (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f) :
    SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) := by
  have h1 : (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) = zsqPz2 f := rfl
  rw [h1]; exact SmoothOpen_zsqPz2 f hf

/-- The global `z`-`θ` `lintegral` of the `ℋ^k`-integrand of `z²∂_z²f` is finite. -/
theorem global_zsqPz2_lt_top (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f)
    (hmQ : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ)) :
    (∫⁻ z' in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z' θ)) < ⊤ := by
  have hQSm : SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) := smooth_zsqPz2 f hf
  have h := LkSq_lt_top α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) hQSm hmQ
  rw [LkSq] at h
  rw [MeasureTheory.lintegral_lintegral_swap
    ((aesm_HkIntegrand_prod α k _ hQSm).prod_swap)] at h
  exact h

/-- **The block of the `ℋ^k`-integrand of `D_z f` at `(0,m)` has finite `θ`-slice integral.** -/
theorem hblk_pure_lt_top (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f)
    (hmf : Work.Spaces.HkMem α k f)
    (hmQ : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ))
    {m : ℕ} (hm : m ≤ k) {z : ℝ} (hz : 0 < z) :
    ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (hblk α k (Work.Spaces.Dz f) (0, m) z θ) < ⊤ := by
  have hcongr : (fun θ => ENNReal.ofReal (hblk α k (Work.Spaces.Dz f) (0, m) z θ))
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => ENNReal.ofReal ((Work.Spaces.Dz (Work.Spaces.DzIter m f) z θ
        * Work.Spaces.w z * |angZ θ|) ^ 2)) := by
    filter_upwards [ae_mem_Ioo_theta] with θ hθ
    rw [hblk_eq α k (Work.Spaces.Dz f) (0, m) z θ (by omega), angw_zero]
    simp only [hblkR, Work.Spaces.DthIter_zero]
    rw [DzIter_Dz_eq]
    simp only [mul_pow, sq_abs, angZ_sq ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩] <;> ring_nf
  rw [lintegral_congr_ae hcongr]
  have hG : ∀ z' ∈ Set.Ioi (0 : ℝ),
      ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal ((Work.Spaces.DzIter m f z' θ * |angZ θ|) ^ 2) < ⊤ := by
    intro z' hz'
    have hpt : ∀ θ ∈ Work.Spaces.Iθ, hblk α k f (0, m) z' θ
        = (Work.Spaces.w z') ^ 2 * ((Work.Spaces.DzIter m f z' θ * |angZ θ|) ^ 2) := by
      intro θ hθ
      rw [hblk_eq α k f (0, m) z' θ (by omega), angw_zero]
      simp only [hblkR, Work.Spaces.DthIter_zero]
      simp only [mul_pow, sq_abs, angZ_sq hθ] <;> ring_nf
    have hrel : (fun θ => ENNReal.ofReal (hblk α k f (0, m) z' θ))
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ => ENNReal.ofReal ((Work.Spaces.w z') ^ 2)
          * ENNReal.ofReal ((Work.Spaces.DzIter m f z' θ * |angZ θ|) ^ 2)) := by
      filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from
        measurableSet_Icc)] with θ hθ
      rw [hpt θ hθ, ENNReal.ofReal_mul (by positivity)]
    have h4 : ENNReal.ofReal ((Work.Spaces.w z') ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((Work.Spaces.DzIter m f z' θ * |angZ θ|) ^ 2)) < ⊤ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne, lintegral_congr_ae hrel.symm]
      exact hblk_Iθ_lt_top α k f hf hmf 0 m hz'
    have hpos : ENNReal.ofReal ((Work.Spaces.w z') ^ 2) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      have hthis : (0 : ℝ) < ((1 + z') ^ 2 / z' ^ 2) ^ 2 := by
        have hz'pos : (0 : ℝ) < z' := hz'
        positivity
      simpa only [Work.Spaces.w] using hthis
    rcases ENNReal.mul_lt_top_iff.mp h4 with ⟨-, h⟩ | h0 | h0
    · rwa [lintegral_Iθ_eq_Ioo] at h
    · exact absurd h0 hpos
    · rw [← lintegral_Iθ_eq_Ioo, h0]; exact ENNReal.zero_lt_top
  have hB : ∀ z' ∈ Set.Ioi (0 : ℝ), ∃ δ : ℝ, 0 < δ ∧
      ∫⁻ z'' in Set.Ioo z' (z' + δ), ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal ((Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z'' θ
          * |angZ θ|) ^ 2) < ⊤ := by
    intro z' hz'
    refine ⟨1, one_pos, ?_⟩
    have hglob := global_zsqPz2_lt_top α k f hf hmQ
    have hstep : (∫⁻ z'' in Set.Ioo z' (z' + 1), ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          ENNReal.ofReal ((Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z'' θ
            * |angZ θ|) ^ 2))
        ≤ (∫⁻ z'' in Set.Ioo z' (z' + 1), ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z'' θ)) := by
      refine lintegral_mono_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet (Set.Ioo z' (z' + 1)) from
        measurableSet_Ioo)] with z'' hz''
      have hz''0 : 0 < z'' := lt_trans hz' hz''.1
      refine le_trans ?_ (lintegral_mono_ae (by
        filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from
          measurableSet_Icc)] with θ hθ
        exact ENNReal.ofReal_le_ofReal (hblk_le_HkIntegrand α k
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) 0 m hθ)))
      rw [← lintegral_Iθ_eq_Ioo]
      refine lintegral_mono_ae ?_
      filter_upwards [ae_mem_Ioo_theta] with θ hθ
      have hcom := AgmonSlice.zsq_pzIter2_mixed_open f (smooth_raw hf) m 0 hz''0 hθ
      have hcom' : Work.Spaces.DzIter m (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z'' θ
          = z'' ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z'' θ := by
        simpa only [Work.Spaces.mixed, Work.Spaces.DthIter_zero] using hcom.symm
      have hval2 : hblk α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) (0, m) z'' θ
          = (1 + z'') ^ 4
            * (Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z'' θ * angZ θ) ^ 2 := by
        rw [hblk_eq α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) (0, m) z'' θ (by omega),
          angw_zero]
        simp only [hblkR, Work.Spaces.DthIter_zero]
        rw [hcom']
        simp only [mul_pow, angZ_sq ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩]
        have hzne : z'' ≠ 0 := ne_of_gt hz''0
        rw [Work.Spaces.w]
        field_simp
      rw [hval2]
      have hsq : ENNReal.ofReal ((Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z'' θ
            * |angZ θ|) ^ 2)
          = ENNReal.ofReal ((Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z'' θ
              * angZ θ) ^ 2) := by
        congr 1
        simp only [mul_pow, sq_abs]
      rw [hsq]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : (1 : ℝ) ≤ (1 + z'') ^ 4 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + z'')
      have h2 : (0 : ℝ) ≤ (Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z'' θ * angZ θ) ^ 2 :=
        sq_nonneg _
      simpa using mul_le_mul_of_nonneg_right h1 h2
    have hdom : (∫⁻ z'' in Set.Ioo z' (z' + 1), ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z'' θ))
        ≤ (∫⁻ z'' in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z'' θ)) :=
      MeasureTheory.lintegral_mono_set
        (fun z'' hz'' => show z'' ∈ Work.Spaces.Iz from
          le_of_lt (lt_trans (show (0 : ℝ) < z' from hz') hz''.1))
    exact lt_of_le_of_lt (le_trans hstep hdom) hglob
  exact sliceDz_lintegral_lt_top (Work.Spaces.DzIter m f) (fun θ => |angZ θ|)
    (fun θ => abs_nonneg _) measurable_angZ.abs
    (show ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.DzIter m f))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) from (hf.DzIter m).forall 2) hG hB hz

theorem hblk_mixed_lt_top (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f)
    (hmf : Work.Spaces.HkMem α k f)
    (hmQ : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ))
    {i m : ℕ} (hi : 1 ≤ i) (him : i + m ≤ k) {z : ℝ} (hz : 0 < z) :
    ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (hblk α k (Work.Spaces.Dz f) (i, m) z θ) < ⊤ := by
  have hcongr : (fun θ => ENNReal.ofReal (hblk α k (Work.Spaces.Dz f) (i, m) z θ))
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => ENNReal.ofReal ((Work.Spaces.Dz (Work.Spaces.mixed m i f) z θ
        * Work.Spaces.w z * |angM α θ|) ^ 2)) := by
    filter_upwards [ae_mem_Ioo_theta] with θ hθ
    have hcom : Work.Spaces.DzIter m (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
        = Work.Spaces.Dz (Work.Spaces.mixed m i f) z θ := by
      rw [show Work.Spaces.DzIter m (Work.Spaces.DthIter i (Work.Spaces.Dz f))
          = Work.Spaces.mixed m i (Work.Spaces.Dz f) from rfl,
        show Work.Spaces.mixed m i (Work.Spaces.Dz f)
          = Work.Spaces.mixed m i (Work.Spaces.DzIter 1 f) from rfl,
        AgmonSlice.mixed_DzIter_open f hf m i 1 z θ hz hθ.1 hθ.2]
      rfl
    rw [hblk_eq α k (Work.Spaces.Dz f) (i, m) z θ (by omega), angw_pos α hi]
    simp only [hblkR]
    rw [hcom]
    simp only [mul_pow, sq_abs, angM_sq α ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩] <;> ring_nf
  rw [lintegral_congr_ae hcongr]
  have hG : ∀ z' ∈ Set.Ioi (0 : ℝ),
      ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal ((Work.Spaces.mixed m i f z' θ * |angM α θ|) ^ 2) < ⊤ := by
    intro z' hz'
    have hpt : ∀ θ ∈ Work.Spaces.Iθ, hblk α k f (i, m) z' θ
        = (Work.Spaces.w z') ^ 2 * ((Work.Spaces.mixed m i f z' θ * |angM α θ|) ^ 2) := by
      intro θ hθ
      rw [hblk_eq α k f (i, m) z' θ (by omega), angw_pos α hi]
      simp only [hblkR]
      simp only [Work.Spaces.mixed, mul_pow, sq_abs, angM_sq α hθ] <;> ring_nf
    have hrel : (fun θ => ENNReal.ofReal (hblk α k f (i, m) z' θ))
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ => ENNReal.ofReal ((Work.Spaces.w z') ^ 2)
          * ENNReal.ofReal ((Work.Spaces.mixed m i f z' θ * |angM α θ|) ^ 2)) := by
      filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from
        measurableSet_Icc)] with θ hθ
      rw [hpt θ hθ, ENNReal.ofReal_mul (by positivity)]
    have h4 : ENNReal.ofReal ((Work.Spaces.w z') ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((Work.Spaces.mixed m i f z' θ * |angM α θ|) ^ 2)) < ⊤ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne, lintegral_congr_ae hrel.symm]
      exact hblk_Iθ_lt_top α k f hf hmf i m hz'
    have hpos : ENNReal.ofReal ((Work.Spaces.w z') ^ 2) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      have hthis : (0 : ℝ) < ((1 + z') ^ 2 / z' ^ 2) ^ 2 := by
        have hz'pos : (0 : ℝ) < z' := hz'
        positivity
      simpa only [Work.Spaces.w] using hthis
    rcases ENNReal.mul_lt_top_iff.mp h4 with ⟨-, h⟩ | h0 | h0
    · rwa [lintegral_Iθ_eq_Ioo] at h
    · exact absurd h0 hpos
    · rw [← lintegral_Iθ_eq_Ioo, h0]; exact ENNReal.zero_lt_top
  have hB : ∀ z' ∈ Set.Ioi (0 : ℝ), ∃ δ : ℝ, 0 < δ ∧
      ∫⁻ z'' in Set.Ioo z' (z' + δ), ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal ((Work.Spaces.pzIter 2 (Work.Spaces.mixed m i f) z'' θ
          * |angM α θ|) ^ 2) < ⊤ := by
    intro z' hz'
    refine ⟨1, one_pos, ?_⟩
    have hglob := global_zsqPz2_lt_top α k f hf hmQ
    have hstep : (∫⁻ z'' in Set.Ioo z' (z' + 1), ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          ENNReal.ofReal ((Work.Spaces.pzIter 2 (Work.Spaces.mixed m i f) z'' θ
            * |angM α θ|) ^ 2))
        ≤ (∫⁻ z'' in Set.Ioo z' (z' + 1), ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z'' θ)) := by
      refine lintegral_mono_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet (Set.Ioo z' (z' + 1)) from
        measurableSet_Ioo)] with z'' hz''
      have hz''0 : 0 < z'' := lt_trans hz' hz''.1
      refine le_trans ?_ (lintegral_mono_ae (by
        filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from
          measurableSet_Icc)] with θ hθ
        exact ENNReal.ofReal_le_ofReal (hblk_le_HkIntegrand α k
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) i m hθ)))
      rw [← lintegral_Iθ_eq_Ioo]
      refine lintegral_mono_ae ?_
      filter_upwards [ae_mem_Ioo_theta] with θ hθ
      have hcomA := AgmonSlice.zsq_pzIter2_mixed_open f (smooth_raw hf) m i hz''0 hθ
      have hcom' : Work.Spaces.DzIter m (Work.Spaces.DthIter i
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ)) z'' θ
          = z'' ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.mixed m i f) z'' θ := by
        simpa only [Work.Spaces.mixed] using hcomA.symm
      have hval2 : hblk α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) (i, m) z'' θ
          = (1 + z'') ^ 4
            * (Work.Spaces.pzIter 2 (Work.Spaces.mixed m i f) z'' θ * angM α θ) ^ 2 := by
        rw [hblk_eq α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) (i, m) z'' θ (by omega),
          angw_pos α hi]
        simp only [hblkR]
        rw [hcom']
        simp only [mul_pow, angM_sq α ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩]
        have hzne : z'' ≠ 0 := ne_of_gt hz''0
        rw [Work.Spaces.w]
        field_simp
      rw [hval2]
      have hsq : ENNReal.ofReal ((Work.Spaces.pzIter 2 (Work.Spaces.mixed m i f) z'' θ
            * |angM α θ|) ^ 2)
          = ENNReal.ofReal ((Work.Spaces.pzIter 2 (Work.Spaces.mixed m i f) z'' θ
              * angM α θ) ^ 2) := by
        congr 1
        simp only [mul_pow, sq_abs]
      rw [hsq]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : (1 : ℝ) ≤ (1 + z'') ^ 4 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + z'')
      have h2 : (0 : ℝ) ≤ (Work.Spaces.pzIter 2 (Work.Spaces.mixed m i f) z'' θ * angM α θ) ^ 2 :=
        sq_nonneg _
      simpa using mul_le_mul_of_nonneg_right h1 h2
    have hdom : (∫⁻ z'' in Set.Ioo z' (z' + 1), ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z'' θ))
        ≤ (∫⁻ z'' in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z'' θ)) :=
      MeasureTheory.lintegral_mono_set
        (fun z'' hz'' => show z'' ∈ Work.Spaces.Iz from
          le_of_lt (lt_trans (show (0 : ℝ) < z' from hz') hz''.1))
    exact lt_of_le_of_lt (le_trans hstep hdom) hglob
  exact sliceDz_lintegral_lt_top (Work.Spaces.mixed m i f) (fun θ => |angM α θ|)
    (fun θ => abs_nonneg _) (measurable_angM α).abs
    (show ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.mixed m i f))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) from (hf.mixed m i).forall 2) hG hB hz

/-- **The pointwise-in-`z` honesty of `HkIntegrand α k (D_z f)`.** -/
theorem HkMem_Dz_slices (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f)
    (hmf : Work.Spaces.HkMem α k f)
    (hmQ : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ)) :
    ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.Dz f) z θ)
        Work.Spaces.Iθ := by
  intro z hz
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
  · subst h0
    have h : (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.Dz f) 0 θ)
        = fun _ => (0 : ℝ) := by
      funext θ; exact Work.Coercivity.HkIntegrand_zero_left α k (Work.Spaces.Dz f) θ
    rw [h]; exact integrableOn_zero
  · have hDzSm : SmoothOpen (Work.Spaces.Dz f) := hf.Dz
    have haesm : AEStronglyMeasurable
        (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.Dz f) z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd _ (hDzSm.continuousOn_HkIntegrand α k) hz0
    have hfin : (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Work.Spaces.Dz f) z θ)) < ⊤ := by
      have hpt : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Work.Spaces.Dz f) z θ)
            = ∑ i ∈ Finset.range (k + 1), ∑ m ∈ Finset.range (k + 1),
                ENNReal.ofReal (hblk α k (Work.Spaces.Dz f) (i, m) z θ) := by
        filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from
          measurableSet_Icc)] with θ hθ
        rw [HkIntegrand_eq_hblk α k (Work.Spaces.Dz f) hθ]
        rw [ENNReal.ofReal_sum_of_nonneg
          (fun i _ => Finset.sum_nonneg (fun m _ =>
            hblk_nonneg α k (Work.Spaces.Dz f) (i, m) z θ hθ))]
        exact Finset.sum_congr rfl fun i _ =>
          ENNReal.ofReal_sum_of_nonneg
            (fun m _ => hblk_nonneg α k (Work.Spaces.Dz f) (i, m) z θ hθ)
      have haesm_blk : ∀ i m : ℕ, AEMeasurable
          (fun θ => ENNReal.ofReal (hblk α k (Work.Spaces.Dz f) (i, m) z θ))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := fun i m =>
        ((Work.Spaces.aesm_slice_of_continuousOn_Qd _
          (continuousOn_hblk_Q0 α k (Work.Spaces.Dz f) (smooth_raw hDzSm) i m) hz0).aemeasurable).ennreal_ofReal
      rw [lintegral_congr_ae hpt]
      have houter := MeasureTheory.lintegral_finsetSum' (s := Finset.range (k + 1))
        (f := fun i a => ∑ m ∈ Finset.range (k + 1),
          ENNReal.ofReal (hblk α k (Work.Spaces.Dz f) (i, m) z a))
        (fun i _ => (Finset.aemeasurable_sum (Finset.range (k + 1))
          (fun m _ => haesm_blk i m)).congr
          (Filter.Eventually.of_forall fun a => by simp only [Finset.sum_apply]))
      rw [houter]
      refine ENNReal.sum_lt_top.mpr (fun i hi => ?_)
      have hinner := MeasureTheory.lintegral_finsetSum' (s := Finset.range (k + 1))
        (f := fun m a => ENNReal.ofReal (hblk α k (Work.Spaces.Dz f) (i, m) z a))
        (fun m _ => haesm_blk i m)
      rw [hinner]
      refine ENNReal.sum_lt_top.mpr (fun m hm => ?_)
      by_cases him : i + m ≤ k
      · rcases eq_or_ne i 0 with h | h
        · subst h
          exact hblk_pure_lt_top α k f hf hmf hmQ (by omega) hz0
        · exact hblk_mixed_lt_top α k f hf hmf hmQ (by omega) him hz0
      · have hzero : (fun θ => ENNReal.ofReal (hblk α k (Work.Spaces.Dz f) (i, m) z θ))
            = fun _ => (0 : ℝ≥0∞) := by
          funext θ
          rw [hblk_eq_zero α k (Work.Spaces.Dz f) (i, m) z θ him]
          simp
        rw [hzero, lintegral_zero]
        exact ENNReal.zero_lt_top


    refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable haesm
      (Filter.Eventually.of_forall fun θ =>
        Work.Spaces.HkIntegrand_nonneg α k (Work.Spaces.Dz f) z θ)).mp ?_
    exact lt_top_iff_ne_top.mp hfin

end Cert


/-! ## The last bridges -/

/-- The second `HkMem` conjunct of `g`, from the finiteness of `LkSq α k g`. -/
theorem integrableOn_sliceIntegral_of_LkSq_lt_top (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ)
    (hg : SmoothOpen g) (h : LkSq α k g < ⊤) :
    IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
      Work.Spaces.Iz := by
  have hprod : AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k g p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    aesm_HkIntegrand_prod α k g hg
  have hswap : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ)) < ⊤ := by
    rw [LkSq] at h
    rwa [MeasureTheory.lintegral_lintegral_swap (hprod.prod_swap)] at h
  have hA : AEMeasurable (fun z => ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hprod.lintegral_prod_right'
  have hintA : Integrable (fun z => (∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ)).toReal)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    MeasureTheory.integrable_toReal_of_lintegral_ne_top hA (ne_of_lt hswap)
  have hpos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), (0 : ℝ) < z := by
    rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
  refine hintA.congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from
    measurableSet_Ici), hpos] with z hz hzpos
  exact (MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)
    (Work.Spaces.aesm_slice_of_continuousOn_Qd _ (hg.continuousOn_HkIntegrand α k) hzpos)).symm

/-- The `θ`-integrated Agmon interface, assembled from the one-dimensional estimate. -/
theorem hgen_of_agmon : ∃ C : ℝ, 0 < C ∧
    (∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (MeasureTheory.lintegral
          (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))
          (fun θ => MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
            (fun z => ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))))
        ≤ ENNReal.ofReal (C ^ 2) *
            (ENNReal.ofReal (α ^ 4) * (MeasureTheory.lintegral
                (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))
                (fun θ => MeasureTheory.lintegral
                  (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                  (fun z => ENNReal.ofReal
                    ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))))
              + (MeasureTheory.lintegral
                  (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))
                  (fun θ => MeasureTheory.lintegral
                    (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                    (fun z => ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2)))))) := by
  obtain ⟨C, hC, h1D⟩ := DzAgmon1D_clean
  refine ⟨C, hC, ?_⟩
  intro α hα hα1 V wth hV hwth
  exact TermAgmon C hC h1D α V wth hα hα1 hV hwth

/-- **Agmon--Nirenberg (interpolation) for `D_z = z∂_z` in the weighted `H^k`-norm.** -/
theorem HkNorm_Dz_amgm (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      Work.Spaces.HkMem α k f →
      Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz f) ∧
        α * Work.Spaces.HkNorm α k (Work.Spaces.Dz f)
          ≤ C * (Work.Spaces.HkNorm α k f
              + α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ)) := by
  obtain ⟨C, hC, hgen⟩ := hgen_of_agmon
  refine ⟨C, hC, ?_⟩
  intro α f hα hα1 hf hmf hmQ
  have hF : SmoothOpen f := smoothOpen_of_forall hf
  have hmQ' : Work.Spaces.HkMem α k (zsqPz2 f) := hmQ
  have hmDz : Work.Spaces.HkMem α k (Work.Spaces.Dz f) :=
    ⟨HkMem_Dz_slices α k f hF hmf hmQ',
      integrableOn_sliceIntegral_of_LkSq_lt_top α k (Work.Spaces.Dz f) hF.Dz
        (LkSq_Dz_lt_top C hC hgen α hα hα1 k f hF hmf hmQ')⟩
  exact ⟨hmDz, HkNorm_Dz_le_of C hC hgen α hα hα1 k f hF hmf hmQ' hmDz⟩

end DzVamgm


end Work.Blocks
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.Q0.localEq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Work.EllipticEst.InteriorRegularity.Q0

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! ## Integrability from local integrability on a set

If `V` is locally integrable on `s` and `g` is continuous with compact support contained in
`closure (support g) ⊆ s`, then `g · V` is integrable.  (The global version,
`LocallyIntegrable.integrable_smul_left_of_hasCompactSupport`, is not available under the
weaker hypothesis `LocallyIntegrableOn V s`; the proof is the same, using that
`tsupport g` is a compact subset of `s`.) -/

theorem integrable_mul_of_locallyIntegrableOn {V g : E2 → ℂ} {s : Set E2}
    (hV : MeasureTheory.LocallyIntegrableOn V s) (hg : Continuous g)
    (hgc : HasCompactSupport g) (hsub : tsupport g ⊆ s) :
    Integrable (fun x : E2 => g x * V x) := by
  have hK : IsCompact (tsupport g) := hgc
  have hVK : MeasureTheory.IntegrableOn V (tsupport g) :=
    hV.integrableOn_compact_subset hsub hK
  have hIntK : MeasureTheory.IntegrableOn (fun x : E2 => g x * V x) (tsupport g) :=
    MeasureTheory.IntegrableOn.continuousOn_mul hg.continuousOn hVK hK
  exact hIntK.integrable_of_forall_notMem_eq_zero (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul])

/-! ## Topological supports of the differentiated cut-off

`tsupport (d0 f) ⊆ tsupport f` for any `f`, and the analogous statements for the
combinations of `χ`-derivatives appearing in the pointwise identity. -/

theorem tsupport_d0_subset (f : E2 → ℂ) : tsupport (d0 f) ⊆ tsupport f := by
  refine closure_minimal (fun x hx => ?_) (isClosed_tsupport f)
  by_contra h
  exact hx (Loc.d0_eq_zero_of_eventuallyEq_zero (notMem_tsupport_iff_eventuallyEq.mp h))

theorem tsupport_d1_subset (f : E2 → ℂ) : tsupport (d1 f) ⊆ tsupport f := by
  refine closure_minimal (fun x hx => ?_) (isClosed_tsupport f)
  by_contra h
  exact hx (Loc.d1_eq_zero_of_eventuallyEq_zero (notMem_tsupport_iff_eventuallyEq.mp h))





/-! ## The local equation -/


end Work.EllipticEst.InteriorRegularity.Q0
end
end
-- ===== merged: Submission.Work.FTS.Apriori.Limit.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.Apriori.Limit

set_option autoImplicit false

open Work.FTS.LocData (SmoothQuad)

/-- The open quadrant `(0,∞) × (0,π/2)` of the self-similar variables (definitionally the
same set as `Work.Construction.Qd` and `Work.FTS.LocData.Qd`). -/
abbrev Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

/-- The weight of the slot `ji = (j,i)`: the pure `D_z`-slots (`i = 0`) carry
`w(z)/sin(2θ)^{η/2}` and the mixed slots (`i ≥ 1`) carry `Wt α = w(z)·sin(2θ)^{-γ/2}`. -/
def slotWeight (α : ℝ) (ji : ℕ × ℕ) (z θ : ℝ) : ℝ :=
  if ji.2 = 0 then Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
  else Work.Spaces.Wt α z θ

/-- The weighted slot `mixed j i f · slotWeight α (j,i)`. -/
def slot (α : ℝ) (ji : ℕ × ℕ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Spaces.mixed ji.1 ji.2 f z θ * slotWeight α ji z θ

/-- The active slots of the `ℋ⁴`-norm: `(j,0)` with `j ≤ 4` (the pure `D_z`-slots) together
with `(j,i)` with `1 ≤ i` and `i + j ≤ 4` (the mixed slots with at least one `D_θ`). -/
def activeSlots : Finset (ℕ × ℕ) :=
  ((Finset.range 5) ×ˢ (Finset.range 5)).filter
    (fun ji => ji.2 = 0 ∨ (1 ≤ ji.2 ∧ ji.1 + ji.2 ≤ 4))

/-- The test functions of the pairing: `ψ` is smooth on the open quadrant
`(0,∞) × (0,π/2)` (the genuine `C^∞`-order `Work.Stability.smoothOrder`, as in
`SmoothQuad`, but only on the quadrant, where the weights are smooth) and has compact
support contained in it. -/
def TestQ (ψ : ℝ → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry ψ) Qd ∧
    HasCompactSupport (Function.uncurry ψ) ∧ tsupport (Function.uncurry ψ) ⊆ Qd

/-- The formal adjoint of `D_z = z ∂_z`: `φ ↦ -∂_z(z φ)`. -/
def adjZ (φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -deriv (fun z' => z' * φ z' θ) z

/-- The formal adjoint of `D_θ = sin(2θ) ∂_θ`: `φ ↦ -∂_θ(sin(2θ) φ)`. -/
def adjTh (φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -deriv (fun θ' => Real.sin (2 * θ') * φ z θ') θ

/-- The `j`-fold adjoint of `D_z^j`, `(D_z^j)^* = ((D_z)^*)^j`. -/
def adjDzIter : ℕ → (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)
  | 0, φ => φ
  | n + 1, φ => adjDzIter n (adjZ φ)

/-- The `i`-fold adjoint of `D_θ^i`, `(D_θ^i)^* = ((D_θ)^*)^i`. -/
def adjDthIter : ℕ → (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)
  | 0, φ => φ
  | n + 1, φ => adjDthIter n (adjTh φ)

/-- The adjoint of `mixed j i = D_z^j ∘ D_θ^i`: `(D_z^j D_θ^i)^* = (D_θ^i)^* (D_z^j)^*`. -/
def adjMixed (ji : ℕ × ℕ) (φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  adjDthIter ji.2 (adjDzIter ji.1 φ)

/-- The product measure `dz dθ` restricted to the closed quadrant
`[0,∞) × [0,π/2]`, i.e. `(volume.restrict Iz).prod (volume.restrict Iθ)`. -/
def Qμ : Measure (ℝ × ℝ) :=
  (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)

/-- The cut-off `ℋ⁴`-energy: `∫∫ HkIntegrand α 4 f · η` over the closed quadrant, i.e. the
`L¹`-norm of the `ℋ⁴`-integrand of `f` against the cut-off `η` with respect to the product
measure `Qμ = dz dθ` on `Iz ×ˢ Iθ`. -/
def HksqCut (α : ℝ) (f η : ℝ → ℝ → ℝ) : ℝ :=
  ∫ p, Work.Spaces.HkIntegrand α 4 f p.1 p.2 * η p.1 p.2 ∂Qμ

end Work.FTS.Apriori.Limit
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Assembly.WitDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

set_option autoImplicit false

/-- **The radial factor of the witness**: `ρ(z) = z ∂_z(bumpZ)(z) = D_z(bumpZ)(z)`, the
`D_z`-derivative of the compactly supported bump `bumpZ = χ(4· − 5)` of
`Work.FTS.LocData`.

* its support is contained in `[3/4, 7/4]` (the support of `bumpZ`), so it vanishes on a
  neighbourhood of `z = 0` and at infinity;
* `ρ(z)/z = ∂_z(bumpZ)(z)`, hence `∫_0^∞ ρ(s)/s ds = 0` — this is what makes the witness
  `L₁₂`-orthogonal;
* `D_z^j ρ = D_z^{j+1} bumpZ` is bounded for every `j` (the jets of a smooth compactly
  supported bump), which is the radial input of the separable `𝓗^k`-majorant. -/
noncomputable def radW (z : ℝ) : ℝ := z * deriv Work.FTS.LocData.bumpZ z

/-- **The witness** of the non-vacuity lemma: `f(z,θ) = ρ(z)·Γ(θ)`, with `ρ = radW` and
`Γ(θ) = (sinθ cos²θ)^{α/3}` the paper's angular factor. -/
noncomputable def witF (α : ℝ) : ℝ → ℝ → ℝ := fun z θ => radW z * Work.Spaces.Gam α θ

@[simp] theorem radW_apply (z : ℝ) : radW z = z * deriv Work.FTS.LocData.bumpZ z := rfl

@[simp] theorem witF_apply (α z θ : ℝ) : witF α z θ = radW z * Work.Spaces.Gam α θ := rfl


/-! ## The `D_z`-iterates of the radial factor -/

/-- `D_z`-iterating a `D_z`-derivative: `D_z^j (D_z f) = D_z^{j+1} f`. -/
theorem DzIter_Dz (j : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter j (Work.Spaces.Dz f) = Work.Spaces.DzIter (j + 1) f := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, ih]
      rfl



/-! ## Elementary properties of the witness -/











end Work.FTS.CoercivityFix.Assembly
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.E2Bound.HkMem_dth_of_RegQ_ge =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.E2Bound

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The weight comparison in the sharp range `α ≥ -1/10` -/

/-- `Work.Spaces.H_le_Wt` in its full range of validity: the light `H^0`-weight
`w/ sin(2θ)^{η/2}` is dominated by the heavy weight `Wt α = w·sin(2θ)^{-γ(α)/2}`
whenever `η ≤ γ(α)`, i.e. for `α ≥ -1/10` — the hypothesis of `H_le_Wt` (`0 < α`) can be
weakened to the sharp threshold, since its only use is `η ≤ γ(α)`. -/
theorem H_le_Wt_ge (α : ℝ) (hα : -(1/10 : ℝ) ≤ α) (z θ : ℝ)
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta]
  -- `w z ≥ 0` always, and `s := sin(2θ) ∈ [0,1]` for `θ ∈ [0,π/2]`.
  have ha : 0 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w]
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hs0 : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith [hθ.1]
    · linarith [hθ.2, Real.pi_pos]
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  -- `η ≤ γ(α)` is exactly `α ≥ -1/10`.
  have hgam : Work.Spaces.eta ≤ Work.Spaces.gam α := by
    rw [Work.Spaces.gam, Work.Spaces.eta]; linarith
  -- Since `-γ/2 ≤ -η/2` and `sin(2θ) ∈ [0,1]`, we have `sin(2θ)^{-η/2} ≤ sin(2θ)^{-γ/2}`.
  have hkey : 1 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
    have h1 : 1 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) := by
      rw [one_div, ← Real.rpow_neg hs0]
    rw [h1]
    apply Real.rpow_le_rpow_of_exponent_ge_of_imp hs0 hs1
    · linarith
    · intro _ hy
      exact absurd hy (by norm_num [Work.Spaces.eta])
  -- Multiply by `w z ≥ 0` and square (both sides are nonnegative).
  calc (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z * (1 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [div_eq_mul_one_div]
    _ ≤ (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2 := by
        apply pow_le_pow_left₀ _ _ 2
        · exact mul_nonneg ha (div_nonneg zero_le_one (Real.rpow_nonneg hs0 _))
        · exact mul_le_mul_of_nonneg_left hkey ha

/-! ## Structural identities for the shifted families -/

/-- The pure family of the `H^k`-integrand of `D_θ f` is the family of mixed derivatives
`D_z^i D_θ f = mixed i 1 f` of `f`. -/
private lemma DzIter_Dth_eq (i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter i (Work.Spaces.Dth f) = Work.Spaces.mixed i 1 f := by
  simp only [Work.Spaces.mixed, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]

/-- The mixed family of the `H^k`-integrand of `D_θ f` is the mixed family of `f` with
the `D_θ`-order raised by one: `D_z^j D_θ^i D_θ f = mixed j (i+1) f`. -/
private lemma mixed_Dth_eq (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (Work.Spaces.Dth f) = Work.Spaces.mixed j (i + 1) f := by
  simp only [Work.Spaces.mixed]
  have h : Work.Spaces.Dth f = Work.Spaces.DthIter 1 f := rfl
  rw [h, Work.Spaces.DthIter_add_right]

/-! ## Pointwise domination of the shifted integrands -/

/-- **Pointwise domination, `D_θ` case, sharp range.**  Every summand of the `H^k`-integrand
of `D_θ f` is dominated by a summand of the `H^{k+1}`-integrand of `f`: the pure summands
`D_z^i D_θ f` are mixed summands of `f` with weight `w/√sin^η ≤ W` (valid for `α ≥ -1/10`),
and the mixed summands `D_z^j D_θ^{i+1} f` are themselves mixed summands of `f` at level
`k + 1`. -/
theorem HkIntegrand_Dth_le_ge (α : ℝ) (hα : -(1/10 : ℝ) ≤ α) (k : ℕ) (f : ℝ → ℝ → ℝ)
    (z θ : ℝ) (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k (Work.Spaces.Dth f) z θ
      ≤ Work.Spaces.HkIntegrand α (k + 1) f z θ := by
  set H : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hH
  set W : ℝ := Work.Spaces.Wt α z θ with hW
  have hLHS : Work.Spaces.HkIntegrand α k (Work.Spaces.Dth f) z θ
      = (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i (Work.Spaces.Dth f) z θ * H) ^ 2)
        + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i (Work.Spaces.Dth f) z θ * W) ^ 2
              else 0)) := by
    simp only [Work.Spaces.HkIntegrand, ← hH, ← hW]
  have hRHS : Work.Spaces.HkIntegrand α (k + 1) f z θ
      = (∑ a ∈ Finset.range (k + 2), (Work.Spaces.DzIter a f z θ * H) ^ 2)
        + (∑ a ∈ Finset.range (k + 2), ∑ b ∈ Finset.range (k + 2),
            (if 1 ≤ a ∧ a + b ≤ k + 1 then (Work.Spaces.mixed b a f z θ * W) ^ 2 else 0)) := by
    simp only [Work.Spaces.HkIntegrand, ← hH, ← hW]
  have h1 : (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i (Work.Spaces.Dth f) z θ * H) ^ 2)
      ≤ ∑ i ∈ Finset.range (k + 1), (Work.Spaces.mixed i 1 f z θ * W) ^ 2 := by
    calc (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i (Work.Spaces.Dth f) z θ * H) ^ 2)
        = ∑ i ∈ Finset.range (k + 1), (Work.Spaces.mixed i 1 f z θ * H) ^ 2 :=
          Finset.sum_congr rfl (fun i _ => by rw [DzIter_Dth_eq i f])
      _ ≤ ∑ i ∈ Finset.range (k + 1), (Work.Spaces.mixed i 1 f z θ * W) ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have hw := H_le_Wt_ge α hα z θ hz hθ
          have h1 : (Work.Spaces.mixed i 1 f z θ * H) ^ 2
              = (Work.Spaces.mixed i 1 f z θ) ^ 2 * H ^ 2 := by ring
          have h2 : (Work.Spaces.mixed i 1 f z θ * W) ^ 2
              = (Work.Spaces.mixed i 1 f z θ) ^ 2 * W ^ 2 := by ring
          rw [h1, h2]
          exact mul_le_mul_of_nonneg_left hw (sq_nonneg _)
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i (Work.Spaces.Dth f) z θ * W) ^ 2
                else 0))
      = (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j (i + 1) f z θ * W) ^ 2 else 0)) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc, if_pos hc, mixed_Dth_eq j i f]
    · rw [if_neg hc, if_neg hc]
  have hkey : (∑ i ∈ Finset.range (k + 1), (Work.Spaces.mixed i 1 f z θ * W) ^ 2)
      + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j (i + 1) f z θ * W) ^ 2 else 0))
      = (∑ a ∈ Finset.range (k + 2), ∑ b ∈ Finset.range (k + 2),
          (if 1 ≤ a ∧ a + b ≤ k + 1 then (Work.Spaces.mixed b a f z θ * W) ^ 2 else 0)) := by
    simpa only using Work.Coercivity.SumRowShift_eq k
      (fun a b => (Work.Spaces.mixed b a f z θ * W) ^ 2)
  have hnn : 0 ≤ ∑ a ∈ Finset.range (k + 2), (Work.Spaces.DzIter a f z θ * H) ^ 2 :=
    Finset.sum_nonneg (fun a _ => sq_nonneg _)
  rw [hLHS, hRHS]
  linarith [h1, h2, hkey, hnn]

/-! ## The membership target -/

/-- **`ℋ^k` is closed under `D_θ`, for `α ≥ -1/10`.**  The statement `HkMem_dth_of_RegQ_ge`
of the `E2Bound` node: if `f` lies in the regular class `RegQ α (n+1)`, then `D_θ f` lies in
`ℋⁿ`.  The class supplies the interior smoothness (`SmoothQuad`, hence the a.e. strong
measurability of the integrand needed by `HkMem_of_majorant`) and the honest `ℋ^{n+1}`
membership of `f`, which together with the pointwise domination `HkIntegrand_Dth_le_ge`
gives the claim. -/
theorem HkMem_dth_of_RegQ_ge (α : ℝ) (n : ℕ) (hα : -(1/10 : ℝ) ≤ α) {f : ℝ → ℝ → ℝ} (h : Work.FTS.Nonlin.RegQ α (n + 1) f) : Work.Spaces.HkMem α n (Work.Spaces.Dth f) := by
  obtain ⟨hsm, hmem, _hbd⟩ := h
  have hsm' : Work.FTS.LocData.SmoothQuad (Work.Spaces.Dth f) := by
    simpa using hsm.DthIter 1
  refine Work.FTS.LocData.HkMem_of_majorant α n
    (f := Work.Spaces.Dth f)
    (M := fun z θ => Work.Spaces.HkIntegrand α (n + 1) f z θ) ?_ hmem.1 hmem.2 ?_
  · exact Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α n (Work.Spaces.Dth f) hsm'
  · exact fun z hz θ hθ => HkIntegrand_Dth_le_ge α hα n f z θ hz hθ

end Work.FTS.CoercivityFix.E2Bound
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.GamSmooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer

set_option autoImplicit false

/-- **`Γ α = (sin θ·cos²θ)^{α/3}` is `C^n` on the open quadrant**, for every `n` and every `α`:
the base `sin θ·cos²θ` is positive and smooth there. -/
theorem contDiffOn_Gam_Qd (α : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2) Work.Construction.Qd := by
  have hbase : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin p.2 * Real.cos p.2 ^ 2)
      Work.Construction.Qd :=
    (((Real.contDiff_sin.comp contDiff_snd).mul
      ((Real.contDiff_cos.comp contDiff_snd).pow 2)).contDiffOn).of_le le_top
  have hpos : ∀ p ∈ Work.Construction.Qd, 0 < Real.sin p.2 * Real.cos p.2 ^ 2 := by
    intro p hp
    have hs : 0 < Real.sin p.2 := Real.sin_pos_of_pos_of_lt_pi
      (by linarith [hp.2.1, Real.pi_pos])
      (by linarith [hp.2.2, Real.pi_pos])
    have hc : 0 < Real.cos p.2 := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩
    positivity
  simpa only [Work.Spaces.Gam] using
    hbase.rpow_const_of_ne (fun p hp => ne_of_gt (hpos p hp))

end Work.FTS.CoercivityFix.Transfer
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.L12f_contDiffOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer


end Work.FTS.CoercivityFix.Transfer
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeS1.AgmonSliceBlocks =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AgmonFts.LinAgmon =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.EllipticEst.AgmonSlice (cutRho cutRho_nonneg cutU cutF cutHs cutH cutQs)

namespace Work.FTS.EllipticEst.AgmonFts

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## 1. Elementary inequalities -/

/-- `a² ≤ 1` for `|a| ≤ 1`. -/
private lemma sq_le_one_of_abs_le_one {a : ℝ} (h : |a| ≤ 1) : a ^ 2 ≤ 1 := by
  nlinarith only [h, abs_nonneg a, sq_abs a]

/-- `3Wp²XY ≤ (1/4)Wp²X² + 9WY²` for `W, p, X, Y ≥ 0`, `p ≤ 1`. -/
private lemma young_3W (W p X Y : ℝ) (hW : 0 ≤ W) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    3 * W * p ^ 2 * X * Y ≤ (1 / 4) * (W * p ^ 2 * X ^ 2) + 9 * (W * Y ^ 2) := by
  have h1 : 12 * p * X * Y ≤ p ^ 2 * X ^ 2 + 36 * Y ^ 2 := by
    have h := sq_nonneg (p * X - 6 * Y)
    nlinarith only [h]
  have h2 : 12 * p ^ 2 * X * Y ≤ p * (p ^ 2 * X ^ 2 + 36 * Y ^ 2) := by
    have h := mul_le_mul_of_nonneg_left h1 hp0
    nlinarith only [h]
  have hbnn : 0 ≤ p ^ 2 * X ^ 2 + 36 * Y ^ 2 := by nlinarith only [sq_nonneg X, sq_nonneg Y]
  have h1mp : 0 ≤ 1 - p := by linarith only [hp1]
  have h3 : p * (p ^ 2 * X ^ 2 + 36 * Y ^ 2) ≤ p ^ 2 * X ^ 2 + 36 * Y ^ 2 := by
    nlinarith only [hbnn, h1mp, hp0]
  have h4 : 12 * W * p ^ 2 * X * Y ≤ W * (p ^ 2 * X ^ 2 + 36 * Y ^ 2) := by
    have h := mul_le_mul_of_nonneg_left (le_trans h2 h3) hW
    nlinarith only [h]
  nlinarith only [h4]

/-- `2cWpXY ≤ (1/12)Wp²X² + 12c(c+1)WY²` for `W, p, X, Y, c ≥ 0`. -/
private lemma young_2cW (W p X Y c : ℝ) (hW : 0 ≤ W) (hc : 0 ≤ c) :
    2 * c * W * p * X * Y ≤ (1 / 12) * (W * p ^ 2 * X ^ 2)
      + 12 * c * (c + 1) * (W * Y ^ 2) := by
  have h1 : 24 * c * p * X * Y ≤ p ^ 2 * X ^ 2 + 144 * c ^ 2 * Y ^ 2 := by
    have h := sq_nonneg (p * X - 12 * c * Y)
    nlinarith only [h]
  have h1' : 24 * c * p * X * Y ≤ p ^ 2 * X ^ 2 + 144 * c * (c + 1) * Y ^ 2 := by
    nlinarith only [h1, hc, sq_nonneg Y]
  have h2 : 2 * c * p * X * Y ≤ (1 / 12) * (p ^ 2 * X ^ 2) + 12 * c * (c + 1) * Y ^ 2 := by
    nlinarith only [h1']
  have h3 : W * (2 * c * p * X * Y)
      ≤ W * ((1 / 12) * (p ^ 2 * X ^ 2) + 12 * c * (c + 1) * Y ^ 2) :=
    mul_le_mul_of_nonneg_left h2 hW
  nlinarith only [h3]

/-- `2ν·Wp²(X+Z)Y ≤ ν²Wp²X² + ν²Wp²Z² + 2WY²` for `W, p, X, Z, Y, ν ≥ 0`, `p ≤ 1`. -/
private lemma young_split_clear (W p X Z Y ν : ℝ) (hW : 0 ≤ W) (hν : 0 ≤ ν) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) :
    2 * ν * (W * p ^ 2 * (X + Z) * Y)
      ≤ ν ^ 2 * (W * p ^ 2 * X ^ 2) + ν ^ 2 * (W * p ^ 2 * Z ^ 2) + 2 * (W * Y ^ 2) := by
  have h1 : 2 * ν * X * Y ≤ ν ^ 2 * X ^ 2 + Y ^ 2 := by
    have h := sq_nonneg (ν * X - Y)
    nlinarith only [h]
  have h2 : 2 * ν * W * p * X * Y ≤ ν ^ 2 * W * p * X ^ 2 + W * p * Y ^ 2 := by
    have h := mul_le_mul_of_nonneg_left h1 (mul_nonneg hW hp0)
    nlinarith only [h]
  have h3 : 2 * ν * W * p ^ 2 * X * Y ≤ ν ^ 2 * W * p ^ 2 * X ^ 2 + W * p ^ 2 * Y ^ 2 := by
    have h := mul_le_mul_of_nonneg_left h2 hp0
    nlinarith only [h]
  have h4 : W * p ^ 2 * Y ^ 2 ≤ W * Y ^ 2 := by
    have hp2 : p ^ 2 ≤ 1 := by nlinarith only [hp0, hp1]
    have h := mul_le_mul_of_nonneg_right hp2 hW
    have h' := mul_le_mul_of_nonneg_right h (sq_nonneg Y)
    nlinarith only [h']
  have h5 : 2 * ν * W * p ^ 2 * X * Y ≤ ν ^ 2 * W * p ^ 2 * X ^ 2 + W * Y ^ 2 := by
    linarith only [h3, h4]
  have h6 : 2 * ν * Z * Y ≤ ν ^ 2 * Z ^ 2 + Y ^ 2 := by
    have h := sq_nonneg (ν * Z - Y)
    nlinarith only [h]
  have h7 : 2 * ν * W * p ^ 2 * Z * Y ≤ ν ^ 2 * W * p ^ 2 * Z ^ 2 + W * Y ^ 2 := by
    have h := mul_le_mul_of_nonneg_left h6 (mul_nonneg hW (sq_nonneg p))
    have hz : W * p ^ 2 * Y ^ 2 ≤ W * Y ^ 2 := h4
    nlinarith only [h, hz]
  have h8 : 2 * ν * (W * p ^ 2 * (X + Z) * Y)
      = 2 * ν * W * p ^ 2 * X * Y + 2 * ν * W * p ^ 2 * Z * Y := by ring
  rw [h8]
  linarith only [h5, h7]

/-- The pointwise assembly (cleared of denominators): all variables nonnegative. -/
private lemma pointwise_final {α Kc W p A Z B D : ℝ} (hα : 0 < α) (hKc : 0 ≤ Kc)
    (hW : 0 ≤ W) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hA : 0 ≤ A) (hZ : 0 ≤ Z) (hB : 0 ≤ B)
    (hD : D ≤ 3 * W * p ^ 2 * A + 2 * Kc * W * p * A + W * p ^ 2 * (A + Z)) :
    12 * (α ^ 2 * (D * B))
      ≤ 12 * ((1 / 3 + α ^ 2 / 4) * (α ^ 2 * (W * p ^ 2 * A ^ 2)))
        + 12 * (((9 + 12 * Kc * (Kc + 1)) * α ^ 2 + 2) * (W * B ^ 2))
        + 12 * ((α ^ 4 / 4) * (W * p ^ 2 * Z ^ 2)) := by
  have hν : 0 ≤ α ^ 2 / 2 := by positivity
  have h1 := young_3W W p A B hW hp0 hp1
  have h2 := young_2cW W p A B Kc hW hKc
  have h3 := young_split_clear W p A Z B (α ^ 2 / 2) hW hν hp0 hp1
  have h4 : D * B ≤ (3 * W * p ^ 2 * A + 2 * Kc * W * p * A + W * p ^ 2 * (A + Z)) * B :=
    mul_le_mul_of_nonneg_right hD hB
  have hgoal : α ^ 2 * (D * B)
      ≤ (1 / 3 + α ^ 2 / 4) * (α ^ 2 * (W * p ^ 2 * A ^ 2))
        + ((9 + 12 * Kc * (Kc + 1)) * α ^ 2 + 2) * (W * B ^ 2)
        + (α ^ 4 / 4) * (W * p ^ 2 * Z ^ 2) := by
    nlinarith only [h1, h2, h3, h4, hα, hKc, hW, hp0, hp1]
  linarith only [hgoal]

/-- The final arithmetic: from `α²X ≤ (1/3+α²/4)(α²X) + (c α² + 2)P + (α⁴/4)Q` with
`c ≤ c₀`, `0 < α ≤ 1`, `X, P, Q ≥ 0`, `c, c₀ ≥ 0` and `C₀ = 100 + 100 c₀(c₀+1)`,
conclude `α²X ≤ C₀ (P + α⁴Q)`. -/
private lemma arith_final {α X P Q c c0 C0 : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hX : 0 ≤ X) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hc : 0 ≤ c) (hc0 : 0 ≤ c0) (hcc : c ≤ c0)
    (hC1 : (12 / 5) * (c0 + 2) ≤ C0) (hC2 : (12 / 5 : ℝ) ≤ C0)
    (h1 : α ^ 2 * X ≤ (1 / 3 + α ^ 2 / 4) * (α ^ 2 * X) + (c * α ^ 2 + 2) * P
      + (α ^ 4 / 4) * Q) :
    α ^ 2 * X ≤ C0 * (P + α ^ 4 * Q) := by
  have hα2 : 0 < α ^ 2 := pow_pos hα 2
  have hα2le : α ^ 2 ≤ 1 := by nlinarith only [hα, hα1]
  have hα4 : 0 ≤ α ^ 4 := by positivity
  have h2 : (5 / 12) * (α ^ 2 * X) ≤ (c * α ^ 2 + 2) * P + (α ^ 4 / 4) * Q := by
    have hle : (5 / 12 : ℝ) * (α ^ 2 * X) ≤ (2 / 3 - α ^ 2 / 4) * (α ^ 2 * X) := by
      have h56 : (5 / 12 : ℝ) ≤ 2 / 3 - α ^ 2 / 4 := by linarith only [hα2le]
      exact mul_le_mul_of_nonneg_right h56 (by positivity)
    have h1' : (2 / 3 - α ^ 2 / 4) * (α ^ 2 * X)
        ≤ (c * α ^ 2 + 2) * P + (α ^ 4 / 4) * Q := by
      nlinarith only [h1]
    linarith only [hle, h1']
  have h3 : α ^ 2 * X ≤ (12 / 5) * ((c * α ^ 2 + 2) * P + (α ^ 4 / 4) * Q) := by
    linarith only [h2]
  have h4 : c * α ^ 2 ≤ c0 := by nlinarith only [hcc, hα2le, hc, hc0]
  have h5 : (c * α ^ 2 + 2) * P ≤ (c0 + 2) * P := by nlinarith only [h4, hP]
  have h6 : (α ^ 4 / 4) * Q ≤ α ^ 4 * Q := by nlinarith only [hQ, hα4]
  have h7 : (12 / 5) * ((c * α ^ 2 + 2) * P + (α ^ 4 / 4) * Q)
      ≤ (12 / 5) * ((c0 + 2) * P + α ^ 4 * Q) := by nlinarith only [h5, h6]
  have h8a : (12 / 5) * ((c0 + 2) * P) ≤ C0 * P := by
    have h := mul_le_mul_of_nonneg_right hC1 hP
    linarith only [h]
  have h8b : (12 / 5) * (α ^ 4 * Q) ≤ C0 * (α ^ 4 * Q) := by
    have hPQ : 0 ≤ α ^ 4 * Q := mul_nonneg hα4 hQ
    have h := mul_le_mul_of_nonneg_right hC2 hPQ
    linarith only [h]
  have h8 : (12 / 5) * ((c0 + 2) * P + α ^ 4 * Q) ≤ C0 * (P + α ^ 4 * Q) := by
    linarith only [h8a, h8b]
  linarith only [h3, h7, h8]

/-- `rDzIter 2 h z = z h'(z) + z² h''(z)` on `(0,∞)`. -/
private lemma rDzIter_two_eq {h : ℝ → ℝ} (hh : ContDiffOn ℝ 2 h (Set.Ioi 0)) {z : ℝ}
    (hz : 0 < z) : rDzIter 2 h z = z * deriv h z + z ^ 2 * deriv (deriv h) z := by
  have hd1 : ContDiffOn ℝ 1 (deriv h) (Set.Ioi 0) := hh.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hdiff : DifferentiableAt ℝ (deriv h) z :=
    (hd1.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hprod : HasDerivAt (fun y : ℝ => y * deriv h y) (deriv h z + z * deriv (deriv h) z) z := by
    have h := (hasDerivAt_id z).mul hdiff.hasDerivAt
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  change z * deriv (fun y : ℝ => y * deriv h y) z = _
  rw [hprod.deriv]
  ring

/-! ## 2. The cut-off family `psiFun chi k` -/

/-- The cut-offs `psiFun chi k` are nondecreasing in `k` at every `z > 0`. -/
private lemma chi_psiFun_mono {z : ℝ} (hz : 0 < z) :
    ∀ k l : ℕ, 2 ≤ k → k ≤ l →
      Work.FTS.EllipticEst.psiFun Work.Stability.chi k z
        ≤ Work.FTS.EllipticEst.psiFun Work.Stability.chi l z := by
  have hpsi : ∀ k : ℕ, 0 < Real.log (k : ℝ) →
      Work.FTS.EllipticEst.psiFun Work.Stability.chi k z
        = Work.Stability.chi (|Real.log z| / Real.log (k : ℝ)) := by
    intro k hlog
    rw [Work.FTS.EllipticEst.psiFun]
    rcases lt_or_ge (Real.log z) 0 with h | h
    · have hlogz : Real.log z = -|Real.log z| := by rw [abs_of_neg h, neg_neg]
      have h2 : Real.log z / Real.log (k : ℝ) = -(|Real.log z| / Real.log (k : ℝ)) := by
        conv_lhs => rw [hlogz, neg_div]
      rw [h2, Work.Stability.chi_neg]
    · rw [abs_of_nonneg h]
  intro k l hk hkl
  have hk1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 1 < k)
  have hl1 : (1 : ℝ) < (l : ℝ) := by exact_mod_cast (by omega : 1 < l)
  have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos hk1
  have hlogl : 0 < Real.log (l : ℝ) := Real.log_pos hl1
  rw [hpsi k hlogk, hpsi l hlogl]
  rcases eq_or_ne z 1 with rfl | hz1
  · simp
  · have hlogz : Real.log z ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hz hz1
    have habs : 0 < |Real.log z| := abs_pos.mpr hlogz
    have hlogkl : Real.log (k : ℝ) ≤ Real.log (l : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hkl)
    refine Work.ChiExplicit.chi_antitoneOn (le_of_lt (div_pos habs hlogl))
      (le_of_lt (div_pos habs hlogk)) ?_
    exact div_le_div_of_nonneg_left habs.le hlogk hlogkl

/-- The cut-offs tend to `1` as `k → ∞` at every fixed `z > 0`. -/
private lemma chi_psiFun_tendsto_one {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto (fun k : ℕ => Work.FTS.EllipticEst.psiFun Work.Stability.chi k z)
      Filter.atTop (nhds 1) := by
  have hlog : Filter.Tendsto (fun k : ℕ => Real.log z / Real.log (k : ℝ)) Filter.atTop
      (nhds 0) :=
    Filter.Tendsto.const_div_atTop
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))) (Real.log z)
  have h1 : Filter.Tendsto (fun k : ℕ => Work.Stability.chi (Real.log z / Real.log (k : ℝ)))
      Filter.atTop (nhds (Work.Stability.chi 0)) :=
    Work.Stability.chi_continuous.continuousAt.tendsto.comp hlog
  rw [Work.Stability.chi_zero] at h1
  simpa only [Work.FTS.EllipticEst.psiFun] using h1

/-! ## 3. The unconditional `ℝ≥0∞` Agmon inequality -/

/-- **The unconditional `ℝ≥0∞` weighted Agmon inequality.**  For `w z = (1+z)²/z²`,
`ρ = w²`, `rDz h = z h'`, every `0 < α ≤ 1` and every `h` which is `C^∞` on `(0,∞)`,

  `α² ∫⁻_{[0,∞)} ρ (rDz h)² ≤ C ((∫⁻_{[0,∞)} ρ h²) + α⁴ (∫⁻_{[0,∞)} ρ (z²h'')²))`

with `C` universal. -/
theorem rDz_agmon_lintegral_fts : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    ∀ (h : ℝ → ℝ), ContDiffOn ℝ Work.Stability.smoothOrder h (Set.Ioi 0) →
    ENNReal.ofReal (α ^ 2) * (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (rDz h z) ^ 2))
      ≤ ENNReal.ofReal C * ((∫⁻ z in Work.Spaces.Iz,
            ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (h z) ^ 2))
          + ENNReal.ofReal (α ^ 4) * (∫⁻ z in Work.Spaces.Iz,
            ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2))) := by
  obtain ⟨K, hK0, hKb, -, -⟩ := Work.R1G7.chi_deriv_bound
  have hφcd : ContDiff ℝ Work.Stability.smoothOrder Work.Stability.chi := by
    simpa only [Work.Stability.smoothOrder] using Work.Stability.chi_contDiff
  have hφ0z : ∀ t : ℝ, 2 ≤ |t| → Work.Stability.chi t = 0 := fun t ht =>
    Work.Stability.chi_eq_zero ht
  have hφbdd : ∀ t : ℝ, 0 ≤ Work.Stability.chi t ∧ Work.Stability.chi t ≤ 1 := fun t =>
    ⟨Work.Stability.chi_nonneg t, Work.Stability.chi_le_one t⟩
  have hφcont : ContinuousAt Work.Stability.chi 0 := Work.Stability.chi_continuous.continuousAt
  have hφzero : Work.Stability.chi 0 = 1 := Work.Stability.chi_zero
  have hφanti : AntitoneOn Work.Stability.chi (Set.Ici 0) := Work.ChiExplicit.chi_antitoneOn
  set Kc0 : ℝ := K / Real.log 2 with hKc0def
  have hKc0 : 0 ≤ Kc0 := by
    rw [hKc0def]; exact div_nonneg hK0 (Real.log_pos (by norm_num)).le
  set C0 : ℝ := 100 + 100 * (Kc0 * (Kc0 + 1)) with hC0def
  have hC0 : 0 < C0 := by
    rw [hC0def]
    nlinarith only [hKc0, sq_nonneg Kc0]
  refine ⟨C0, hC0, ?_⟩
  intro α hα hα1 h hh
  have hα2pos : 0 < α ^ 2 := pow_pos hα 2
  have hα4pos : 0 < α ^ 4 := pow_pos hα 4
  -- trivial cases: one of the two sibling integrals is `⊤`
  by_cases hPtop : (∫⁻ z in Work.Spaces.Iz,
      ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (h z) ^ 2)) = ⊤
  · rw [hPtop, top_add, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hC0))]
    exact le_top
  by_cases hQtop : (∫⁻ z in Work.Spaces.Iz,
      ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2)) = ⊤
  · have h4 : ENNReal.ofReal (α ^ 4) * ⊤ = ⊤ :=
      ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hα4pos))
    rw [hQtop, h4, add_top, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hC0))]
    exact le_top
  -- ## the honest case
  have hIoi_eq_Ici : volume.restrict (Set.Ioi (0 : ℝ)) = volume.restrict (Set.Ici (0 : ℝ)) :=
    MeasureTheory.restrict_Ioi_eq_restrict_Ici
  have hPf : (∫⁻ z, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (h z) ^ 2)
      ∂volume.restrict (Set.Ioi (0 : ℝ))) ≠ ⊤ := by
    simpa only [Work.Spaces.Iz, hIoi_eq_Ici] using hPtop
  have hQf : (∫⁻ z, ENNReal.ofReal ((Work.Spaces.w z) ^ 2
      * (z ^ 2 * deriv (deriv h) z) ^ 2) ∂volume.restrict (Set.Ioi (0 : ℝ))) ≠ ⊤ := by
    simpa only [Work.Spaces.Iz, hIoi_eq_Ici] using hQtop
  have hw2cont : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    have h : ContinuousOn (fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2) (Set.Ioi 0) :=
      ContinuousOn.pow (ContinuousOn.div (by fun_prop) (by fun_prop)
        (fun z hz => pow_ne_zero 2 (ne_of_gt hz))) 2
    simpa only [Work.Spaces.w] using h
  have hhcont : ContinuousOn h (Set.Ioi 0) := hh.continuousOn
  have hd1 : ContDiffOn ℝ Work.Stability.smoothOrder (deriv h) (Set.Ioi 0) :=
    ((contDiffOn_infty_iff_deriv_of_isOpen (𝕜 := ℝ) (f := h) isOpen_Ioi).1 hh).2
  have hd2 : ContDiffOn ℝ Work.Stability.smoothOrder (deriv (deriv h)) (Set.Ioi 0) :=
    ((contDiffOn_infty_iff_deriv_of_isOpen (𝕜 := ℝ) (f := deriv h) isOpen_Ioi).1 hd1).2
  have hQcont : ContinuousOn (fun z : ℝ => (z ^ 2 * deriv (deriv h) z) ^ 2) (Set.Ioi 0) :=
    ((continuousOn_id.pow 2).mul hd2.continuousOn).pow 2
  have hPint : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (h z) ^ 2) (Set.Ioi 0) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      ((hw2cont.mul (hhcont.pow 2)).aestronglyMeasurable measurableSet_Ioi)
      (Filter.Eventually.of_forall
        (fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)))).1 hPf
  have hQint : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2)
      (Set.Ioi 0) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      ((hw2cont.mul hQcont).aestronglyMeasurable measurableSet_Ioi)
      (Filter.Eventually.of_forall
        (fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)))).1 hQf
  -- `P`, `Q` are the honest integrals over the whole half-line
  set P : ℝ := ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * (h z) ^ 2 with hPdef
  set Q : ℝ := ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2
    with hQdef
  have hPnn : 0 ≤ P := by
    rw [hPdef]
    exact setIntegral_nonneg measurableSet_Ici (fun z _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hQnn : 0 ≤ Q := by
    rw [hQdef]
    exact setIntegral_nonneg measurableSet_Ici (fun z _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hh2 : ContDiffOn ℝ 2 h (Set.Ioi 0) := hh.of_le (by simp [Work.Stability.smoothOrder])
  -- ## the estimate at cut-off level
  have hkey : ∀ n : ℕ,
      IntegrableOn (cutF h (Work.FTS.EllipticEst.psiFun Work.Stability.chi (n + 2)))
        (Set.Ioi 0) ∧
      α ^ 2 * (∫ z in Set.Ioi 0,
          cutF h (Work.FTS.EllipticEst.psiFun Work.Stability.chi (n + 2)) z)
        ≤ C0 * (P + α ^ 4 * Q) := by
    intro n
    set k : ℕ := n + 2 with hkdef
    set ψ : ℝ → ℝ := Work.FTS.EllipticEst.psiFun Work.Stability.chi k with hψdef
    set Kc : ℝ := K / Real.log (k : ℝ) with hKcdef
    set cK : ℝ := 9 + 12 * Kc * (Kc + 1) with hcKdef
    have hk : 2 ≤ k := by omega
    have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hlogk_pos : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
    have hKc : 0 ≤ Kc := by
      rw [hKcdef]; exact div_nonneg hK0 hlogk_pos.le
    have hcle : Kc ≤ Kc0 := by
      rw [hKcdef, hKc0def]
      exact div_le_div_of_nonneg_left hK0 (Real.log_pos (by norm_num))
        (Real.log_le_log (by norm_num) hkR)
    have hcK0 : 0 ≤ cK := by rw [hcKdef]; positivity
    have hψsm : ContDiffOn ℝ Work.Stability.smoothOrder ψ (Set.Ioi 0) := by
      rw [hψdef]
      exact Work.FTS.EllipticEst.ZCuts.psiFun_contDiffOn hφcd hk
    have hψ2sm : ContDiffOn ℝ 2 ψ (Set.Ioi 0) :=
      hψsm.of_le (by simp [Work.Stability.smoothOrder])
    have hψK : ∀ z ∈ Set.Ioi (0 : ℝ), |z * deriv ψ z| ≤ Kc := by
      intro z hz
      rw [hKcdef, hψdef]
      exact Work.FTS.EllipticEst.ZCuts.abs_mul_deriv_psiFun_le hφcd hKb hk hz
    have hψsupp : ∀ z : ℝ, 0 < z → z ≤ 1 / (k : ℝ) ^ 2 ∨ (k : ℝ) ^ 2 ≤ z → ψ z = 0 := by
      intro z hz h
      rw [hψdef]
      exact Work.FTS.EllipticEst.ZCuts.psiFun_eq_zero (k := k) hφ0z hk hz h
    have hψle1 : ∀ z : ℝ, |ψ z| ≤ 1 := by
      intro z
      have hmem := Work.FTS.EllipticEst.ZCuts.psiFun_mem_Icc (k := k) hφbdd z
      rw [hψdef]
      exact abs_le.mpr ⟨by linarith [hmem.1], hmem.2⟩
    have ha : (0 : ℝ) < 1 / (k : ℝ) ^ 2 := by positivity
    have hab : 1 / (k : ℝ) ^ 2 < (k : ℝ) ^ 2 := by
      have hk2 : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith only [hkR]
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) ^ 2)]
      nlinarith only [hk2]
    obtain ⟨hFint, hGint, hIBPeq⟩ :=
      cut_IBP h ψ (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) ha hab hh2 hψ2sm hψsupp
    -- integrability of the two siblings
    have hH_int : IntegrableOn (cutH h) (Set.Ioi 0) := by
      have hfun : cutH h = fun z => (Work.Spaces.w z) ^ 2 * (h z) ^ 2 := by
        funext z
        simp only [cutH, cutRho]
      rw [hfun]
      exact hPint
    have hcont_Qs : ContinuousOn (cutQs h ψ) (Set.Ioi 0) :=
      ((hw2cont.mul (hψsm.continuousOn.pow 2)).mul hQcont)
    have hQs_int : IntegrableOn (cutQs h ψ) (Set.Ioi 0) := by
      refine Integrable.mono' hQint (hcont_Qs.aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
      have hnn : 0 ≤ cutQs h ψ z := by
        simp only [cutQs, cutRho]
        exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      simp only [cutQs, cutRho]
      have hw : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      have hψ2 : ψ z ^ 2 ≤ 1 := sq_le_one_of_abs_le_one (hψle1 z)
      have hZ : (0 : ℝ) ≤ (z ^ 2 * deriv (deriv h) z) ^ 2 := sq_nonneg _
      have hprod : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2 :=
        mul_nonneg hw hZ
      have h := mul_le_mul_of_nonneg_left hψ2 hprod
      linarith only [h]
    -- the (cleared) pointwise bound
    have hpt : ∀ z ∈ Set.Ioi (0 : ℝ),
        12 * (α ^ 2 * |deriv (cutU h ψ) z * h z|)
          ≤ 12 * ((1 / 3 + α ^ 2 / 4) * (α ^ 2 * cutF h ψ z))
            + 12 * ((cK * α ^ 2 + 2) * cutH h z)
            + 12 * ((α ^ 4 / 4) * cutQs h ψ z) := by
      intro z hz
      have hD := abs_deriv_cutU_mul_le h ψ Kc hh2 hψ2sm hψle1 hψK z hz
      have hr : rDzIter 2 h z = z * deriv h z + z ^ 2 * deriv (deriv h) z :=
        rDzIter_two_eq hh2 hz
      have hD' : |deriv (cutU h ψ) z|
          ≤ 3 * cutRho z * |ψ z| ^ 2 * |z * deriv h z|
            + 2 * Kc * cutRho z * |ψ z| * |z * deriv h z|
            + cutRho z * |ψ z| ^ 2 * (|z * deriv h z| + |z ^ 2 * deriv (deriv h) z|) := by
        rw [hr] at hD
        have h2 : |z * deriv h z + z ^ 2 * deriv (deriv h) z|
            ≤ |z * deriv h z| + |z ^ 2 * deriv (deriv h) z| := abs_add_le _ _
        have h3 : ψ z ^ 2 = |ψ z| ^ 2 := (sq_abs (ψ z)).symm
        rw [h3] at hD
        have hcut : cutRho z * |ψ z| ^ 2 * |z * deriv h z + z ^ 2 * deriv (deriv h) z|
            ≤ cutRho z * |ψ z| ^ 2
              * (|z * deriv h z| + |z ^ 2 * deriv (deriv h) z|) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg (cutRho_nonneg z) (sq_nonneg _))
        linarith only [hD, hcut]
      have hkey' := pointwise_final (α := α) (Kc := Kc) (W := cutRho z) (p := |ψ z|)
        (A := |z * deriv h z|) (Z := |z ^ 2 * deriv (deriv h) z|) (B := |h z|)
        (D := |deriv (cutU h ψ) z|) hα hKc (cutRho_nonneg z) (abs_nonneg _) (hψle1 z)
        (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) hD'
      have hp2 : |ψ z| ^ 2 = ψ z ^ 2 := sq_abs (ψ z)
      have hA2 : |z * deriv h z| ^ 2 = (z * deriv h z) ^ 2 := sq_abs _
      have hZ2 : |z ^ 2 * deriv (deriv h) z| ^ 2 = (z ^ 2 * deriv (deriv h) z) ^ 2 := sq_abs _
      have hB2 : |h z| ^ 2 = (h z) ^ 2 := sq_abs (h z)
      have habs : |deriv (cutU h ψ) z * h z| = |deriv (cutU h ψ) z| * |h z| := abs_mul _ _
      simp only [cutF, cutH, cutQs]
      rw [hcKdef, habs, ← hp2, ← hA2, ← hZ2, ← hB2]
      exact hkey'
    -- the absorption (cleared by 12)
    set G : ℝ → ℝ := fun z => 12 * ((1 / 3 + α ^ 2 / 4) * (α ^ 2 * cutF h ψ z))
        + 12 * ((cK * α ^ 2 + 2) * cutH h z) + 12 * ((α ^ 4 / 4) * cutQs h ψ z) with hGdef
    have hcombo_int : IntegrableOn G (Set.Ioi 0) := by
      rw [hGdef]
      have hA : IntegrableOn (fun z => (1 / 3 + α ^ 2 / 4) * (α ^ 2 * cutF h ψ z)) (Set.Ioi 0) :=
        (hFint.const_mul (α ^ 2)).const_mul _
      have hB : IntegrableOn (fun z => (cK * α ^ 2 + 2) * cutH h z) (Set.Ioi 0) :=
        hH_int.const_mul _
      have hC : IntegrableOn (fun z => (α ^ 4 / 4) * cutQs h ψ z) (Set.Ioi 0) :=
        hQs_int.const_mul _
      exact ((hA.const_mul 12).add (hB.const_mul 12)).add (hC.const_mul 12)
    have hXleAbs : 12 * (α ^ 2 * (∫ z in Set.Ioi 0, cutF h ψ z))
        ≤ ∫ z in Set.Ioi 0, 12 * (α ^ 2 * |deriv (cutU h ψ) z * h z|) := by
      have hcut : (∫ z in Set.Ioi 0, cutF h ψ z)
          = -(∫ z in Set.Ioi 0, deriv (cutU h ψ) z * h z) := hIBPeq
      have hnorm := MeasureTheory.norm_integral_le_integral_norm
        (μ := volume.restrict (Set.Ioi (0 : ℝ)))
        (fun z => deriv (cutU h ψ) z * h z)
      rw [Real.norm_eq_abs] at hnorm
      simp_rw [Real.norm_eq_abs] at hnorm
      have h1 : -(∫ z in Set.Ioi 0, deriv (cutU h ψ) z * h z)
          ≤ ∫ z in Set.Ioi 0, |deriv (cutU h ψ) z * h z| := (neg_le_abs _).trans hnorm
      have h2 : 12 * (α ^ 2 * (∫ z in Set.Ioi 0, |deriv (cutU h ψ) z * h z|))
          = ∫ z in Set.Ioi 0, 12 * (α ^ 2 * |deriv (cutU h ψ) z * h z|) := by
        rw [integral_const_mul, integral_const_mul]
      rw [hcut, ← h2]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (le_of_lt hα2pos))
        (by norm_num)
    have hAbsLe : (∫ z in Set.Ioi 0, 12 * (α ^ 2 * |deriv (cutU h ψ) z * h z|))
        ≤ ∫ z in Set.Ioi 0, G z := by
      rw [hGdef]
      refine integral_mono_of_nonneg
        (Filter.Eventually.of_forall
          (fun z => mul_nonneg (by norm_num) (mul_nonneg (le_of_lt hα2pos) (abs_nonneg _))))
        hcombo_int ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
      exact hpt z hz
    have hsplit : (∫ z in Set.Ioi 0, G z)
        = 12 * ((1 / 3 + α ^ 2 / 4) * (α ^ 2 * (∫ z in Set.Ioi 0, cutF h ψ z)))
          + 12 * ((cK * α ^ 2 + 2) * (∫ z in Set.Ioi 0, cutH h z))
          + 12 * ((α ^ 4 / 4) * (∫ z in Set.Ioi 0, cutQs h ψ z)) := by
      rw [hGdef]
      have hA : IntegrableOn (fun z => (1 / 3 + α ^ 2 / 4) * (α ^ 2 * cutF h ψ z)) (Set.Ioi 0) :=
        (hFint.const_mul (α ^ 2)).const_mul _
      have hB : IntegrableOn (fun z => (cK * α ^ 2 + 2) * cutH h z) (Set.Ioi 0) :=
        hH_int.const_mul _
      have hC : IntegrableOn (fun z => (α ^ 4 / 4) * cutQs h ψ z) (Set.Ioi 0) :=
        hQs_int.const_mul _
      have hA' : IntegrableOn (fun z => 12 * ((1 / 3 + α ^ 2 / 4) * (α ^ 2 * cutF h ψ z)))
          (Set.Ioi 0) := hA.const_mul 12
      have hB' : IntegrableOn (fun z => 12 * ((cK * α ^ 2 + 2) * cutH h z)) (Set.Ioi 0) :=
        hB.const_mul 12
      have hC' : IntegrableOn (fun z => 12 * ((α ^ 4 / 4) * cutQs h ψ z)) (Set.Ioi 0) :=
        hC.const_mul 12
      have e1 : (∫ z in Set.Ioi 0, (12 * ((1 / 3 + α ^ 2 / 4) * (α ^ 2 * cutF h ψ z))
            + 12 * ((cK * α ^ 2 + 2) * cutH h z) + 12 * ((α ^ 4 / 4) * cutQs h ψ z)))
          = (∫ z in Set.Ioi 0, (12 * ((1 / 3 + α ^ 2 / 4) * (α ^ 2 * cutF h ψ z))
                + 12 * ((cK * α ^ 2 + 2) * cutH h z)))
            + (∫ z in Set.Ioi 0, 12 * ((α ^ 4 / 4) * cutQs h ψ z)) := by
        have h := integral_add (μ := volume.restrict (Set.Ioi (0 : ℝ)))
          (hA'.add hB') hC'
        simpa using h
      have e2 : (∫ z in Set.Ioi 0, (12 * ((1 / 3 + α ^ 2 / 4) * (α ^ 2 * cutF h ψ z))
              + 12 * ((cK * α ^ 2 + 2) * cutH h z)))
          = (∫ z in Set.Ioi 0, 12 * ((1 / 3 + α ^ 2 / 4) * (α ^ 2 * cutF h ψ z)))
            + (∫ z in Set.Ioi 0, 12 * ((cK * α ^ 2 + 2) * cutH h z)) := by
        have h := integral_add (μ := volume.restrict (Set.Ioi (0 : ℝ))) hA' hB'
        simpa using h
      have e3 : (∫ z in Set.Ioi 0, 12 * ((1 / 3 + α ^ 2 / 4) * (α ^ 2 * cutF h ψ z)))
          = 12 * ((1 / 3 + α ^ 2 / 4) * (α ^ 2 * (∫ z in Set.Ioi 0, cutF h ψ z))) := by
        rw [integral_const_mul, integral_const_mul, integral_const_mul]
      have e4 : (∫ z in Set.Ioi 0, 12 * ((cK * α ^ 2 + 2) * cutH h z))
          = 12 * ((cK * α ^ 2 + 2) * (∫ z in Set.Ioi 0, cutH h z)) := by
        rw [integral_const_mul, integral_const_mul]
      have e5 : (∫ z in Set.Ioi 0, 12 * ((α ^ 4 / 4) * cutQs h ψ z))
          = 12 * ((α ^ 4 / 4) * (∫ z in Set.Ioi 0, cutQs h ψ z)) := by
        rw [integral_const_mul, integral_const_mul]
      rw [e1, e2, e3, e4, e5]
    have hHval : (∫ z in Set.Ioi 0, cutH h z) = P := by
      have hfun : cutH h = fun z => (Work.Spaces.w z) ^ 2 * (h z) ^ 2 := by
        funext z
        simp only [cutH, cutRho]
      rw [hfun, hPdef, Work.Spaces.Iz, ← MeasureTheory.integral_Ici_eq_integral_Ioi]
    have hQsle : (∫ z in Set.Ioi 0, cutQs h ψ z) ≤ Q := by
      have hQeq : Q = ∫ z in Set.Ioi 0,
          (Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2 := by
        rw [hQdef, Work.Spaces.Iz, MeasureTheory.integral_Ici_eq_integral_Ioi]
      rw [hQeq]
      refine integral_mono_of_nonneg ?_ hQint ?_
      · filter_upwards with z
        simp only [cutQs, cutRho]
        exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
      · filter_upwards with z
        simp only [cutQs, cutRho]
        have hw : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
        have hψ2 : ψ z ^ 2 ≤ 1 := sq_le_one_of_abs_le_one (hψle1 z)
        have hZ : (0 : ℝ) ≤ (z ^ 2 * deriv (deriv h) z) ^ 2 := sq_nonneg _
        have hprod : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2 :=
          mul_nonneg hw hZ
        have h := mul_le_mul_of_nonneg_left hψ2 hprod
        linarith only [h]
    have hmain : α ^ 2 * (∫ z in Set.Ioi 0, cutF h ψ z) ≤ C0 * (P + α ^ 4 * Q) := by
      have h12 : 12 * (α ^ 2 * (∫ z in Set.Ioi 0, cutF h ψ z))
          ≤ 12 * ((1 / 3 + α ^ 2 / 4) * (α ^ 2 * (∫ z in Set.Ioi 0, cutF h ψ z)))
            + 12 * ((cK * α ^ 2 + 2) * P) + 12 * ((α ^ 4 / 4) * Q) := by
        calc 12 * (α ^ 2 * (∫ z in Set.Ioi 0, cutF h ψ z))
            ≤ ∫ z in Set.Ioi 0, 12 * (α ^ 2 * |deriv (cutU h ψ) z * h z|) := hXleAbs
          _ ≤ ∫ z in Set.Ioi 0, G z := hAbsLe
          _ = _ := hsplit
          _ ≤ 12 * ((1 / 3 + α ^ 2 / 4) * (α ^ 2 * (∫ z in Set.Ioi 0, cutF h ψ z)))
              + 12 * ((cK * α ^ 2 + 2) * P) + 12 * ((α ^ 4 / 4) * Q) := by
            rw [hHval]
            exact add_le_add (add_le_add le_rfl le_rfl)
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hQsle (by positivity)) (by norm_num))
      have hstep : α ^ 2 * (∫ z in Set.Ioi 0, cutF h ψ z)
          ≤ (1 / 3 + α ^ 2 / 4) * (α ^ 2 * (∫ z in Set.Ioi 0, cutF h ψ z))
            + (cK * α ^ 2 + 2) * P + (α ^ 4 / 4) * Q := by
        linarith only [h12]
      have hcc : cK ≤ 9 + 12 * Kc0 * (Kc0 + 1) := by
        rw [hcKdef]
        nlinarith only [hKc, hcle, hKc0, sq_nonneg Kc, sq_nonneg Kc0]
      have hXn : 0 ≤ ∫ z in Set.Ioi 0, cutF h ψ z := by
        refine integral_nonneg (fun z => ?_)
        simp only [cutF, cutRho]
        exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
      have hC1 : (12 / 5) * ((9 + 12 * Kc0 * (Kc0 + 1)) + 2) ≤ C0 := by
        rw [hC0def]
        nlinarith only [hKc0, sq_nonneg Kc0]
      have hC2 : (12 / 5 : ℝ) ≤ C0 := by
        rw [hC0def]
        nlinarith only [hKc0, sq_nonneg Kc0]
      exact arith_final (α := α) (X := ∫ z in Set.Ioi 0, cutF h ψ z) (P := P) (Q := Q)
        (c := cK) (c0 := 9 + 12 * Kc0 * (Kc0 + 1)) (C0 := C0) hα hα1 hXn hPnn hQnn hcK0
        (by nlinarith only [hKc0, sq_nonneg Kc0]) hcc hC1 hC2 hstep
    exact ⟨hFint, hmain⟩
  -- ## monotone convergence
  have hmeas : ∀ n : ℕ, AEMeasurable
      (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2
        * (Work.FTS.EllipticEst.psiFun Work.Stability.chi (n + 2) z) ^ 2
        * (z * deriv h z) ^ 2)) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    intro n
    have hpsi : ContDiffOn ℝ Work.Stability.smoothOrder
        (Work.FTS.EllipticEst.psiFun Work.Stability.chi (n + 2)) (Set.Ioi 0) :=
      Work.FTS.EllipticEst.ZCuts.psiFun_contDiffOn hφcd (by omega)
    have hdh : ContinuousOn (deriv h) (Set.Ioi 0) := hd1.continuousOn
    have hcont : ContinuousOn (fun z => (Work.Spaces.w z) ^ 2
        * (Work.FTS.EllipticEst.psiFun Work.Stability.chi (n + 2) z) ^ 2
        * (z * deriv h z) ^ 2) (Set.Ioi 0) :=
      (hw2cont.mul (hpsi.continuousOn.pow 2)).mul ((continuousOn_id.mul hdh).pow 2)
    exact ((ENNReal.continuous_ofReal.comp_continuousOn hcont).aestronglyMeasurable
      measurableSet_Ioi).aemeasurable
  have hmono : ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))), Monotone
      (fun n : ℕ => ENNReal.ofReal ((Work.Spaces.w z) ^ 2
        * (Work.FTS.EllipticEst.psiFun Work.Stability.chi (n + 2) z) ^ 2
        * (z * deriv h z) ^ 2)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
    intro n m hnm
    have h1 : Work.FTS.EllipticEst.psiFun Work.Stability.chi (n + 2) z
        ≤ Work.FTS.EllipticEst.psiFun Work.Stability.chi (m + 2) z :=
      chi_psiFun_mono hz (n + 2) (m + 2) (by omega) (by omega)
    have h0n : 0 ≤ Work.FTS.EllipticEst.psiFun Work.Stability.chi (n + 2) z :=
      (Work.FTS.EllipticEst.ZCuts.psiFun_mem_Icc (k := n + 2) hφbdd z).1
    have h3 : (Work.FTS.EllipticEst.psiFun Work.Stability.chi (n + 2) z) ^ 2
        ≤ (Work.FTS.EllipticEst.psiFun Work.Stability.chi (m + 2) z) ^ 2 := by
      have h := mul_self_le_mul_self h0n h1
      simpa only [sq] using h
    refine ENNReal.ofReal_le_ofReal ?_
    have hw : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have hz : (0 : ℝ) ≤ (z * deriv h z) ^ 2 := sq_nonneg _
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hw) hz
    nlinarith only [h]
  have htendsto : ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))), Filter.Tendsto
      (fun n : ℕ => ENNReal.ofReal ((Work.Spaces.w z) ^ 2
        * (Work.FTS.EllipticEst.psiFun Work.Stability.chi (n + 2) z) ^ 2
        * (z * deriv h z) ^ 2))
      Filter.atTop (nhds (ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2))) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
    have h1 : Filter.Tendsto
        (fun n : ℕ => Work.FTS.EllipticEst.psiFun Work.Stability.chi (n + 2) z)
        Filter.atTop (nhds 1) :=
      (chi_psiFun_tendsto_one hz).comp (Filter.tendsto_add_atTop_nat 2)
    have h2 : Filter.Tendsto
        (fun n : ℕ => (Work.FTS.EllipticEst.psiFun Work.Stability.chi (n + 2) z) ^ 2)
        Filter.atTop (nhds 1) := by simpa using h1.pow 2
    have h3 : Filter.Tendsto
        (fun n : ℕ => (Work.Spaces.w z) ^ 2
          * (Work.FTS.EllipticEst.psiFun Work.Stability.chi (n + 2) z) ^ 2
          * (z * deriv h z) ^ 2) Filter.atTop
        (nhds ((Work.Spaces.w z) ^ 2 * 1 * (z * deriv h z) ^ 2)) :=
      (tendsto_const_nhds.mul h2).mul tendsto_const_nhds
    have h4 := ENNReal.continuous_ofReal.tendsto _ |>.comp h3
    simpa only [Function.comp_def, mul_one] using h4
  have hconv := MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone hmeas hmono htendsto
  -- the `α²`-weighted bound for the uncut integrand
  have hFatou : ENNReal.ofReal (α ^ 2)
      * (∫⁻ z, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2)
          ∂volume.restrict (Set.Ioi (0 : ℝ))) ≤ ENNReal.ofReal (C0 * (P + α ^ 4 * Q)) := by
    have hcontmul := (ENNReal.continuous_const_mul
      (ENNReal.ofReal_ne_top (r := α ^ 2))).tendsto
      (∫⁻ z, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2)
        ∂volume.restrict (Set.Ioi (0 : ℝ)))
    refine le_of_tendsto (hcontmul.comp hconv) (Filter.Eventually.of_forall ?_)
    intro n
    have hInt : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
        * (Work.FTS.EllipticEst.psiFun Work.Stability.chi (n + 2) z) ^ 2
        * (z * deriv h z) ^ 2) (Set.Ioi 0) := (hkey n).1
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] (fun z => (Work.Spaces.w z) ^ 2
        * (Work.FTS.EllipticEst.psiFun Work.Stability.chi (n + 2) z) ^ 2
        * (z * deriv h z) ^ 2) :=
      Filter.Eventually.of_forall
        (fun z => mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))
    simp only [Function.comp_apply]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn]
    rw [← ENNReal.ofReal_mul (le_of_lt hα2pos)]
    refine ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mpr ?_
    have h2 := (hkey n).2
    simp only [cutF, cutRho] at h2
    exact h2
  -- back to `Iz` and to the two honest integrals
  have hgoal_eq : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (rDz h z) ^ 2))
      = ∫⁻ z, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2)
          ∂volume.restrict (Set.Ioi (0 : ℝ)) := by
    show (∫⁻ z, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2)
          ∂volume.restrict (Set.Ici (0 : ℝ)))
        = ∫⁻ z, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2)
          ∂volume.restrict (Set.Ioi (0 : ℝ))
    rw [← hIoi_eq_Ici]
  have hPeq : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (h z) ^ 2)) = ENNReal.ofReal P := by
    have h := Work.FTS.EllipticEst.ofReal_integral_eq_lintegral_Iz
      (g := fun z => (Work.Spaces.w z) ^ 2 * (h z) ^ 2)
      (hw2cont.mul (hhcont.pow 2))
      (fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hPtop
    rw [hPdef, h]
  have hQeq : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2))
      = ENNReal.ofReal Q := by
    have h := Work.FTS.EllipticEst.ofReal_integral_eq_lintegral_Iz
      (g := fun z => (Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2)
      (hw2cont.mul hQcont)
      (fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hQtop
    rw [hQdef, h]
  rw [hgoal_eq, hPeq, hQeq]
  refine hFatou.trans (le_of_eq ?_)
  have h1 : ENNReal.ofReal (C0 * (P + α ^ 4 * Q))
      = ENNReal.ofReal C0 * ENNReal.ofReal (P + α ^ 4 * Q) :=
    ENNReal.ofReal_mul (le_of_lt hC0)
  have h2 : ENNReal.ofReal (P + α ^ 4 * Q)
      = ENNReal.ofReal P + ENNReal.ofReal (α ^ 4) * ENNReal.ofReal Q := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (le_of_lt hα4pos)]
  rw [h1, h2]

end Work.FTS.EllipticEst.AgmonFts
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.GbarRdzIterIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

open Work.FTS.EllipticEst.Cert.GbarSin

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Two elementary facts about the radial weight -/

/-- The radial weight `w(z)² = ((1+z)²/z²)²` is continuous on `(0,∞)`. -/
theorem continuousOn_w_sq :
    ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have hw0 : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
    unfold Work.Spaces.w
    exact ((continuous_const.add continuous_id).pow 2).continuousOn.div
      (continuous_id.pow 2).continuousOn (fun z hz => by
        simp only [Set.mem_Ioi] at hz
        positivity)
  exact hw0.pow 2

/-- The radial weight dominates `1` on `(0,∞)`: `w(z) = (1+z)²/z² ≥ 1` for `z > 0`. -/
theorem one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  have hz2 : (0 : ℝ) < z ^ 2 := pow_pos hz 2
  rw [Work.Spaces.w, le_div_iff₀ hz2]
  nlinarith

/-! ## The real-integral form of the weighted Hardy inequality -/


/-! ## Continuity of the Hardy operator applied to the angular moment -/


/-! ## The main theorem -/


end Work.FTS.EllipticEst.Cert
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.GbarSin_layer =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert

open scoped Real Topology
open MeasureTheory Set Filter


end Work.FTS.EllipticEst.Cert
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Dispatch.aeFirstEnergyDTools =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Dispatch

set_option autoImplicit false
set_option linter.unusedVariables false

abbrev AeData := Work.FTS.EllipticEst.H2W.Ae.AeData

/-! ## The truncated radial weights -/

/-- The radial weight `χ z · w(z)²` of the truncated energy identity. -/
def Wcut (χ : ℝ → ℝ) : ℝ → ℝ := fun z => χ z * (Work.Spaces.w z) ^ 2




/-! ## The weights -/

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
theorem sin_two_nonneg_Iθ_D {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin(2θ) > 0` on the open interval. -/
theorem sin_two_pos_Ioo_D {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `σ θ = sin(2θ)^{-η} ≥ 0` on `Iθ`. -/
theorem sEta_nonneg_Iθ_D {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ :=
  Real.rpow_nonneg (sin_two_nonneg_Iθ_D hθ) _

/-- `1 ≤ σ θ` on the open interval. -/
theorem one_le_sEta_D {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  have hpos := sin_two_pos_Ioo_D hθ
  have hle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h := Real.rpow_le_rpow_of_nonpos hpos hle
    (show -(Work.Spaces.eta) ≤ 0 by norm_num [Work.Spaces.eta])
  rwa [Real.one_rpow] at h


theorem w_pos_D {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

theorem one_le_w_D {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0:ℝ) < z ^ 2)]
  nlinarith

/-! ## The level-`0` integrand -/

/-- On `Iθ` the level-`0` integrand is `w(z)² · g² · σ`. -/
theorem HkIntegrand_zero_D (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq, mul_pow,
    Work.FTS.EllipticEst.Honest.sq_weight_eq (sin_two_nonneg_Iθ_D hθ)]
  simp only [Work.FTS.EllipticEst.sEta]
  ring


/-! ## Slicewise honesty from the `ℋ⁰`-memberships -/

/-- **`σ`-honesty of the `θ`-slice of a function whose `ℋ⁰`-integrand is honest.** -/
theorem slice_sigma_sq_of_hkMem_D {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hm : Work.Spaces.HkMem α 0 g) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
  have h0 := hm.1 z (le_of_lt hz)
  have h1 := h0.const_mul (1 / (Work.Spaces.w z) ^ 2)
  have hw : Work.Spaces.w z ≠ 0 := ne_of_gt (w_pos_D hz)
  refine h1.congr ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
  show (1 / (Work.Spaces.w z) ^ 2) * Work.Spaces.HkIntegrand α 0 g z θ
    = (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
  rw [HkIntegrand_zero_D α g hθ, ← mul_assoc, one_div,
    inv_mul_cancel₀ (pow_ne_zero 2 hw), one_mul]



/-! ## The `z`-slices -/

/-- For interior `θ` the `z`-slice of an `AeData` datum is `C^∞` on `(0,∞)`. -/
theorem slice_z_smooth_D {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (n : ℕ) :
    ContDiffOn ℝ n (fun z => u z θ) (Set.Ioi 0) := by
  have hSO : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  exact contDiffOn_iff_forall_nat_le.mp (hSO.curry_z hθ) n le_top



end Work.FTS.EllipticEst.Dispatch
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Final.Rep.Mine.TopSlotTwo =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Mine

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## The pointwise expansion of `D_θ²` and the weight algebra -/

/-- **The expansion of `D_θ²`**: `D_θ²f = sin²(2θ)·∂_θ²f + 2 sin(2θ)cos(2θ)·∂_θf`. -/
theorem DthIter_two_eq (f : ℝ → ℝ → ℝ) (z θ : ℝ)
    (h2 : DifferentiableAt ℝ (fun θ' => deriv (fun t => f z t) θ') θ) :
    Work.Spaces.DthIter 2 f z θ
      = (Real.sin (2 * θ)) ^ 2 * deriv (fun θ' => deriv (fun t => f z t) θ') θ
        + 2 * Real.sin (2 * θ) * Real.cos (2 * θ) * deriv (fun t => f z t) θ := by
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
    have h1 : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have h2' := h1.sin
    rw [show Real.cos (2 * θ) * 2 = 2 * Real.cos (2 * θ) by ring] at h2'
    exact h2'
  have hd2 : deriv (fun t => Real.sin (2 * t) * deriv (fun t' => f z t') t) θ
      = 2 * Real.cos (2 * θ) * deriv (fun t => f z t) θ
        + Real.sin (2 * θ) * deriv (fun θ' => deriv (fun t => f z t) θ') θ := by
    have heq : (fun t : ℝ => Real.sin (2 * t) * deriv (fun t' => f z t') t)
        = (fun t : ℝ => Real.sin (2 * t)) * (fun t : ℝ => deriv (fun t' => f z t') t) := rfl
    rw [heq, deriv_mul hsin.differentiableAt h2, hsin.deriv]
  show Real.sin (2 * θ) *
      deriv (fun t => Real.sin (2 * t) * deriv (fun t' => f z t') t) θ = _
  rw [hd2]
  ring

/-- **The squared `D_θ²`-weight identity**: for `θ` in the open interval the `Tk`-integrand at
level `2` is `w(z)²` times the square of the expansion, weighted by `sGam`. -/
theorem Tk_pointwise_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : 0 < θ)
    (hθ' : θ < Real.pi / 2)
    (h2 : DifferentiableAt ℝ (fun θ' => deriv (fun t => f z t) θ') θ) :
    (Work.Spaces.DthIter 2 f z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 *
          (((Real.sin (2 * θ)) ^ 2 * deriv (fun θ' => deriv (fun t => f z t) θ') θ
              + 2 * Real.sin (2 * θ) * Real.cos (2 * θ) * deriv (fun t => f z t) θ) ^ 2
            * Work.FTS.EllipticEst.sGam α θ) := by
  rw [DthIter_two_eq f z θ h2, mix_term_eq ⟨hθ.le, hθ'.le⟩ α z]

/-- `sin²(2θ)·sGam α θ = σ₂` on the open interval. -/
theorem sin_sq_mul_sGam (α : ℝ) {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    (Real.sin (2 * θ)) ^ 2 * Work.FTS.EllipticEst.sGam α θ
      = sig2 (Work.Spaces.gam α) θ := by
  have hs : 0 < Real.sin (2 * θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]
  have h : (Real.sin (2 * θ)) ^ 2 * Work.FTS.EllipticEst.sGam α θ
      = (Real.sin (2 * θ)) ^ ((2 : ℝ) + (-(Work.Spaces.gam α))) := by
    rw [Work.FTS.EllipticEst.sGam, ← Real.rpow_ofNat, ← Real.rpow_add hs]
  rw [h, show (2 : ℝ) + (-(Work.Spaces.gam α)) = 2 - Work.Spaces.gam α by ring]
  rfl

/-- `sin⁴(2θ)·sGam α θ = σ₄` on the open interval. -/
theorem sin_four_mul_sGam (α : ℝ) {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    (Real.sin (2 * θ)) ^ 4 * Work.FTS.EllipticEst.sGam α θ
      = sig4 (Work.Spaces.gam α) θ := by
  have hs : 0 < Real.sin (2 * θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]
  have h : (Real.sin (2 * θ)) ^ 4 * Work.FTS.EllipticEst.sGam α θ
      = (Real.sin (2 * θ)) ^ ((4 : ℝ) + (-(Work.Spaces.gam α))) := by
    rw [Work.FTS.EllipticEst.sGam, ← Real.rpow_ofNat, ← Real.rpow_add hs]
  rw [h, show (4 : ℝ) + (-(Work.Spaces.gam α)) = 4 - Work.Spaces.gam α by ring]
  rfl

/-- **The `σ₄`/`σ₂` decomposition of the level-`2` `Tk`-integrand**: pointwise,

`(D_θ²f · Wt)² ≤ 2 w²·(∂_θ²f)²·σ₄ + 8 w²·(∂_θf)²·σ₂`,

where `σ₄ = sin(2θ)^{4-γ}`, `σ₂ = sin(2θ)^{2-γ}` at `γ = gam α`.  This is the pointwise form of
`Tk α 2 f ≤ 2∫∫(∂_θ²f)²σ₄w² + 8∫∫(∂_θf)²σ₂w²`; it is the only place where the weight arithmetic
(`sin²·sGam = σ₂`, `sin⁴·sGam = σ₄`) is used. -/
theorem Tk_pointwise_le (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : 0 < θ)
    (hθ' : θ < Real.pi / 2)
    (h2 : DifferentiableAt ℝ (fun θ' => deriv (fun t => f z t) θ') θ) :
    (Work.Spaces.DthIter 2 f z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ 2 * (Work.Spaces.w z) ^ 2 *
            ((deriv (fun θ' => deriv (fun t => f z t) θ') θ) ^ 2 * sig4 (Work.Spaces.gam α) θ)
        + 8 * (Work.Spaces.w z) ^ 2 *
            ((deriv (fun t => f z t) θ) ^ 2 * sig2 (Work.Spaces.gam α) θ) := by
  have hs : 0 < Real.sin (2 * θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]
  have hg : 0 < Work.FTS.EllipticEst.sGam α θ := by
    rw [Work.FTS.EllipticEst.sGam]
    exact Real.rpow_pos_of_pos hs _
  have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  set a : ℝ := deriv (fun θ' => deriv (fun t => f z t) θ') θ with hadef
  set b : ℝ := deriv (fun t => f z t) θ with hbdef
  set s : ℝ := Real.sin (2 * θ) with hsdef
  set c : ℝ := Real.cos (2 * θ) with hcdef
  have hcore : (s ^ 2 * a + 2 * s * c * b) ^ 2 * Work.FTS.EllipticEst.sGam α θ
      ≤ 2 * (a ^ 2 * sig4 (Work.Spaces.gam α) θ)
        + 8 * (b ^ 2 * sig2 (Work.Spaces.gam α) θ) := by
    have h1 : (s ^ 2 * a + 2 * s * c * b) ^ 2
        ≤ 2 * (s ^ 2 * a) ^ 2 + 2 * (2 * s * c * b) ^ 2 := by
      nlinarith [sq_nonneg (s ^ 2 * a - 2 * s * c * b)]
    have h3 : c ^ 2 ≤ 1 := by
      rw [hcdef]
      exact Real.cos_sq_le_one (2 * θ)
    have h5 : (2 * (s ^ 2 * a) ^ 2 + 2 * (2 * s * c * b) ^ 2)
          * Work.FTS.EllipticEst.sGam α θ
        ≤ (2 * (s ^ 2 * a) ^ 2 + 2 * (2 * s * b) ^ 2)
            * Work.FTS.EllipticEst.sGam α θ := by
      have hkey : (2 * s * c * b) ^ 2 ≤ (2 * s * b) ^ 2 := by
        nlinarith [h3, sq_nonneg (2 * s * b), sq_nonneg s, sq_nonneg b]
      exact mul_le_mul_of_nonneg_right (by linarith [hkey]) hg.le
    have h6 : (2 * (s ^ 2 * a) ^ 2 + 2 * (2 * s * b) ^ 2) * Work.FTS.EllipticEst.sGam α θ
        = 2 * (a ^ 2 * (s ^ 4 * Work.FTS.EllipticEst.sGam α θ))
          + 8 * (b ^ 2 * (s ^ 2 * Work.FTS.EllipticEst.sGam α θ)) := by ring
    have h7 : s ^ 4 * Work.FTS.EllipticEst.sGam α θ = sig4 (Work.Spaces.gam α) θ := by
      rw [hsdef]
      exact sin_four_mul_sGam α hθ hθ'
    have h8 : s ^ 2 * Work.FTS.EllipticEst.sGam α θ = sig2 (Work.Spaces.gam α) θ := by
      rw [hsdef]
      exact sin_sq_mul_sGam α hθ hθ'
    calc (s ^ 2 * a + 2 * s * c * b) ^ 2 * Work.FTS.EllipticEst.sGam α θ
        ≤ (2 * (s ^ 2 * a) ^ 2 + 2 * (2 * s * c * b) ^ 2)
            * Work.FTS.EllipticEst.sGam α θ := mul_le_mul_of_nonneg_right h1 hg.le
      _ ≤ (2 * (s ^ 2 * a) ^ 2 + 2 * (2 * s * b) ^ 2)
            * Work.FTS.EllipticEst.sGam α θ := h5
      _ = 2 * (a ^ 2 * (s ^ 4 * Work.FTS.EllipticEst.sGam α θ))
            + 8 * (b ^ 2 * (s ^ 2 * Work.FTS.EllipticEst.sGam α θ)) := h6
      _ = 2 * (a ^ 2 * sig4 (Work.Spaces.gam α) θ)
            + 8 * (b ^ 2 * sig2 (Work.Spaces.gam α) θ) := by rw [h7, h8]
  rw [Tk_pointwise_eq α f z θ hθ hθ' h2]
  have hone : (Work.Spaces.w z) ^ 2
        * (((Real.sin (2 * θ)) ^ 2 * deriv (fun θ' => deriv (fun t => f z t) θ') θ
              + 2 * Real.sin (2 * θ) * Real.cos (2 * θ) * deriv (fun t => f z t) θ) ^ 2
            * Work.FTS.EllipticEst.sGam α θ)
      = (Work.Spaces.w z) ^ 2 * ((s ^ 2 * a + 2 * s * c * b) ^ 2
          * Work.FTS.EllipticEst.sGam α θ) := by
    rw [hsdef, hcdef, hadef, hbdef]
  rw [hone]
  calc (Work.Spaces.w z) ^ 2 * ((s ^ 2 * a + 2 * s * c * b) ^ 2
          * Work.FTS.EllipticEst.sGam α θ)
      ≤ (Work.Spaces.w z) ^ 2 * (2 * (a ^ 2 * sig4 (Work.Spaces.gam α) θ)
          + 8 * (b ^ 2 * sig2 (Work.Spaces.gam α) θ)) := mul_le_mul_of_nonneg_left hcore hw2
    _ = 2 * (Work.Spaces.w z) ^ 2
          * ((deriv (fun θ' => deriv (fun t => f z t) θ') θ) ^ 2 * sig4 (Work.Spaces.gam α) θ)
        + 8 * (Work.Spaces.w z) ^ 2
          * ((deriv (fun t => f z t) θ) ^ 2 * sig2 (Work.Spaces.gam α) θ) := by
        rw [hadef, hbdef]; ring

/-- `Wt` vanishes wherever `sin(2θ)` does (for `α > 0`). -/
theorem Wt_zero_of_sin_eq_zero {α z θ : ℝ} (hα : 0 < α) (h : Real.sin (2 * θ) = 0) :
    Work.Spaces.Wt α z θ = 0 := by
  have hg : Work.Spaces.gam α ≠ 0 := ne_of_gt (Work.Spaces.gam_pos hα)
  have hneg : -(Work.Spaces.gam α / 2) ≠ 0 := by
    intro hc
    exact hg (by linarith)
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, h, Real.zero_rpow hneg, mul_zero]

/-- **The closed-interval form of `Tk_pointwise_le`.**  On the closed slice `Iθ` both sides
vanish at the two endpoints (`Wt` and the weights `σ₄`, `σ₂` all vanish there, `4 - gam α` and
`2 - gam α` being non-zero for `α ≤ 1/4`), so the pointwise bound holds on all of `Iθ` as soon as
it holds on the open interval. -/
theorem Tk_pointwise_le_closed (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (f : ℝ → ℝ → ℝ)
    (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ)
    (h2 : ∀ θ' ∈ Set.Ioo 0 (Real.pi / 2),
      DifferentiableAt ℝ (fun t => deriv (fun s => f z s) t) θ') :
    (Work.Spaces.DthIter 2 f z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ 2 * (Work.Spaces.w z) ^ 2 *
            ((deriv (fun θ' => deriv (fun t => f z t) θ') θ) ^ 2 * sig4 (Work.Spaces.gam α) θ)
        + 8 * (Work.Spaces.w z) ^ 2 *
            ((deriv (fun t => f z t) θ) ^ 2 * sig2 (Work.Spaces.gam α) θ) := by
  have hgam2 : Work.Spaces.gam α ≤ 11 / 10 := by
    rw [Work.Spaces.gam]
    linarith
  rcases hθ with ⟨h0, hpi⟩
  rcases lt_or_eq_of_le h0 with h | h
  · rcases lt_or_eq_of_le hpi with h' | h'
    · exact Tk_pointwise_le α f z θ h h' (h2 θ ⟨h, h'⟩)
    · subst h'
      have hsin : Real.sin (2 * (Real.pi / 2)) = 0 := by
        rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      have hW : Work.Spaces.Wt α z (Real.pi / 2) = 0 := Wt_zero_of_sin_eq_zero hα hsin
      have hlhs : (Work.Spaces.DthIter 2 f z (Real.pi / 2)
          * Work.Spaces.Wt α z (Real.pi / 2)) ^ 2 = 0 := by simp [hW]
      have h4 : sig4 (Work.Spaces.gam α) (Real.pi / 2) = 0 := by
        rw [sig4, hsin]
        exact Real.zero_rpow (x := (4 : ℝ) - Work.Spaces.gam α) (by linarith)
      have h2'' : sig2 (Work.Spaces.gam α) (Real.pi / 2) = 0 := by
        rw [sig2, hsin]
        exact Real.zero_rpow (x := (2 : ℝ) - Work.Spaces.gam α) (by linarith)
      rw [hlhs, h4, h2'']
      norm_num
  · subst h
    have hsin : Real.sin (2 * 0) = 0 := by rw [mul_zero, Real.sin_zero]
    have hW : Work.Spaces.Wt α z 0 = 0 := Wt_zero_of_sin_eq_zero hα hsin
    have hlhs : (Work.Spaces.DthIter 2 f z 0 * Work.Spaces.Wt α z 0) ^ 2 = 0 := by simp [hW]
    have h4 : sig4 (Work.Spaces.gam α) 0 = 0 := by
      rw [sig4, hsin]
      exact Real.zero_rpow (x := (4 : ℝ) - Work.Spaces.gam α) (by linarith)
    have h2'' : sig2 (Work.Spaces.gam α) 0 = 0 := by
      rw [sig2, hsin]
      exact Real.zero_rpow (x := (2 : ℝ) - Work.Spaces.gam α) (by linarith)
    rw [hlhs, h4, h2'']
    simp

end Work.FTS.EllipticEst.Mine
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.Ae.aesliceU =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.Ae

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 800000

/-! ## Helper lemmas

The proof of `aesliceU` uses only the *first* solvability condition of `AeData`
(`Fstar u z = 0` for almost every `z`): for such a `z` the slice `θ ↦ u z θ` is, after
subtraction of `L · jumpProf` (`L` the left endpoint limit, which exists because
`∫_θ (∂_θθu)² σ < ∞`), a function with both endpoint limits `0`, to which the two-derivative
weighted Hardy inequality `SliceSigmaHardyTwo` applies; the moment condition then bounds `L`. -/

/-- The affine profile with the value `1` at `θ = 0` and `0` at `θ = π/2`: the profile of an
endpoint jump of size `1` at `θ = 0`. -/
def jumpProf (θ : ℝ) : ℝ := 1 - (2 / Real.pi) * θ

theorem jumpProf_zero : jumpProf 0 = 1 := by unfold jumpProf; norm_num

theorem jumpProf_pi : jumpProf (Real.pi / 2) = 0 := by
  unfold jumpProf
  field_simp
  ring

theorem continuous_jumpProf : Continuous jumpProf := by unfold jumpProf; fun_prop

theorem contDiff_jumpProf : ContDiff ℝ 2 jumpProf := by unfold jumpProf; fun_prop

theorem hasDerivAt_jumpProf (θ : ℝ) : HasDerivAt jumpProf (-(2 / Real.pi)) θ := by
  unfold jumpProf
  have h : HasDerivAt (fun t : ℝ => 1 - (2 / Real.pi) * t) (0 - (2 / Real.pi) * 1) θ :=
    (hasDerivAt_const (x := θ) (c := (1 : ℝ))).sub
      ((hasDerivAt_id θ).const_mul (2 / Real.pi))
  simpa using h

theorem deriv_jumpProf : deriv jumpProf = fun _ : ℝ => -(2 / Real.pi) := by
  funext θ; exact (hasDerivAt_jumpProf θ).deriv


theorem jumpProf_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : |jumpProf θ| ≤ 1 := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  have h2 : 0 ≤ (2 / Real.pi) * θ := mul_nonneg (by positivity) hθ.1
  have h3 : (2 / Real.pi) * θ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hθ.2 (by positivity : (0 : ℝ) ≤ 2 / Real.pi)
    have h4 : (2 / Real.pi) * (Real.pi / 2) = 1 := by
      have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      field_simp
    linarith [h, h4]
  unfold jumpProf
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

theorem jumpProf_sq_le_one {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : (jumpProf θ) ^ 2 ≤ 1 := by
  have h := jumpProf_mem_Iθ hθ
  nlinarith [h, abs_nonneg (jumpProf θ), sq_abs (jumpProf θ)]

/-! ### Elementary integrals of the angular profile `sin θ cos²θ` -/

theorem continuous_sinCos2 : Continuous fun θ : ℝ => Work.Elliptic.sinCos2 θ :=
  Real.continuous_sin.mul (Real.continuous_cos.pow 2)

/-- `θ ↦ -cos³θ/3` is a primitive of the angular profile `sin θ cos²θ`. -/
def psiPrim (θ : ℝ) : ℝ := -((Real.cos θ) ^ 3) / 3

theorem continuous_psiPrim : Continuous psiPrim := by unfold psiPrim; fun_prop

theorem psiPrim_zero : psiPrim 0 = -(1 / 3) := by
  unfold psiPrim; norm_num

theorem psiPrim_pi : psiPrim (Real.pi / 2) = 0 := by
  unfold psiPrim; simp

theorem hasDerivAt_psiPrim (θ : ℝ) : HasDerivAt psiPrim (Work.Elliptic.sinCos2 θ) θ := by
  have h4 : HasDerivAt (fun t : ℝ => -((Real.cos t) ^ 3) / 3) (Work.Elliptic.sinCos2 θ) θ := by
    have h1 : HasDerivAt (fun t : ℝ => Real.cos t) (-Real.sin θ) θ := Real.hasDerivAt_cos θ
    have h2 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * (Real.cos θ) ^ 2) (Real.cos θ) := by
      simpa using hasDerivAt_pow 3 (Real.cos θ)
    exact ((h2.comp θ h1).neg.div_const 3).congr_deriv
      (by rw [Work.Elliptic.sinCos2]; ring)
  unfold psiPrim
  exact h4

theorem sinCos2_integral :
    (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ) = 1 / 3 := by
  have hInt : IntervalIntegrable (fun θ : ℝ => Work.Elliptic.sinCos2 θ) volume 0 (Real.pi / 2) :=
    continuous_sinCos2.intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ))
    (b := Real.pi / 2) (f := psiPrim) (fun x _ => hasDerivAt_psiPrim x) hInt
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi / 2),
    hFTC, psiPrim_pi, psiPrim_zero]
  norm_num

/-- `θ ↦ sin θ - sin³θ/3` is a primitive of `cos³θ`. -/
def cosCube (θ : ℝ) : ℝ := Real.sin θ - (Real.sin θ) ^ 3 / 3


theorem cosCube_zero : cosCube 0 = 0 := by unfold cosCube; simp

theorem cosCube_pi : cosCube (Real.pi / 2) = 2 / 3 := by
  unfold cosCube; norm_num

theorem hasDerivAt_cosCube (θ : ℝ) : HasDerivAt cosCube ((Real.cos θ) ^ 3) θ := by
  have h4 : HasDerivAt (fun t : ℝ => Real.sin t - (Real.sin t) ^ 3 / 3) ((Real.cos θ) ^ 3) θ := by
    have h1 : HasDerivAt (fun t : ℝ => Real.sin t) (Real.cos θ) θ := Real.hasDerivAt_sin θ
    have h2 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * (Real.sin θ) ^ 2) (Real.sin θ) := by
      simpa using hasDerivAt_pow 3 (Real.sin θ)
    refine (h1.sub ((h2.comp θ h1).div_const 3)).congr_deriv ?_
    rw [show 3 * Real.sin θ ^ 2 * Real.cos θ / 3 = Real.sin θ ^ 2 * Real.cos θ by ring]
    have hs : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
      linarith [Real.sin_sq_add_cos_sq θ]
    rw [hs]; ring
  unfold cosCube
  exact h4

theorem psiPrim_integral : (∫ θ in Work.Spaces.Iθ, psiPrim θ) = -(2 / 9) := by
  have hInt : IntervalIntegrable (fun θ : ℝ => (Real.cos θ) ^ 3) volume 0 (Real.pi / 2) :=
    (Real.continuous_cos.pow 3).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ))
    (b := Real.pi / 2) (f := cosCube) (fun x _ => hasDerivAt_cosCube x) hInt
  have hkey : (∫ θ in Work.Spaces.Iθ, psiPrim θ)
      = -(1 / 3) * ∫ θ in Work.Spaces.Iθ, (Real.cos θ) ^ 3 := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    unfold psiPrim; ring
  rw [hkey, Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi / 2),
    hFTC, cosCube_pi, cosCube_zero]
  norm_num

theorem theta_sinCos2_integral :
    (∫ θ in Work.Spaces.Iθ, θ * Work.Elliptic.sinCos2 θ) = 2 / 9 := by
  -- the product `θ * psiPrim θ` has derivative `psiPrim θ + θ * sinCos2 θ`
  have hderiv : ∀ θ : ℝ, HasDerivAt (fun t : ℝ => t * psiPrim t)
      (psiPrim θ + θ * Work.Elliptic.sinCos2 θ) θ := by
    intro θ
    have h := (hasDerivAt_psiPrim θ).mul (hasDerivAt_id θ)
    convert h using 1
    · ext t; simp only [Pi.mul_apply, id_eq]; ring
    · simp only [id_eq]; ring
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hcont : Continuous fun θ : ℝ => psiPrim θ + θ * Work.Elliptic.sinCos2 θ :=
    continuous_psiPrim.add (continuous_id.mul continuous_sinCos2)
  have hIntF : IntervalIntegrable (fun θ : ℝ => psiPrim θ + θ * Work.Elliptic.sinCos2 θ)
      volume 0 (Real.pi / 2) := hcont.intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ))
    (b := Real.pi / 2) (f := fun t : ℝ => t * psiPrim t) (fun x _ => hderiv x) hIntF
  have hA : (∫ θ in (0 : ℝ)..(Real.pi / 2), (psiPrim θ + θ * Work.Elliptic.sinCos2 θ)) = 0 := by
    rw [hFTC, psiPrim_pi]; ring
  have hint1 : IntervalIntegrable psiPrim volume 0 (Real.pi / 2) :=
    continuous_psiPrim.intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun θ : ℝ => θ * Work.Elliptic.sinCos2 θ) volume 0
      (Real.pi / 2) :=
    (continuous_id.mul continuous_sinCos2).intervalIntegrable _ _
  have hsplit := intervalIntegral.integral_add (f := psiPrim)
    (g := fun θ : ℝ => θ * Work.Elliptic.sinCos2 θ) hint1 hint2
  have hIθ1 : (∫ θ in (0 : ℝ)..(Real.pi / 2), psiPrim θ)
      = ∫ θ in Work.Spaces.Iθ, psiPrim θ := by
    rw [intervalIntegral.integral_of_le hle, Work.Spaces.Iθ,
      MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hIθ2 : (∫ θ in (0 : ℝ)..(Real.pi / 2), θ * Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ, θ * Work.Elliptic.sinCos2 θ := by
    rw [intervalIntegral.integral_of_le hle, Work.Spaces.Iθ,
      MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hA] at hsplit
  rw [hIθ1, hIθ2, psiPrim_integral] at hsplit
  linarith

theorem jumpProf_moment :
    (∫ θ in Work.Spaces.Iθ, jumpProf θ * Work.Elliptic.sinCos2 θ) = 1 / 3 - 4 / (9 * Real.pi) := by
  have hcontt : Continuous fun θ : ℝ => θ * Work.Elliptic.sinCos2 θ :=
    continuous_id.mul continuous_sinCos2
  have hint1 : IntegrableOn (fun θ : ℝ => Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    continuous_sinCos2.continuousOn.integrableOn_compact isCompact_Icc
  have hint2 : IntegrableOn (fun θ : ℝ => θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    hcontt.continuousOn.integrableOn_compact isCompact_Icc
  have hpt : ∀ θ : ℝ, jumpProf θ * Work.Elliptic.sinCos2 θ
      = Work.Elliptic.sinCos2 θ - (2 / Real.pi) * (θ * Work.Elliptic.sinCos2 θ) := by
    intro θ; unfold jumpProf; ring
  rw [integral_congr_ae (Eventually.of_forall hpt),
    MeasureTheory.integral_sub hint1 (hint2.const_mul (2 / Real.pi)),
    MeasureTheory.integral_const_mul, sinCos2_integral, theta_sinCos2_integral]
  ring

theorem jumpProf_moment_ge :
    (1 : ℝ) / 6 ≤ ∫ θ in Work.Spaces.Iθ, jumpProf θ * Work.Elliptic.sinCos2 θ := by
  rw [jumpProf_moment]
  have h1 : 4 / (9 * Real.pi) ≤ 1 / 6 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 9 * Real.pi)]
    have hpi : (8 : ℝ) / 3 < Real.pi := by linarith [Real.pi_gt_three]
    linarith
  linarith

theorem sinCos2_sq_integral_le :
    (∫ θ in Work.Spaces.Iθ, (Work.Elliptic.sinCos2 θ) ^ 2) ≤ Real.pi / 2 := by
  have hcont : Continuous fun θ : ℝ => (Work.Elliptic.sinCos2 θ) ^ 2 := continuous_sinCos2.pow 2
  have hint : IntegrableOn (fun θ : ℝ => (Work.Elliptic.sinCos2 θ) ^ 2) Work.Spaces.Iθ :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    integrableOn_const (μ := volume) (s := Work.Spaces.Iθ) (C := (1 : ℝ))
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
  have hle : ∀ θ ∈ Work.Spaces.Iθ, (Work.Elliptic.sinCos2 θ) ^ 2 ≤ (1 : ℝ) := by
    intro θ hθ
    have hs : |Real.sin θ| ≤ 1 := abs_le.2 ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
    have hc : |Real.cos θ| ≤ 1 := abs_le.2 ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
    have h4 : |Work.Elliptic.sinCos2 θ| ≤ 1 := by
      rw [Work.Elliptic.sinCos2, abs_mul, abs_pow]
      have hc2 : |Real.cos θ| ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hc 2
      have hm : |Real.sin θ| * |Real.cos θ| ^ 2 ≤ 1 * 1 :=
        mul_le_mul hs (by simpa using hc2) (by positivity) (by norm_num)
      simpa using hm
    nlinarith [h4, abs_nonneg (Work.Elliptic.sinCos2 θ), sq_abs (Work.Elliptic.sinCos2 θ)]
  calc (∫ θ in Work.Spaces.Iθ, (Work.Elliptic.sinCos2 θ) ^ 2)
      ≤ ∫ _θ in Work.Spaces.Iθ, (1 : ℝ) :=
        MeasureTheory.setIntegral_mono_on hint hconst measurableSet_Icc hle
    _ = Real.pi / 2 := by
        rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, Measure.real_def,
          Work.Spaces.Iθ, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi / 2 - 0),
          sub_zero]

end

/-! ## The main slice estimate -/

/-- The second derivative of `θ ↦ g θ - c * jumpProf θ` agrees with that of `g`. -/
theorem deriv2_sub_const_mul_jumpProf {g : ℝ → ℝ} {c : ℝ} {θ : ℝ}
    (hg : ∀ᶠ t in 𝓝 θ, DifferentiableAt ℝ g t)
    (hg' : DifferentiableAt ℝ (deriv g) θ) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => g s - c * jumpProf s) t) θ = deriv (deriv g) θ := by
  have hpt : ∀ᶠ t in 𝓝 θ,
      deriv (fun s : ℝ => g s - c * jumpProf s) t = deriv g t + c * (2 / Real.pi) := by
    filter_upwards [hg] with t hgt
    rw [show (fun s : ℝ => g s - c * jumpProf s)
        = (fun s : ℝ => g s) - (fun s : ℝ => c * jumpProf s) from rfl,
      deriv_sub hgt (((hasDerivAt_jumpProf t).differentiableAt).const_mul c),
      deriv_const_mul c (hasDerivAt_jumpProf t).differentiableAt, deriv_jumpProf]
    ring
  have h2 : deriv (fun t : ℝ => deriv (fun s : ℝ => g s - c * jumpProf s) t) θ
      = deriv (fun t : ℝ => deriv g t + c * (2 / Real.pi)) θ :=
    Filter.EventuallyEq.deriv_eq hpt
  rw [h2, show (fun t : ℝ => deriv g t + c * (2 / Real.pi))
      = (fun t : ℝ => deriv g t) + (fun _ : ℝ => c * (2 / Real.pi)) from rfl,
    deriv_add hg' (differentiableAt_const _), deriv_const, add_zero]

section Main

variable {α : ℝ} {u G : ℝ → ℝ → ℝ}

/-- **The `z`-slicewise estimate.**  For almost every `z` (here: for every `z` at which the first
solvability condition holds), the `σ`-weighted `L²`-norm of the slice of `u` is controlled by the
`σ`-weighted `L²`-norm of its second `θ`-derivative. -/
theorem slice_le (CA : ℝ) (hCA : 0 < CA)
    (hA : ∀ g : ℝ → ℝ, ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn
        (fun θ => (deriv (fun t => deriv g t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ →
      Filter.Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto g (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ ENNReal.ofReal CA
          * ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal ((deriv (fun t => deriv g t) θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ))
    (h : AeData α u G) {z : ℝ} (hz : 0 < z)
    (hRlim : Filter.Tendsto (fun θ => u z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hmom : Work.Elliptic.Fstar u z = 0) :
    ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ ENNReal.ofReal (10 ^ 7 * CA)
        * ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((Work.Spaces.pthIter 2 u z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ) := by
  have hIoo_ae : volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = volume.restrict Work.Spaces.Iθ :=
    Measure.restrict_congr_set (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)
  have hsEta_nonneg : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      0 ≤ Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
      Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ)
  have hsEta_ge_one : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      1 ≤ Work.FTS.EllipticEst.sEta θ := by
    rw [← hIoo_ae]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact Work.FTS.EllipticEst.H2W.one_le_sEta hθ
  have hsEta_aemeas : AEMeasurable (fun θ => Work.FTS.EllipticEst.sEta θ)
      (volume.restrict Work.Spaces.Iθ) := by
    have hcont : ContinuousOn (fun θ => Work.FTS.EllipticEst.sEta θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      fun θ hθ => (Work.FTS.EllipticEst.H2W.continuousAt_sEta hθ).continuousWithinAt
    have h1 : AEMeasurable (fun θ => Work.FTS.EllipticEst.sEta θ)
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
      hcont.aemeasurable measurableSet_Ioo
    rwa [hIoo_ae] at h1
  -- the slice of `u` and the finiteness of its `σ`-weighted second derivative
  have hsm_slice : ContDiffOn ℝ 2 (fun θ : ℝ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Honest.contDiffOn_slice u hz (h.smooth 2)
  have hInt2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun θ' : ℝ => u z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    (Work.FTS.EllipticEst.Honest.HkMemSliceSqSigma h.memAng2 hz).congr_fun
      (fun θ _ => rfl) measurableSet_Icc
  have hnn2 : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => (deriv (fun t => deriv (fun θ' : ℝ => u z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ))
  set D : ℝ := ∫ θ in Work.Spaces.Iθ,
      (deriv (fun t => deriv (fun θ' : ℝ => u z θ') t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    with hD
  have hDnn : 0 ≤ D := by
    rw [hD]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ))
  have hDlin : (∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal ((Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      = ENNReal.ofReal D := by
    have hcongr : (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
        = ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((deriv (fun t => deriv (fun θ' : ℝ => u z θ') t) θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ) :=
      MeasureTheory.lintegral_congr (fun θ => congrArg ENNReal.ofReal rfl)
    rw [hcongr, hD]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt2 hnn2).symm
  -- boundedness of the slice and of its derivative
  obtain ⟨Mb, hMbpos, hMb⟩ := Work.FTS.EllipticEst.Honest.SliceBddSqSigma hsm_slice hInt2
  -- the left endpoint limit
  have hderiv_at : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      HasDerivAt (fun θ : ℝ => u z θ) (deriv (fun θ : ℝ => u z θ) x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
    exact ((hsm_slice.contDiffAt (isOpen_Ioo.mem_nhds hx')).differentiableAt
      (by norm_num)).hasDerivAt
  have hint_deriv : MeasureTheory.IntegrableOn (deriv (fun θ : ℝ => u z θ))
      (Set.Ioo (0 : ℝ) (Real.pi / 4)) := by
    refine MeasureTheory.IntegrableOn.of_bound (s := Set.Ioo (0 : ℝ) (Real.pi / 4)) ?_ ?_ Mb ?_
    · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    · exact (measurable_deriv _).aestronglyMeasurable
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_eq_abs]
      exact (hMb θ ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩).1
  obtain ⟨L₀, hL₀lim⟩ := Work.FTS.EllipticEst.exists_tendsto_nhdsGT_zero_of_integrableOn_deriv
    (f := fun θ : ℝ => u z θ) (f' := deriv (fun θ : ℝ => u z θ)) (δ := Real.pi / 4)
    (by linarith [Real.pi_pos]) hderiv_at hint_deriv
  -- the corrected slice
  set w : ℝ → ℝ := (fun θ : ℝ => u z θ) - (fun θ : ℝ => L₀ * jumpProf θ) with hw
  have hw_apply : ∀ θ : ℝ, w θ = u z θ - L₀ * jumpProf θ := fun θ => rfl
  have hsm_w : ContDiffOn ℝ 2 w (Set.Ioo 0 (Real.pi / 2)) := by
    rw [hw]
    exact hsm_slice.sub ((contDiff_const.mul contDiff_jumpProf).contDiffOn)
  have hlim0_w : Filter.Tendsto w (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h1 : Filter.Tendsto (fun θ : ℝ => L₀ * jumpProf θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (L₀ * jumpProf 0)) :=
      (continuous_jumpProf.tendsto 0).const_mul L₀ |>.mono_left nhdsWithin_le_nhds
    have h2 := hL₀lim.sub h1
    have h3 : L₀ - L₀ * jumpProf 0 = 0 := by rw [jumpProf_zero]; ring
    rw [h3] at h2
    rw [hw]
    exact h2
  have hlimL_w : Filter.Tendsto w
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have h1 : Filter.Tendsto (fun θ : ℝ => L₀ * jumpProf θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
        (nhds (L₀ * jumpProf (Real.pi / 2))) :=
      (continuous_jumpProf.tendsto (Real.pi / 2)).const_mul L₀ |>.mono_left nhdsWithin_le_nhds
    have h2 := hRlim.sub h1
    have h3 : 0 - L₀ * jumpProf (Real.pi / 2) = 0 := by rw [jumpProf_pi]; ring
    rw [h3] at h2
    rw [hw]
    exact h2
  -- the second derivative of `w` agrees with that of the slice of `u`
  have hdw2 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv (fun t : ℝ => deriv w t) θ
        = deriv (fun t : ℝ => deriv (fun θ' : ℝ => u z θ') t) θ := by
    intro θ hθ
    have hgn : ∀ᶠ t in 𝓝 θ, DifferentiableAt ℝ (fun θ' : ℝ => u z θ') t := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
      exact (hsm_slice.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt (by norm_num)
    have hder1 : ContDiffOn ℝ 1 (deriv (fun θ' : ℝ => u z θ')) (Set.Ioo 0 (Real.pi / 2)) :=
      hsm_slice.deriv_of_isOpen isOpen_Ioo (by norm_num)
    have hg' : DifferentiableAt ℝ (deriv (fun θ' : ℝ => u z θ')) θ :=
      (hder1.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)
    rw [hw]
    exact deriv2_sub_const_mul_jumpProf hgn hg'
  have hInt2_w : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv w t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    refine hInt2.congr ?_
    rw [← hIoo_ae]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    rw [hdw2 θ hθ]
  have haesm_w : AEStronglyMeasurable w (volume.restrict Work.Spaces.Iθ) := by
    rw [hw]
    exact (Work.FTS.EllipticEst.Honest.aesm_of_contDiffOn_Ioo hsm_slice).sub
      ((continuous_jumpProf.const_mul L₀).aestronglyMeasurable)
  have haesm_w2 : AEStronglyMeasurable (fun θ => (w θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) :=
    haesm_w.pow 2
  -- the piece `A` gives the bound for the corrected slice
  have hA_w := hA w hsm_w hInt2_w hlim0_w hlimL_w
  have hwlin : (∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal ((deriv (fun t => deriv w t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      = ENNReal.ofReal D := by
    have heq : (fun θ => ENNReal.ofReal ((deriv (fun t => deriv w t) θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ))
        =ᵐ[volume.restrict Work.Spaces.Iθ]
          (fun θ => ENNReal.ofReal
            ((deriv (fun t => deriv (fun θ' : ℝ => u z θ') t) θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ)) := by
      rw [← hIoo_ae]
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [hdw2 θ hθ]
    rw [MeasureTheory.lintegral_congr_ae heq, hD]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt2 hnn2).symm
  have hA_w' : (∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal ((w θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      ≤ ENNReal.ofReal (CA * D) := by
    rw [hwlin] at hA_w
    rwa [← ENNReal.ofReal_mul hCA.le] at hA_w
  have hnn_w : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      0 ≤ (w θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ))
  have hnn_w2 : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), 0 ≤ (w θ) ^ 2 :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => sq_nonneg _)
  have hw2sig_le : (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ CA * D := by
    calc (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((w θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)).toReal :=
          Work.FTS.EllipticEst.Honest.setIntegral_le_toReal_lintegral _ hnn_w
      _ ≤ (ENNReal.ofReal (CA * D)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hA_w'
      _ = CA * D := ENNReal.toReal_ofReal (mul_nonneg hCA.le hDnn)
  have hwlin_le : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((w θ) ^ 2))
      ≤ ENNReal.ofReal (CA * D) := by
    calc (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((w θ) ^ 2))
        ≤ ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((w θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
          refine MeasureTheory.lintegral_mono_ae ?_
          filter_upwards [hsEta_ge_one] with θ hθ
          rw [ENNReal.ofReal_le_ofReal_iff
            (mul_nonneg (sq_nonneg _) (le_trans zero_le_one hθ))]
          have hx := mul_le_mul_of_nonneg_left hθ (sq_nonneg (w θ))
          simpa only [mul_one] using hx
      _ ≤ ENNReal.ofReal (CA * D) := hA_w'
  have hw2_int : MeasureTheory.IntegrableOn (fun θ => (w θ) ^ 2) Work.Spaces.Iθ :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable haesm_w2 hnn_w2).mp
      (ne_of_lt (lt_of_le_of_lt hwlin_le ENNReal.ofReal_lt_top))
  have hw2sig_int : MeasureTheory.IntegrableOn
      (fun θ => (w θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      (haesm_w2.mul hsEta_aemeas.aestronglyMeasurable) hnn_w).mp
      (ne_of_lt (lt_of_le_of_lt hA_w' ENNReal.ofReal_lt_top))
  have hw2_le : (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2) ≤ CA * D := by
    calc (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2)
        ≤ (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((w θ) ^ 2)).toReal :=
          Work.FTS.EllipticEst.Honest.setIntegral_le_toReal_lintegral _ hnn_w2
      _ ≤ (ENNReal.ofReal (CA * D)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hwlin_le
      _ = CA * D := ENNReal.toReal_ofReal (mul_nonneg hCA.le hDnn)
  -- the moment condition
  have hgψ_int : MeasureTheory.IntegrableOn
      (fun θ => u z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
    refine MeasureTheory.IntegrableOn.of_bound (s := Work.Spaces.Iθ) ?_ ?_ Mb ?_
    · rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top
    · exact (Work.FTS.EllipticEst.Honest.aesm_of_contDiffOn_Ioo hsm_slice).mul
        continuous_sinCos2.aestronglyMeasurable
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      have hb : |u z θ| ≤ Mb := by
        rcases eq_or_lt_of_le hθ.1 with h0 | h0
        · rw [← h0, h.dirZero z, abs_zero]; exact hMbpos.le
        · rcases eq_or_lt_of_le hθ.2 with hpi | hpi
          · rw [hpi, h.dirPi z, abs_zero]; exact hMbpos.le
          · exact (hMb θ ⟨h0, hpi⟩).2
      have hs1 : |Real.sin θ| ≤ 1 := abs_le.2 ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
      have hc1 : |Real.cos θ| ≤ 1 := abs_le.2 ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
      have hψ1 : |Work.Elliptic.sinCos2 θ| ≤ 1 := by
        rw [Work.Elliptic.sinCos2, abs_mul, abs_pow]
        have hc2 : |Real.cos θ| ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hc1 2
        have hm : |Real.sin θ| * |Real.cos θ| ^ 2 ≤ 1 * 1 :=
          mul_le_mul hs1 (by simpa using hc2) (by positivity) (by norm_num)
        simpa using hm
      rw [Real.norm_eq_abs, abs_mul]
      calc |u z θ| * |Work.Elliptic.sinCos2 θ| ≤ Mb * 1 :=
            mul_le_mul hb hψ1 (abs_nonneg _) hMbpos.le
        _ = Mb := mul_one _
  have hjψ_int : MeasureTheory.IntegrableOn
      (fun θ => jumpProf θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    (continuous_jumpProf.mul continuous_sinCos2).continuousOn.integrableOn_compact isCompact_Icc
  have hwψ_int : MeasureTheory.IntegrableOn
      (fun θ => w θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
    have heq : (fun θ => w θ * Work.Elliptic.sinCos2 θ)
        = (fun θ => u z θ * Work.Elliptic.sinCos2 θ
            - L₀ * (jumpProf θ * Work.Elliptic.sinCos2 θ)) := by
      funext θ; rw [hw_apply θ]; ring
    rw [heq]
    exact hgψ_int.sub (hjψ_int.const_mul L₀)
  have hmomid : L₀ * (∫ θ in Work.Spaces.Iθ, jumpProf θ * Work.Elliptic.sinCos2 θ)
      = -(∫ θ in Work.Spaces.Iθ, w θ * Work.Elliptic.sinCos2 θ) := by
    have hmom' : (∫ θ in Work.Spaces.Iθ, u z θ * Work.Elliptic.sinCos2 θ) = 0 := hmom
    have hsplit : (∫ θ in Work.Spaces.Iθ, u z θ * Work.Elliptic.sinCos2 θ)
        = L₀ * (∫ θ in Work.Spaces.Iθ, jumpProf θ * Work.Elliptic.sinCos2 θ)
          + ∫ θ in Work.Spaces.Iθ, w θ * Work.Elliptic.sinCos2 θ := by
      rw [← MeasureTheory.integral_const_mul L₀
          (fun θ => jumpProf θ * Work.Elliptic.sinCos2 θ),
        ← MeasureTheory.integral_add (hjψ_int.const_mul L₀) hwψ_int]
      refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun θ => ?_))
      show u z θ * Work.Elliptic.sinCos2 θ
        = L₀ * (jumpProf θ * Work.Elliptic.sinCos2 θ) + w θ * Work.Elliptic.sinCos2 θ
      rw [hw_apply θ]; ring
    linarith
  -- Cauchy--Schwarz and the bound on the jump
  have hw_memLp : MemLp w 2 (volume.restrict Work.Spaces.Iθ) := by
    rw [memLp_two_iff_integrable_sq haesm_w]
    exact hw2_int
  have hpsi_memLp : MemLp (fun θ : ℝ => Work.Elliptic.sinCos2 θ) 2
      (volume.restrict Work.Spaces.Iθ) := by
    rw [memLp_two_iff_integrable_sq continuous_sinCos2.aestronglyMeasurable]
    exact (continuous_sinCos2.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hcs : (∫ θ in Work.Spaces.Iθ, w θ * Work.Elliptic.sinCos2 θ) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2)
        * (∫ θ in Work.Spaces.Iθ, (Work.Elliptic.sinCos2 θ) ^ 2) :=
    Work.Spaces.cs_integral hw_memLp hpsi_memLp
  have hL0sq : L₀ ^ 2 ≤ 18 * Real.pi * (CA * D) := by
    have hc1 : (1 : ℝ) / 6 ≤ ∫ θ in Work.Spaces.Iθ, jumpProf θ * Work.Elliptic.sinCos2 θ :=
      jumpProf_moment_ge
    have hsq : (L₀ * (∫ θ in Work.Spaces.Iθ, jumpProf θ * Work.Elliptic.sinCos2 θ)) ^ 2
        = (∫ θ in Work.Spaces.Iθ, w θ * Work.Elliptic.sinCos2 θ) ^ 2 := by
      rw [hmomid]; ring
    have h1 : L₀ ^ 2 * ((1 : ℝ) / 6) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ, w θ * Work.Elliptic.sinCos2 θ) ^ 2 := by
      calc L₀ ^ 2 * ((1 : ℝ) / 6) ^ 2
          ≤ L₀ ^ 2 * (∫ θ in Work.Spaces.Iθ, jumpProf θ * Work.Elliptic.sinCos2 θ) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hc1 2) (sq_nonneg L₀)
        _ = (∫ θ in Work.Spaces.Iθ, w θ * Work.Elliptic.sinCos2 θ) ^ 2 := by rw [← hsq]; ring
    have h2 : (∫ θ in Work.Spaces.Iθ, w θ * Work.Elliptic.sinCos2 θ) ^ 2
        ≤ (CA * D) * (Real.pi / 2) := by
      refine hcs.trans ?_
      exact mul_le_mul hw2_le sinCos2_sq_integral_le
        (integral_nonneg fun _ => sq_nonneg _) (mul_nonneg hCA.le hDnn)
    have hkey : L₀ ^ 2 ≤ 36 * ((CA * D) * (Real.pi / 2)) := by linarith
    calc L₀ ^ 2 ≤ 36 * ((CA * D) * (Real.pi / 2)) := hkey
      _ = 18 * Real.pi * (CA * D) := by ring
  -- the final real bound
  have hj2sig_int : MeasureTheory.IntegrableOn
      (fun θ => (jumpProf θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    refine Integrable.mono' Work.FTS.EllipticEst.H2W.integrableOn_sEta_and_integral_le.1 ?_ ?_
    · exact (continuous_jumpProf.pow 2).aestronglyMeasurable.mul
        hsEta_aemeas.aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
        (Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ))]
      exact mul_le_of_le_one_left (Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ)
        (jumpProf_sq_le_one hθ)
  have hj2sig_le : (∫ θ in Work.Spaces.Iθ, (jumpProf θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ 10 ^ 4 := by
    calc (∫ θ in Work.Spaces.Iθ, (jumpProf θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ :=
          MeasureTheory.setIntegral_mono_on hj2sig_int
            Work.FTS.EllipticEst.H2W.integrableOn_sEta_and_integral_le.1 measurableSet_Icc
            (fun θ hθ => mul_le_of_le_one_left
              (Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ) (jumpProf_sq_le_one hθ))
      _ ≤ 10 ^ 4 := Work.FTS.EllipticEst.H2W.integrableOn_sEta_and_integral_le.2
  have hdom_int : MeasureTheory.IntegrableOn
      (fun θ => (2 * L₀ ^ 2 * (jumpProf θ) ^ 2 + 2 * (w θ) ^ 2)
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    have h1 : (fun θ => (2 * L₀ ^ 2 * (jumpProf θ) ^ 2 + 2 * (w θ) ^ 2)
          * Work.FTS.EllipticEst.sEta θ)
        = fun θ => (2 * L₀ ^ 2) * ((jumpProf θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            + 2 * ((w θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
      funext θ; ring
    rw [h1]
    exact (hj2sig_int.const_mul (2 * L₀ ^ 2)).add (hw2sig_int.const_mul 2)
  have hpt_ub : ∀ θ ∈ Work.Spaces.Iθ,
      (u z θ) ^ 2 ≤ 2 * L₀ ^ 2 * (jumpProf θ) ^ 2 + 2 * (w θ) ^ 2 := by
    intro θ _
    rw [hw_apply θ]
    nlinarith [sq_nonneg (u z θ - 2 * (L₀ * jumpProf θ))]
  have hu_int : MeasureTheory.IntegrableOn
      (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    refine Integrable.mono' hdom_int ?_ ?_
    · exact ((Work.FTS.EllipticEst.Honest.aesm_of_contDiffOn_Ioo hsm_slice).pow 2).mul
        hsEta_aemeas.aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      have hσ : 0 ≤ Work.FTS.EllipticEst.sEta θ :=
        Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hσ)]
      exact mul_le_mul_of_nonneg_right (hpt_ub θ hθ) hσ
  have hreal : (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ 10 ^ 7 * CA * D := by
    have h1 : (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ ∫ θ in Work.Spaces.Iθ, (2 * L₀ ^ 2 * (jumpProf θ) ^ 2 + 2 * (w θ) ^ 2)
            * Work.FTS.EllipticEst.sEta θ := by
      refine MeasureTheory.integral_mono_ae hu_int hdom_int ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      have hσ : 0 ≤ Work.FTS.EllipticEst.sEta θ :=
        Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ
      exact mul_le_mul_of_nonneg_right (hpt_ub θ hθ) hσ
    have hsplit : (∫ θ in Work.Spaces.Iθ,
          (2 * L₀ ^ 2 * (jumpProf θ) ^ 2 + 2 * (w θ) ^ 2) * Work.FTS.EllipticEst.sEta θ)
        = (2 * L₀ ^ 2) * (∫ θ in Work.Spaces.Iθ,
              (jumpProf θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
      rw [show (fun θ => (2 * L₀ ^ 2 * (jumpProf θ) ^ 2 + 2 * (w θ) ^ 2)
            * Work.FTS.EllipticEst.sEta θ)
          = fun θ => (2 * L₀ ^ 2) * ((jumpProf θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
              + 2 * ((w θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) from by funext θ; ring]
      rw [MeasureTheory.integral_add (hj2sig_int.const_mul (2 * L₀ ^ 2))
          (hw2sig_int.const_mul 2),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have hCADnn : 0 ≤ CA * D := mul_nonneg hCA.le hDnn
    have h3 : (2 * L₀ ^ 2) * (∫ θ in Work.Spaces.Iθ,
          (jumpProf θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ 2 * (18 * Real.pi * (CA * D)) * 10 ^ 4 := by
      have h4 : (2 * L₀ ^ 2) ≤ 2 * (18 * Real.pi * (CA * D)) := by linarith
      have h4b : (0 : ℝ) ≤ 2 * (18 * Real.pi * (CA * D)) := by
        have := Real.pi_pos; nlinarith [mul_nonneg hCA.le hDnn]
      have h4c : (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ,
          (jumpProf θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
        MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ =>
          mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ))
      calc (2 * L₀ ^ 2) * (∫ θ in Work.Spaces.Iθ,
              (jumpProf θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          ≤ (2 * (18 * Real.pi * (CA * D))) * (∫ θ in Work.Spaces.Iθ,
              (jumpProf θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
            mul_le_mul_of_nonneg_right h4 h4c
        _ ≤ (2 * (18 * Real.pi * (CA * D))) * 10 ^ 4 :=
            mul_le_mul_of_nonneg_left hj2sig_le h4b
    have h5 : 2 * (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ 2 * (CA * D) := mul_le_mul_of_nonneg_left hw2sig_le (by norm_num)
    have h6 : 2 * (18 * Real.pi * (CA * D)) * 10 ^ 4 + 2 * (CA * D)
        ≤ 10 ^ 7 * CA * D := by
      have hcoeff : (2 * (18 * Real.pi) * 10 ^ 4 + 2 : ℝ) ≤ 10 ^ 7 := by
        nlinarith [Real.pi_lt_four]
      calc 2 * (18 * Real.pi * (CA * D)) * 10 ^ 4 + 2 * (CA * D)
          = (2 * (18 * Real.pi) * 10 ^ 4 + 2) * (CA * D) := by ring
        _ ≤ 10 ^ 7 * (CA * D) := mul_le_mul_of_nonneg_right hcoeff hCADnn
        _ = 10 ^ 7 * CA * D := by ring
    refine h1.trans ?_
    rw [hsplit]
    linarith [h3, h5, h6]
  have hgoal : (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      ≤ ENNReal.ofReal (10 ^ 7 * CA * D) := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hu_int
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
        mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ)))]
    exact ENNReal.ofReal_le_ofReal hreal
  rw [hDlin, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 10 ^ 7 * CA)]
  exact hgoal



end Main

/-- **Assembly.**  The target follows from the two pieces: the right-endpoint limit vanishing for
the class `AeData`, and the two-derivative weighted Hardy inequality. -/
theorem aesliceU_of
    (hB : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G → ∀ z, 0 < z →
      Filter.Tendsto (fun θ => u z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hA : ∃ C : ℝ, 0 < C ∧ ∀ g : ℝ → ℝ,
      ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn
        (fun θ => (deriv (fun t => deriv g t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ →
      Filter.Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto g (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ ENNReal.ofReal C
          * ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal ((deriv (fun t => deriv g t) θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
        ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
          ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            ≤ ENNReal.ofReal C
              * ∫⁻ θ in Work.Spaces.Iθ,
                  ENNReal.ofReal ((Work.Spaces.pthIter 2 u z θ) ^ 2
                    * Work.FTS.EllipticEst.sEta θ) := by
  obtain ⟨CA, hCApos, hA'⟩ := hA
  refine ⟨10 ^ 7 * CA, by positivity, ?_⟩
  intro α u G h
  filter_upwards [h.momU, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hmom hz
  exact slice_le CA hCApos hA' h hz (hB α u G h z hz) hmom

theorem aesliceU : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          ≤ ENNReal.ofReal C
            * ∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal ((Work.Spaces.pthIter 2 u z θ) ^ 2
                  * Work.FTS.EllipticEst.sEta θ) :=
  aesliceU_of AeSliceRightTendsto SliceSigmaHardyTwo

end Work.FTS.EllipticEst.H2W.Ae
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSigmaUpgradeU =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeProof

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Work.FTS.EllipticEst.Honest Work.FTS.EllipticEst.H2W.Ae

/-- **The slicewise σ-upgrade**, a.e. in `z`, for the fibres of an `AeData` datum: the
`σ`-weighted angular square integral of `u(z,·)` is controlled by the unweighted angular square
integral of `∂_θu(z,·)`.  The only extra input is the honesty of the moment
`θ ↦ u(z,θ) sinθcos²θ` (it holds whenever the fibre is bounded, e.g. from `HkMem α 0 (∂_θθu)`). -/
theorem AeSigmaUpgradeU_ae : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G →
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        MeasureTheory.IntegrableOn (fun θ => u z θ * (Real.sin θ * Real.cos θ ^ 2))
          Work.Spaces.Iθ) →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
          ≤ ENNReal.ofReal C
            * (∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)) := by
  obtain ⟨C, hCpos, hC⟩ := SigmaPoincare
  refine ⟨C, hCpos, ?_⟩
  intro α u G h hint
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi, hint, AeData.momU h]
    with z hz hintz hmomz
  have hslice : ContDiffOn ℝ 1 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_slice u hz (h.smooth 1)
  have hmom : (∫ θ in Work.Spaces.Iθ, u z θ * Real.sin θ * Real.cos θ ^ 2) = 0 := by
    simpa only [Work.Elliptic.Fstar, Work.Elliptic.sinCos2, mul_assoc] using hmomz
  have hkey := hC (fun θ => u z θ) hslice hintz hmom
  simpa only [Work.Spaces.pth] using hkey

/-- **The integrated σ-upgrade**: multiplying the a.e. slicewise inequality by the radial weight
`w²` and integrating in `z` gives the `ρ`-form. -/
theorem AeSigmaUpgradeU : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G →
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        MeasureTheory.IntegrableOn (fun θ => u z θ * (Real.sin θ * Real.cos θ ^ 2))
          Work.Spaces.Iθ) →
      (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
        ≤ ENNReal.ofReal C
          * (∫⁻ z in Work.Spaces.Iz,
              ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
                * (∫⁻ θ in Work.Spaces.Iθ,
                    ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2))) := by
  obtain ⟨C, hCpos, hC⟩ := AeSigmaUpgradeU_ae
  refine ⟨C, hCpos, ?_⟩
  intro α u G h hint
  have hae := hC α u G h hint
  have hIzm : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi 0) := by
    rw [Work.Spaces.Iz]
    rw [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))]
  have haeI : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
        ≤ ENNReal.ofReal C
          * (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)) := by
    rw [hIzm]
    exact hae
  have hmono : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
      ≤ ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (ENNReal.ofReal C * (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2))) := by
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [haeI] with z hz
    exact mul_le_mul_right hz _
  refine hmono.trans (le_of_eq ?_)
  rw [← MeasureTheory.lintegral_const_mul']
  · refine MeasureTheory.lintegral_congr fun z => ?_
    ring
  · exact ENNReal.ofReal_ne_top

/-! ## Discharging the honesty hypothesis -/

/-- **The fibre moment `θ ↦ u z θ · sinθcos²θ` is honest.**  The fibre is `C²` on the open
interval and `(∂_θθu)² σ` is integrable there (`HkMemSliceSqSigma`), so the fibre and its
derivative are bounded on the open interval; the product with the bounded profile
`sinθcos²θ` is therefore integrable. -/
theorem AeSliceMomentU_integrable (α : ℝ) (u G : ℝ → ℝ → ℝ) (h : AeData α u G)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => u z θ * (Real.sin θ * Real.cos θ ^ 2))
      Work.Spaces.Iθ := by
  have hsm : ContDiffOn ℝ 2 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_slice u hz (h.smooth 2)
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t : ℝ => deriv (fun θ' => u z θ') t) θ) ^ 2 * sEta θ)
      Work.Spaces.Iθ := by
    have h0 := HkMemSliceSqSigma h.memAng2 hz
    simpa only [Work.Spaces.pth, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
      Nat.reduceAdd] using h0
  obtain ⟨C, hCpos, hC⟩ := SliceBddSqSigma hsm h2
  have hbdd : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖u z θ * (Real.sin θ * Real.cos θ ^ 2)‖ ≤ C := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have hcos : |Real.cos θ ^ 2| ≤ 1 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [Real.cos_sq_le_one θ]
    have hsin : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
    have hsin2 : |Real.sin θ| * |Real.cos θ ^ 2| ≤ 1 := by
      nlinarith [abs_nonneg (Real.sin θ), abs_nonneg (Real.cos θ ^ 2)]
    have hu : |u z θ| ≤ C := by
      rcases eq_or_lt_of_le hθ.1 with h0 | h0
      · rw [← h0, AeData.dirZero h z, abs_zero]; exact hCpos.le
      · rcases eq_or_lt_of_le hθ.2 with h1 | h1
        · rw [h1, AeData.dirPi h z, abs_zero]; exact hCpos.le
        · exact (hC θ ⟨h0, h1⟩).2
    calc |u z θ| * (|Real.sin θ| * |Real.cos θ ^ 2|) ≤ C * 1 :=
          mul_le_mul hu hsin2 (by positivity) hCpos.le
      _ = C := by ring
  refine MeasureTheory.IntegrableOn.of_bound (isCompact_Icc.measure_lt_top) ?_ C hbdd
  exact (aesm_of_contDiffOn_Ioo hsm).mul
    (by
      show AEStronglyMeasurable (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) _
      fun_prop)

/-- **The σ-upgrade of the `u`-norm, integrated, with the honesty hypothesis discharged.** -/
theorem AeSigmaUpgradeU_all : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G →
      (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
        ≤ ENNReal.ofReal C
          * (∫⁻ z in Work.Spaces.Iz,
              ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
                * (∫⁻ θ in Work.Spaces.Iθ,
                    ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2))) := by
  obtain ⟨C, hCpos, hC⟩ := AeSigmaUpgradeU
  refine ⟨C, hCpos, ?_⟩
  intro α u G h
  refine hC α u G h ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz
  exact AeSliceMomentU_integrable α u G h hz

end Work.FTS.EllipticEst.H2W.AeProof
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.PsiSlices.PsiMoments =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.PsiSlices

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## §0 Elementary facts -/

/-- `sinθcos²θ` is continuous. -/
theorem continuous_sinCos2 : Continuous fun θ : ℝ => Work.Elliptic.sinCos2 θ := by
  simp only [Work.Elliptic.sinCos2]
  exact Real.continuous_sin.mul (Real.continuous_cos.pow 2)

/-- The first coordinate is a.e. non-zero on the box `(s,z] × Iθ` when `s > 0`. -/
theorem ae_fst_ne_zero {s z : ℝ} (hs : 0 < s) :
    ∀ᵐ p ∂((volume.restrict (Set.Ioc s z)).prod (volume.restrict Work.Spaces.Iθ)), p.1 ≠ 0 := by
  rw [MeasureTheory.Measure.ae_prod_iff_ae_ae (p := fun p : ℝ × ℝ => p.1 ≠ 0)
    ((measurableSet_singleton 0).compl.preimage measurable_fst)]
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with r hr
  filter_upwards with θ
  exact ne_of_gt (lt_trans hs hr.1)

/-! ## §1 Slice integrability from the Taylor estimate -/

/-- `θ ↦ D_z^i Ψ(u,θ)·sinθcos²θ` is integrable on `Iθ` for `i ≤ 2` and `u > 0`. -/
theorem slice_integrableOn {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) (i : ℕ) (hi : i ≤ 2)
    {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun θ : ℝ => Work.Spaces.DzIter i Ψ u θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ :=
  (Work.FTS.EllipticEst.Mine.SliceMomentTaylor (contDiffOn_slice_two (hΨ.DzIter i) hu)
    (integrableOn_pthIter2_slice hΨ hB i hi hu)).1

/-- `|D_z^i Ψ(u,·)|·sinθcos²θ` is integrable on `Iθ`. -/
theorem slice_abs_integrableOn {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) (i : ℕ) (hi : i ≤ 2)
    {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun θ : ℝ => |Work.Spaces.DzIter i Ψ u θ| * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ :=
  (slice_integrableOn hΨ hB i hi hu).norm.congr
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
      show ‖Work.Spaces.DzIter i Ψ u θ * Work.Elliptic.sinCos2 θ‖
        = |Work.Spaces.DzIter i Ψ u θ| * Work.Elliptic.sinCos2 θ
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sinCos2_nonneg hθ)]))

/-- `θ ↦ |∂_zΨ(u,θ)|·sinθcos²θ` is integrable on `Iθ` for `u > 0`. -/
theorem slice_abs_pz_integrableOn {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun θ : ℝ => Work.Spaces.pz Ψ u θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := by
  have hkey : ∀ p : ℝ × ℝ, p.1 ≠ 0 → Work.Spaces.Dz Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2 / p.1
      = Work.Spaces.pz Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2 := by
    intro p hp
    simp only [Work.Spaces.Dz]
    field_simp
  refine (((slice_integrableOn hΨ hB 1 (by norm_num) hu).div_const u)).congr ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
  exact hkey (u, θ) (ne_of_gt hu)

/-! ## §2 Box integrability of the two differentiated moments -/

/-- **Box integrability of `∂_zΨ·sinθcos²θ`.** -/
theorem box_pz {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) {s z : ℝ} (hs : 0 < s)
    (hsz : s ≤ z) :
    Integrable (Function.uncurry (fun r θ : ℝ => Work.Spaces.pz Ψ r θ * Work.Elliptic.sinCos2 θ))
      ((volume.restrict (Set.Ioc s z)).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hr0 := ae_fst_ne_zero (s := s) (z := z) hs
  have hsm : ContinuousOn (Function.uncurry (fun r θ : ℝ =>
      Work.Spaces.pz Ψ r θ * Work.Elliptic.sinCos2 θ)) Work.FTS.EllipticEst.Q0 :=
    (hΨ.pz.continuousOn).mul ((continuous_sinCos2.comp continuous_snd).continuousOn)
  have hkey : ∀ p : ℝ × ℝ, p.1 ≠ 0 → Work.Spaces.Dz Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2 / p.1
      = Work.Spaces.pz Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2 := by
    intro p hp
    simp only [Work.Spaces.Dz]
    field_simp
  have hae : AEStronglyMeasurable (Function.uncurry (fun r θ : ℝ =>
      Work.Spaces.Dz Ψ r θ * Work.Elliptic.sinCos2 θ / r))
      ((volume.restrict (Set.Ioc s z)).prod (volume.restrict Work.Spaces.Iθ)) :=
    (Work.FTS.EllipticEst.aesm_uncurry_restrict_open
      (fun p : ℝ × ℝ => Work.Spaces.pz Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2) hsm
      hs.le).congr (by
        filter_upwards [hr0] with p hp
        simp only [Function.uncurry]
        exact (hkey p hp).symm)
  have hfib : ∀ r ∈ Set.Ioc s z,
      IntegrableOn (fun θ : ℝ => Work.Spaces.Dz Ψ r θ * Work.Elliptic.sinCos2 θ)
        Work.Spaces.Iθ :=
    fun r hr => slice_integrableOn hΨ hB 1 (by norm_num) (lt_trans hs hr.1)
  have hle : ∀ r ∈ Set.Ioc s z,
      ∫ θ in Work.Spaces.Iθ, |Work.Spaces.Dz Ψ r θ * Work.Elliptic.sinCos2 θ| ≤ Bnd Ψ 1 r := by
    intro r hr
    have hsb := slice_bound hΨ hB 1 (by norm_num) r (lt_trans hs hr.1)
    have heq : (∫ θ in Work.Spaces.Iθ, |Work.Spaces.Dz Ψ r θ
          * Work.Elliptic.sinCos2 θ|)
        = ∫ θ in Work.Spaces.Iθ, |Work.Spaces.Dz Ψ r θ| * Work.Elliptic.sinCos2 θ :=
      MeasureTheory.integral_congr_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
          show |Work.Spaces.Dz Ψ r θ * Work.Elliptic.sinCos2 θ|
            = |Work.Spaces.Dz Ψ r θ| * Work.Elliptic.sinCos2 θ
          rw [abs_mul, abs_of_nonneg (sinCos2_nonneg hθ)]))
    rw [heq]
    exact hsb
  have hb := integrable_uncurry_div_of_fibre_bound hs hsz hae hfib hle
    (Bnd_integrableOn hΨ hB 1 (by norm_num) hs)
  refine hb.congr (by
    filter_upwards [hr0] with p hp
    simp only [Function.uncurry]
    exact hkey p hp)

/-- **Box integrability of `∂_z²Ψ·sinθcos²θ`.** -/
theorem box_pzIter2 {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) {s z : ℝ} (hs : 0 < s)
    (hsz : s ≤ z) :
    Integrable (Function.uncurry (fun r θ : ℝ =>
      Work.Spaces.pzIter 2 Ψ r θ * Work.Elliptic.sinCos2 θ))
      ((volume.restrict (Set.Ioc s z)).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hr0 := ae_fst_ne_zero (s := s) (z := z) hs
  have hsm : ContinuousOn (Function.uncurry (fun r θ : ℝ =>
      Work.Spaces.pzIter 2 Ψ r θ * Work.Elliptic.sinCos2 θ)) Work.FTS.EllipticEst.Q0 :=
    ((hΨ.pzIter 2).continuousOn).mul ((continuous_sinCos2.comp continuous_snd).continuousOn)
  have hkey : ∀ p : ℝ × ℝ, p.1 ≠ 0 →
      p.1 * Work.Spaces.pzIter 2 Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2 / p.1
        = Work.Spaces.pzIter 2 Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2 := by
    intro p hp
    field_simp
  have hae : AEStronglyMeasurable (Function.uncurry (fun r θ : ℝ =>
      r * Work.Spaces.pzIter 2 Ψ r θ * Work.Elliptic.sinCos2 θ / r))
      ((volume.restrict (Set.Ioc s z)).prod (volume.restrict Work.Spaces.Iθ)) :=
    (Work.FTS.EllipticEst.aesm_uncurry_restrict_open
      (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2)
      hsm hs.le).congr (by
        filter_upwards [hr0] with p hp
        simp only [Function.uncurry]
        exact (hkey p hp).symm)
  -- the fibre pointwise bound `|r ∂_z²Ψ| ≤ (|D_z²Ψ| + |D_zΨ|)·s⁻¹`
  have hpt : ∀ r ∈ Set.Ioc s z, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |r * Work.Spaces.pzIter 2 Ψ r θ| ≤ (|Work.Spaces.DzIter 2 Ψ r θ|
        + |Work.Spaces.Dz Ψ r θ|) * s⁻¹ := by
    intro r hr θ hθ
    have hr0' : 0 < r := lt_trans hs hr.1
    have hid := Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_eq_open Ψ hΨ hr0' hθ
    have h1 : r * Work.Spaces.pzIter 2 Ψ r θ
        = (Work.Spaces.DzIter 2 Ψ r θ - Work.Spaces.Dz Ψ r θ) / r := by
      rw [← hid]
      field_simp
    rw [h1, abs_div, abs_of_pos hr0']
    calc |Work.Spaces.DzIter 2 Ψ r θ - Work.Spaces.Dz Ψ r θ| / r
        ≤ (|Work.Spaces.DzIter 2 Ψ r θ| + |Work.Spaces.Dz Ψ r θ|) / r :=
          div_le_div_of_nonneg_right (abs_sub _ _) (le_of_lt hr0')
      _ = (|Work.Spaces.DzIter 2 Ψ r θ| + |Work.Spaces.Dz Ψ r θ|) * r⁻¹ := by
          rw [div_eq_mul_inv]
      _ ≤ (|Work.Spaces.DzIter 2 Ψ r θ| + |Work.Spaces.Dz Ψ r θ|) * s⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ hs (le_of_lt hr.1)) (by positivity)
  -- the `D_z`-form of the `i = 1` slice integrability
  have hm2 : ∀ r : ℝ, 0 < r → IntegrableOn (fun θ : ℝ =>
      |Work.Spaces.Dz Ψ r θ| * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
    intro r hr
    exact (slice_abs_integrableOn hΨ hB 1 (by norm_num) hr).congr
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
        show |Work.Spaces.DzIter 1 Ψ r θ| * Work.Elliptic.sinCos2 θ
          = |Work.Spaces.Dz Ψ r θ| * Work.Elliptic.sinCos2 θ
        rfl))
  -- the majorant is integrable
  have hmaj : ∀ r ∈ Set.Ioc s z,
      IntegrableOn (fun θ : ℝ => s⁻¹ * (|Work.Spaces.DzIter 2 Ψ r θ|
        * Work.Elliptic.sinCos2 θ + |Work.Spaces.Dz Ψ r θ| * Work.Elliptic.sinCos2 θ))
        Work.Spaces.Iθ := by
    intro r hr
    have hr0' : 0 < r := lt_trans hs hr.1
    exact ((slice_abs_integrableOn hΨ hB 2 (by norm_num) hr0').add (hm2 r hr0')).const_mul s⁻¹
  have hfib : ∀ r ∈ Set.Ioc s z, IntegrableOn (fun θ : ℝ =>
      r * Work.Spaces.pzIter 2 Ψ r θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
    intro r hr
    have hr0' : 0 < r := lt_trans hs hr.1
    refine Integrable.mono' (hmaj r hr) ?_ ?_
    · exact ((hΨ.aesm_slice_pzIter 2 hr0').const_mul r).mul
        continuous_sinCos2.aestronglyMeasurable
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc,
        Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => hpt r hr θ hθ)]
        with θ hθ hb
      show ‖r * Work.Spaces.pzIter 2 Ψ r θ * Work.Elliptic.sinCos2 θ‖
        ≤ s⁻¹ * (|Work.Spaces.DzIter 2 Ψ r θ| * Work.Elliptic.sinCos2 θ
            + |Work.Spaces.Dz Ψ r θ| * Work.Elliptic.sinCos2 θ)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sinCos2_nonneg hθ)]
      calc |r * Work.Spaces.pzIter 2 Ψ r θ| * Work.Elliptic.sinCos2 θ
          ≤ ((|Work.Spaces.DzIter 2 Ψ r θ| + |Work.Spaces.Dz Ψ r θ|) * s⁻¹)
              * Work.Elliptic.sinCos2 θ := mul_le_mul_of_nonneg_right hb (sinCos2_nonneg hθ)
        _ = s⁻¹ * ((|Work.Spaces.DzIter 2 Ψ r θ| + |Work.Spaces.Dz Ψ r θ|)
              * Work.Elliptic.sinCos2 θ) := by ring
        _ = s⁻¹ * (|Work.Spaces.DzIter 2 Ψ r θ| * Work.Elliptic.sinCos2 θ
              + |Work.Spaces.Dz Ψ r θ| * Work.Elliptic.sinCos2 θ) := by ring
  have hle : ∀ r ∈ Set.Ioc s z, ∫ θ in Work.Spaces.Iθ,
      |r * Work.Spaces.pzIter 2 Ψ r θ * Work.Elliptic.sinCos2 θ|
        ≤ s⁻¹ * (Bnd Ψ 2 r + Bnd Ψ 1 r) := by
    intro r hr
    have hr0' : 0 < r := lt_trans hs hr.1
    have hb1 := slice_bound hΨ hB 2 (by norm_num) r hr0'
    have hb2 : ∫ θ in Work.Spaces.Iθ, |Work.Spaces.Dz Ψ r θ| * Work.Elliptic.sinCos2 θ
        ≤ Bnd Ψ 1 r := by
      have h := slice_bound hΨ hB 1 (by norm_num) r hr0'
      have heq : (∫ θ in Work.Spaces.Iθ, |Work.Spaces.DzIter 1 Ψ r θ|
            * Work.Elliptic.sinCos2 θ)
          = ∫ θ in Work.Spaces.Iθ, |Work.Spaces.Dz Ψ r θ| * Work.Elliptic.sinCos2 θ :=
        MeasureTheory.integral_congr_ae
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
            show |Work.Spaces.DzIter 1 Ψ r θ| * Work.Elliptic.sinCos2 θ
              = |Work.Spaces.Dz Ψ r θ| * Work.Elliptic.sinCos2 θ
            rfl))
      rwa [heq] at h
    have hm1 := slice_abs_integrableOn hΨ hB 2 (by norm_num) hr0'
    have hm2' := hm2 r hr0'
    have hmono : ∫ θ in Work.Spaces.Iθ, |r * Work.Spaces.pzIter 2 Ψ r θ
          * Work.Elliptic.sinCos2 θ|
        ≤ ∫ θ in Work.Spaces.Iθ, s⁻¹ * (|Work.Spaces.DzIter 2 Ψ r θ|
            * Work.Elliptic.sinCos2 θ + |Work.Spaces.Dz Ψ r θ| * Work.Elliptic.sinCos2 θ) := by
      refine integral_mono_ae ?_ (hmaj r hr) ?_
      · refine (hfib r hr).norm.congr (Filter.Eventually.of_forall fun θ => ?_)
        show ‖r * Work.Spaces.pzIter 2 Ψ r θ * Work.Elliptic.sinCos2 θ‖
          = |r * Work.Spaces.pzIter 2 Ψ r θ * Work.Elliptic.sinCos2 θ|
        rw [Real.norm_eq_abs]
      · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc,
          Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => hpt r hr θ hθ)]
          with θ hθ hb
        show |r * Work.Spaces.pzIter 2 Ψ r θ * Work.Elliptic.sinCos2 θ|
          ≤ s⁻¹ * (|Work.Spaces.DzIter 2 Ψ r θ| * Work.Elliptic.sinCos2 θ
              + |Work.Spaces.Dz Ψ r θ| * Work.Elliptic.sinCos2 θ)
        rw [abs_mul, abs_of_nonneg (sinCos2_nonneg hθ)]
        calc |r * Work.Spaces.pzIter 2 Ψ r θ| * Work.Elliptic.sinCos2 θ
            ≤ ((|Work.Spaces.DzIter 2 Ψ r θ| + |Work.Spaces.Dz Ψ r θ|) * s⁻¹)
                * Work.Elliptic.sinCos2 θ := mul_le_mul_of_nonneg_right hb (sinCos2_nonneg hθ)
          _ = s⁻¹ * ((|Work.Spaces.DzIter 2 Ψ r θ| + |Work.Spaces.Dz Ψ r θ|)
                * Work.Elliptic.sinCos2 θ) := by ring
          _ = s⁻¹ * (|Work.Spaces.DzIter 2 Ψ r θ| * Work.Elliptic.sinCos2 θ
                + |Work.Spaces.Dz Ψ r θ| * Work.Elliptic.sinCos2 θ) := by ring
    have hEq : (∫ θ in Work.Spaces.Iθ, s⁻¹ * (|Work.Spaces.DzIter 2 Ψ r θ|
          * Work.Elliptic.sinCos2 θ + |Work.Spaces.Dz Ψ r θ| * Work.Elliptic.sinCos2 θ))
        = s⁻¹ * ((∫ θ in Work.Spaces.Iθ,
              |Work.Spaces.DzIter 2 Ψ r θ| * Work.Elliptic.sinCos2 θ)
            + ∫ θ in Work.Spaces.Iθ, |Work.Spaces.Dz Ψ r θ| * Work.Elliptic.sinCos2 θ) := by
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hm1 hm2']
    rw [hEq] at hmono
    refine le_trans hmono ?_
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (le_of_lt hs))
    linarith [hb1, hb2]
  have hb := ((Bnd_integrableOn hΨ hB 2 (by norm_num) (b := z) hs).add
      (Bnd_integrableOn hΨ hB 1 (by norm_num) (b := z) hs)).const_mul s⁻¹
  refine (integrable_uncurry_div_of_fibre_bound hs hsz hae hfib hle hb).congr ?_
  filter_upwards [hr0] with p hp
  simp only [Function.uncurry]
  exact hkey p hp

/-! ## §3 The integrated moment chain -/

/-- The chain rule for the moment of `Ψ` itself. -/
theorem Fstar_sub_pz {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) {s z : ℝ} (hs : 0 < s)
    (hsz : s ≤ z) :
    Work.Elliptic.Fstar Ψ z - Work.Elliptic.Fstar Ψ s
      = ∫ r in s..z, Work.Elliptic.Fstar (Work.Spaces.pz Ψ) r :=
  Work.EllipticEst.H2W.Fstar_sub_eq_integral_pz hΨ hs hsz
    (slice_integrableOn hΨ hB 0 (by norm_num) hs)
    (slice_integrableOn hΨ hB 0 (by norm_num) (lt_of_lt_of_le hs hsz))
    (box_pz hΨ hB hs hsz)

/-- The chain rule for the moment of `∂_zΨ`. -/
theorem Fstar_sub_pzIter2 {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) {s z : ℝ} (hs : 0 < s)
    (hsz : s ≤ z) :
    Work.Elliptic.Fstar (Work.Spaces.pz Ψ) z - Work.Elliptic.Fstar (Work.Spaces.pz Ψ) s
      = ∫ r in s..z, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) r := by
  have hz : 0 < z := lt_of_lt_of_le hs hsz
  exact Work.EllipticEst.H2W.Fstar_sub_eq_integral_pz hΨ.pz hs hsz
    (slice_abs_pz_integrableOn hΨ hB hs) (slice_abs_pz_integrableOn hΨ hB hz)
    (box_pzIter2 hΨ hB hs hsz)

end Work.FTS.EllipticEst.H2W.PsiSlices
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.step3BAngularClean =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 4000000



end

end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.ESW.ChainAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Auxiliaries for the top-slot chain `Tk α k (∂_θθΨ) ≤ C·(chain of ∂_θ^r ∂_θθΨ)`

This file collects the bookkeeping lemmas used by `Tk_B_le_chain`:

* `SmoothOpen.pthIter`, `pthIter_add` (iterated plain angular derivatives);
* `Icc_one_split` / `not_mem_Icc_pred` (splitting `Icc 1 k = Icc 1 (k-1) ∪ {k}`);
* `setIntegral_mono_of_nonneg_ae` (the a.e. version of `setIntegral_mono_of_nonneg`);
* the abbreviations `ChainG` (the pointwise chain slots) and `ChainH` (their `θ`-integrals);
* `Tk_chain_of`, the measure-theoretic assembly: a pointwise chain bound together with the
  integrability of the chain slots gives the bound on `Step.Tk`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT.ESW

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Iterated plain angular derivatives -/

/-- `SmoothOpen` is preserved by the iterated plain angular derivative `∂_θ^n`. -/
theorem SmoothOpen.pthIter {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F) (n : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter n F) := by
  induction n with
  | zero => simpa using hF
  | succ n ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

/-- `∂_θ^{m+n} = ∂_θ^m ∂_θ^n` for the iterated plain angular derivative. -/
theorem pthIter_add (m n : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter (m + n) f = Work.Spaces.pthIter m (Work.Spaces.pthIter n f) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_add, Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]

/-! ## Splitting `Icc 1 k` at its top element -/

theorem Icc_one_split {k : ℕ} (hk : 1 ≤ k) :
    Finset.Icc 1 k = insert k (Finset.Icc 1 (k - 1)) := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

theorem not_mem_Icc_pred {k : ℕ} (hk : 1 ≤ k) : k ∉ Finset.Icc 1 (k - 1) := by
  simp only [Finset.mem_Icc]; omega

/-! ## An a.e. version of `setIntegral_mono_of_nonneg` -/

/-- `setIntegral_mono_of_nonneg` with the two pointwise hypotheses weakened to a.e. ones
(along the restricted measure); only the majorant needs to be integrable. -/
theorem setIntegral_mono_of_nonneg_ae {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : 0 ≤ᵐ[volume.restrict s] f) (h : f ≤ᵐ[volume.restrict s] g)
    (hg : IntegrableOn g s volume) :
    ∫ x in s, f x ≤ ∫ x in s, g x := by
  by_cases hf' : AEStronglyMeasurable f (volume.restrict s)
  · exact integral_mono_of_nonneg hf hg h
  · rw [integral_non_aestronglyMeasurable hf']
    exact integral_nonneg_of_ae (hf.trans h)

/-! ## The chain slots -/

/-- The pointwise chain slot `w(z)^2 · (∂_θ^r v(z,θ))^2 · sin(2θ)^{2r-γ}`. -/
abbrev ChainG (α : ℝ) (v : ℝ → ℝ → ℝ) (z θ : ℝ) (r : ℕ) : ℝ :=
  (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter r v z θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (2 * (r : ℝ) - Work.Spaces.gam α))

/-- The `θ`-integral of the chain slot `ChainG`. -/
abbrev ChainH (α : ℝ) (v : ℝ → ℝ → ℝ) (z : ℝ) (r : ℕ) : ℝ :=
  (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter r v z θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (2 * (r : ℝ) - Work.Spaces.gam α))

/-! ## The assembly -/

/-- **The measure-theoretic assembly of the chain.**  If the top angular slot
`(D_θ^k v · Wt α)²` is dominated pointwise (on the open interval) by the chain slots
`ChainG`, and each chain slot is `θ`-integrable with `z`-integrable `θ`-integral, then
`Tk α k v ≤ C · ∑_{r ∈ Icc 1 k} ∫_z ChainH α v z r`. -/
theorem Tk_chain_of {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {v : ℝ → ℝ → ℝ} {Ca : ℝ} (hCa : 0 < Ca)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry v)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hcore : ∀ (z θ : ℝ), θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (∀ n : ℕ, ContDiffAt ℝ n (Function.uncurry v) (z, θ)) →
      (Work.Spaces.DthIter k v z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Ca * ∑ r ∈ Finset.Icc 1 k, ChainG α v z θ r)
    (hintθ : ∀ m : ℕ, 1 ≤ m → m ≤ k → ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => ChainG α v z θ m) Work.Spaces.Iθ)
    (hintz : ∀ m : ℕ, 1 ≤ m → m ≤ k →
      MeasureTheory.IntegrableOn (fun z => ChainH α v z m) Work.Spaces.Iz) :
    Work.FTS.EllipticEst.remov.Step.Tk α k v
      ≤ Ca * ∑ r ∈ Finset.Icc 1 k, ∫ z in Work.Spaces.Iz, ChainH α v z r := by
  have hstep : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed 0 k v z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ Ca * ∑ r ∈ Finset.Icc 1 k, ChainH α v z r := by
    intro z hz
    have hz0 : (0 : ℝ) ≤ z := hz
    have hmaj : MeasureTheory.IntegrableOn
        (fun θ => Ca * ∑ r ∈ Finset.Icc 1 k, ChainG α v z θ r) Work.Spaces.Iθ :=
      (integrable_finsetSum (Finset.Icc 1 k)
        (fun r hr => hintθ r (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2 z hz)).const_mul Ca
    have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        (Work.Spaces.mixed 0 k v z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ Ca * ∑ r ∈ Finset.Icc 1 k, ChainG α v z θ r := by
      rcases eq_or_lt_of_le hz0 with hzeq | hzpos
      · have hw0 : Work.Spaces.w z = 0 := by rw [← hzeq]; norm_num [Work.Spaces.w]
        refine Filter.Eventually.of_forall (fun θ => ?_)
        have hL : Work.Spaces.mixed 0 k v z θ * Work.Spaces.Wt α z θ = 0 := by
          rw [Work.Spaces.Wt, hw0, zero_mul, mul_zero]
        have hR : ∑ r ∈ Finset.Icc 1 k, ChainG α v z θ r = 0 := by
          refine Finset.sum_eq_zero (fun r hr => ?_)
          simp only [ChainG, hw0]
          ring
        rw [hL, hR, mul_zero]
        simp
      · refine Work.FTS.EllipticEst.remov.selfdth.ae_mem_Ioo_of_Iθ.mono (fun θ hθ => ?_)
        have hsm' : ∀ n : ℕ, ContDiffAt ℝ n (Function.uncurry v) (z, θ) :=
          fun n => (hsm n).contDiffAt ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds ⟨hzpos, hθ⟩)
        simpa only [Work.Spaces.mixed_zero_left] using hcore z θ hθ hsm'
    have hmono := setIntegral_mono_of_nonneg_ae
      (f := fun θ => (Work.Spaces.mixed 0 k v z θ * Work.Spaces.Wt α z θ) ^ 2)
      (g := fun θ => Ca * ∑ r ∈ Finset.Icc 1 k, ChainG α v z θ r)
      (Filter.Eventually.of_forall (fun θ => sq_nonneg _)) hae hmaj
    calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed 0 k v z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Ca * ∑ r ∈ Finset.Icc 1 k, ChainG α v z θ r := hmono
      _ = Ca * ∑ r ∈ Finset.Icc 1 k, ChainH α v z r := by
          have hsum : (∫ θ in Work.Spaces.Iθ, ∑ r ∈ Finset.Icc 1 k, ChainG α v z θ r)
              = ∑ r ∈ Finset.Icc 1 k, ∫ θ in Work.Spaces.Iθ, ChainG α v z θ r :=
            MeasureTheory.integral_finsetSum (Finset.Icc 1 k) (fun r hr =>
              hintθ r (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2 z hz)
          rw [MeasureTheory.integral_const_mul, hsum]
          congr 1
          refine Finset.sum_congr rfl (fun r hr => ?_)
          show (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
              ((Work.Spaces.pthIter r v z θ) ^ 2 *
                Real.rpow (Real.sin (2 * θ)) (2 * (r : ℝ) - Work.Spaces.gam α)))
            = ChainH α v z r
          rw [MeasureTheory.integral_const_mul]
  have hzstep : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed 0 k v z θ * Work.Spaces.Wt α z θ) ^ 2)
      ≤ ∫ z in Work.Spaces.Iz, Ca * ∑ r ∈ Finset.Icc 1 k, ChainH α v z r := by
    have hmaj : MeasureTheory.IntegrableOn
        (fun z => Ca * ∑ r ∈ Finset.Icc 1 k, ChainH α v z r) Work.Spaces.Iz :=
      (integrable_finsetSum (Finset.Icc 1 k)
        (fun r hr => hintz r (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2)).const_mul Ca
    refine setIntegral_mono_of_nonneg_ae
      (f := fun z => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed 0 k v z θ * Work.Spaces.Wt α z θ) ^ 2)
      (g := fun z => Ca * ∑ r ∈ Finset.Icc 1 k, ChainH α v z r) ?_ ?_ hmaj
    · exact Filter.Eventually.of_forall (fun z => integral_nonneg (fun θ => sq_nonneg _))
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hstep z hz)
  calc Work.FTS.EllipticEst.remov.Step.Tk α k v
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed 0 k v z θ * Work.Spaces.Wt α z θ) ^ 2 := rfl
    _ ≤ ∫ z in Work.Spaces.Iz, Ca * ∑ r ∈ Finset.Icc 1 k, ChainH α v z r := hzstep
    _ = Ca * ∑ r ∈ Finset.Icc 1 k, ∫ z in Work.Spaces.Iz, ChainH α v z r := by
        have hsum : (∫ z in Work.Spaces.Iz, ∑ r ∈ Finset.Icc 1 k, ChainH α v z r)
            = ∑ r ∈ Finset.Icc 1 k, ∫ z in Work.Spaces.Iz, ChainH α v z r :=
          MeasureTheory.integral_finsetSum (Finset.Icc 1 k) (fun r hr =>
            hintz r (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2)
        rw [MeasureTheory.integral_const_mul, hsum]

/-! ## The target conclusion, from the two inputs -/


end Work.FTS.EllipticEst.TT.ESW
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.Baux.Tk_congr_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The top angular slot `Tk` only sees the values of `f` on the open quadrant

`Tk α k f = ∫_0^∞ ∫_0^{π/2} (D_θ^k f · W)² dθ dz` is the iterated integral over the closed
quadrant `[0,∞) × [0,π/2]` of a function whose pointwise value at an *interior* point
`z > 0`, `0 < θ < π/2` only depends on the values of `f` near that point.  Hence if two
functions agree on the open quadrant `(0,∞) × (0,π/2)`, then `D_θ^k f` and `D_θ^k g` agree
there (`Work.FTS.EllipticEst.AgreeOnQ.DthIter`), so the two integrands agree off the null
set `{z = 0} ∪ {θ = 0} ∪ {θ = π/2}` and the iterated integrals coincide.

This mirrors `Work.FTS.EllipticEst.HkSq_congr_open`.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.EllipticEst.remov.Baux




end Work.FTS.EllipticEst.remov.Baux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.EllEstUnif_top_core_of_halves =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `EllEstUnif_top_core_of_halves`: the top core from its two slot estimates

`Work.FTS.EllipticEst.remov.EllEstUnif_top_core` (the `hcore` slot of
`EllEstUnif_step_of_pieces`, hence of `EllEstUnif_step`) asks for

  `α²√(Tk α k (z²∂_zzΨ)) + √(Tk α k (∂_θθΨ)) ≤ C |F|_k`

under `EllWeakPos α k F Ψ` and the two level-`(k-1)` bounds (constant `D`).  Writing
`A := z²∂_zzΨ`, `B := ∂_θθΨ`, the exact identity

  `α² A + B = ∂_θ(tanθ·Ψ) - 6Ψ - F - α(5+α) D_z Ψ =: R̃`   (the equation `bslOp α Ψ = F`)

(the pointwise identity behind `(★★)` in `remov/NOTES_EllEstUnif_step.md`) means the two
summands can be estimated *separately*:

* the `A`-slot `α²√(Tk α k A)` — the radial estimate, delegated as `A_top_slot_bound`;
* the `B`-slot `√(Tk α k B)` — delegated as `B_top_slot_bound` (its proof uses the identity
  above together with `A_top_slot_bound` and `Rtilde_Tk_bound`).

This file performs the (elementary) combination: it takes the two slot estimates as *hypotheses*
(so that it is independent of the order in which they land, and carries no `sorry` itself) and
returns the frozen `EllEstUnif_top_core`. -/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

open Work.FTS.EllipticEst.TT

/-- **The top core from its two slot estimates.**  Both slot bounds are stated with exactly the
hypotheses of `EllEstUnif_top_core` (so they are the conclusions of `A_top_slot_bound` and
`B_top_slot_bound`); their sum is the top core, with constant `C_A + C_B`. -/
theorem EllEstUnif_top_core_of_halves (D : ℝ) (hD : 0 < D)
    (hA : ∀ k : ℕ, 3 ≤ k → ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
        Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
        α ^ 2 * Work.Spaces.HkNorm α (k - 1)
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
          ≤ D * Work.Spaces.HkNorm α k F →
        α ^ 2 * Work.Spaces.HkNorm α (k - 1)
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
            + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
          ≤ D * Work.Spaces.HkNorm α k F →
        α ^ 2 * Real.sqrt (Step.Tk α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
          ≤ C * Work.Spaces.HkNorm α k F)
    (hB : ∀ k : ℕ, 3 ≤ k → ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
        Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
        α ^ 2 * Work.Spaces.HkNorm α (k - 1)
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
          ≤ D * Work.Spaces.HkNorm α k F →
        α ^ 2 * Work.Spaces.HkNorm α (k - 1)
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
            + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
          ≤ D * Work.Spaces.HkNorm α k F →
        Real.sqrt (Step.Tk α k (Work.Spaces.pthIter 2 Ψ))
          ≤ C * Work.Spaces.HkNorm α k F) :
    ∀ k : ℕ, 3 ≤ k → ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      α ^ 2 * Work.Spaces.HkNorm α (k - 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
        ≤ D * Work.Spaces.HkNorm α k F →
      α ^ 2 * Work.Spaces.HkNorm α (k - 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
          + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        ≤ D * Work.Spaces.HkNorm α k F →
      α ^ 2 * Real.sqrt (Step.Tk α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        + Real.sqrt (Step.Tk α k (Work.Spaces.pthIter 2 Ψ))
          ≤ C * Work.Spaces.HkNorm α k F := by
  intro k hk
  obtain ⟨CA, hCApos, hCA⟩ := hA k hk
  obtain ⟨CB, hCBpos, hCB⟩ := hB k hk
  refine ⟨CA + CB, by positivity, ?_⟩
  intro α F Ψ hα hα4 hwk h1 h2
  have eA := hCA α F Ψ hα hα4 hwk h1 h2
  have eB := hCB α F Ψ hα hα4 hwk h1 h2
  calc α ^ 2 * Real.sqrt (Step.Tk α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        + Real.sqrt (Step.Tk α k (Work.Spaces.pthIter 2 Ψ))
      ≤ CA * Work.Spaces.HkNorm α k F + CB * Work.Spaces.HkNorm α k F := add_le_add eA eB
    _ = (CA + CB) * Work.Spaces.HkNorm α k F := by ring

end Work.FTS.EllipticEst.remov
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.Fstar_DzIter_one_F =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The angular moment of `D_z F` vanishes for `k ≥ 2`.**

For `k ≥ 2` the moment chain `F_*(D_z^j F) z - F_*(D_z^j F) s = ∫_s^z F_*(D_z^{j+1}F) r/r dr`
(`FstarDzIter_chain_open`) is available *both* at `j = 0` and at `j = 1`.  From `j = 0`, with
`F_*(F) ≡ 0` (the hypothesis), the primitive of `r ↦ F_*(D_zF)(r)/r` vanishes identically, so
`F_*(D_zF) = 0` almost everywhere; from `j = 1` that function is itself an indefinite integral of
the locally integrable function `r ↦ F_*(D_z^2F)(r)/r`, hence continuous; a continuous function
which vanishes almost everywhere is identically zero. -/
theorem Fstar_DzIter_one_of_two_le {α : ℝ} {k : ℕ} (hk : 2 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) z = 0 := by
  -- the source is `C^∞` on the open quadrant
  have hF : Work.FTS.EllipticEst.SmoothOpen F :=
    (smoothOpen_slices_weak h 0).1
  -- and honestly in `ℋ¹`
  have hmem1 : Work.Spaces.HkMem α 1 F :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (by omega : 1 ≤ k)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall F).mp hF) h.memF
  -- `B₁ = F_*(D_zF)` vanishes almost everywhere on `(0,∞)`
  have hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.FTS.EllipticEst.Bmom F 1 z = 0 := by
    have hd := Work.FTS.EllipticEst.Cert.radIter_bmom_ae_hasDerivAt α 1 hF hmem1
      (le_refl 1)
    rw [show (1 : ℕ) - 1 = 0 from rfl, MeasureTheory.ae_restrict_iff' measurableSet_Ioi] at hd
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [hd] with z hzimp hzmem
    have hz0 : 0 < z := hzmem
    have hev : (fun w : ℝ => Work.FTS.EllipticEst.Bmom F 0 w) =ᶠ[𝓝 z]
        (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz0] with w hw
      rw [Work.FTS.EllipticEst.Bmom_eq_Fstar_DzIter]
      simpa using h.orthF w hw
    have hder0 : HasDerivAt (fun _ : ℝ => (0 : ℝ))
        (Work.FTS.EllipticEst.Bmom F 1 z / z) z :=
      hev.hasDerivAt_iff.mp (hzimp hzmem)
    have hval : Work.FTS.EllipticEst.Bmom F 1 z / z = 0 :=
      (hder0.unique (hasDerivAt_const z 0))
    rw [div_eq_zero_iff] at hval
    rcases hval with h' | h'
    · exact h'
    · exact absurd h' hz0.ne'
  -- `B₁` is continuous on `(0,∞)`
  have hcont : ContinuousOn (fun z : ℝ => Work.FTS.EllipticEst.Bmom F 1 z) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Cert.radIter_bmom_continuousOn α k hF h.memF 1 (by omega)
  -- hence it is everywhere zero
  have hEq := MeasureTheory.Measure.eqOn_of_ae_eq hae hcont continuousOn_const
    (fun x hx => by rw [interior_Ioi]; exact subset_closure hx)
  intro z hz
  rw [← Work.FTS.EllipticEst.Bmom_eq_Fstar_DzIter]
  exact hEq hz


end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.HkSq_Dz_shift_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `D_z`-shift estimate for the squared `ℋ^k`-norm

For `k ≥ 1`, `α ∈ ℝ` and `f` of class `C^∞` on the open quadrant and in `ℋ^k`,

`|D_z f|²_{ℋ^{k-1}} ≤ (k + k²) · |f|²_{ℋ^k}`.

The point of the estimate is that shifting by `D_z` *removes* slots from the `ℋ^k`-integrand:
`D_z^{i}(D_z f) = D_z^{i+1} f` and `D_z^j D_θ^i D_z f = D_z^{j+1} D_θ^i f` (`i ≥ 1`), so every
slot of `HkIntegrand α (k-1) (D_z f)` may be compared with a slot of `HkIntegrand α k f`.  The
factor `k + k²` is the crude slot count: `k` for the radial half (each single radial slot is
dominated by the whole integrand, `Work.Spaces.sq_le_HkIntegrand_z`) and `k·k` for the mixed
half (`Work.Spaces.sq_le_HkIntegrand_mixed`).

The mathematical content is the *pointwise* bound on the open quadrant
`Q0 = (0,∞) × (0,π/2)` (`HkIntegrand_shift_le_smooth` below); the only smoothness it needs is
`C^∞` in the sense of `Work.Stability.smoothOrder` — the operators' commutation
`D_z (D_θ^i g) = D_θ^i (D_z g)` is `Work.FTS.EllipticEst.DzAmgm.DthIterDzCommOpen`.  (The
sibling `Step.HkIntegrand_shift_le` of `EllEstUnifStepAux` is stated for `ContDiffOn ℝ ⊤`,
which in this Mathlib is *analyticity*, so it cannot be applied to the `C^∞` data of the
theorem.)  What remains here is the passage to the integrals, which is done *slicing in `θ`
first*: for each fixed `z > 0` the `θ`-interval bound is `MeasureTheory.integral_mono_of_nonneg`
(nonnegativity, integrability of the majorant — supplied by `HkMem α k f` — and an a.e.
pointwise bound whose exceptional set is the null set `{0, π/2}`), and the resulting `z`-bound is
integrated with the same lemma.  The advantage of this route is that neither `HkSq α (k-1) (D_z f)`
nor any of its slices has to be shown to be (a.e. strongly measurable and) integrable.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-! ## The pointwise bound on the open quadrant -/

/-- The shifted mixed slots, at the genuine smooth order: for `f` of class `C^∞` on the open
quadrant and `(z,θ)` in the open quadrant,

`D_z^j D_θ^i (D_z f) = D_z^{j+1} D_θ^i f`.

This is `D_z` commutation with `D_θ^i` (`DthIterDzCommOpen`) followed by the algebraic identity
`D_z^j (D_z g) = D_z^{j+1} g` (`Step.DzIter_Dz`), together with the local congruence of iterated
`D_z` on the open quadrant. -/
private lemma mixed_shift_apply_smooth {j i : ℕ} (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hg : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ = Work.Spaces.mixed (j + 1) i f z θ := by
  have hcomm : Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i f)))
      (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz f))) Step.Qd :=
    Work.FTS.EllipticEst.DzAmgm.DthIterDzCommOpen f hg i
  have hpt : (z, θ) ∈ Step.Qd := ⟨hz, hθ⟩
  have hcongr : Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
      = Work.Spaces.DzIter j (Work.Spaces.Dz (Work.Spaces.DthIter i f)) z θ :=
    Step.DzIter_congr_of_isOpen Step.isOpen_Qd hcomm.symm j hpt
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
    = Work.Spaces.DzIter (j + 1) (Work.Spaces.DthIter i f) z θ
  rw [hcongr, Step.DzIter_Dz j (Work.Spaces.DthIter i f)]

/-- **The shifted integrand is dominated by the level-`k` integrand.**  Every slot of
`HkIntegrand α (k-1) (D_z f)` is a slot of `HkIntegrand α k f` (up to the commutation of `D_z`
with `D_θ^i`), and each single slot is dominated by the whole integrand; counting `k` radial
and `k·k` mixed slots gives the factor `k + k²`. -/
private theorem HkIntegrand_shift_le_smooth (α : ℝ) {k : ℕ} (hk : 1 ≤ k) (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hg : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ
      ≤ ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α k f z θ :=
    Work.Spaces.HkIntegrand_nonneg α k f z θ
  have hZ : Step.Zsum (k - 1) (Work.Spaces.Dz f) z θ
      ≤ (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
    have hterm : ∀ i ∈ Finset.range k,
        (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Step.Zu z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hik : i + 1 ≤ k := by
        have := Finset.mem_range.mp hi
        omega
      rw [Step.DzIter_Dz i f]
      exact Work.Spaces.sq_le_HkIntegrand_z α k f z θ (i + 1) hik
    have h1 : Step.Zsum (k - 1) (Work.Spaces.Dz f) z θ
        = ∑ i ∈ Finset.range k,
            (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Step.Zu z θ) ^ 2 := by
      unfold Step.Zsum
      exact Finset.sum_congr (by rw [show k - 1 + 1 = k from by omega])
        (fun i _ => rfl)
    rw [h1]
    calc (∑ i ∈ Finset.range k,
          (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Step.Zu z θ) ^ 2)
        ≤ ∑ _i ∈ Finset.range k, Work.Spaces.HkIntegrand α k f z θ :=
          Finset.sum_le_sum hterm
      _ = (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hM : Step.Msum α (k - 1) (Work.Spaces.Dz f) z θ
      ≤ ((k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
    rw [Step.Msum_eq_rows, show k - 1 + 1 = k from by omega]
    have hterm : ∀ i ∈ Finset.range k,
        (∑ j ∈ Finset.range (k - i),
          (if 1 ≤ i then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hstep : (∑ j ∈ Finset.range (k - i),
          (if 1 ≤ i then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ ∑ _j ∈ Finset.range (k - i), Work.Spaces.HkIntegrand α k f z θ := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        by_cases hi1 : 1 ≤ i
        · rw [if_pos hi1]
          rw [mixed_shift_apply_smooth f hz hθ hg]
          have hj' : i + (j + 1) ≤ k := by
            have := Finset.mem_range.mp hj
            omega
          exact Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i (j + 1) hi1 hj'
        · rw [if_neg hi1]
          exact hHnn
      refine le_trans hstep ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hcast : ((k - i : ℕ) : ℝ) ≤ (k : ℝ) := by
        have : k - i ≤ k := by omega
        exact_mod_cast this
      have hci : (0 : ℝ) ≤ ((k - i : ℕ) : ℝ) := by positivity
      nlinarith [hHnn, hcast, hci]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have hsum : (∑ _i ∈ Finset.range k, (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ)
        = ((k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    exact hsum.le
  rw [Step.HkIntegrand_eq α k f z θ] at hZ hM ⊢
  rw [Step.HkIntegrand_eq α (k - 1) (Work.Spaces.Dz f) z θ]
  have hnn : 0 ≤ Step.Zsum k f z θ + Step.Msum α k f z θ :=
    Work.Spaces.HkIntegrand_nonneg α k f z θ
  nlinarith [hZ, hM, hnn]

/-! ## The target: integration of the pointwise bound -/

/-- **The `D_z`-shift estimate.**  For `k ≥ 1`, if `f` is `C^∞` on the open quadrant
`(0,∞) × (0,π/2)` and lies in `ℋ^k`, then

`|D_z f|²_{ℋ^{k-1}} ≤ (k + k²) · |f|²_{ℋ^k}`. -/
theorem HkSq_Dz_shift_le {k : ℕ} (hk : 1 ≤ k) (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hcd : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmem : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkSq α (k - 1) (Work.Spaces.Dz f)
      ≤ (((k : ℝ) + (k : ℝ) * (k : ℝ))) * Work.Spaces.HkSq α k f := by
  have hg : Work.FTS.EllipticEst.SmoothOpen f :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mpr hcd
  -- the open angular interval agrees with the closed one up to a null set
  have hIoo : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rw [Work.Spaces.Iθ]
    exact (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)).symm
  -- *step 1*: the angular slice bound, for every `z > 0`
  have hinner : ∀ z ∈ Set.Ioi (0 : ℝ),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ)
        ≤ ((k : ℝ) + (k : ℝ) * (k : ℝ))
            * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
    intro z hz
    have hzIz : z ∈ Work.Spaces.Iz := by
      rw [Work.Spaces.Iz]
      exact Set.mem_Ici.mpr (le_of_lt hz)
    have hInt : MeasureTheory.Integrable
        (fun θ => ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      MeasureTheory.Integrable.const_mul (hmem.1 z hzIz) _
    have hpt : (fun θ => Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ)
        ≤ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ => ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ) := by
      rw [MeasureTheory.Measure.restrict_congr_set hIoo]
      exact MeasureTheory.ae_restrict_of_forall_mem isOpen_Ioo.measurableSet
        (fun θ hθ => HkIntegrand_shift_le_smooth α hk f hz hθ hg)
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ,
            ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ :=
          MeasureTheory.integral_mono_of_nonneg
            (Eventually.of_forall fun θ =>
              Work.Spaces.HkIntegrand_nonneg α (k - 1) (Work.Spaces.Dz f) z θ) hInt hpt
      _ = ((k : ℝ) + (k : ℝ) * (k : ℝ))
            * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ :=
          MeasureTheory.integral_const_mul _ _
  -- *step 2*: integrability in `z` of the majorant, from the hypothesis `HkMem α k f`
  have hmemIoi : MeasureTheory.Integrable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    rw [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
    exact hmem.2
  have hGint : MeasureTheory.Integrable
      (fun z => ((k : ℝ) + (k : ℝ) * (k : ℝ))
        * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
      (volume.restrict (Set.Ioi (0 : ℝ))) := hmemIoi.const_mul _
  have hle : (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ)
      ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun z => ((k : ℝ) + (k : ℝ) * (k : ℝ))
        * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz
    exact hinner z hz
  have hmain : (∫ z in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ)
      ≤ ∫ z in Set.Ioi (0 : ℝ), ((k : ℝ) + (k : ℝ) * (k : ℝ))
        * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ :=
    MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α (k - 1) (Work.Spaces.Dz f) z θ) hGint hle
  calc Work.Spaces.HkSq α (k - 1) (Work.Spaces.Dz f)
      = ∫ z in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ := by
        simp only [Work.Spaces.HkSq, Work.Spaces.Iz,
          MeasureTheory.integral_Ici_eq_integral_Ioi]
    _ ≤ ∫ z in Set.Ioi (0 : ℝ), ((k : ℝ) + (k : ℝ) * (k : ℝ))
          * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := hmain
    _ = ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkSq α k f := by
        rw [MeasureTheory.integral_const_mul]
        simp only [Work.Spaces.HkSq, Work.Spaces.Iz,
          MeasureTheory.integral_Ici_eq_integral_Ioi]

end Work.FTS.EllipticEst.remov
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SourceBound.weakSlicePzIter3 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## The three angular slices involved

Writing `A`, `B`, `C` for the slices `∂_z(z²∂_z²Ψ)·sinθcos²θ`, `∂_z²Ψ·sinθcos²θ` and
`∂_z³Ψ·sinθcos²θ`, the product rule for `∂_z` reads `A = 2z·B + z²·C` on `(0,∞) × (0,π/2)`,
so that `C = z^{-2}A - 2z^{-1}B` there.  The two lemmas below make this precise. -/




/-! ## Elementary analytic facts -/






/-! ## The main lemma -/


end Work.FTS.EllipticEst.remov.SourceBound
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SourceBound.weakSliceSlots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Arithmetic and order facts -/

/-- `sEta` is nonnegative on the open angular interval. -/
theorem sEta_nonneg_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])) _

/-- The positive order `2` is below the smooth order of the open-quadrant class. -/
theorem two_le_smoothOrder : (2 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
  rw [Work.Stability.smoothOrder]
  exact WithTop.coe_le_coe.mpr le_top

/-! ## The radial product rule for `z²∂_z²Ψ` and the `D_z`-continuity on the quadrant -/

/-- The product rule in the radial variable: `∂_z(z²·B(·,θ))(z,θ) = 2z B(z,θ) + z²∂_zB(z,θ)`. -/
theorem pz_zsq_mul (B : ℝ → ℝ → ℝ) {z θ d : ℝ}
    (h : HasDerivAt (fun z' : ℝ => B z' θ) d z) :
    Work.Spaces.pz (fun z θ' => z ^ 2 * B z θ') z θ = 2 * z * B z θ + z ^ 2 * d := by
  have hz2 : HasDerivAt (fun z' : ℝ => z' ^ 2) (2 * z) z := by
    simpa using (hasDerivAt_pow 2 z)
  have hprod := hz2.mul h
  have hd := hprod.deriv
  show deriv (fun z' : ℝ => z' ^ 2 * B z' θ) z = 2 * z * B z θ + z ^ 2 * d
  exact hd

/-- The uncurried `D_z`-derivative of a function smooth on the open quadrant is continuous
there. -/
theorem continuousOn_uncurry_Dz_of_smoothOpen {A : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.SmoothOpen A) :
    ContinuousOn (Function.uncurry (Work.Spaces.Dz A)) Work.FTS.EllipticEst.Q0 := by
  have h1 : ContinuousOn
      (fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz A) p)
      Work.FTS.EllipticEst.Q0 :=
    continuousOn_fst.mul (hA.pz).continuousOn
  have hEq : Function.uncurry (Work.Spaces.Dz A)
      = fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz A) p := by
    funext p; rfl
  rw [hEq]; exact h1

/-- `z²∂_z²Ψ` is `C^∞` on the open quadrant when `Ψ` is. -/
theorem smoothOpen_zsq_mul_pzIter_two {Ψ : ℝ → ℝ → ℝ}
    (hSO : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
  Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
    Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl (hSO.pzIter 2)

/-! ## The pointwise inequality behind the fourth integrability slot -/

/-- **The pointwise inequality for `z∂_z³Ψ`.**

With `G = z²∂_z²Ψ`, the identity `∂_zG = 2z∂_z²Ψ + z³∂_z³Ψ` gives
`(z∂_z³Ψ)² ≤ 2z^{-4}(∂_zG)² + 8(∂_z²Ψ)²`, hence the same inequality after multiplication by the
nonnegative weight `sEta θ`. -/
theorem slot6_pointwise {Ψ : ℝ → ℝ → ℝ} (hSO : Work.FTS.EllipticEst.SmoothOpen Ψ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.Dz (Work.Spaces.pzIter 2 Ψ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ
      ≤ (2 * (z ^ 4)⁻¹)
          * ((Work.Spaces.DzIter 1 (fun z θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ)
        + 8 * ((Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  obtain ⟨hz4, hsq, hs⟩ : z ^ 4 ≠ 0 ∧ (0 : ℝ) < z ^ 4 ∧ 0 ≤ Work.FTS.EllipticEst.sEta θ :=
    ⟨pow_ne_zero 4 (ne_of_gt hz), by positivity, sEta_nonneg_Ioo hθ⟩
  have hB' : HasDerivAt (fun z' : ℝ => Work.Spaces.pzIter 2 Ψ z' θ)
      (Work.Spaces.pzIter 3 Ψ z θ) z := hSO.hasDerivAt_slice_pzIter 2 hθ hz
  have hpzG := pz_zsq_mul (Work.Spaces.pzIter 2 Ψ) (d := Work.Spaces.pzIter 3 Ψ z θ) hB'
  have hEq : Work.Spaces.DzIter 1 (fun z θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') z θ
      = 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ + z ^ 3 * Work.Spaces.pzIter 3 Ψ z θ := by
    show z * Work.Spaces.pz (fun z θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') z θ
      = 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ + z ^ 3 * Work.Spaces.pzIter 3 Ψ z θ
    rw [hpzG]
    ring
  have hDz : Work.Spaces.Dz (Work.Spaces.pzIter 2 Ψ) z θ
      = z * Work.Spaces.pzIter 3 Ψ z θ := rfl
  rw [hDz]
  have key : z ^ 3 * Work.Spaces.pzIter 3 Ψ z θ
      = Work.Spaces.DzIter 1 (fun z θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') z θ
        - 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ := by
    rw [hEq]; ring
  have h1 : (z ^ 3 * Work.Spaces.pzIter 3 Ψ z θ) ^ 2
      ≤ 2 * (Work.Spaces.DzIter 1 (fun z θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') z θ) ^ 2
        + 8 * z ^ 4 * (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 := by
    rw [key]
    nlinarith [sq_nonneg (Work.Spaces.DzIter 1 (fun z θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ')
        z θ + 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)]
  have h2 : z ^ 4 * ((z * Work.Spaces.pzIter 3 Ψ z θ) ^ 2)
      = (z ^ 3 * Work.Spaces.pzIter 3 Ψ z θ) ^ 2 := by ring
  have h3 : (z * Work.Spaces.pzIter 3 Ψ z θ) ^ 2
      ≤ (z ^ 4)⁻¹
        * (2 * (Work.Spaces.DzIter 1 (fun z θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') z θ) ^ 2
          + 8 * z ^ 4 * (Work.Spaces.pzIter 2 Ψ z θ) ^ 2) := by
    have h4 := mul_le_mul_of_nonneg_left h1 (le_of_lt (inv_pos.mpr hsq))
    rwa [← h2, inv_mul_cancel_left₀ hz4] at h4
  calc (z * Work.Spaces.pzIter 3 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      ≤ ((z ^ 4)⁻¹
          * (2 * (Work.Spaces.DzIter 1 (fun z θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') z θ) ^ 2
            + 8 * z ^ 4 * (Work.Spaces.pzIter 2 Ψ z θ) ^ 2))
        * Work.FTS.EllipticEst.sEta θ := mul_le_mul_of_nonneg_right h3 hs
    _ = (2 * (z ^ 4)⁻¹)
          * ((Work.Spaces.DzIter 1 (fun z θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ)
        + 8 * ((Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
        field_simp
        try ring

/-! ## The target -/

theorem weakSliceSlots {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ z, 0 < z →
      ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) ∧
      ContDiffOn ℝ 2 (fun θ => Work.Spaces.pz Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) ∧
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.Dz (Work.Spaces.pzIter 2 Ψ) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn
        (fun θ => (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.Dz F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ := by
  intro z hz
  have hSO : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hSOB : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hSO 2
  have hGso : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    smoothOpen_zsq_mul_pzIter_two hSO
  have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
  have hz4 : z ^ 4 ≠ 0 := pow_ne_zero 4 (ne_of_gt hz)
  -- slot 3: `(∂_θ²Ψ)² sEta`
  have h3 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ :=
    integrableOn_DzIter_sq_mul_sEta h.memB 0 (Nat.zero_le k) hz
      (aesm_slice_sq_mul_sEta (A := Work.Spaces.pthIter 2 Ψ) hSOB.continuousOn hz)
  -- slot 4: `(∂_z∂_θ²Ψ)² sEta`
  have h4 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    have h1 := integrableOn_DzIter_sq_mul_sEta h.memB 1 (by omega) hz
      (aesm_slice_sq_mul_sEta (A := Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ))
        (continuousOn_uncurry_Dz_of_smoothOpen hSOB) hz)
    refine MeasureTheory.IntegrableOn.congr_fun (h1.const_mul ((z ^ 2)⁻¹))
      (fun θ _ => ?_) measurableSet_Icc
    show (z ^ 2)⁻¹ * ((Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) = (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ
    rw [show Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ
        = z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ from rfl, mul_pow, mul_assoc,
      inv_mul_cancel_left₀ hz2]
  -- slot 5: `(∂_z²Ψ)² sEta`
  have h5 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    have h1 := integrableOn_DzIter_sq_mul_sEta h.memA 0 (Nat.zero_le k) hz
      (aesm_slice_sq_mul_sEta (A := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        hGso.continuousOn hz)
    refine MeasureTheory.IntegrableOn.congr_fun (h1.const_mul ((z ^ 4)⁻¹))
      (fun θ _ => ?_) measurableSet_Icc
    have hsq : (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ^ 2
        = z ^ 4 * (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 := by ring
    show (z ^ 4)⁻¹ * (((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ^ 2)
        * Work.FTS.EllipticEst.sEta θ) = (Work.Spaces.pzIter 2 Ψ z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ
    rw [hsq, mul_assoc, inv_mul_cancel_left₀ hz4]
  -- slot 6: `(z∂_z³Ψ)² sEta`
  have h6 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.Dz (Work.Spaces.pzIter 2 Ψ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    have hAinteg : MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.DzIter 1 (fun z θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ')
          z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
      integrableOn_DzIter_sq_mul_sEta h.memA 1 (by omega) hz
        (aesm_slice_sq_mul_sEta
          (A := Work.Spaces.DzIter 1 (fun z θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ'))
          (by simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using
            continuousOn_uncurry_Dz_of_smoothOpen hGso) hz)
    have hAesm : MeasureTheory.AEStronglyMeasurable
        (fun θ => (Work.Spaces.Dz (Work.Spaces.pzIter 2 Ψ) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      aesm_slice_sq_mul_sEta (A := Work.Spaces.Dz (Work.Spaces.pzIter 2 Ψ))
        (continuousOn_uncurry_Dz_of_smoothOpen (hSO.pzIter 2)) hz
    refine Integrable.mono'
      (g := fun θ => (2 * (z ^ 4)⁻¹)
        * ((Work.Spaces.DzIter 1 (fun z θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ')
            z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        + 8 * ((Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      ((hAinteg.const_mul (2 * (z ^ 4)⁻¹)).add (h5.const_mul 8)) hAesm ?_
    filter_upwards [ae_mem_Ioo_of_mem_Iθ] with θ hθ
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sEta_nonneg_Ioo hθ))]
    exact slot6_pointwise hSO hz hθ
  -- slots 7, 8: `F² sEta` and `(z∂_zF)² sEta`
  have h7 : MeasureTheory.IntegrableOn
      (fun θ => (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    integrableOn_DzIter_sq_mul_sEta h.memF 0 (Nat.zero_le k) hz
      (aesm_F_slots h z hz).1
  have h8 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.Dz F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ :=
    integrableOn_DzIter_sq_mul_sEta h.memF 1 (by omega) hz (aesm_F_slots h z hz).2
  exact ⟨(hSO.curry_θ hz).of_le two_le_smoothOrder,
    ((hSO.pz).curry_θ hz).of_le two_le_smoothOrder, h3, h4, h5, h6, h7, h8⟩

end

end Work.FTS.EllipticEst.remov.SourceBound
end
-- ===== merged: Submission.Work.FTS.LocDataExt.Traces =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocDataExt

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Three one-dimensional limit helpers -/

/-- A function which vanishes eventually in the filter tends to `0`. -/
theorem tendsto_of_eventually_eq_zero {l : Filter ℝ} {g : ℝ → ℝ}
    (h : ∀ᶠ z in l, g z = 0) : Tendsto g l (𝓝 0) :=
  Filter.EventuallyEq.tendsto h

/-- On `z ≥ 1` the square of the radial weight is at most `16`
(`w z = (1+z)²/z² ≤ 4`). -/
theorem w_sq_le_sixteen {z : ℝ} (hz : 1 ≤ z) : (Work.Spaces.w z) ^ 2 ≤ 16 := by
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have h1 : 1 + z ≤ 2 * z := by linarith
  have h2 : (1 + z) ^ 2 ≤ (2 * z) ^ 2 := by nlinarith
  rw [Work.Spaces.w, div_pow]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (z ^ 2) ^ 2)]
  have h3 : ((1 + z) ^ 2) ^ 2 ≤ ((2 * z) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
  nlinarith [h3]

/-- The left `z`-trace: if a slot vanishes eventually at `0⁺`, then `z·(·)² → 0` there. -/
theorem tendsto_z_trace_of_eventually_zero {f : Fn} {b a : ℕ} {θ : ℝ}
    (h : ∀ᶠ z in 𝓝[>] 0, Work.Spaces.mixed b a f z θ = 0) :
    Tendsto (fun z => z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2)
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_of_eventually_eq_zero (h.mono (fun z hz => by rw [hz]; ring))

/-- The right `z`-trace: a slot decaying like `C/z` gives `z·(· w)² → 0` at `∞`. -/
theorem tendsto_z_trace_of_le_div {g : ℝ → ℝ} {C Z : ℝ} (hC : 0 ≤ C)
    (h : ∀ z : ℝ, Z ≤ z → |g z| ≤ C / z) :
    Tendsto (fun z => z * (g z * Work.Spaces.w z) ^ 2) Filter.atTop (𝓝 0) := by
  have hup : Tendsto (fun z : ℝ => 16 * C ^ 2 / z) Filter.atTop (𝓝 0) :=
    tendsto_id.const_div_atTop (16 * C ^ 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (f := fun z : ℝ => z * (g z * Work.Spaces.w z) ^ 2) (g := fun _ : ℝ => (0 : ℝ))
    (h := fun z : ℝ => 16 * C ^ 2 / z) tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop (max Z 1)] with z hz
    have hz1 : (1 : ℝ) ≤ z := le_trans (le_max_right _ _) hz
    exact mul_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one hz1)) (sq_nonneg _)
  · filter_upwards [eventually_ge_atTop (max Z 1)] with z hz
    have hz1 : (1 : ℝ) ≤ z := le_trans (le_max_right _ _) hz
    have hZ : Z ≤ z := le_trans (le_max_left _ _) hz
    have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz1
    have hw := w_sq_le_sixteen hz1
    have hg := h z hZ
    have hg2 : (g z) ^ 2 ≤ (C / z) ^ 2 := by
      have h4 := pow_le_pow_left₀ (abs_nonneg (g z)) hg 2
      rwa [sq_abs] at h4
    calc z * (g z * Work.Spaces.w z) ^ 2 = z * (g z) ^ 2 * (Work.Spaces.w z) ^ 2 := by ring
      _ ≤ z * (C / z) ^ 2 * 16 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hg2 (le_of_lt hz0)) hw (sq_nonneg _) ?_
          positivity
      _ = 16 * C ^ 2 / z := by
          field_simp <;> ring

/-- The angular traces: a slot dominated by `C·Γ` satisfies both `θ`-boundary limits, because
`Γ ≤ sin(2θ)^{α/5}` and `1 - γ + 2·(α/5) = 3α/10 > 0`. -/
theorem tendsto_sin_gam_trace (α : ℝ) (hα : 0 < α) {C : ℝ} (hC : 0 ≤ C) {v : ℝ → ℝ}
    (h : ∀ θ ∈ Work.Spaces.Iθ, |v θ| ≤ C * Work.Spaces.Gam α θ) :
    Tendsto (fun θ => (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α) * (v θ) ^ 2)
        (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun θ => (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α) * (v θ) ^ 2)
        (𝓝[<] (π / 2)) (𝓝 0) := by
  have hp : (0 : ℝ) < 3 * α / 10 := by linarith
  have hbound : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α) * (v θ) ^ 2
        ≤ C ^ 2 * (Real.sin (2 * θ)) ^ (3 * α / 10) := by
    intro θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hs0 : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hs0' : 0 ≤ Real.sin (2 * θ) := le_of_lt hs0
    obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθI
    have hGle : Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 5) :=
      Work.FTS.LocData.Gam_le_sin_two_rpow α hα hθI
    have hv : (v θ) ^ 2 ≤ C ^ 2 * (Work.Spaces.Gam α θ) ^ 2 := by
      have h1 := h θ hθI
      have h2 : (|v θ|) ^ 2 ≤ (C * Work.Spaces.Gam α θ) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
      rw [sq_abs, mul_pow] at h2
      exact h2
    have hsq : (Work.Spaces.Gam α θ) ^ 2 ≤ ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 :=
      pow_le_pow_left₀ hG0 hGle 2
    have hrw1 : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 = (Real.sin (2 * θ)) ^ (2 * α / 5) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs0']
      congr 1
      ring
    have hrw2 : (Real.sin (2 * θ)) ^ (2 * α / 5) * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
        = (Real.sin (2 * θ)) ^ (3 * α / 10) := by
      rw [← Real.rpow_add hs0]
      congr 1
      rw [Work.Spaces.gam]
      ring
    calc (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α) * (v θ) ^ 2
        ≤ (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
            * (C ^ 2 * (Work.Spaces.Gam α θ) ^ 2) :=
          mul_le_mul_of_nonneg_left hv (Real.rpow_nonneg hs0' _)
      _ = C ^ 2 * ((Work.Spaces.Gam α θ) ^ 2
            * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)) := by ring
      _ ≤ C ^ 2 * (((Real.sin (2 * θ)) ^ (2 * α / 5))
            * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg C)
          exact mul_le_mul_of_nonneg_right (le_trans hsq (le_of_eq hrw1))
            (Real.rpow_nonneg hs0' _)
      _ = C ^ 2 * (Real.sin (2 * θ)) ^ (3 * α / 10) := by rw [hrw2]
  have hhalf : (0 : ℝ) < π / 4 := by positivity
  have hlimr : Tendsto (fun θ : ℝ => C ^ 2 * (Real.sin (2 * θ)) ^ (3 * α / 10))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using (Work.FTS.H2.tendsto_sin_rpow_zero_right (3 * α / 10) hp).const_mul (C ^ 2)
  have hliml : Tendsto (fun θ : ℝ => C ^ 2 * (Real.sin (2 * θ)) ^ (3 * α / 10))
      (𝓝[<] (π / 2)) (𝓝 0) := by
    simpa using (Work.FTS.H2.tendsto_sin_rpow_zero_left (3 * α / 10) hp).const_mul (C ^ 2)
  constructor
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (f := fun θ : ℝ => (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α) * (v θ) ^ 2)
      (g := fun _ : ℝ => (0 : ℝ))
      (h := fun θ : ℝ => C ^ 2 * (Real.sin (2 * θ)) ^ (3 * α / 10))
      tendsto_const_nhds hlimr ?_ ?_
    · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hhalf] with θ hθ hθ'
      have hθI : θ ∈ Work.Spaces.Iθ :=
        ⟨le_of_lt hθ, by linarith [hθ'.2, Real.pi_pos]⟩
      exact mul_nonneg
        (Real.rpow_nonneg (Work.FTS.LocData.ZFBase.sin_two_nonneg_Iθ hθI) _) (sq_nonneg _)
    · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hhalf] with θ hθ hθ'
      exact hbound θ ⟨hθ, by linarith [hθ'.2, Real.pi_pos]⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (f := fun θ : ℝ => (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α) * (v θ) ^ 2)
      (g := fun _ : ℝ => (0 : ℝ))
      (h := fun θ : ℝ => C ^ 2 * (Real.sin (2 * θ)) ^ (3 * α / 10))
      tendsto_const_nhds hliml ?_ ?_
    · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsLT (show π / 4 < π / 2 by linarith)]
        with θ hθ hθ'
      have hθI : θ ∈ Work.Spaces.Iθ :=
        ⟨by linarith [hθ'.1, Real.pi_pos], le_of_lt hθ⟩
      exact mul_nonneg
        (Real.rpow_nonneg (Work.FTS.LocData.ZFBase.sin_two_nonneg_Iθ hθI) _) (sq_nonneg _)
    · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsLT (show π / 4 < π / 2 by linarith)]
        with θ hθ hθ'
      exact hbound θ ⟨by linarith [hθ'.1, Real.pi_pos], hθ⟩

/-! ## The boundary traces of the localised datum -/

/-- **The localised datum has vanishing boundary traces in `BdryTraces α k`**, for every order
`k ≤ 5` (the two jet inputs are the only order-dependent data: `hΓ` for the angular limits and
`hF` for the decay of the far factor at `∞`). -/
theorem bdryTraces_locG (α L β : ℝ) (hα : 0 < α) (hL : 1 ≤ L) {k : ℕ} {CΓ CF : ℝ}
    (hCΓ : 0 ≤ CΓ) (hCF : 0 ≤ CF)
    (hΓ : ∀ i ≤ k, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
        ≤ CΓ * Work.Spaces.Gam α θ)
    (hF : ∀ b ≤ k, ∀ z : ℝ, 1 ≤ z → ∀ θ : ℝ,
      |Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z θ| ≤ CF / z) :
    Work.FTS.Nonlin.BdryTraces α k
      (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  intro a b hab
  have hb : b ≤ k := by omega
  have ha : a ≤ k := by omega
  refine ⟨fun θ hθ => ⟨?_, ?_⟩, fun z hz => ?_⟩
  · -- ## the left `z`-trace: `locR` vanishes on `(0, 3/4)`
    apply tendsto_z_trace_of_eventually_zero
      (f := Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α))
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 3 / 4 by norm_num)] with z hz'
    have hev : ∀ᶠ z'' in 𝓝 z, ∀ θ' : ℝ,
        Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α) z'' θ' = 0 := by
      filter_upwards [locR_eventuallyEq_zero (α := α) (L := L) (β := β) (z := z) hLpos
        hz'.1 (by linarith [hz'.2, hL]) hz'.2] with z'' hz''
      intro θ'
      rw [locG_eq_locR_Gam]
      change locR α L β z'' * Work.Spaces.Gam α θ' = 0
      rw [hz'', zero_mul]
    exact Work.FTS.LocData.ZFBase.mixed_eq_zero_of_eventually_zero hev b a
  · -- ## the right `z`-trace: the two radial factors decay like `1/z`
    apply tendsto_z_trace_of_le_div (C := |α / Work.Spaces.c α| * CF * CΓ)
      (Z := max (2 * L) (7 / 4) + 1) (by positivity) ?_
    intro z hz
    have hz2 : 2 * L < z := by
      have h1 : 2 * L ≤ max (2 * L) (7 / 4) := le_max_left _ _
      linarith
    have hz7 : 7 / 4 < z := by
      have h1 : (7 / 4 : ℝ) ≤ max (2 * L) (7 / 4) := le_max_right _ _
      linarith
    have hz1 : (1 : ℝ) ≤ z := by linarith
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    rw [locG_eq_locR_Gam, congrFun (congrFun (mixed_sepGam α (locR α L β) b a) z) θ, abs_mul]
    have hrad : |Work.Spaces.DzIter b (fun z _ => locR α L β z) z θ|
        ≤ |α / Work.Spaces.c α| * (CF / z) := by
      have hev := locR_eventuallyEq_far (α := α) (L := L) (β := β) (z := z) hLpos hz2 hz7
      have hc := DzIter_z_congr_of_eventuallyEq hev b θ
      rw [hc, DzIter_const_mul, abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left (hF b hb z hz1 θ) (abs_nonneg _)
    have hang : |Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ| ≤ CΓ := by
      have h1 := hΓ a ha θ hθI
      have hG1 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθI).2
      calc |Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
          ≤ CΓ * Work.Spaces.Gam α θ := h1
        _ ≤ CΓ * 1 := mul_le_mul_of_nonneg_left hG1 hCΓ
        _ = CΓ := by ring
    calc |Work.Spaces.DzIter b (fun z _ => locR α L β z) z θ|
            * |Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
        ≤ (|α / Work.Spaces.c α| * (CF / z)) * CΓ :=
          mul_le_mul hrad hang (abs_nonneg _) (by positivity)
      _ = (|α / Work.Spaces.c α| * CF * CΓ) / z := by ring
  · -- ## the angular traces: domination by `R·Γ`
    set R : ℝ := |Work.Spaces.DzIter b (fun z _ => locR α L β z) z 0| + 1 with hRdef
    have hR0 : 0 ≤ R := by rw [hRdef]; positivity
    have hdom : ∀ θ' ∈ Work.Spaces.Iθ,
        |Work.Spaces.mixed b a (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) z θ'|
          ≤ (R * CΓ) * Work.Spaces.Gam α θ' := by
      intro θ' hθ'
      rw [locG_eq_locR_Gam, congrFun (congrFun (mixed_sepGam α (locR α L β) b a) z) θ', abs_mul]
      have hR : |Work.Spaces.DzIter b (fun z _ => locR α L β z) z θ'| ≤ R := by
        rw [DzIter_z_only_apply (locR α L β) b z θ', hRdef]
        linarith [abs_nonneg (Work.Spaces.DzIter b (fun z _ => locR α L β z) z 0)]
      have hang := hΓ a ha θ' hθ'
      calc |Work.Spaces.DzIter b (fun z _ => locR α L β z) z θ'|
              * |Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ'|
          ≤ R * (CΓ * Work.Spaces.Gam α θ') := mul_le_mul hR hang (abs_nonneg _) hR0
        _ = (R * CΓ) * Work.Spaces.Gam α θ' := by ring
    exact tendsto_sin_gam_trace α hα (mul_nonneg hR0 hCΓ) hdom

end Work.FTS.LocDataExt
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.Rl1.SliceSlot =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.Rl1

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

/-! ## The two weight comparisons of a single angular slice

The `H^k`-integrand carries the weights `w(z)²·sin(2θ)^{-η}` (radial slots) and
`w(z)²·sin(2θ)^{-γ}` (mixed slots).  On `z > 0` one has `1 ≤ w z`, and on
`0 < θ < π/2` one has `1 ≤ sin(2θ)^{-r}` for every `r ≥ 0`; hence each slot weight
dominates `w z` alone, which is exactly the amount of weight needed to compare the
plain angular `L²`-norm of a slot with its weighted version. -/

/-- `1 ≤ w z` for `z > 0`, since `w z = (1+z)²/z²` and `(1+z)² ≥ z²`. -/
private lemma one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith [sq_nonneg z]

/-- For `0 < y ≤ 1` and `0 ≤ r` one has `1 ≤ y ^ (-r)`. -/
private lemma one_le_rpow_neg {y r : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) (hr : 0 ≤ r) :
    1 ≤ y ^ (-r) := by
  rw [Real.rpow_neg hy.le, one_le_inv₀ (Real.rpow_pos_of_pos hy r)]
  exact Real.rpow_le_one hy.le hy1 hr

/-- `sin (2θ) > 0` on the open angular interval. -/
private lemma sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `1 ≤ sin(2θ)^{-γ}` on the open angular interval, for `0 < α` (i.e. `γ > 0`). -/
private lemma one_le_thGam {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    1 ≤ Work.FTS.EllipticEst.thGam α θ := by
  rw [Work.FTS.EllipticEst.thGam]
  exact one_le_rpow_neg (sin_two_pos hθ) (Real.sin_le_one _) (Work.Spaces.gam_pos hα).le

/-- `1 ≤ sin(2θ)^{-η}` on the open angular interval (`η = 99/100 > 0`). -/
private lemma one_le_thEta {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    1 ≤ Work.FTS.EllipticEst.thEta θ := by
  rw [Work.FTS.EllipticEst.thEta]
  exact one_le_rpow_neg (sin_two_pos hθ) (Real.sin_le_one _) Work.Spaces.eta_pos.le

/-- Pointwise slot comparison for a mixed derivative: on the open angular interval the
weighted square `(a·Wt)² = a²·w(z)²·sin(2θ)^{-γ}` dominates `w(z)·a²`, because
`w(z)·sin(2θ)^{-γ} ≥ 1`. -/
private lemma w_mul_sq_le_mixed {α z θ a : ℝ} (hα : 0 < α) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.w z * a ^ 2 ≤ (a * Work.Spaces.Wt α z θ) ^ 2 := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hw1 : 1 ≤ Work.Spaces.w z := one_le_w hz
  have hw0 : 0 ≤ Work.Spaces.w z := le_trans zero_le_one hw1
  have hprod : 1 ≤ Work.Spaces.w z * Work.FTS.EllipticEst.thGam α θ := by
    have h := mul_le_mul hw1 (one_le_thGam hα hθ) (zero_le_one (α := ℝ)) hw0
    simpa using h
  calc Work.Spaces.w z * a ^ 2 = a ^ 2 * Work.Spaces.w z * 1 := by ring
    _ ≤ a ^ 2 * Work.Spaces.w z * (Work.Spaces.w z * Work.FTS.EllipticEst.thGam α θ) :=
        mul_le_mul_of_nonneg_left hprod (mul_nonneg (sq_nonneg a) hw0)
    _ = (a * Work.Spaces.Wt α z θ) ^ 2 := by
        rw [mul_pow, Work.FTS.EllipticEst.Wt_sq hθI α z]
        ring

/-- Pointwise slot comparison for a pure `D_z`-derivative: on the open angular interval the
weighted square `(a·w(z)/sin(2θ)^{η/2})² = a²·w(z)²·sin(2θ)^{-η}` dominates `w(z)·a²`,
because `w(z)·sin(2θ)^{-η} ≥ 1`. -/
private lemma w_mul_sq_le_rad {z θ a : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.w z * a ^ 2
      ≤ (a * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hw1 : 1 ≤ Work.Spaces.w z := one_le_w hz
  have hw0 : 0 ≤ Work.Spaces.w z := le_trans zero_le_one hw1
  have hprod : 1 ≤ Work.Spaces.w z * Work.FTS.EllipticEst.thEta θ := by
    have h := mul_le_mul hw1 (one_le_thEta hθ) (zero_le_one (α := ℝ)) hw0
    simpa using h
  calc Work.Spaces.w z * a ^ 2 = a ^ 2 * Work.Spaces.w z * 1 := by ring
    _ ≤ a ^ 2 * Work.Spaces.w z * (Work.Spaces.w z * Work.FTS.EllipticEst.thEta θ) :=
        mul_le_mul_of_nonneg_left hprod (mul_nonneg (sq_nonneg a) hw0)
    _ = (a * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [mul_pow, Work.FTS.EllipticEst.w_div_sin_sq hθI z]
        ring


end Work.FTS.Nonlinear.Pieces.Rl1
end
-- ===== merged: Submission.Work.FTS.OpenPkg.QangOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg.QangOpen

open Work.FTS.H2

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **The primitive formula along a `z`-slice.**  For `g` of class `SmoothQuad`, every
`j : ℕ`, every `z, z₀ > 0` and every `θ ∈ (0,π/2)`,

  `D_z^j g z θ - D_z^j g z₀ θ = ∫_{z₀}^{z} D_z^{j+1} g x θ / x dx`. -/
theorem QangSliceFTC_open {g : ℝ → ℝ → ℝ} (hO : Work.FTS.EllipticEst.SmoothOpen g) (j : ℕ)
    {z z₀ θ : ℝ} (hz : 0 < z) (hz₀ : 0 < z₀) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.DzIter j g z θ - Work.Spaces.DzIter j g z₀ θ
      = ∫ x in z₀..z, Work.Spaces.DzIter (j + 1) g x θ / x := by
  -- the derivative of the `θ`-slice of `D_z^j g`, in divided form
  have hderiv : ∀ r : ℝ, r ∈ Set.uIcc z₀ z →
      Work.Spaces.pz (Work.Spaces.DzIter j g) r θ
        = Work.Spaces.DzIter (j + 1) g r θ / r := by
    intro r hr
    have hrpos : 0 < r := lt_of_lt_of_le (lt_min hz₀ hz) hr.1
    have h1 : Work.Spaces.DzIter (j + 1) g r θ
        = r * Work.Spaces.pz (Work.Spaces.DzIter j g) r θ := rfl
    rw [h1, mul_comm r, mul_div_cancel_right₀ _ (ne_of_gt hrpos)]
  rcases le_total z₀ z with hle | hle
  · have hF := Work.FTS.EllipticEst.DzIter_slice_FTC_open hO j hz₀ hle hθ
    rw [hF]
    refine intervalIntegral.integral_congr (a := z₀) (b := z)
      (f := fun r => Work.Spaces.pz (Work.Spaces.DzIter j g) r θ)
      (g := fun r => Work.Spaces.DzIter (j + 1) g r θ / r) (fun r hr => hderiv r hr)
  · have hF := Work.FTS.EllipticEst.DzIter_slice_FTC_open hO j hz hle hθ
    have hF' : Work.Spaces.DzIter j g z θ - Work.Spaces.DzIter j g z₀ θ
        = -∫ r in z..z₀, Work.Spaces.pz (Work.Spaces.DzIter j g) r θ := by
      linarith [hF]
    rw [hF']
    rw [intervalIntegral.integral_congr (a := z) (b := z₀)
      (f := fun r => Work.Spaces.pz (Work.Spaces.DzIter j g) r θ)
      (g := fun r => Work.Spaces.DzIter (j + 1) g r θ / r)
      (fun r hr => hderiv r (by rwa [Set.uIcc_comm]))]
    rw [intervalIntegral.integral_symm, neg_neg]

/-! ## Integrability of the angular slice of `Ktheta · D_z^j g` -/

/-- The pair `(z,θ) ↦ Ktheta θ · D_z^j g z θ` is continuous on the open quadrant. -/
theorem continuousOn_Ktheta_DzIter_open {g : ℝ → ℝ → ℝ} (hO : Work.FTS.EllipticEst.SmoothOpen g)
    (j : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
      * Work.Spaces.DzIter j g p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hK : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2)
        = fun p : ℝ × ℝ => 3 * Real.sin p.2 * Real.cos p.2 ^ 2 := by
      funext p; rfl
    rw [hfun]
    exact ((continuous_const.mul (Real.continuous_sin.comp continuous_snd)).mul
      ((Real.continuous_cos.comp continuous_snd).pow 2)).continuousOn
  have hD : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter j g p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := (hO.DzIter j).continuousOn
  refine (hD.mul hK).congr (fun p hp => ?_)
  exact mul_comm _ _

/-- **The angular slice `θ ↦ Ktheta θ · D_z^j g z θ` is integrable on `Iθ`** for `z > 0` and
`j ≤ 4`, in the interior class `SmoothQuad g + HkMem α 4 g`. -/
theorem QangSliceIntegrable_open {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    {j : ℕ} (hj : j ≤ 4) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ)
      Work.Spaces.Iθ := by
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd _ (continuousOn_Ktheta_DzIter_open hO j) hz
  have hmaj : MeasureTheory.Integrable (fun θ : ℝ =>
      3 * (Work.Spaces.HkIntegrand α 4 g z θ / (Work.Spaces.w z) ^ 2 + 1))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h1 : MeasureTheory.Integrable (fun θ : ℝ =>
        Work.Spaces.HkIntegrand α 4 g z θ / (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (hmem.1 z (Set.mem_Ici.mpr hz.le)).div_const _
    have h2 : MeasureTheory.Integrable (fun _ : ℝ => (1 : ℝ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      MeasureTheory.integrableOn_const (s := Work.Spaces.Iθ) (C := (1 : ℝ)) (by
        rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    exact (h1.add h2).const_mul 3
  refine MeasureTheory.Integrable.mono' hmaj haesm ?_
  rw [show (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      = MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2)) from by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have hKh := abs_Ktheta_le_three θ
  have hDh := sq_DzIter_le_HkIntegrand_div_w_sq α 4 g j hj hz hθ
  have hsq : |Work.Spaces.DzIter j g z θ| ≤ (Work.Spaces.DzIter j g z θ) ^ 2 + 1 := by
    nlinarith [sq_nonneg (|Work.Spaces.DzIter j g z θ| - 1),
      sq_abs (Work.Spaces.DzIter j g z θ), abs_nonneg (Work.Spaces.DzIter j g z θ)]
  have hDnn : 0 ≤ |Work.Spaces.DzIter j g z θ| := abs_nonneg _
  have hDh' : |Work.Spaces.DzIter j g z θ|
      ≤ Work.Spaces.HkIntegrand α 4 g z θ / (Work.Spaces.w z) ^ 2 + 1 :=
    le_trans hsq (by linarith)
  calc |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g z θ|
      ≤ 3 * |Work.Spaces.DzIter j g z θ| := mul_le_mul_of_nonneg_right hKh hDnn
    _ ≤ 3 * (Work.Spaces.HkIntegrand α 4 g z θ / (Work.Spaces.w z) ^ 2 + 1) :=
        mul_le_mul_of_nonneg_left hDh' (by norm_num)


/-- The uncurried `ℋ⁴`-integrand of a `SmoothQuad` function is a.e. strongly measurable for the
product of the restrictions of Lebesgue measure. -/
theorem aesm_joint_HkIntegrand_open {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _
    (hO.continuousOn_HkIntegrand α 4)

/-- **`HkIntegrand α 4 g` is jointly integrable on the quadrant** for
`SmoothQuad g + HkMem α 4 g`, by Tonelli: both iterated integrals are the two halves of
`HkMem α 4 g`. -/
theorem HkIntegrand_joint_integrable_open {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hnn : ∀ z θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have haesm := aesm_joint_HkIntegrand_open (α := α) hO
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => Work.Spaces.HkIntegrand α 4 g z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    exact hmem.1 z hz
  have houter : MeasureTheory.Integrable
      (fun z => ∫ θ, Work.Spaces.HkIntegrand α 4 g z θ
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hmem.2
  exact (Work.Spaces.integrable_prod_of_iterated hnn haesm hslice houter).1

/-! ## Joint integrability of the square of a `D_z`-iterate -/

/-- **`(D_zⁱ g)²` is jointly integrable on the quadrant** for `i ≤ 4`: it is dominated by
`HkIntegrand α 4 g` because `w ≥ 1` on `z > 0`. -/
theorem DzIter_sq_joint_integrable_open {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    {i : ℕ} (hi : i ≤ 4) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.DzIter i g p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  refine MeasureTheory.Integrable.mono' (HkIntegrand_joint_integrable_open hO hmem) ?_ ?_
  · have hcont : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter i g p.1 p.2) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      ((hO.DzIter i).continuousOn).pow 2
    exact Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  · refine ae_prod_quad (fun z θ hz hθ1 hθ2 => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h1 := sq_DzIter_le_HkIntegrand_div_w_sq α 4 g i hi hz ⟨hθ1, hθ2⟩
    have h2 : Work.Spaces.HkIntegrand α 4 g z θ / (Work.Spaces.w z) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
      rw [div_le_iff₀ (pow_pos (w_pos hz) 2)]
      have hw2 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := by
        have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (one_le_w hz) 2
        simpa using h
      nlinarith [Work.Spaces.HkIntegrand_nonneg α 4 g z θ, hw2]
    linarith

/-! ## The joint integrand of the angular moment on a box -/

/-- The joint integrand `(x,θ) ↦ Kθ(θ)·D_z^{j+1} g x θ / x` is continuous on the open
quadrant. -/
theorem continuousOn_Ktheta_DzIter_div_open {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (j : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
      * Work.Spaces.DzIter j g p.1 p.2 / p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  (continuousOn_Ktheta_DzIter_open hO j).div continuousOn_fst (fun p hp => ne_of_gt hp.1)

/-- **Joint integrability on a box, and of its `θ`-integral.**  For `0 < a ≤ b` and `j ≤ 3`,

* the joint integrand `(x,θ) ↦ Kθ(θ)·D_z^{j+1} g x θ / x` is integrable on the box
  `uIoc a b ×ˢ uIoc 0 (π/2)` (this is the Fubini hypothesis);
* its `θ`-integral `x ↦ Qang g (j+1) x / x` is integrable on `uIoc a b`. -/
theorem QangBoxIntegrable_open {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    {j : ℕ} (hj : j ≤ 3) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    MeasureTheory.IntegrableOn
        (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * Work.Spaces.DzIter (j + 1) g p.1 p.2 / p.1)
        (Set.uIoc a b ×ˢ Set.uIoc 0 (π / 2)) ∧
      MeasureTheory.IntegrableOn (fun x : ℝ => Work.Elliptic.Qang g (j + 1) x / x)
        (Set.uIoc a b) := by
  have hsub1 : Set.uIoc a b ⊆ Work.Spaces.Iz := by
    rw [Work.Spaces.Iz, Set.uIoc_of_le hab]
    exact fun x hx => le_of_lt (lt_trans ha hx.1)
  have hsub2 : Set.uIoc 0 (π / 2) ⊆ Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ, Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ π / 2)]
    exact fun x hx => ⟨le_of_lt hx.1, hx.2⟩
  have hle : (MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))
      ≤ (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.Measure.restrict_mono (Set.prod_mono hsub1 hsub2) le_rfl
  have hD2 : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.DzIter (j + 1) g p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))) :=
    (DzIter_sq_joint_integrable_open hO hmem (by omega)).mono_measure hle
  have hconst : MeasureTheory.Integrable (fun _ : ℝ × ℝ => (1 : ℝ))
      ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))) := by
    have hne : ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))) Set.univ ≠ ⊤ := by
      rw [← Set.univ_prod_univ, MeasureTheory.Measure.prod_prod,
        MeasureTheory.Measure.restrict_apply_univ, MeasureTheory.Measure.restrict_apply_univ,
        Set.uIoc_of_le hab, Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ π / 2),
        Real.volume_Ioc, Real.volume_Ioc]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    simpa only [MeasureTheory.IntegrableOn, MeasureTheory.Measure.restrict_univ] using
      (MeasureTheory.integrableOn_const (μ := (MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))) (s := Set.univ) (C := (1 : ℝ)) hne)
  -- the a.e. domination of the joint integrand
  have haesmF : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
        * Work.Spaces.DzIter (j + 1) g p.1 p.2 / p.1)
      ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))) :=
    (Work.Spaces.aesm_of_continuousOn_Qd _
      (continuousOn_Ktheta_DzIter_div_open hO (j + 1))).mono_measure hle
  have hdom : ∀ᵐ p ∂((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
      (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))),
      ‖Work.Elliptic.Ktheta p.2 * Work.Spaces.DzIter (j + 1) g p.1 p.2 / p.1‖
        ≤ (3 / a) * ((Work.Spaces.DzIter (j + 1) g p.1 p.2) ^ 2 + 1) := by
    refine ae_prod_box hab (fun z θ hz hθ1 hθ2 => ?_)
    have hzpos : 0 < z := by
      rw [Set.uIoc_of_le hab] at hz
      exact lt_trans ha hz.1
    have haz : a ≤ z := by
      rw [Set.uIoc_of_le hab] at hz
      exact hz.1.le
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hzpos, abs_mul]
    have hD1 : |Work.Spaces.DzIter (j + 1) g z θ|
        ≤ (Work.Spaces.DzIter (j + 1) g z θ) ^ 2 + 1 := by
      nlinarith [sq_nonneg (|Work.Spaces.DzIter (j + 1) g z θ| - 1),
        sq_abs (Work.Spaces.DzIter (j + 1) g z θ),
        abs_nonneg (Work.Spaces.DzIter (j + 1) g z θ)]
    have hDnn : 0 ≤ |Work.Spaces.DzIter (j + 1) g z θ| := abs_nonneg _
    have h1 : |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter (j + 1) g z θ| / z
        ≤ 3 * |Work.Spaces.DzIter (j + 1) g z θ| / z :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (abs_Ktheta_le_three θ) hDnn) hzpos.le
    have h2 : 3 * |Work.Spaces.DzIter (j + 1) g z θ| / z
        ≤ 3 * ((Work.Spaces.DzIter (j + 1) g z θ) ^ 2 + 1) / z :=
      div_le_div_of_nonneg_right (by linarith) hzpos.le
    have h3 : 3 * ((Work.Spaces.DzIter (j + 1) g z θ) ^ 2 + 1) / z
        ≤ 3 * ((Work.Spaces.DzIter (j + 1) g z θ) ^ 2 + 1) / a :=
      div_le_div_of_nonneg_left (by positivity) ha haz
    have h4 : 3 * ((Work.Spaces.DzIter (j + 1) g z θ) ^ 2 + 1) / a
        = (3 / a) * ((Work.Spaces.DzIter (j + 1) g z θ) ^ 2 + 1) := by ring
    linarith [h1, h2, h3, h4.le, h4.ge]
  have hFbox : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
        * Work.Spaces.DzIter (j + 1) g p.1 p.2 / p.1)
      ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))) :=
    MeasureTheory.Integrable.mono' ((hD2.add hconst).const_mul (3 / a)) haesmF hdom
  refine ⟨?_, ?_⟩
  · have hvol : (MeasureTheory.volume : Measure (ℝ × ℝ)).restrict
        (Set.uIoc a b ×ˢ Set.uIoc 0 (π / 2))
        = (MeasureTheory.volume.restrict (Set.uIoc a b)).prod
          (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2))) := by
      rw [MeasureTheory.Measure.prod_restrict]
      rfl
    show MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
        * Work.Spaces.DzIter (j + 1) g p.1 p.2 / p.1)
      ((MeasureTheory.volume : Measure (ℝ × ℝ)).restrict
        (Set.uIoc a b ×ˢ Set.uIoc 0 (π / 2)))
    rw [hvol]
    exact hFbox
  · have h1 : MeasureTheory.Integrable
        (fun x : ℝ => ∫ θ, (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
            * Work.Spaces.DzIter (j + 1) g p.1 p.2 / p.1) (x, θ)
          ∂(MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2))))
        (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
      MeasureTheory.Integrable.integral_prod_left hFbox
    have hset : Set.uIoc 0 (π / 2) =ᵐ[MeasureTheory.volume] Work.Spaces.Iθ := by
      rw [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ π / 2), Work.Spaces.Iθ]
      exact MeasureTheory.Ioc_ae_eq_Icc
    refine h1.congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc (fun x hx => ?_)
    have hxpos : 0 < x := by
      rw [Set.uIoc_of_le hab] at hx
      exact lt_trans ha hx.1
    change (∫ θ in Set.uIoc 0 (π / 2),
        Work.Elliptic.Ktheta θ * Work.Spaces.DzIter (j + 1) g x θ / x)
      = Work.Elliptic.Qang g (j + 1) x / x
    rw [MeasureTheory.setIntegral_congr_set hset, MeasureTheory.integral_div]
    rfl


/-- Cauchy–Schwarz in `θ` for the angular moment, in the interior class: for
`SmoothQuad g`, `HkMem α 4 g`, `j ≤ 4` and `z > 0`,

  `(Qang g j z)² ≤ (∫_θ Ktheta θ²)·(∫_θ (D_z^j g z θ)²)`,

`Qang g j z = ∫_θ Ktheta θ · D_z^j g z θ dθ`.  This is `Work.Elliptic.Qang_sq_le` with the
analyticity hypothesis `Work.Spaces.SmoothNbhd g` replaced by `SmoothQuad g`: both `θ`-slices are
measurable on `Iθ` (they are continuous on the open interval, `SmoothQuad` +
`Work.Spaces.aesm_slice_of_continuousOn_Qd`) and square-integrable there (`Ktheta` is continuous
on the compact `Iθ`; `(D_z^j g z ·)²` is dominated by `HkIntegrand α 4 g z ·` by
`Work.Spaces.sq_le_HkIntegrand_z` and `hmem.1`, on the full-measure open interval `Ioo 0 (π/2)`),
so the inequality is the standard Cauchy–Schwarz for the Bochner integral
(`MeasureTheory.integral_mul_le_Lp_mul_Lq`, or a version of
`Work.Spaces.hardyZ_interval_integral_mul_le_sqrt` for functions merely continuous on the open
interval); no continuity at the angular endpoints `θ = 0, π/2` is needed.  The hypothesis
`j ≤ 4` is needed: `sq_le_HkIntegrand_z` gives the domination only for `j ≤ 4`, and that is what
makes the second factor finite. -/
theorem Qang_sq_leQ_open (α : ℝ) (g : ℝ → ℝ → ℝ) (hO : Work.FTS.EllipticEst.SmoothOpen g)
    (hmem : Work.Spaces.HkMem α 4 g) (j : ℕ) (hj : j ≤ 4) {z : ℝ} (hz : 0 < z) :
    (Work.Elliptic.Qang g j z) ^ 2 ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
      * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2) := by
  -- `Iθ = Icc 0 (π/2)` and the open interval `Ioo 0 (π/2)` differ by the two endpoints, a null
  -- set: every integral below can be taken over the open interval, where the `θ`-slice of
  -- `D_z^j g` is continuous (`SmoothQuad` only gives smoothness on the *open* quadrant).
  have hIoo : (Set.Icc (0 : ℝ) (π / 2)) =ᵐ[volume] (Set.Ioo (0 : ℝ) (π / 2)) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
  have hQeq : Work.Elliptic.Qang g j z
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2),
          Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ := by
    rw [Work.Elliptic.Qang]
    exact MeasureTheory.setIntegral_congr_set hIoo
  have hKeq : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.setIntegral_congr_set hIoo
  have hAeq : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2)
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2 :=
    MeasureTheory.setIntegral_congr_set hIoo
  -- the `θ`-slice of `D_z^j g` at `z > 0` is continuous on `(0,π/2)`
  have hzIoi : (0 : ℝ) < z := hz
  have hAcont : ContinuousOn (fun θ => Work.Spaces.DzIter j g z θ)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    ((hO.DzIter j).curry_θ hzIoi).continuousOn
  -- `Ktheta` is continuous everywhere (hence on `Iθ` and on `Ioo 0 (π/2)`)
  have hKcont : Continuous (fun θ => Work.Elliptic.Ktheta θ) := by
    unfold Work.Elliptic.Ktheta
    fun_prop
  -- integrability of `Ktheta²` on the open interval (continuity on the compact closure)
  have hK2int : IntegrableOn (fun θ => Work.Elliptic.Ktheta θ ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    ((hKcont.pow 2).continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Set.Ioo_subset_Icc_self
  -- integrability of `HkIntegrand α 4 g z ·`, transported from `hmem` to the open interval
  have hHkint : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 g z θ)
      (Set.Ioo (0 : ℝ) (π / 2)) := by
    change Integrable (fun θ => Work.Spaces.HkIntegrand α 4 g z θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2)))
    rw [← MeasureTheory.Measure.restrict_congr_set hIoo]
    simpa only [Work.Spaces.Iθ, IntegrableOn] using hmem.1 z (le_of_lt hz)
  -- a.e. strong measurability of the `θ`-slice
  have hAesm : AEStronglyMeasurable (fun θ => |Work.Spaces.DzIter j g z θ|)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    simpa only [Real.norm_eq_abs] using (hAcont.aestronglyMeasurable measurableSet_Ioo).norm
  -- integrability of `(D_z^j g z ·)²`: dominated by the `ℋ⁴`-integrand on the open interval
  have hA2int : IntegrableOn (fun θ => |Work.Spaces.DzIter j g z θ| ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) := by
    refine hHkint.mono' (hAesm.pow 2) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_abs]
    exact Work.Elliptic.sq_DzIter_le_HkIntegrand_Qd α g hj hz hθ.1 hθ.2
  have hKesm : AEStronglyMeasurable (fun θ => |Work.Elliptic.Ktheta θ|)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    simpa only [Real.norm_eq_abs] using hKcont.aestronglyMeasurable.norm
  have hKabs : IntegrableOn (fun θ => |Work.Elliptic.Ktheta θ| ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) := by
    simpa only [sq_abs] using hK2int
  -- `L²`-membership of the two factors (`p = q = 2`)
  have hKmem : MemLp (fun θ => |Work.Elliptic.Ktheta θ|) (ENNReal.ofReal 2)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    exact (MeasureTheory.memLp_two_iff_integrable_sq hKesm).mpr hKabs
  have hAmem : MemLp (fun θ => |Work.Spaces.DzIter j g z θ|) (ENNReal.ofReal 2)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    exact (MeasureTheory.memLp_two_iff_integrable_sq hAesm).mpr hA2int
  -- Cauchy–Schwarz for the Bochner integral (`p = q = 2`, both factors nonnegative)
  have hcs := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (Set.Ioo (0 : ℝ) (π / 2)))
    (p := 2) (q := 2) (f := fun θ => |Work.Elliptic.Ktheta θ|)
    (g := fun θ => |Work.Spaces.DzIter j g z θ|)
    (by norm_num [Real.holderConjugate_iff])
    (Filter.Eventually.of_forall fun θ => abs_nonneg _)
    (Filter.Eventually.of_forall fun θ => abs_nonneg _) hKmem hAmem
  have hnQ : |∫ θ in Set.Ioo (0 : ℝ) (π / 2),
        Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ|
      ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2),
          |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g z θ| := by
    have h := MeasureTheory.norm_integral_le_integral_norm
      (μ := volume.restrict (Set.Ioo (0 : ℝ) (π / 2)))
      (fun θ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ)
    simpa only [Real.norm_eq_abs, abs_mul] using h
  have hKIsq : (∫ θ in Set.Ioo (0 : ℝ) (π / 2), |Work.Elliptic.Ktheta θ| ^ (2 : ℝ))
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by
      simp only [Real.rpow_two, sq_abs])
  have hAIsq : (∫ θ in Set.Ioo (0 : ℝ) (π / 2), |Work.Spaces.DzIter j g z θ| ^ (2 : ℝ))
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2 :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by
      simp only [Real.rpow_two, sq_abs])
  have hK0 : 0 ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.integral_nonneg (fun θ => sq_nonneg _)
  have hA0 : 0 ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2 :=
    MeasureTheory.integral_nonneg (fun θ => sq_nonneg _)
  have hmain : (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
        Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ) ^ 2
      ≤ (∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2)
        * (∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2) := by
    calc (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
          Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ) ^ 2
        = |∫ θ in Set.Ioo (0 : ℝ) (π / 2),
            Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ| ^ 2 := by rw [sq_abs]
      _ ≤ (Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2)
            * Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                (Work.Spaces.DzIter j g z θ) ^ 2)) ^ 2 := by
          apply pow_le_pow_left₀ (abs_nonneg _)
          calc |∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ|
              ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                  |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g z θ| := hnQ
            _ ≤ (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                    |Work.Elliptic.Ktheta θ| ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
                * (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                    |Work.Spaces.DzIter j g z θ| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hcs
            _ = Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2)
                * Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                    (Work.Spaces.DzIter j g z θ) ^ 2) := by
                rw [hKIsq, hAIsq, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      _ = (∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2)
          * (∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2) := by
          rw [mul_pow, Real.sq_sqrt hK0, Real.sq_sqrt hA0]
  rw [hQeq, hKeq, hAeq]
  exact hmain


/-- **The primitive identity for `z₀ ≤ z`.**  For every `j ≤ 3` and `0 < z₀ ≤ z`,

  `Qang g j z - Qang g j z₀ = ∫_{z₀}^{z} Qang g (j+1) x / x dx`.

The proof integrates the slice formula
`D_z^j g z θ - D_z^j g z₀ θ = ∫_{z₀}^{z} D_z^{j+1} g x θ / x dx`
(`QangSliceFTC_open`) against `Ktheta` and swaps the two integrations with Fubini on the box
`uIoc z₀ z ×ˢ uIoc 0 (π/2)`, whose joint integrability is `QangBoxIntegrable_open`. -/
theorem Qang_primitive_le_open (α : ℝ) (g : ℝ → ℝ → ℝ) (hO : Work.FTS.EllipticEst.SmoothOpen g)
    (hmem : Work.Spaces.HkMem α 4 g) {j : ℕ} (hj : j ≤ 3) {z z₀ : ℝ} (hz : 0 < z)
    (hz₀ : 0 < z₀) (hle : z₀ ≤ z) :
    Work.Elliptic.Qang g j z - Work.Elliptic.Qang g j z₀
      = ∫ x in z₀..z, Work.Elliptic.Qang g (j + 1) x / x := by
  -- integral integrability of the two angular slices over `0..π/2`
  have hslice : ∀ {w : ℝ}, 0 < w →
      IntervalIntegrable (fun θ : ℝ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g w θ)
        volume 0 (π/2) := by
    intro w hw
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0 : ℝ) ≤ π / 2)]
    refine (QangSliceIntegrable_open hO hmem (by omega : j ≤ 4) hw).mono_set ?_
    rw [Work.Spaces.Iθ]
    exact Set.Ioc_subset_Icc_self
  have hIi_z := hslice hz
  have hIi_z₀ := hslice hz₀
  -- Step 1: split the difference of the two θ-integrals
  have h1 : Work.Elliptic.Qang g j z - Work.Elliptic.Qang g j z₀
      = ∫ θ in (0 : ℝ)..(π / 2), (Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ
          - Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z₀ θ) := by
    rw [Qang_eq_intervalIntegral g j z, Qang_eq_intervalIntegral g j z₀]
    exact (intervalIntegral.integral_sub hIi_z hIi_z₀).symm
  -- Step 2: factor out the angular weight
  have h2 : (∫ θ in (0 : ℝ)..(π / 2), (Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ
        - Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z₀ θ))
      = ∫ θ in (0 : ℝ)..(π / 2), Work.Elliptic.Ktheta θ
          * (Work.Spaces.DzIter j g z θ - Work.Spaces.DzIter j g z₀ θ) := by
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    ring
  -- Step 3: the slice formula
  have h3 : (∫ θ in (0 : ℝ)..(π / 2), Work.Elliptic.Ktheta θ
        * (Work.Spaces.DzIter j g z θ - Work.Spaces.DzIter j g z₀ θ))
      = ∫ θ in (0 : ℝ)..(π / 2), Work.Elliptic.Ktheta θ
          * (∫ x in z₀..z, Work.Spaces.DzIter (j + 1) g x θ / x) := by
    refine intervalIntegral.integral_congr_ae ?_
    refine ae_imp_uIoc (fun θ hθ1 hθ2 => ?_)
    rw [QangSliceFTC_open hO j hz hz₀ ⟨hθ1, hθ2⟩]
  -- Step 4: pull the angular weight inside the inner integral
  have h4 : (∫ θ in (0 : ℝ)..(π / 2), Work.Elliptic.Ktheta θ
        * (∫ x in z₀..z, Work.Spaces.DzIter (j + 1) g x θ / x))
      = ∫ θ in (0 : ℝ)..(π / 2), ∫ x in z₀..z,
          Work.Elliptic.Ktheta θ * (Work.Spaces.DzIter (j + 1) g x θ / x) := by
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    exact (intervalIntegral.integral_const_mul (Work.Elliptic.Ktheta θ)
      (fun x => Work.Spaces.DzIter (j + 1) g x θ / x)).symm
  -- Step 5: Fubini on the box
  have hFbox : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
        * (Work.Spaces.DzIter (j + 1) g p.1 p.2 / p.1))
      (Set.uIoc z₀ z ×ˢ Set.uIoc 0 (π / 2)) :=
    (QangBoxIntegrable_open hO hmem hj hz₀ hle).1.congr_fun (fun p _ => by ring)
      ((measurableSet_uIoc).prod measurableSet_uIoc)
  have h5 : (∫ θ in (0 : ℝ)..(π / 2), ∫ x in z₀..z,
        Work.Elliptic.Ktheta θ * (Work.Spaces.DzIter (j + 1) g x θ / x))
      = ∫ x in z₀..z, ∫ θ in (0 : ℝ)..(π / 2),
          Work.Elliptic.Ktheta θ * (Work.Spaces.DzIter (j + 1) g x θ / x) :=
    (MeasureTheory.intervalIntegral_intervalIntegral_swap
      (F := fun x θ => Work.Elliptic.Ktheta θ
        * (Work.Spaces.DzIter (j + 1) g x θ / x)) hFbox).symm
  -- Step 6: identify the inner integral with `Qang g (j+1) x / x`
  have h6 : (∫ x in z₀..z, ∫ θ in (0 : ℝ)..(π / 2),
        Work.Elliptic.Ktheta θ * (Work.Spaces.DzIter (j + 1) g x θ / x))
      = ∫ x in z₀..z, Work.Elliptic.Qang g (j + 1) x / x := by
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    have hq : Work.Elliptic.Qang g (j + 1) x
        = ∫ θ in (0 : ℝ)..(π / 2), Work.Elliptic.Ktheta θ * Work.Spaces.DzIter (j + 1) g x θ :=
      Qang_eq_intervalIntegral g (j + 1) x
    have hfun : (fun θ : ℝ => Work.Elliptic.Ktheta θ
          * (Work.Spaces.DzIter (j + 1) g x θ / x))
        = fun θ : ℝ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter (j + 1) g x θ / x := by
      funext θ; ring
    rw [hfun, hq, intervalIntegral.integral_div]
  rw [h1, h2, h3, h4, h5, h6]

/-- **The primitive identity.**  For every `j ≤ 3` and every `z, z₀ > 0`,

  `Qang g j z - Qang g j z₀ = ∫_{z₀}^{z} Qang g (j+1) x / x dx`. -/
theorem Qang_primitive_open (α : ℝ) (g : ℝ → ℝ → ℝ) (hO : Work.FTS.EllipticEst.SmoothOpen g)
    (hmem : Work.Spaces.HkMem α 4 g) {j : ℕ} (hj : j ≤ 3) {z z₀ : ℝ} (hz : 0 < z)
    (hz₀ : 0 < z₀) :
    Work.Elliptic.Qang g j z - Work.Elliptic.Qang g j z₀
      = ∫ x in z₀..z, Work.Elliptic.Qang g (j + 1) x / x := by
  rcases le_total z₀ z with hle | hle
  · exact Qang_primitive_le_open α g hO hmem hj hz hz₀ hle
  · have h := Qang_primitive_le_open α g hO hmem hj hz₀ hz hle
    rw [intervalIntegral.integral_symm z₀ z] at h
    linarith [h]

/-- `z ↦ Qang g (j+1) z / z` is continuous at every `z > 0`, for `j ≤ 2`: this is the
integrand of the primitive identity, and it is continuous because `Qang g (j+1)` is
(`j + 1 ≤ 3`) and `z ≠ 0`. -/
theorem continuousAt_Qang_div {g : ℝ → ℝ → ℝ} {j : ℕ} {z : ℝ}
    (hcont : ContinuousOn (fun w => Work.Elliptic.Qang g (j + 1) w) (Set.Ioi 0))
    (hz : 0 < z) :
    ContinuousAt (fun x => Work.Elliptic.Qang g (j + 1) x / x) z :=
  (hcont.continuousAt (isOpen_Ioi.mem_nhds hz)).div continuousAt_id (ne_of_gt hz)

/-- `Qang g j` is continuous on `(0,∞)` for `j ≤ 3`: it is (a constant plus) the primitive of
`x ↦ Qang g (j+1) x / x`, which is integrable on every compact subinterval of `(0,∞)`. -/
theorem continuousOn_Qang_open (α : ℝ) (g : ℝ → ℝ → ℝ) (hO : Work.FTS.EllipticEst.SmoothOpen g)
    (hmem : Work.Spaces.HkMem α 4 g) {j : ℕ} (hj : j ≤ 3) :
    ContinuousOn (fun z => Work.Elliptic.Qang g j z) (Set.Ioi 0) := by
  intro z hz
  have hzpos : 0 < z := hz
  have hz2pos : 0 < z / 2 := by linarith
  have hle1 : z / 2 ≤ 2 * z := by linarith
  -- integrability of the integrand on a closed interval around `z`
  obtain ⟨-, hint⟩ := QangBoxIntegrable_open hO hmem hj hz2pos hle1
  have hintIcc : MeasureTheory.IntegrableOn (fun x => Work.Elliptic.Qang g (j + 1) x / x)
      (Set.uIcc (z / 2) (2 * z)) := by
    rw [Set.uIcc_of_le hle1]
    refine (integrableOn_Icc_iff_integrableOn_Ioc (a := z / 2)
      (f := fun x => Work.Elliptic.Qang g (j + 1) x / x)).mpr ?_
    rwa [Set.uIoc_of_le hle1] at hint
  have hcont := intervalIntegral.continuousOn_primitive_interval hintIcc
  -- the primitive is `Qang g j · - Qang g j (z/2)` on the interval
  have hcongr : Set.EqOn (fun x => ∫ t in z / 2..x, Work.Elliptic.Qang g (j + 1) t / t)
      (fun x => Work.Elliptic.Qang g j x - Work.Elliptic.Qang g j (z / 2))
      (Set.uIcc (z / 2) (2 * z)) := by
    intro x hx
    have hxpos : 0 < x := by
      rw [Set.uIcc_of_le hle1] at hx
      linarith [hx.1]
    exact (Qang_primitive_open α g hO hmem hj hxpos hz2pos).symm
  have hcont2 : ContinuousOn
      (fun x => Work.Elliptic.Qang g j x - Work.Elliptic.Qang g j (z / 2))
      (Set.uIcc (z / 2) (2 * z)) := hcont.congr hcongr.symm
  have hnhds : Set.uIcc (z / 2) (2 * z) ∈ 𝓝 z := by
    rw [Set.uIcc_of_le hle1]
    exact Icc_mem_nhds (by linarith) (by linarith)
  have hcat : ContinuousAt
      (fun x => Work.Elliptic.Qang g j x - Work.Elliptic.Qang g j (z / 2)) z :=
    hcont2.continuousAt hnhds
  exact ((hcat.add_const (Work.Elliptic.Qang g j (z / 2))).congr
    (Filter.Eventually.of_forall (fun x => by ring))).continuousWithinAt

/-- **`Qang g j` is differentiable on `(0,∞)` for `j ≤ 2`, with derivative
`Qang g (j+1) z / z`**: the primitive identity exhibits it as the primitive of a function
which is continuous at `z` (`continuousOn_Qang_open` at level `j + 1 ≤ 3`). -/
theorem hasDerivAt_Qang_open (α : ℝ) (g : ℝ → ℝ → ℝ) (hO : Work.FTS.EllipticEst.SmoothOpen g)
    (hmem : Work.Spaces.HkMem α 4 g) {j : ℕ} (hj : j ≤ 2) {z : ℝ} (hz : 0 < z)
    (hcont : ContinuousOn (fun w => Work.Elliptic.Qang g (j + 1) w) (Set.Ioi 0)) :
    HasDerivAt (fun z => Work.Elliptic.Qang g j z)
      (Work.Elliptic.Qang g (j + 1) z / z) z := by
  have hz2pos : 0 < z / 2 := by linarith
  have hle1 : z / 2 ≤ z := by linarith
  obtain ⟨-, hint⟩ := QangBoxIntegrable_open hO hmem (by omega : j ≤ 3) hz2pos hle1
  have hInt : IntervalIntegrable (fun x => Work.Elliptic.Qang g (j + 1) x / x) volume
      (z / 2) z := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle1]
    rwa [Set.uIoc_of_le hle1] at hint
  have hcontAt := continuousAt_Qang_div hcont hz
  have hcontOn : ContinuousOn (fun x => Work.Elliptic.Qang g (j + 1) x / x) (Set.Ioi 0) :=
    hcont.div continuousOn_id (fun x hx => ne_of_gt hx)
  have hsmAt := ContinuousOn.stronglyMeasurableAtFilter (μ := volume) isOpen_Ioi hcontOn z hz
  have hprim : HasDerivAt (fun u => ∫ x in z / 2..u, Work.Elliptic.Qang g (j + 1) x / x)
      (Work.Elliptic.Qang g (j + 1) z / z) z :=
    intervalIntegral.integral_hasDerivAt_right hInt hsmAt hcontAt
  have heq : (fun u => Work.Elliptic.Qang g j u - Work.Elliptic.Qang g j (z / 2))
      =ᶠ[𝓝 z] (fun u => ∫ x in z / 2..u, Work.Elliptic.Qang g (j + 1) x / x) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with u hu
    exact Qang_primitive_open α g hO hmem (by omega : j ≤ 3) hu hz2pos
  have h1 := hprim.congr_of_eventuallyEq heq
  have h2 := h1.add_const (Work.Elliptic.Qang g j (z / 2))
  exact h2.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun u => by ring))

/-- `z`-differentiation of the angular moments `Qang g j z = ∫_θ Ktheta θ · D_z^j g z θ dθ`
in the interior class `SmoothQuad g + HkMem α 4 g` (no analyticity/`SmoothNbhd`):
`Qang g j` is continuous on `(0,∞)` for `j ≤ 3`, and for `j ≤ 2` it is differentiable at every
`z > 0` with `∂_z (Qang g j) z = Qang g (j+1) z / z`.

Route.  For each `θ ∈ (0,π/2)` the slice `z ↦ D_z^j g z θ` is `C^∞` on `Ioi (-1)`
(`Work.FTS.LocData.SmoothQuad.curry_z`), and `z·∂_z(D_z^j g) = D_z^{j+1} g`, so the primitive
formula (FTC) on `z₀..z` gives
`D_z^j g z θ - D_z^j g z₀ θ = ∫_{z₀}^z D_z^{j+1} g x θ / x dx` for every `θ ∈ (0,π/2)`.
Multiply by `Ktheta θ` and integrate in `θ`: the difference of the two `θ`-integrals is the
`θ`-integral of the difference (each `θ ↦ Ktheta θ · D_z^j g z θ` is integrable on `Iθ` for
`z > 0`, by Cauchy–Schwarz with `∫_θ (D_z^j g z θ)² < ∞`; the latter follows from `hmem.1` and
the pointwise domination of `(D_z^j g)²` by the `j`-th summand of `HkIntegrand α 4 g`, which is
`Work.Spaces.sq_le_HkIntegrand_z`).  Then Fubini/Tonelli on the box
`[min z z₀, max z z₀] × Iθ`: the joint integrand `(x,θ) ↦ Ktheta θ · D_z^{j+1} g x θ / x` is
integrable there because `|Ktheta| ≤ 3` and Cauchy–Schwarz bounds it by
`(∫∫ (D_z^{j+1} g)²/x²)^{1/2}`, while on the box `1/x² ≤ C·w(x)²·sin(2θ)^{-η}`
(`w ≥ w_min > 0` since `x ≥ min z z₀ > 0`, and `sin(2θ)^{-η} ≥ 1`) and the `(j+1)`-th pure
`D_z` slot of `HkIntegrand α 4 g` is integrable over `Iz × Iθ` by `hmem`; continuity of the
joint integrand on the box gives measurability.  This yields, for all `z, z₀ > 0`,
`Qang g j z - Qang g j z₀ = ∫_{z₀}^z Qang g (j+1) x / x dx`, and also that
`x ↦ Qang g (j+1) x / x` is integrable on each compact subinterval of `(0,∞)`.
Consequently `Qang g j` is continuous on `(0,∞)` (it is a primitive plus a constant), and for
`j ≤ 2` the right-hand integrand `x ↦ Qang g (j+1) x / x` is continuous at `z` (continuity of
`Qang g (j+1)`, obtained at the level `j+1 ≤ 3`), so
`HasDerivAt (Qang g j) (Qang g (j+1) z / z) z`.
(`j ≤ 3` in the continuity part is sharp: continuity of `Qang g 3` uses the Fubini identity at
level 3, hence the 4-th pure `D_z` slot of `HkMem α 4 g`.)
Useful existing siblings (all with the analyticity hypothesis `Spaces.SmoothNbhd`, which must
NOT be used): `Work.Elliptic.Qang_deriv_mul`, `Work.Elliptic.L12Iterate` (and
`Work.EllipticEst.Blocks.L12Gen.L12Iterate_k`), `Work.Elliptic.L12k0`. -/
theorem QangDiff_open (α : ℝ) (g : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g) :
    (∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
        HasDerivAt (Work.Elliptic.Qang g j) (Work.Elliptic.Qang g (j + 1) z / z) z) ∧
      (∀ j : ℕ, j ≤ 3 → ContinuousOn (Work.Elliptic.Qang g j) (Set.Ioi 0)) := by
  have hcont : ∀ j : ℕ, j ≤ 3 → ContinuousOn (fun z => Work.Elliptic.Qang g j z) (Set.Ioi 0) :=
    fun j hj => continuousOn_Qang_open α g hO hmem hj
  refine ⟨?_, hcont⟩
  intro j hj z hz
  exact hasDerivAt_Qang_open α g hO hmem hj hz (hcont (j + 1) (by omega))


/-- The `z = 0`-slice of `Iz = [0,∞)` is null, so every almost-everywhere statement on
`Iz` may be proved on the open half-line. -/
private theorem Iz_ae_eq_Ioi : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
  (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm

/-- The two angular endpoints of `Iθ = [0,π/2]` are null. -/
private theorem Iθ_ae_eq_Ioo : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
  (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm

/-- **The pure `D_z`-slot domination with the full weight.**  For `z > 0` and
`0 < θ < π/2`, the square of the weighted iterate is dominated by the `ℋ⁴`-integrand:

  `(D_z^i g z θ)² w(z)² ≤ HkIntegrand α 4 g z θ`   (`i ≤ 4`).

This is `Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq` (which gives
`(D_z^i g)² ≤ HkIntegrand/w²`) multiplied by `w² > 0`. -/
private theorem DzIter_sq_w_sq_le_HkIntegrand (α : ℝ) (g : ℝ → ℝ → ℝ) {i : ℕ} (hi : i ≤ 4)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.DzIter i g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have h1 := Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq α 4 g i hi hz hθ
  have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg (Work.Spaces.w z))
  rwa [div_mul_cancel₀ _
    (pow_ne_zero 2 (ne_of_gt (Work.FTS.H2.w_pos hz)))] at h2

/-- The radial weight `w` squared is continuous on `(0,∞)`. -/
private theorem continuousOn_w_sq :
    ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) := by
  have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      = fun z : ℝ => (((1 + z) ^ 2 / z ^ 2) ^ 2) := by
    funext z; rw [Work.Spaces.w]
  rw [hfun]
  exact (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
    (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))).pow 2

theorem Qang_sq_w_sq_integral_open {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    {i : ℕ} (hi : i ≤ 4) :
    MeasureTheory.IntegrableOn (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz ∧
    (∫ z in Work.Spaces.Iz, (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α 4 g := by
  -- the pointwise (in `z > 0`) bound
  have hpt : ∀ z : ℝ, 0 < z →
      (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) := by
    intro z hz
    -- Cauchy–Schwarz in `θ`
    have hCS := Qang_sq_leQ_open α g hO hmem i hi hz
    -- the `θ`-slice domination, with the weight `w z` on the left
    have hslice : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2)
          * (Work.Spaces.w z) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ := by
      have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          (Work.Spaces.DzIter i g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
        rw [MeasureTheory.Measure.restrict_congr_set Iθ_ae_eq_Ioo]
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
          (fun θ hθ => DzIter_sq_w_sq_le_HkIntegrand α g hi hz hθ)
      have hmono := MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (hmem.1 z (le_of_lt hz)) hae
      simpa only [MeasureTheory.integral_mul_const] using hmono
    calc (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2))
            * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hCS (sq_nonneg _)
      _ = (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2)
                * (Work.Spaces.w z) ^ 2) := by ring
      _ ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) :=
          mul_le_mul_of_nonneg_left hslice
            (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)
  -- the bound holds almost everywhere on `Iz`
  have hle : (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)) := by
    rw [MeasureTheory.Measure.restrict_congr_set Iz_ae_eq_Ioi]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hpt
  -- a.e. strong measurability of the left-hand side
  have haesm : AEStronglyMeasurable
      (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hQ : AEStronglyMeasurable (fun z => Work.Elliptic.Qang g i z)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      have h := (Work.Spaces.aesm_of_continuousOn_Qd
        (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * Work.Spaces.DzIter i g p.1 p.2)
        (continuousOn_Ktheta_DzIter_open hO i)).integral_prod_right'
      simpa only [Work.Elliptic.Qang] using h
    have hw : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      rw [MeasureTheory.Measure.restrict_congr_set Iz_ae_eq_Ioi]
      exact continuousOn_w_sq.aestronglyMeasurable measurableSet_Ioi
    exact (hQ.pow 2).mul hw
  -- the dominating function is integrable
  have hdom : MeasureTheory.Integrable
      (fun z => (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hmem.2.const_mul _
  refine ⟨?_, ?_⟩
  · refine MeasureTheory.Integrable.mono' hdom haesm ?_
    filter_upwards [hle] with z hz
    rwa [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  · have hmono := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      hdom hle
    rw [MeasureTheory.integral_const_mul] at hmono
    exact hmono.trans (le_of_eq rfl)


/-! ## The iterated `z ∂_z`-identity from a primitive relation -/

/-- If `u = Φ 0` and `Φ j` has derivative `Φ (j+1) z / z` at every `z > 0` (for `j ≤ 2`), then
`DzdIter i u = Φ i` on `(0,∞)` for every `i ≤ 3`.

This is the pointwise half of the main theorem, stated for an abstract pair `(u, Φ)` so that
the induction is independent of `Qang`.  The hypothesis `j ≤ 2` is what makes
`z * ∂_z(Φ j) z = Φ (j+1) z` hold: `DzdIter i u` agrees with `Φ i` on the open half-line, so
their derivatives at `z > 0` agree, and the divided derivative `Φ (j+1) z / z` is undone by the
multiplication by `z`. -/
private theorem DzdIter_eq_of_hasDerivAt {u : ℝ → ℝ} {Φ : ℕ → ℝ → ℝ}
    (h0 : ∀ z, u z = Φ 0 z)
    (hder : ∀ j ≤ 2, ∀ z, 0 < z → HasDerivAt (Φ j) (Φ (j + 1) z / z) z) :
    ∀ i ≤ 3, ∀ z, 0 < z → Work.Elliptic.DzdIter i u z = Φ i z := by
  intro i
  induction i with
  | zero => intro _ z _; exact h0 z
  | succ i ih =>
    intro _ z hz
    have hprev : Work.Elliptic.DzdIter i u =ᶠ[𝓝 z] Φ i := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      exact ih (by omega) w hw
    rw [Work.Elliptic.DzdIter_succ, Work.Elliptic.Dzd]
    rw [hprev.deriv_eq, (hder i (by omega) z hz).deriv]
    rw [mul_comm z, div_mul_cancel₀ _ (ne_of_gt hz)]

/-! ## The main identity -/

theorem DzdIter_Qang_ae_open {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ᵐ z ∂(MeasureTheory.volume), 0 < z → ∀ i ∈ Finset.range 5,
      Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang g 0 z) z = Work.Elliptic.Qang g i z := by
  -- the divided derivative of `Qang g j` for `j ≤ 2` (continuity of `Qang g (j+1)`, `j+1 ≤ 3`)
  have hder2 : ∀ j ≤ 2, ∀ z : ℝ, 0 < z →
      HasDerivAt (fun z => Work.Elliptic.Qang g j z) (Work.Elliptic.Qang g (j + 1) z / z) z := by
    intro j hj z hz
    exact hasDerivAt_Qang_open α g hO hmem hj hz
      (continuousOn_Qang_open α g hO hmem (by omega))
  -- the pointwise identity for `i ≤ 3`
  have hpoint : ∀ i ≤ 3, ∀ z, 0 < z →
      Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang g 0 z) z = Work.Elliptic.Qang g i z :=
    DzdIter_eq_of_hasDerivAt (fun z => rfl) hder2
  -- the integrand `x ↦ Qang g 4 x / x` is interval integrable on every compact subinterval of
  -- `(0,∞)`: this is the `j = 3` instance of the Fubini/box integrability
  have hφint : ∀ n : ℕ, IntervalIntegrable (fun x => Work.Elliptic.Qang g 4 x / x) volume
      (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) := by
    intro n
    have ha : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    have hab : 1 / ((n : ℝ) + 2) ≤ (n : ℝ) + 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact intervalIntegrable_iff.mpr
      (QangBoxIntegrable_open hO hmem (j := 3) le_rfl ha hab).2
  -- the Lebesgue differentiation theorem on each piece of the countable cover
  have hldt : ∀ᵐ z ∂volume, ∀ n : ℕ, (z ∈ Set.uIcc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) →
      ∀ c ∈ Set.uIcc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2),
        HasDerivAt (fun y => ∫ t in c..y, Work.Elliptic.Qang g 4 t / t)
          (Work.Elliptic.Qang g 4 z / z) z) :=
    MeasureTheory.ae_all_iff.mpr fun n => (hφint n).ae_hasDerivAt_integral
  -- every `z > 0` lies in one of the pieces of the cover
  have hcover : ∀ z : ℝ, 0 < z → ∃ n : ℕ, z ∈ Set.uIcc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) := by
    intro z hz
    obtain ⟨n, hn⟩ := exists_nat_gt (max (1 / z) z)
    refine ⟨n, ?_⟩
    have hnz : z < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
    have hn1 : 1 / z < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
    have hzn : 1 < z * (n : ℝ) := by
      rw [div_lt_iff₀ hz] at hn1
      linarith
    have hab : 1 / ((n : ℝ) + 2) ≤ (n : ℝ) + 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [Set.uIcc_of_le hab, Set.mem_Icc]
    exact ⟨by
      rw [div_le_iff₀ (by positivity)]
      nlinarith, by linarith⟩
  -- `1` lies in every piece of the cover, so the primitive can be taken from `1`
  have h1mem : ∀ n : ℕ, (1 : ℝ) ∈ Set.uIcc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) := by
    intro n
    have hab : 1 / ((n : ℝ) + 2) ≤ (n : ℝ) + 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [Set.uIcc_of_le hab, Set.mem_Icc]
    exact ⟨by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)],
      by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]⟩
  -- a.e. differentiability of the primitive `y ↦ ∫_1^y Qang g 4 t / t`
  have hprim : ∀ᵐ z ∂volume, 0 < z →
      HasDerivAt (fun y => ∫ t in (1 : ℝ)..y, Work.Elliptic.Qang g 4 t / t)
        (Work.Elliptic.Qang g 4 z / z) z := by
    filter_upwards [hldt] with z hz hzpos
    obtain ⟨n, hn⟩ := hcover z hzpos
    exact hz n hn 1 (h1mem n)
  -- hence `Qang g 3` is differentiable a.e. with the divided derivative `Qang g 4 z / z`
  have hderiv3 : ∀ᵐ z ∂volume, 0 < z →
      HasDerivAt (fun y => Work.Elliptic.Qang g 3 y) (Work.Elliptic.Qang g 4 z / z) z := by
    filter_upwards [hprim] with z hz hzpos
    have hev : (fun y => Work.Elliptic.Qang g 3 y) =ᶠ[𝓝 z]
        (fun y => (∫ t in (1 : ℝ)..y, Work.Elliptic.Qang g 4 t / t)
          + Work.Elliptic.Qang g 3 1) := by
      filter_upwards [isOpen_Ioi.mem_nhds hzpos] with y hy
      have h := Qang_primitive_open α g hO hmem (j := 3) (by norm_num) hy
        (by norm_num : (0 : ℝ) < 1)
      linarith
    exact ((hz hzpos).add_const _).congr_of_eventuallyEq hev
  -- the fourth iterate
  have h4 : ∀ᵐ z ∂volume, 0 < z →
      Work.Elliptic.DzdIter 4 (fun z => Work.Elliptic.Qang g 0 z) z
        = Work.Elliptic.Qang g 4 z := by
    filter_upwards [hderiv3] with z hz3 hzpos
    have h3eq : Work.Elliptic.DzdIter 3 (fun z => Work.Elliptic.Qang g 0 z) =ᶠ[𝓝 z]
        (fun w => Work.Elliptic.Qang g 3 w) := by
      filter_upwards [isOpen_Ioi.mem_nhds hzpos] with w hw
      exact hpoint 3 le_rfl w hw
    have hd : deriv (Work.Elliptic.DzdIter 3 (fun z => Work.Elliptic.Qang g 0 z)) z
        = Work.Elliptic.Qang g 4 z / z := by
      rw [h3eq.deriv_eq, (hz3 hzpos).deriv]
    rw [Work.Elliptic.DzdIter_succ, Work.Elliptic.Dzd, hd]
    rw [mul_comm z, div_mul_cancel₀ _ (ne_of_gt hzpos)]
  filter_upwards [h4] with z hz4 hz i hi
  have hi4 : i ≤ 4 := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rcases Nat.lt_or_ge i 4 with hlt | hge
  · exact hpoint i (by omega) z hz
  · have hieq : i = 4 := by omega
    subst hieq
    exact hz4 hz


end Work.FTS.OpenPkg.QangOpen
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.ThetaTracesBdry =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `PhiStar.thetaTraces_of_bdryTraces` (lead install R6, 2026-10-11)

`BdryTraces α k F` implies its θ-part `ThetaTraces α k F` (at `(a,b) = (0,s)`).
-/

namespace Work.FTS.PhiStar


end Work.FTS.PhiStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.B4Aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux

set_option autoImplicit false

/-- `(Xn α f)² = HkSq α 4 f`. -/
theorem xn_sq {α : ℝ} (f : ℝ → ℝ → ℝ) :
    (Work.FTS.Nonlin.Xn α f) ^ 2 = Work.Spaces.HkSq α 4 f := by
  rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 f)]

/-- `HkSq α 4 f = (Xn α f)²`. -/
theorem sq_xn {α : ℝ} (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 4 f = (Work.FTS.Nonlin.Xn α f) ^ 2 := (xn_sq f).symm


/-- `(α^{-1/2})² = α^{-1}`. -/
theorem rpow_neg_half_sq {α : ℝ} (hα : 0 < α) :
    (α ^ (-(1 / 2 : ℝ))) ^ 2 = α ^ (-(1 : ℝ)) := by
  rw [← Real.rpow_natCast (α ^ (-(1 / 2 : ℝ))) 2, ← Real.rpow_mul hα.le]
  norm_num






end Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_Gam_mul_rad =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Filter Set

namespace Work.FTS.StrongEps.EpsE4Thr.TracesAux

/-! ## The mixed derivatives of a separated (angular × radial) product

For a factor `G` of `θ` alone and a factor `h` of `z` alone the mixed operator splits exactly
(`mixed_ang_mul_rad`): `D_z^b D_θ^a (G(θ)·h(z)) = (D_θ^a G)(θ)·(D_z^b h)(z)`.

The two ingredients are the facts that the operators preserve the class:

* `DthIter_mul_zfac` — `D_θ^i` commutes with multiplication by a `z`-only factor (no smoothness
  is needed: the only ingredient is the unconditional scalar linearity of `deriv`, provided here
  by `deriv_mul_const_uncond` / `deriv_const_mul_uncond`);
* `DzIter_angfac` — `D_z^b` commutes with multiplication by a `θ`-only factor. -/

/-- `deriv` is scalar homogeneous **unconditionally** on the right (Mathlib's `deriv_mul_const`
needs differentiability): if `f` is not differentiable at `x`, then neither is `f · c` for
`c ≠ 0`, so both sides are `0`. -/
private theorem deriv_mul_const_uncond (c x : ℝ) (f : ℝ → ℝ) :
    deriv (fun y => f y * c) x = deriv f x * c := by
  rcases eq_or_ne c 0 with h | h
  · subst h; simp
  · rcases em (DifferentiableAt ℝ f x) with hf | hf
    · exact deriv_mul_const hf c
    · have h2 : ¬ DifferentiableAt ℝ (fun y => f y * c) x := by
        intro hh
        apply hf
        have he : f = fun y => (f y * c) * c⁻¹ := by
          funext y; rw [mul_assoc, mul_inv_cancel₀ h, mul_one]
        rw [he]
        exact hh.mul_const c⁻¹
      rw [deriv_zero_of_not_differentiableAt hf,
        deriv_zero_of_not_differentiableAt h2, zero_mul]

/-- `deriv` is scalar homogeneous **unconditionally** on the left. -/
private theorem deriv_const_mul_uncond (c x : ℝ) (f : ℝ → ℝ) :
    deriv (fun y => c * f y) x = c * deriv f x := by
  rcases eq_or_ne c 0 with h | h
  · subst h; simp
  · rcases em (DifferentiableAt ℝ f x) with hf | hf
    · exact deriv_const_mul c hf
    · have h2 : ¬ DifferentiableAt ℝ (fun y => c * f y) x := by
        intro hh
        apply hf
        have he : f = fun y => c⁻¹ * (c * f y) := by
          funext y; rw [← mul_assoc, inv_mul_cancel₀ h, one_mul]
        rw [he]
        exact hh.const_mul c⁻¹
      rw [deriv_zero_of_not_differentiableAt hf,
        deriv_zero_of_not_differentiableAt h2, mul_zero]

/-- `D_θ^i` commutes with multiplication by a factor depending only on `z`. -/
private theorem DthIter_mul_zfac (i : ℕ) (G : ℝ → ℝ) (h : ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => G θ * h z)
      = fun z θ => (Work.Spaces.DthIter i (fun _ θ' => G θ') 0 θ) * h z := by
  induction i with
  | zero => rfl
  | succ i ih =>
      funext z θ
      show Work.Spaces.Dth (Work.Spaces.DthIter i (fun z θ => G θ * h z)) z θ
        = (Work.Spaces.DthIter (i + 1) (fun _ θ' => G θ') 0 θ) * h z
      rw [ih]
      show Real.sin (2 * θ)
          * deriv (fun θ' => (Work.Spaces.DthIter i (fun _ θ' => G θ') 0 θ') * h z) θ
        = (Real.sin (2 * θ)
          * deriv (fun θ' => Work.Spaces.DthIter i (fun _ θ' => G θ') 0 θ') θ) * h z
      rw [deriv_mul_const_uncond]
      ring

/-- `D_z^b` commutes with multiplication by a factor depending only on `θ`. -/
private theorem DzIter_angfac (b : ℕ) (c : ℝ → ℝ) (h : ℝ → ℝ) :
    Work.Spaces.DzIter b (fun z θ => c θ * h z)
      = fun z θ => c θ * Work.Elliptic.DzdIter b h z := by
  induction b with
  | zero => rfl
  | succ b ih =>
      funext z θ
      show Work.Spaces.Dz (Work.Spaces.DzIter b (fun z θ => c θ * h z)) z θ
        = c θ * Work.Elliptic.DzdIter (b + 1) h z
      rw [ih]
      show z * deriv (fun z' => c θ * Work.Elliptic.DzdIter b h z') z
        = c θ * (z * deriv (Work.Elliptic.DzdIter b h) z)
      rw [deriv_const_mul_uncond]
      ring

/-- **Exact separation of the mixed derivatives of an angular × radial product**:
`D_z^b D_θ^a (G(θ)·h(z)) = (D_θ^a G)(θ)·(D_z^b h)(z)`, for every `z` and `θ` (no smoothness
whatsoever is needed — the operators are the totalised `deriv`-based ones). -/
theorem mixed_ang_mul_rad (a b : ℕ) (G h : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed b a (fun z θ => G θ * h z) z θ
      = (Work.Spaces.DthIter a (fun _ θ' => G θ') 0 θ) * Work.Elliptic.DzdIter b h z := by
  rw [Work.Spaces.mixed, DthIter_mul_zfac a G h,
    DzIter_angfac b (fun θ => Work.Spaces.DthIter a (fun _ θ' => G θ') 0 θ) h]

/-! ## The explicit vanishing of the angular weight times `Γ²`

The angular trace weighs `D_θ^aΓ` by `sin(2θ)^{1-γ}` with `γ = gam α = 1 + α/10 > 1`, so the
weight *diverges* at both endpoints.  What saves the day is that `Γ` itself vanishes there:
`Γ(θ)² ≲ θ^{2α/3}` near `0` and `≲ (π/2-θ)^{4α/3}` near `π/2`, while Jordan's inequality gives
`sin(2θ)^{-α/10} ≲ θ^{-α/10}` (resp. `≲ (π/2-θ)^{-α/10}`), so the products behave like
`θ^{17α/30}` (resp. `(π/2-θ)^{37α/30}`) with **positive** exponents.

Everything is squeezed through the explicit majorant `sin_rpow_le_majorant` of
`Submission/Work/Spaces/sin_rpow_le_majorant.lean`. -/

/-- `Γ(θ)² ≤ θ^{2α/3}` for `0 < θ < π/4`: this is `sin θ ≤ θ` and `cos²θ ≤ 1` raised to the
power `α/3` and squared. -/
private theorem Gam_sq_le_rpow_right {α : ℝ} (hα : 0 < α) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 4) :
    Work.Spaces.Gam α θ ^ 2 ≤ θ ^ (2 * α / 3) := by
  have hθpi : θ < Real.pi := by linarith [Real.pi_pos, hθ1]
  have hsin0 : 0 ≤ Real.sin θ := (Real.sin_pos_of_pos_of_lt_pi hθ0 hθpi).le
  have hsinle : Real.sin θ ≤ θ := Real.sin_le hθ0.le
  have hcosle : Real.cos θ ^ 2 ≤ 1 := Real.cos_sq_le_one θ
  have hbase : Real.sin θ * Real.cos θ ^ 2 ≤ θ := by
    have := mul_le_mul hsinle hcosle (sq_nonneg (Real.cos θ)) hθ0.le
    simpa using this
  have hle1 : Work.Spaces.Gam α θ ≤ θ ^ (α / 3) := by
    rw [Work.Spaces.Gam]
    exact Real.rpow_le_rpow (by positivity) hbase (by positivity)
  have hsq : (θ ^ (α / 3)) ^ 2 = θ ^ (2 * α / 3) := by
    rw [← Real.rpow_two (θ ^ (α / 3)), ← Real.rpow_mul hθ0.le (α / 3) (2 : ℝ)]
    congr 1
    ring
  calc Work.Spaces.Gam α θ ^ 2 ≤ (θ ^ (α / 3)) ^ 2 :=
        pow_le_pow_left₀ (Real.rpow_nonneg (mul_nonneg hsin0 (sq_nonneg _)) _) hle1 2
    _ = θ ^ (2 * α / 3) := hsq

/-- `Γ(θ)² ≤ (π/2-θ)^{4α/3}` for `π/4 < θ < π/2`: here `sin θ ≤ 1`, so `Γ ≤ (cos²θ)^{α/3}`,
and `cos θ = sin (π/2-θ) ≤ π/2-θ`. -/
private theorem Gam_sq_le_rpow_left {α : ℝ} (hα : 0 < α) {θ : ℝ} (hθ0 : Real.pi / 4 < θ)
    (hθ1 : θ < Real.pi / 2) :
    Work.Spaces.Gam α θ ^ 2 ≤ (Real.pi / 2 - θ) ^ (4 * α / 3) := by
  have hd0 : 0 < Real.pi / 2 - θ := by linarith
  have hsin0 : 0 ≤ Real.sin θ :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ0, Real.pi_pos])
      (by linarith [Real.pi_pos])).le
  have hcos0 : 0 ≤ Real.cos θ :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩).le
  have hbb : Real.sin θ * Real.cos θ ^ 2 ≤ Real.cos θ ^ 2 := by
    have := mul_le_mul_of_nonneg_right (Real.sin_le_one θ) (sq_nonneg (Real.cos θ))
    simpa using this
  have hle1 : Work.Spaces.Gam α θ ≤ Real.cos θ ^ (2 * α / 3) := by
    have h1 : Work.Spaces.Gam α θ ≤ (Real.cos θ ^ 2) ^ (α / 3) := by
      rw [Work.Spaces.Gam]
      exact Real.rpow_le_rpow (mul_nonneg hsin0 (sq_nonneg _)) hbb (by positivity)
    have h2 : (Real.cos θ ^ 2) ^ (α / 3) = Real.cos θ ^ (2 * α / 3) := by
      rw [← Real.rpow_two (Real.cos θ), ← Real.rpow_mul hcos0 (2 : ℝ) (α / 3)]
      congr 1
      ring
    rw [h2] at h1
    exact h1
  have hle2 : Real.cos θ ^ (2 * α / 3) ≤ (Real.pi / 2 - θ) ^ (2 * α / 3) := by
    rw [← Real.sin_pi_div_two_sub θ]
    exact Real.rpow_le_rpow
      (Real.sin_pos_of_pos_of_lt_pi hd0 (by linarith [Real.pi_pos])).le
      (Real.sin_le hd0.le) (by positivity)
  have hsq : ((Real.pi / 2 - θ) ^ (2 * α / 3)) ^ 2 = (Real.pi / 2 - θ) ^ (4 * α / 3) := by
    rw [← Real.rpow_two ((Real.pi / 2 - θ) ^ (2 * α / 3)),
      ← Real.rpow_mul hd0.le (2 * α / 3) (2 : ℝ)]
    congr 1
    ring
  calc Work.Spaces.Gam α θ ^ 2 ≤ ((Real.pi / 2 - θ) ^ (2 * α / 3)) ^ 2 :=
        pow_le_pow_left₀ (Real.rpow_nonneg (mul_nonneg hsin0 (sq_nonneg _)) _)
          (le_trans hle1 hle2) 2
    _ = (Real.pi / 2 - θ) ^ (4 * α / 3) := hsq

/-- `sin(2θ)^{1-γ}·Γ(θ)² → 0` as `θ → 0⁺`. -/
private theorem tendsto_sin_rpow_gam_sq_right {α : ℝ} (hα : 0 < α) :
    Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
      * Work.Spaces.Gam α θ ^ 2) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hexp : (1 : ℝ) - Work.Spaces.gam α = -(α / 10) := by rw [Work.Spaces.gam]; ring
  have hp : 0 < α / 10 := by positivity
  have hq : 0 < 17 * α / 30 := by linarith
  have hpow : Filter.Tendsto (fun θ : ℝ => θ ^ (17 * α / 30))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h : Filter.Tendsto (fun θ : ℝ => θ ^ (17 * α / 30)) (nhds (0 : ℝ))
        (nhds (0 ^ (17 * α / 30))) :=
      (Real.continuousAt_rpow_const 0 (17 * α / 30) (Or.inr hq.le)).tendsto
    rw [Real.zero_rpow (ne_of_gt hq)] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hdom := hpow.const_mul (2 * (Real.pi / 4) ^ (α / 10))
  rw [mul_zero] at hdom
  refine squeeze_zero' ?_ ?_ hdom
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi / 4 by positivity)] with θ hθ
    rw [hexp]
    exact mul_nonneg (Real.rpow_nonneg (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])).le _) (sq_nonneg _)
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi / 4 by positivity)] with θ hθ
    rw [hexp]
    have hGam2 := Gam_sq_le_rpow_right hα hθ.1 hθ.2
    have hmaj := Work.Spaces.sin_rpow_le_majorant (α / 10) θ hp
      ⟨hθ.1.le, by linarith [hθ.2, Real.pi_pos]⟩
    have hle2 : (Real.pi / 2 - θ) ^ (-(α / 10)) ≤ θ ^ (-(α / 10)) :=
      Real.rpow_le_rpow_of_nonpos hθ.1 (by linarith [hθ.2]) (by linarith)
    have h2 : (Real.pi / 4) ^ (α / 10) * (θ ^ (-(α / 10)) + (Real.pi / 2 - θ) ^ (-(α / 10)))
        ≤ (Real.pi / 4) ^ (α / 10) * (2 * θ ^ (-(α / 10))) :=
      mul_le_mul_of_nonneg_left (by linarith [hle2])
        (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 4) (α / 10))
    have hmaj' : Real.sin (2 * θ) ^ (-(α / 10))
        ≤ 2 * (Real.pi / 4) ^ (α / 10) * θ ^ (-(α / 10)) := by
      refine le_trans hmaj (le_trans h2 ?_)
      exact le_of_eq (by ring)
    have hb : 0 ≤ 2 * (Real.pi / 4) ^ (α / 10) * θ ^ (-(α / 10)) :=
      mul_nonneg (mul_nonneg (by norm_num)
        (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 4) _))
        (Real.rpow_nonneg hθ.1.le _)
    have hprod := mul_le_mul hmaj' hGam2 (sq_nonneg _) hb
    have hrw : (2 * (Real.pi / 4) ^ (α / 10) * θ ^ (-(α / 10))) * θ ^ (2 * α / 3)
        = 2 * (Real.pi / 4) ^ (α / 10) * θ ^ (17 * α / 30) := by
      rw [mul_assoc, mul_assoc, ← Real.rpow_add hθ.1]
      rw [show -(α / 10) + 2 * α / 3 = 17 * α / 30 by ring]
      ring
    exact le_trans hprod hrw.le

/-- `sin(2θ)^{1-γ}·Γ(θ)² → 0` as `θ → (π/2)⁻`. -/
private theorem tendsto_sin_rpow_gam_sq_left {α : ℝ} (hα : 0 < α) :
    Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
      * Work.Spaces.Gam α θ ^ 2) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hexp : (1 : ℝ) - Work.Spaces.gam α = -(α / 10) := by rw [Work.Spaces.gam]; ring
  have hp : 0 < α / 10 := by positivity
  have hq2 : 0 < 37 * α / 30 := by linarith
  have hδ : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h3 : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (nhds (Real.pi / 2)) (nhds 0) := by
        simpa using (tendsto_const_nhds.sub Filter.tendsto_id :
          Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (nhds (Real.pi / 2))
            (nhds (Real.pi / 2 - Real.pi / 2)))
      exact h3.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with θ hθ
      show (0 : ℝ) < Real.pi / 2 - θ
      have := Set.mem_Iio.mp hθ
      linarith
  have hpowδ : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (37 * α / 30))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have h := (Real.continuousAt_rpow_const 0 (37 * α / 30) (Or.inr hq2.le)).tendsto.comp
      (hδ.mono_right nhdsWithin_le_nhds)
    simpa [Function.comp_def, Real.zero_rpow (ne_of_gt hq2)] using h
  have hdom := hpowδ.const_mul (2 * (Real.pi / 4) ^ (α / 10))
  rw [mul_zero] at hdom
  refine squeeze_zero' ?_ ?_ hdom
  · filter_upwards [Ioo_mem_nhdsLT (show Real.pi / 4 < Real.pi / 2 by linarith [Real.pi_pos])]
      with θ hθ
    rw [hexp]
    exact mul_nonneg (Real.rpow_nonneg (Real.sin_pos_of_pos_of_lt_pi
      (by linarith [hθ.1, Real.pi_pos]) (by linarith [hθ.2, Real.pi_pos])).le _) (sq_nonneg _)
  · filter_upwards [Ioo_mem_nhdsLT (show Real.pi / 4 < Real.pi / 2 by linarith [Real.pi_pos])]
      with θ hθ
    rw [hexp]
    have hG := Gam_sq_le_rpow_left hα hθ.1 hθ.2
    have hmaj := Work.Spaces.sin_rpow_le_majorant (α / 10) θ hp
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
    have hle3 : θ ^ (-(α / 10)) ≤ (Real.pi / 2 - θ) ^ (-(α / 10)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith [hθ.2]) (by linarith [hθ.1]) (by linarith)
    have h2 : (Real.pi / 4) ^ (α / 10) * (θ ^ (-(α / 10)) + (Real.pi / 2 - θ) ^ (-(α / 10)))
        ≤ (Real.pi / 4) ^ (α / 10) * (2 * (Real.pi / 2 - θ) ^ (-(α / 10))) :=
      mul_le_mul_of_nonneg_left (by linarith [hle3])
        (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 4) (α / 10))
    have hmaj' : Real.sin (2 * θ) ^ (-(α / 10))
        ≤ 2 * (Real.pi / 4) ^ (α / 10) * (Real.pi / 2 - θ) ^ (-(α / 10)) := by
      refine le_trans hmaj (le_trans h2 ?_)
      exact le_of_eq (by ring)
    have hb : 0 ≤ 2 * (Real.pi / 4) ^ (α / 10) * (Real.pi / 2 - θ) ^ (-(α / 10)) :=
      mul_nonneg (mul_nonneg (by norm_num)
        (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 4) _))
        (Real.rpow_nonneg (by linarith [hθ.2]) _)
    have hprod := mul_le_mul hmaj' hG (sq_nonneg _) hb
    have hrw : (2 * (Real.pi / 4) ^ (α / 10) * (Real.pi / 2 - θ) ^ (-(α / 10)))
          * (Real.pi / 2 - θ) ^ (4 * α / 3)
        = 2 * (Real.pi / 4) ^ (α / 10) * (Real.pi / 2 - θ) ^ (37 * α / 30) := by
      rw [mul_assoc, mul_assoc, ← Real.rpow_add (by linarith [hθ.2])]
      rw [show -(α / 10) + 4 * α / 3 = 37 * α / 30 by ring]
      ring
    exact le_trans hprod hrw.le

/-- **The angular trace of a `D_θ`-iterate of `Γ`.**  Squeezing the hypothesis
`|D_θ^aΓ| ≤ Cg·Γ` between `0` and `Cg²·sin(2θ)^{1-γ}Γ²` reduces the two one-sided limits to the
explicit vanishing proved above. -/
private theorem trace_aux_base {α : ℝ} (hα : 0 < α) {a : ℕ} {Cg : ℝ} (hCg : 0 < Cg)
    (hgam : ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
        ≤ Cg * Work.Spaces.Gam α θ) :
    (Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) ∧
    (Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) := by
  have hCg2 : 0 ≤ Cg ^ 2 := sq_nonneg Cg
  refine ⟨?_, ?_⟩
  · have h := (tendsto_sin_rpow_gam_sq_right hα).const_mul (Cg ^ 2)
    rw [mul_zero] at h
    refine squeeze_zero' ?_ ?_ h
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi / 4 by positivity)] with θ hθ
      exact mul_nonneg (Real.rpow_nonneg (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])).le _) (sq_nonneg _)
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi / 4 by positivity)] with θ hθ
      have hs : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
        Real.rpow_nonneg (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos])).le _
      have h1 : (Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
          ≤ (Cg * Work.Spaces.Gam α θ) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _)
          (hgam θ hθ.1 (by linarith [hθ.2, Real.pi_pos])) 2
      calc Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
          ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Cg * Work.Spaces.Gam α θ) ^ 2 := mul_le_mul_of_nonneg_left h1 hs
        _ = Cg ^ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * Work.Spaces.Gam α θ ^ 2) := by ring
  · have h := (tendsto_sin_rpow_gam_sq_left hα).const_mul (Cg ^ 2)
    rw [mul_zero] at h
    refine squeeze_zero' ?_ ?_ h
    · filter_upwards [Ioo_mem_nhdsLT (show Real.pi / 4 < Real.pi / 2 by linarith [Real.pi_pos])]
        with θ hθ
      exact mul_nonneg (Real.rpow_nonneg (Real.sin_pos_of_pos_of_lt_pi
        (by linarith [hθ.1, Real.pi_pos]) (by linarith [hθ.2, Real.pi_pos])).le _) (sq_nonneg _)
    · filter_upwards [Ioo_mem_nhdsLT (show Real.pi / 4 < Real.pi / 2 by linarith [Real.pi_pos])]
        with θ hθ
      have hs : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
        Real.rpow_nonneg (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
          (by linarith [hθ.2, Real.pi_pos])).le _
      have h1 : (Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
          ≤ (Cg * Work.Spaces.Gam α θ) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _)
          (hgam θ (by linarith [hθ.1, Real.pi_pos]) hθ.2) 2
      calc Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
          ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Cg * Work.Spaces.Gam α θ) ^ 2 := mul_le_mul_of_nonneg_left h1 hs
        _ = Cg ^ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * Work.Spaces.Gam α θ ^ 2) := by ring

/-- **The boundary traces of a separated (angular × radial) product `Γ(θ)·r(z)`** for
`α > 0`.

The mixed derivatives of the product are *globally* separable:
`D_z^bD_θ^a(Γ(θ)·r(z)) = (D_θ^a Γ)(θ)·(D_z^b r)(z)` (`mixed_mul_rad_ang`, i.e. the `z`-iterates
commute with the `θ`-only factor and the `θ`-iterates with the `z`-only factor), so

* the radial traces reduce to `z·(D_z^b r·w)² → 0` (`hr0`, `hr1`) times the fixed constant
  `(D_θ^aΓ)(θ)²`, and
* the angular traces reduce to `sin(2θ)^{1-γ}·(D_θ^aΓ)² → 0` at `θ = 0, π/2⁻`, squeezed
  through `hgam` and the explicit vanishing `sin(2θ)^{1-γ}Γ(θ)² → 0`, where
  `1-γ+2α/3 = 17α/30 > 0` at `θ=0` and `1-γ+4α/3 = 37α/30 > 0` at `θ=π/2`; this is exactly
  where `hα : 0 < α` is needed (at `α = 0` the angular trace is a nonzero constant).

The hypothesis `ContDiffOn ℝ (k+1) r (Ioi 0)` only records that `D_z^b r` is honest for
`b ≤ k` (the `D_z`-iterates stay in the same smoothness class). -/
theorem BdryTraces_Gam_mul_rad {α : ℝ} (hα : 0 < α) {k : ℕ} {r : ℝ → ℝ} {Cg : ℝ}
    (hCg : 0 < Cg)
    (hgam : ∀ a : ℕ, a ≤ k → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ| ≤ Cg * Work.Spaces.Gam α θ)
    (hrsm : ContDiffOn ℝ (k + 1) r (Set.Ioi 0))
    (hr0 : ∀ b : ℕ, b ≤ k → Filter.Tendsto
      (fun z : ℝ => z * (Work.Elliptic.DzdIter b r z * Work.Spaces.w z) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hr1 : ∀ b : ℕ, b ≤ k → Filter.Tendsto
      (fun z : ℝ => z * (Work.Elliptic.DzdIter b r z * Work.Spaces.w z) ^ 2) Filter.atTop (nhds 0)) :
    Work.FTS.Nonlin.BdryTraces α k (fun z θ => Work.Spaces.Gam α θ * r z) := by
  intro a b hab
  have ha : a ≤ k := by omega
  have hb : b ≤ k := by omega
  -- the exact separation of the mixed derivatives of the product
  have hsep : ∀ z θ : ℝ, Work.Spaces.mixed b a (fun z θ => Work.Spaces.Gam α θ * r z) z θ
      = (Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ)
        * Work.Elliptic.DzdIter b r z :=
    fun z θ => mixed_ang_mul_rad a b (fun θ => Work.Spaces.Gam α θ) r z θ
  obtain ⟨hbase0, hbaseπ⟩ := trace_aux_base hα hCg (hgam a ha)
  refine ⟨fun θ hθ => ⟨?_, ?_⟩, fun z hz => ⟨?_, ?_⟩⟩
  · -- radial trace at `z → 0⁺`: the constant `(D_θ^aΓ)(θ)²` times the trace of `D_z^b r`
    have h := (hr0 b hb).const_mul
      ((Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2)
    rw [mul_zero] at h
    refine h.congr' (Filter.Eventually.of_forall fun z => ?_)
    beta_reduce
    rw [hsep z θ]
    ring
  · -- radial trace at `z → ∞`
    have h := (hr1 b hb).const_mul
      ((Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2)
    rw [mul_zero] at h
    refine h.congr' (Filter.Eventually.of_forall fun z => ?_)
    beta_reduce
    rw [hsep z θ]
    ring
  · -- angular trace at `θ → 0⁺`: the constant `(D_z^b r)(z)²` times the angular trace of `Γ`
    have h := hbase0.const_mul ((Work.Elliptic.DzdIter b r z) ^ 2)
    rw [mul_zero] at h
    refine h.congr' (Filter.Eventually.of_forall fun θ => ?_)
    beta_reduce
    rw [hsep z θ]
    ring
  · -- angular trace at `θ → (π/2)⁻`
    have h := hbaseπ.const_mul ((Work.Elliptic.DzdIter b r z) ^ 2)
    rw [mul_zero] at h
    refine h.congr' (Filter.Eventually.of_forall fun θ => ?_)
    beta_reduce
    rw [hsep z θ]
    ring

end Work.FTS.StrongEps.EpsE4Thr.TracesAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.BdryTracesMixedTendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX.ProfRHSAux

open scoped Real Topology
open Filter

/-! ## The endpoint limits of a mixed derivative, from the boundary traces

The angular clause of `Work.FTS.Nonlin.BdryTraces α k f` says, for the slot `(a,b)` with
`a + b ≤ k`, that at both endpoints `θ = 0⁺` and `θ = (π/2)⁻` one has

  `sin(2θ)^{1-γ}·(D_z^b D_θ^a f (z,θ))² ⟶ 0`,   `γ = Work.Spaces.gam α`.

Since `γ = 1 + α/10 > 1` when `α > 0`, the weight `sin(2θ)^{1-γ}` *diverges* at the endpoints
(`sin(2θ) → 0` there), so the square of the slot has to vanish faster than `sin(2θ)^{γ-1}`:
multiplying the trace by the (bounded, in fact `≤ 1` near the endpoints) factor
`sin(2θ)^{γ-1}` exhibits the square of the slot as tending to `0`.  Taking square roots gives the
slot itself.

These two one-sided `θ`-facts are the content of this file, together with the target lemma, which
reads them off from the two angular conjuncts of `BdryTraces`. -/

/-- **A diverging weight kills the function (right endpoint).**  If `γ > 1` and
`sin (2θ) ^ (1 - γ) · X θ ^ 2 → 0` as `θ → 0⁺`, then `X θ → 0` as `θ → 0⁺`.

On the neighbourhood `(0, π/4)` of `0⁺` the two weights multiply to `1`
(`Real.rpow_add`, both bases positive), so `sin(2θ)^{γ-1}·(sin(2θ)^{1-γ}·X θ ^ 2) = X θ ^ 2`;
the left-hand side tends to `0·0 = 0` because `sin(2θ)^{γ-1} → 0` there
(`Work.FTS.H2.tendsto_sin_rpow_zero_right`).  Finally `X ↦ |X| = √(X²)` and
`tendsto_zero_iff_norm_tendsto_zero`. -/
theorem tendsto_zero_of_sin_rpow_mul_sq_right {γ : ℝ} (hγ : 1 < γ) {X : ℝ → ℝ}
    (h : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ) ^ (1 - γ) * X θ ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) :
    Filter.Tendsto X (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hpos : 0 < γ - 1 := by linarith
  have hmul : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ) ^ (γ - 1)
      * (Real.sin (2 * θ) ^ (1 - γ) * X θ ^ 2))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa using (Work.FTS.H2.tendsto_sin_rpow_zero_right (γ - 1) hpos).mul h
  -- On a right neighbourhood of `0` the two weights multiply to `1`.
  have hsplit : (fun θ : ℝ => Real.sin (2 * θ) ^ (γ - 1)
      * (Real.sin (2 * θ) ^ (1 - γ) * X θ ^ 2))
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)] (fun θ : ℝ => X θ ^ 2) := by
    filter_upwards [self_mem_nhdsWithin,
      Ioo_mem_nhdsGT (show (0 : ℝ) < π / 4 by positivity)] with θ hθ hlt
    have hs : 0 < Real.sin (2 * θ) :=
      Work.FTS.H2.sin_two_pos_of_Ioo ⟨hθ, by linarith [hlt.2, Real.pi_pos]⟩
    rw [← mul_assoc, ← Real.rpow_add hs (γ - 1) (1 - γ),
      show γ - 1 + (1 - γ) = 0 by ring, Real.rpow_zero, one_mul]
  have hsq : Filter.Tendsto (fun θ : ℝ => X θ ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := hmul.congr' hsplit
  -- The square root of the square is `|X|`.
  have hsqrt : Filter.Tendsto (fun θ : ℝ => Real.sqrt (X θ ^ 2))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  have habs : Filter.Tendsto (fun θ : ℝ => |X θ|)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa [Real.sqrt_sq_eq_abs] using hsqrt
  exact tendsto_zero_iff_norm_tendsto_zero.2 (by simpa [Real.norm_eq_abs] using habs)

/-- **A diverging weight kills the function (left endpoint).**  If `γ > 1` and
`sin (2θ) ^ (1 - γ) · X θ ^ 2 → 0` as `θ → (π/2)⁻`, then `X θ → 0` as `θ → (π/2)⁻`.

The same proof as the right-endpoint version: `sin(2θ) → 0` at `π/2` is
`Work.FTS.H2.tendsto_sin_rpow_zero_left`, and the neighbourhood `(π/4, π/2)` of `π/2` in which
`sin(2θ) > 0` (so that the `rpow` exponents may be added) is `Ioo_mem_nhdsLT`. -/
theorem tendsto_zero_of_sin_rpow_mul_sq_left {γ : ℝ} (hγ : 1 < γ) {X : ℝ → ℝ}
    (h : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ) ^ (1 - γ) * X θ ^ 2)
      (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0)) :
    Filter.Tendsto X (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0) := by
  have hpos : 0 < γ - 1 := by linarith
  have hmul : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ) ^ (γ - 1)
      * (Real.sin (2 * θ) ^ (1 - γ) * X θ ^ 2))
      (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0) := by
    simpa using (Work.FTS.H2.tendsto_sin_rpow_zero_left (γ - 1) hpos).mul h
  have hsplit : (fun θ : ℝ => Real.sin (2 * θ) ^ (γ - 1)
      * (Real.sin (2 * θ) ^ (1 - γ) * X θ ^ 2))
      =ᶠ[nhdsWithin (π / 2) (Set.Iio (π / 2))] (fun θ : ℝ => X θ ^ 2) := by
    filter_upwards [self_mem_nhdsWithin,
      Ioo_mem_nhdsLT (show π / 4 < π / 2 by linarith [Real.pi_pos])] with θ hθ hlt
    have hs : 0 < Real.sin (2 * θ) :=
      Work.FTS.H2.sin_two_pos_of_Ioo ⟨by linarith [hlt.1, Real.pi_pos], hlt.2⟩
    rw [← mul_assoc, ← Real.rpow_add hs (γ - 1) (1 - γ),
      show γ - 1 + (1 - γ) = 0 by ring, Real.rpow_zero, one_mul]
  have hsq : Filter.Tendsto (fun θ : ℝ => X θ ^ 2)
      (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0) := hmul.congr' hsplit
  have hsqrt : Filter.Tendsto (fun θ : ℝ => Real.sqrt (X θ ^ 2))
      (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0) := by
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  have habs : Filter.Tendsto (fun θ : ℝ => |X θ|)
      (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0) := by
    simpa [Real.sqrt_sq_eq_abs] using hsqrt
  exact tendsto_zero_iff_norm_tendsto_zero.2 (by simpa [Real.norm_eq_abs] using habs)

/-- **The endpoint limits of a mixed derivative, from the boundary traces.**  For `z > 0`, the
mixed derivative `D_z^b D_θ^a f` of a profile whose boundary traces vanish (`BdryTraces α k f`,
which supplies the slot `(a,b)` as soon as `a + b ≤ k`) tends to `0` as `θ → 0⁺` and as
`θ → (π/2)⁻`. -/
theorem BdryTracesMixedTendsto {α : ℝ} (hα : 0 < α) {k : ℕ} {f : Work.FTS.Galerkin.Fn}
    (htr : Work.FTS.Nonlin.BdryTraces α k f) {a b : ℕ} (hab : a + b ≤ k) {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto (fun θ : ℝ => Work.Spaces.mixed b a f z θ) (𝓝[>] 0) (𝓝 0) ∧
    Filter.Tendsto (fun θ : ℝ => Work.Spaces.mixed b a f z θ) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  have hγ : 1 < Work.Spaces.gam α := by
    simp only [Work.Spaces.gam]; linarith
  obtain ⟨h0, hπ⟩ := (htr a b hab).2 z hz
  exact ⟨tendsto_zero_of_sin_rpow_mul_sq_right hγ h0,
    tendsto_zero_of_sin_rpow_mul_sq_left hγ hπ⟩

end Work.FTS.StrongEps.EpsRLX.ProfRHSAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Slice facts for the class-`C` datum of the `L₁₂` zero-mode chapter

This file proves `Work.FTS.StrongEps.EpsZero.slice_facts_of_classC`: for a datum `f` which is
`C^∞` on the *open* quadrant (`Work.FTS.EllipticEst.SmoothOpen f`), whose weighted boundary
traces vanish (`Work.FTS.Nonlin.BdryTraces α 6 f`) and which vanishes off the open quadrant
(`hzero`), the radial slices `z ↦ f z θ` are

* differentiable on `(0,∞)` with derivative `Work.Spaces.pz f z θ` (`= ∂_z f`),
* continuous on `[0,∞)`, and
* vanishing at `z → +∞`,

**for every** `θ ∈ Work.Spaces.Iθ = [0,π/2]`, including the endpoints `θ = 0`, `π/2`.

At the endpoints the slice is identically zero by `hzero` (so all three clauses are immediate);
at an interior angle `θ ∈ (0,π/2)` the first clause is the open-quadrant smoothness `SmoothOpen`,
the third is the `z → +∞` clause of `BdryTraces` (via
`Work.FTS_RegExport.RXB.tendsto_nhdsGT_zero_of_radial_trace` and the `atTop` analogue proved
below), and the second combines the same two facts with `f 0 θ = 0` (again `hzero`) and the
elementary observation that a function with a limit along `𝓝[>] 0` attaining that limit at `0`
is continuous within `[0,∞)` at `0`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsZero

set_option autoImplicit false

/-! ## Two elementary limit bridges -/

/-- A function with a limit along the *punctured* right neighbourhood `𝓝[>] a`, whose value at `a`
is that limit, has the same limit along the closed right neighbourhood `𝓝[≥] a`.  (The
`𝓝[>]`-filter is finer than `𝓝[≥]`, so the implication needs the explicit value at `a`; we go
through the bases `Ioo a u` resp. `Ico a u`.) -/
theorem tendsto_Ici_of_tendsto_Ioi {F : ℝ → ℝ} {a b : ℝ}
    (h : Filter.Tendsto F (𝓝[>] a) (𝓝 b)) (hb : F a = b) :
    Filter.Tendsto F (𝓝[≥] a) (𝓝 b) := by
  intro t ht
  obtain ⟨u, hau, hu⟩ := (nhdsGT_basis a).mem_iff.mp (h ht)
  refine (nhdsGE_basis_Ico a).mem_iff.mpr ⟨u, hau, ?_⟩
  rintro x ⟨hax, hxu⟩
  rcases eq_or_lt_of_le hax with rfl | hlt
  · simp only [Set.mem_preimage]
    rw [hb]
    exact mem_of_mem_nhds ht
  · exact hu ⟨hlt, hxu⟩

/-- A function which is continuous on the *open* right half-line, vanishes at `0` and tends to `0`
at `0⁺` is continuous on the closed half-line `[0,∞)`. -/
theorem continuousOn_Ici_of_continuousOn_Ioi_of_tendsto {u : ℝ → ℝ}
    (h : ContinuousOn u (Set.Ioi (0 : ℝ)))
    (hu0 : u 0 = 0)
    (h0 : Filter.Tendsto u (𝓝[≥] (0 : ℝ)) (𝓝 0)) :
    ContinuousOn u (Set.Ici (0 : ℝ)) := by
  intro x hx
  have hx' : (0 : ℝ) ≤ x := hx
  rcases eq_or_lt_of_le hx' with hx0 | hx0
  · rw [← hx0]
    change Filter.Tendsto u (𝓝[≥] (0 : ℝ)) (𝓝 (u 0))
    rw [hu0]
    exact h0
  · exact ((h.continuousWithinAt hx0).continuousAt
      (isOpen_Ioi.mem_nhds hx0)).continuousWithinAt

/-- The `z → +∞` member of the `BdryTraces` pair: if `z·(u z·w z)² → 0` at `+∞` then `u → 0`.
This uses `w z ≥ 1` for `z ≥ 1`, so that `(u z)² ≤ z·(u z·w z)²` there. -/
theorem tendsto_atTop_zero_of_radial_trace {u : ℝ → ℝ}
    (h : Filter.Tendsto (fun z => z * (u z * Work.Spaces.w z) ^ 2) Filter.atTop (𝓝 0)) :
    Filter.Tendsto u Filter.atTop (𝓝 0) := by
  have hw1 : ∀ z : ℝ, 1 ≤ z → (1 : ℝ) ≤ Work.Spaces.w z := by
    intro z hz
    rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
    nlinarith
  have hsq : Filter.Tendsto (fun z : ℝ => (u z) ^ 2) Filter.atTop (𝓝 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun z => sq_nonneg _) ?_ h
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with z hz
    have hw := hw1 z hz
    have hw2 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := by nlinarith
    have huz : (0 : ℝ) ≤ (u z) ^ 2 := sq_nonneg _
    have hA : (0 : ℝ) ≤ (u z) ^ 2 * (Work.Spaces.w z) ^ 2 := mul_nonneg huz (sq_nonneg _)
    have h1 : (u z) ^ 2 ≤ (u z) ^ 2 * (Work.Spaces.w z) ^ 2 := by nlinarith
    have h2 : (u z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ z * ((u z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      simpa using mul_le_mul_of_nonneg_right hz hA
    have h3 : z * ((u z) ^ 2 * (Work.Spaces.w z) ^ 2) = z * (u z * Work.Spaces.w z) ^ 2 := by
      ring
    linarith [h1, h2, h3.le]
  have habs : Filter.Tendsto (fun z => |u z|) Filter.atTop (𝓝 0) := by
    have hcomp : Filter.Tendsto (fun z => Real.sqrt ((u z) ^ 2)) Filter.atTop
        (𝓝 (Real.sqrt 0)) :=
      Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    rw [Real.sqrt_zero] at hcomp
    convert hcomp using 1
    funext z
    rw [Real.sqrt_sq_eq_abs]
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using habs)

/-- An identically vanishing slice is differentiable, with derivative `0 = pz f z θ`. -/
theorem hasDerivAt_of_slice_eq_zero {f : ℝ → ℝ → ℝ} {θ z : ℝ} (h0 : ∀ s : ℝ, f s θ = 0) :
    HasDerivAt (fun s => f s θ) (Work.Spaces.pz f z θ) z := by
  have hfun : (fun s : ℝ => f s θ) = fun _ => (0 : ℝ) := funext h0
  have hpz : Work.Spaces.pz f z θ = 0 := by
    simp only [Work.Spaces.pz]
    rw [hfun]
    exact deriv_const z (0 : ℝ)
  rw [hpz, hfun]
  exact hasDerivAt_const z 0

/-! ## The target -/

theorem slice_facts_of_classC {α : ℝ} {f : Work.FTS.Galerkin.Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hb : Work.FTS.Nonlin.BdryTraces α 6 f)
    (hzero : ∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → f z θ = 0) :
    (∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (fun s => f s θ) (Work.Spaces.pz f z θ) z) ∧
      (∀ θ ∈ Work.Spaces.Iθ, ContinuousOn (fun s => f s θ) (Set.Ici 0)) ∧
      (∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun s => f s θ) Filter.atTop (nhds 0)) := by
  -- `hzero`, in the form we use it: a slice outside the open angle interval vanishes identically.
  have hz0 : ∀ θ : ℝ, θ ∉ Set.Ioo 0 (Real.pi / 2) → ∀ z : ℝ, f z θ = 0 :=
    fun θ hθ z => hzero z θ (fun hc => hθ hc.2)
  -- the value at `z = 0` of every slice
  have hf0 : ∀ θ : ℝ, f 0 θ = 0 :=
    fun θ => hzero 0 θ (fun hc => (lt_irrefl (0 : ℝ)) hc.1)
  -- the two radial clauses of `BdryTraces` at the slot `(a,b) = (0,0)`
  have hbdry0 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Filter.Tendsto (fun z => z * (f z θ * Work.Spaces.w z) ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := fun θ hθ => by
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using
      (hb 0 0 (by norm_num)).1 θ hθ |>.1
  have hbdryTop : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Filter.Tendsto (fun z => z * (f z θ * Work.Spaces.w z) ^ 2)
        Filter.atTop (𝓝 0) := fun θ hθ => by
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using
      (hb 0 0 (by norm_num)).1 θ hθ |>.2
  refine ⟨?_, ?_, ?_⟩
  · intro θ hθ z hz
    by_cases h : θ ∈ Set.Ioo 0 (Real.pi / 2)
    · exact hsm.hasDerivAt_slice h hz
    · exact hasDerivAt_of_slice_eq_zero (hz0 θ h)
  · intro θ hθ
    by_cases h : θ ∈ Set.Ioo 0 (Real.pi / 2)
    · refine continuousOn_Ici_of_continuousOn_Ioi_of_tendsto
        ((hsm.curry_z h).continuousOn) (hf0 θ) ?_
      refine tendsto_Ici_of_tendsto_Ioi (F := fun s : ℝ => f s θ) (a := 0) (b := 0) ?_ (hf0 θ)
      exact Work.FTS_RegExport.RXB.tendsto_nhdsGT_zero_of_radial_trace (hbdry0 θ h)
    · have hfun : (fun s : ℝ => f s θ) = fun _ => (0 : ℝ) := funext (hz0 θ h)
      rw [hfun]
      exact continuousOn_const
  · intro θ hθ
    by_cases h : θ ∈ Set.Ioo 0 (Real.pi / 2)
    · exact tendsto_atTop_zero_of_radial_trace (hbdryTop θ h)
    · have hfun : (fun s : ℝ => f s θ) = fun _ => (0 : ℝ) := funext (hz0 θ h)
      rw [hfun]
      exact tendsto_const_nhds

end Work.FTS.StrongEps.EpsZero
end
end
