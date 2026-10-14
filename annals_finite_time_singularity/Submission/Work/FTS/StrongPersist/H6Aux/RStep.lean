import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.PhiStar.Honesty.Slots.Series
import Submission.Work.FTS.PhiStar.Honesty.Slots.SeriesDeriv
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.H6Aux.E2Facts
import Submission.Work.FTS.StrongPersist.H6Aux.RadialAsm
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkDzdIterSharp
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSlotInt
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.fstarDat
import Submission.Work.FTS.StrongPersist.L3Rhs.CoupledVf
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNstarBlock
import Submission.Work.FTS.StrongPersist.L3Rhs.N3ssPriced
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsJetMajMass
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsRadAux.aestronglyMeasurable_slotSum
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.ExcPairBranches
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBound
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundCore
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundE
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.StrongPersist.SP6.EUz6
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.ClassCHon.perMode_data_of_source =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon

/-- **The two per-mode facts of the level-`0` modal estimate for a general source**: the
weighted `L²`-integrability of each mode coefficient `acoeff α m F`, and the per-mode energy
inequality with the paper's constant `muSeq α m`:

  `muSeq α m · √(∫_z (a_m z)² w z²) ≤ √(∫_z (√(eNorm m) · cmode m F z)² w z²)`.

For `m ≥ 1` this is `Work.FTS.PhiStar.Honesty.acoeff_perModeEnergy` (the sharp per-mode bound
`Work.FTS.PhiStar.Honesty.radGreen_modeEnergy_of_o` at the clamped `cmode m F`, whose analytic
hypotheses come from `cmode_modeEnergy_integrable` and `cmode_isLittleO_at_zero`, with
`muSeq α m = lamR m − 3α² − 3α(5+α)/2`), and `hint_a` from
`Work.FTS.PhiStar.Honesty.integrableOn_acoeff_sq_w_sq_meas`; for `m = 0` the vanishing moment
`hmom` gives `cmode 0 F = 0` on `(0,∞)` and hence `acoeff α 0 F = 0` a.e.
(`Work.FTS.PhiStar.Series.acoeff_zero_of_fstar`), so both claims are trivial there.

These are exactly the `hint_a` and `hper` inputs of
`Work.FTS.ClassC.lintegral_psiTrunc_le` (and hence of the level-`0` honesty of
`psiSeries α F`); the compactly supported sibling of this pair of conjuncts is
`Work.FTS.ClassCHon.CmpSupp.coeff_facts`.  Use `Work.FTS.ClassCHon.CmpSupp.eNorm_bounds` for
`1 ≤ eNorm m`. -/
theorem perMode_data_of_source {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hF0 : Work.Spaces.HkMem α 0 F) (hF1 : Work.Spaces.HkMem α 1 F)
    (hmom : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0) :
    (∀ m : ℕ, MeasureTheory.IntegrableOn (fun z : ℝ =>
        (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz)
    ∧ (∀ m : ℕ, Work.FTS.ClassC.muSeq α m *
        Real.sqrt (∫ z in Work.Spaces.Iz,
          (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ Real.sqrt (∫ z in Work.Spaces.Iz,
          (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
            * Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (Work.Spaces.w z) ^ 2)) := by
  classical
  have hIz : MeasurableSet Work.Spaces.Iz := by
    rw [Work.Spaces.Iz]; exact measurableSet_Ici
  -- the vanishing moment kills the mode-`0` coefficient on the open half-line
  have hzero : ∀ z : ℝ, 0 < z → Work.FTS.PhiStar.Series.acoeff α 0 F z = 0 :=
    fun z hz => Work.FTS.PhiStar.Series.acoeff_zero_of_fstar α F
      (fun t ht => hmom t ht) z hz
  refine ⟨?_, ?_⟩
  · -- conjunct 1: weighted `L²`-integrability of each mode coefficient
    intro m
    rcases Nat.eq_zero_or_pos m with hm0 | hpos
    · subst hm0
      refine (MeasureTheory.integrableOn_zero).congr_fun ?_ hIz
      intro z hz
      change (0 : ℝ) = (Work.FTS.PhiStar.Series.acoeff α 0 F z) ^ 2 * (Work.Spaces.w z) ^ 2
      rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hz0
      · rw [← hz0]
        simp [Work.Spaces.w]
      · rw [hzero z hz0]
        ring
    · exact Work.FTS.PhiStar.Honesty.integrableOn_acoeff_sq_w_sq_meas (α := α) (m := m) (F := F)
        hα hα4 hpos hsm hF0
        (Work.FTS.PhiStar.Honesty.aemeasurable_cmode_clamp (α := α) m hsm)
  · -- conjunct 2: the per-mode weighted energy inequality with `muSeq α m`
    intro m
    rcases Nat.eq_zero_or_pos m with hm0 | hpos
    · subst hm0
      have hInt0 : (∫ z in Work.Spaces.Iz,
          (Work.FTS.PhiStar.Series.acoeff α 0 F z) ^ 2 * (Work.Spaces.w z) ^ 2) = 0 := by
        have h1 : (∫ z in Set.Ioi (0 : ℝ),
            (Work.FTS.PhiStar.Series.acoeff α 0 F z) ^ 2 * (Work.Spaces.w z) ^ 2) = 0 := by
          rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_),
            MeasureTheory.integral_zero]
          rw [hzero z hz]
          ring
        exact (MeasureTheory.setIntegral_congr_set (f := fun z : ℝ =>
            (Work.FTS.PhiStar.Series.acoeff α 0 F z) ^ 2 * (Work.Spaces.w z) ^ 2)
          (MeasureTheory.Ioi_ae_eq_Ici (a := 0)).symm).trans h1
      rw [hInt0, Work.FTS.ClassC.muSeq, if_pos rfl, Real.sqrt_zero, mul_zero]
      exact Real.sqrt_nonneg _
    · have hm : 1 ≤ m := hpos
      have hmu : Work.FTS.ClassC.muSeq α m
          = Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2 := by
        rw [Work.FTS.ClassC.muSeq, if_neg (ne_of_gt hpos)]
      rw [hmu]
      exact Work.FTS.PhiStar.Honesty.acoeff_perModeEnergy (α := α) (F := F) m hα hα4 hm hsm
        hF0 (Work.FTS.ClassCHon.CmpSupp.eNorm_bounds m).1
        (Work.FTS.PhiStar.Honesty.cmode_isLittleO_at_zero m hsm hF1)

end Work.FTS.ClassCHon
end
-- ===== merged: Submission.Work.FTS.GalFields.Norm.radA_contDiffOn_five_of_smoothOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.Norm

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The nonlocal tail integral at order `5` -/

/-- **`L₁₂ f ∈ C⁵((0,∞))`** for a datum smooth on the open quadrant and honest in `ℋ⁵`:
`contDiffOn_L12_k` at `k = 5`, transported from `Work.Elliptic.L12` to the
`Work.Coercivity.L12f = Work.Construction.L12` form used by `radA`. -/
theorem L12f_contDiffOn_five_of_smoothOpen {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α 5 f) :
    ContDiffOn ℝ 5 (Work.Coercivity.L12f f) (Set.Ioi (0 : ℝ)) := by
  have hEll : ContDiffOn ℝ 5 (Work.Elliptic.L12 f) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 5 f hα hα1 hsm hmem (by norm_num)
  have hCon : ContDiffOn ℝ 5 (fun z => Work.Construction.L12 f z) (Set.Ioi (0 : ℝ)) := by
    rw [Work.FTS.H2.constructionL12_eq_ellipticL12 f]
    exact hEll
  have hfun : Work.Coercivity.L12f f = Work.Construction.L12 f := rfl
  rw [hfun]
  exact hCon

/-! ## The radial profile `radA` -/

/-- **`radA α f ∈ C⁵((0,∞))`**: the two rational `z`-factors `a`, `b` are `C⁶` (hence `C⁵`)
there, and the only analytic input is `L₁₂ f ∈ C⁵((0,∞))` of the previous lemma. -/
theorem radA_contDiffOn_five_of_smoothOpen {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 5 f) :
    ContDiffOn ℝ 5 (Work.FTS.CoercivityFix.Transfer.radA α f) (Set.Ioi (0 : ℝ)) := by
  have h12 : ContDiffOn ℝ 5 (Work.Coercivity.L12f f) (Set.Ioi (0 : ℝ)) :=
    L12f_contDiffOn_five_of_smoothOpen hα hα1 hsm hmem
  have hfun : Work.FTS.CoercivityFix.Transfer.radA α f
      = fun z => -(Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z)
          + ((Work.FTS.CoercivityFix.Transfer.ampB α z / Work.Spaces.c α)
              * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) := by
    funext z
    rw [Work.FTS.CoercivityFix.Transfer.radA_eq]
    simp only [Work.FTS.CoercivityFix.Transfer.ampA, Work.FTS.CoercivityFix.Transfer.ampB]
    ring
  rw [hfun]
  exact ((((Work.FTS.StrongPersist.H6Aux.contDiffOn_six_ampA hα hα1).of_le
      (by norm_num)).mul h12).neg).add
    (((Work.FTS.StrongPersist.H6Aux.contDiffOn_six_ampB_div α).of_le
      (by norm_num)).mul contDiffOn_const)

end Work.FTS.GalFields.Norm
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.slots_psiSeries_of_cptQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

/-- At level `0` the honest integrand is the weighted square. -/
theorem HkIntegrand_zero_eq_weighted (α : ℝ) (f : ℝ → ℝ → ℝ) :
    ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ →
      Work.Spaces.HkIntegrand α 0 f z θ
        = (f z θ * Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  intro z θ hθ
  have h1 : Work.Spaces.HkIntegrand α 0 f z θ = (f z θ) ^ 2
      * (Work.Spaces.w z ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    rw [Work.FTS.ClassCHon.CmpSupp.sf_HkIntegrand_zero_eq, mul_pow,
      Work.FTS.ClassCHon.CmpSupp.sf_Whz_sq_Iθ hθ]
  have h2 : (f z θ * Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      = (f z θ) ^ 2 * (Work.Spaces.w z ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    rw [mul_pow, mul_assoc]
    simp only [Work.FTS.EllipticEst.sEta]
  rw [h1, h2]

/-- The level-`0` integrand vanishes at `z = 0` and at `θ = 0`, `θ = π/2`. -/
theorem HkIntegrand_zero_eq_zero_of (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (h : z = 0 ∨ θ = 0 ∨ θ = Real.pi / 2) :
    Work.Spaces.HkIntegrand α 0 f z θ = 0 := by
  rw [Work.FTS.ClassCHon.CmpSupp.sf_HkIntegrand_zero_eq]
  have hη : Work.Spaces.eta / 2 ≠ 0 := by norm_num [Work.Spaces.eta]
  rcases h with h | h | h
  · subst h
    simp [Work.Spaces.w]
  · subst h
    rw [show Real.sin (2 * (0 : ℝ)) = 0 by norm_num, Real.zero_rpow hη]
    ring
  · subst h
    rw [show Real.sin (2 * (Real.pi / 2)) = 0 by
      rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi], Real.zero_rpow hη]
    ring

/-- **`H^0`-membership transports across an equality on the open quadrant.** -/
theorem HkMem_zero_of_eq {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π/2) → f z θ = g z θ)
    (hf : Work.Spaces.HkMem α 0 f) : Work.Spaces.HkMem α 0 g := by
  have hkey : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      Work.Spaces.HkIntegrand α 0 f z θ = Work.Spaces.HkIntegrand α 0 g z θ := by
    intro z θ hz hθ
    by_cases hio : θ ∈ Set.Ioo 0 (π/2)
    · rw [HkIntegrand_zero_eq_weighted α f z θ hθ,
        HkIntegrand_zero_eq_weighted α g z θ hθ, h z θ hz hio]
    · have hθ' : θ = 0 ∨ θ = Real.pi / 2 := by
        rcases eq_or_lt_of_le hθ.1 with h0 | h0
        · exact Or.inl h0.symm
        · exact Or.inr (le_antisymm hθ.2 (le_of_not_gt fun hlt => hio ⟨h0, hlt⟩))
      rw [HkIntegrand_zero_eq_zero_of α f (Or.inr hθ'),
        HkIntegrand_zero_eq_zero_of α g (Or.inr hθ')]
  constructor
  · intro z hz
    rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with hz0 | hz0
    · subst hz0
      have hzero : (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 g 0 θ) = fun _ => (0:ℝ) := by
        funext θ
        exact HkIntegrand_zero_eq_zero_of α g (Or.inl rfl)
      rw [hzero]
      exact MeasureTheory.integrableOn_zero
    · refine (hf.1 z hz).congr_fun ?_ measurableSet_Icc
      intro θ hθ
      exact hkey z θ hz0 hθ
  · refine hf.2.congr_fun ?_ measurableSet_Ici
    intro z hz
    rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with hz0 | hz0
    · subst hz0
      change (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f 0 θ)
        = ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g 0 θ
      have h0 : (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 f 0 θ)
          = fun θ : ℝ => Work.Spaces.HkIntegrand α 0 g 0 θ := by
        funext θ
        rw [HkIntegrand_zero_eq_zero_of α f (Or.inl rfl),
          HkIntegrand_zero_eq_zero_of α g (Or.inl rfl)]
      rw [h0]
    · refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => hkey z θ hz0 hθ)] with θ hθ
      exact hθ

theorem slots_psiSeries_of_cptQ (K : ℕ) {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {G : ℝ → ℝ → ℝ} (hG : Work.FTS.PhiStar.Honesty.SmoothCptQ G)
    (hFs : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar G z = 0) :
    (∀ l m : ℕ, l ≤ K + 2 → m ≤ 2 → Work.Spaces.HkMem α 0
      (Work.Spaces.DzIter l (Work.Spaces.pthIter m (Work.FTS.PhiStar.Series.psiSeries α G)))) ∧
    (∀ t l : ℕ, 3 ≤ t → t ≤ K + 2 → l ≤ K + 2 →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ =>
          (Work.Spaces.DzIter l (Work.Spaces.pthIter t
              (Work.FTS.PhiStar.Series.psiSeries α G)) z θ * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α)) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter l (Work.Spaces.pthIter t
              (Work.FTS.PhiStar.Series.psiSeries α G)) z θ * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α)) Work.Spaces.Iz) := by
  obtain ⟨a, b, c, d, ha, hab', hc, hcd, hd, hsupp_box⟩ := hG.cpt
  have hab : a ≤ b := le_of_lt hab'
  have hsupp : ∀ z θ : ℝ, z ∉ Set.Icc a b → G z θ = 0 := by
    intro z θ hz
    by_contra h
    exact hz (hsupp_box z θ h).1
  have hφint := integrableOn_phiWt_mul_w_sq hα hα4
  have hneg : -1 < -(Work.Spaces.eta) := by
    rw [Work.Spaces.eta]; norm_num
  have hetapos : (0:ℝ) < Work.Spaces.eta := by norm_num [Work.Spaces.eta]
  constructor
  · intro l m _ _
    obtain ⟨K', hK'pos, hK'bd⟩ := dzS_abs_le hα hα4 hG ha hab hsupp hFs l m
    have hcont := dzS_continuousOn hα hα4 hG ha hab hsupp hFs l m
    obtain ⟨h1, h2⟩ := integrableOn_sq_mul_sin_rpow_of_bound (F := dzS α G l m)
      (φ := phiWt α) (K := K') (e := -(Work.Spaces.eta)) hcont hK'pos.le
      (fun z hz => phiWt_nonneg hz) (fun z hz θ hθ => hK'bd z θ hz hθ) hφint hneg
    have hmemS : Work.Spaces.HkMem α 0 (dzS α G l m) := by
      constructor
      · intro z hz
        rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with hz0 | hz0
        · subst hz0
          have hzero : (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 (dzS α G l m) 0 θ)
              = fun _ => (0:ℝ) := by
            funext θ
            exact HkIntegrand_zero_eq_zero_of α (dzS α G l m) (Or.inl rfl)
          rw [hzero]
          exact MeasureTheory.integrableOn_zero
        · refine (h1 z hz).congr_fun ?_ measurableSet_Icc
          intro θ hθ
          exact (HkIntegrand_zero_eq_weighted α (dzS α G l m) z θ hθ).symm
      · refine h2.congr_fun ?_ measurableSet_Ici
        intro z hz
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => (HkIntegrand_zero_eq_weighted α (dzS α G l m) z θ hθ).symm)]
          with θ hθ
        exact hθ
    exact HkMem_zero_of_eq
      (fun z θ hz hθ => (DzIter_psiSeries_eq_dzS hα hα4 hG ha hab hsupp hFs m l z θ hz hθ).symm)
      hmemS
  · intro t l ht _ _
    obtain ⟨K', hK'pos, hK'bd⟩ := dzS_abs_le hα hα4 hG ha hab hsupp hFs l t
    have hcont := dzS_continuousOn hα hα4 hG ha hab hsupp hFs l t
    have hexp : -1 < 2 * (t : ℝ) - 4 - Work.Spaces.gam α := by
      rw [Work.Spaces.gam]
      have : (3:ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
      linarith
    have hne : (2 * (t : ℝ) - 4 - Work.Spaces.gam α) ≠ 0 := by
      have ht' : (3:ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
      have hgam : Work.Spaces.gam α ≤ 3 / 2 := by
        rw [Work.Spaces.gam]
        linarith [hα4]
      exact ne_of_gt (by linarith)
    obtain ⟨h1, h2⟩ := integrableOn_sq_mul_sin_rpow_of_bound (F := dzS α G l t)
      (φ := phiWt α) (K := K') (e := 2 * (t : ℝ) - 4 - Work.Spaces.gam α) hcont hK'pos.le
      (fun z hz => phiWt_nonneg hz) (fun z hz θ hθ => hK'bd z θ hz hθ) hφint hexp
    have hpt : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π/2) →
        Work.Spaces.DzIter l (Work.Spaces.pthIter t (Work.FTS.PhiStar.Series.psiSeries α G))
            z θ = dzS α G l t z θ :=
      fun z θ hz hθ => DzIter_psiSeries_eq_dzS hα hα4 hG ha hab hsupp hFs t l z θ hz hθ
    have hzeroexp : ∀ θ : ℝ, θ = 0 ∨ θ = Real.pi / 2 →
        (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α) = 0 := by
      intro θ hθ
      rcases hθ with h | h
      · subst h
        rw [show Real.sin (2 * (0:ℝ)) = 0 by norm_num, Real.zero_rpow hne]
      · subst h
        rw [show Real.sin (2 * (Real.pi / 2)) = 0 by
          rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi], Real.zero_rpow hne]
    have hkey : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
        (Work.Spaces.DzIter l (Work.Spaces.pthIter t (Work.FTS.PhiStar.Series.psiSeries α G))
            z θ * Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α)
        = (dzS α G l t z θ * Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α) := by
      intro z θ hz hθ
      by_cases hio : θ ∈ Set.Ioo 0 (π/2)
      · rw [hpt z θ hz hio]
      · have hθ' : θ = 0 ∨ θ = Real.pi / 2 := by
          rcases eq_or_lt_of_le hθ.1 with h0 | h0
          · exact Or.inl h0.symm
          · exact Or.inr (le_antisymm hθ.2 (le_of_not_gt fun hlt => hio ⟨h0, hlt⟩))
        rw [hzeroexp θ hθ']
        ring
    constructor
    · intro z hz
      rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with hz0 | hz0
      · subst hz0
        have hz0' : (fun θ : ℝ => (Work.Spaces.DzIter l
              (Work.Spaces.pthIter t (Work.FTS.PhiStar.Series.psiSeries α G)) 0 θ
                * Work.Spaces.w 0) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α))
            = fun _ => (0:ℝ) := by
          funext θ
          simp [Work.Spaces.w]
        rw [hz0']
        exact MeasureTheory.integrableOn_zero
      · refine (h1 z hz).congr_fun ?_ measurableSet_Icc
        intro θ hθ
        exact (hkey z θ hz0 hθ).symm
    · refine h2.congr_fun ?_ measurableSet_Ici
      intro z hz
      rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with hz0 | hz0
      · subst hz0
        change (∫ θ in Work.Spaces.Iθ, (dzS α G l t 0 θ * Work.Spaces.w 0) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α))
          = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter l
              (Work.Spaces.pthIter t (Work.FTS.PhiStar.Series.psiSeries α G)) 0 θ
                * Work.Spaces.w 0) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α)
        have h0 : (fun θ : ℝ => (dzS α G l t 0 θ * Work.Spaces.w 0) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α))
            = fun θ : ℝ => (Work.Spaces.DzIter l
              (Work.Spaces.pthIter t (Work.FTS.PhiStar.Series.psiSeries α G)) 0 θ
                * Work.Spaces.w 0) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α) := by
          funext θ
          simp [Work.Spaces.w]
        rw [h0]
      · refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => (hkey z θ hz0 hθ).symm)] with θ hθ
        exact hθ

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.B4P2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux

open Work.FTS.StrongPersist.H6Pair6Aux (NA1 NA4 NA5 NA6 NP3 NP4a NP4b NP5a NP5b NP6)

set_option autoImplicit false
set_option maxHeartbeats 3200000

theorem NP4a_HkSq4_le (C₀ : ℝ) : ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ w : Work.FTS.Galerkin.Fn,
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    Work.Spaces.HkSq α 4 (NP4a α w) ≤ K * (1 + Work.Spaces.HkSq α 5 w) := by
  obtain ⟨Ka, hKapos, hA⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.angBlk4_VfsA_mass
  obtain ⟨Cr, hCrpos, hrad⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.radBlk5
  obtain ⟨Kr, hKrpos, hKrF, _hKrH⟩ := Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.nzradZop_bound6
  have hK0nn : (0 : ℝ) ≤ Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg hKapos.le hCrpos.le) (sq_nonneg _)) (sq_nonneg _)
  refine ⟨Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 + 1, by linarith, ?_⟩
  intro α hαIoc w hw hXw
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hsmw : Work.FTS.EllipticEst.SmoothOpen w := hw.reg
  have hm4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 4 (by norm_num) hw.mem
  obtain ⟨hAngInt, hAngMass, _hAngInt2, _hAngMass2⟩ := hA α hαIoc
  -- the multiplier `VfsRad = F_*` and its jets
  have hVF5 : ContDiffOn ℝ 5 Work.FTS.StrongPersist.L3Rhs.VfsRad (Set.Ioi 0) :=
    (Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.nzsmoothOn_FMFstar).of_le (by norm_num)
  have hVFjet : ∀ b ≤ 4, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Spaces.Zop^[b] Work.FTS.StrongPersist.L3Rhs.VfsRad z| ≤ Kr :=
    fun b hb z hz => hKrF b (by omega) z hz
  have hradB := hrad α hαIoc Work.FTS.StrongPersist.L3Rhs.VfsRad w Kr hKrpos.le
    hVF5 hVFjet hsmw hm4 hw.l12
  -- the congruence to the separated form and the separation bound
  have hcongr : Work.Spaces.HkSq α 4 (NP4a α w)
      = Work.Spaces.HkSq α 4 (fun z θ => Work.FTS.StrongPersist.L3Rhs.VfsA1 α θ
          * (Work.FTS.StrongPersist.L3Rhs.VfsRad z * Work.Construction.L12 w z)) :=
    Work.FTS.EllipticEst.HkSq_congr_open α 4 (NP4a_eq_sep4 hα w)
  have hsep := Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.sep_HkSq4_le
    (α := α) (C := Work.FTS.StrongPersist.L3Rhs.VfsA1 α)
    (B := fun z => Work.FTS.StrongPersist.L3Rhs.VfsRad z * Work.Construction.L12 w z)
    hAngInt hradB.1
  -- the arithmetic
  have hw5 : Work.Spaces.HkSq α 4 w ≤ C₀ ^ 2 * α ^ 4 := by
    rw [sq_xn w]
    calc (Work.FTS.Nonlin.Xn α w) ^ 2 ≤ (C₀ * α ^ 2) ^ 2 :=
          pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 w) hXw 2
      _ = C₀ ^ 2 * α ^ 4 := by ring
  have hIntnn : (0 : ℝ) ≤ ∫ z in Work.Spaces.Iz,
      SlotSum4 (fun z => Work.FTS.StrongPersist.L3Rhs.VfsRad z * Work.Construction.L12 w z) z :=
    integral_nonneg fun z => SlotSum4_nonneg _ z
  have h1 : (α * (∫ θ in Work.Spaces.Iθ,
        AngBlk4 α (Work.FTS.StrongPersist.L3Rhs.VfsA1 α) θ))
      * (∫ z in Work.Spaces.Iz,
          SlotSum4 (fun z => Work.FTS.StrongPersist.L3Rhs.VfsRad z
            * Work.Construction.L12 w z) z)
      ≤ Ka * (Cr * (1 + Kr) ^ 2 * Work.Spaces.HkSq α 4 w) :=
    mul_le_mul hAngMass hradB.2 hIntnn hKapos.le
  have hprod : (∫ θ in Work.Spaces.Iθ,
        AngBlk4 α (Work.FTS.StrongPersist.L3Rhs.VfsA1 α) θ)
      * (∫ z in Work.Spaces.Iz,
          SlotSum4 (fun z => Work.FTS.StrongPersist.L3Rhs.VfsRad z
            * Work.Construction.L12 w z) z)
      ≤ Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 * α ^ 3 := by
    refine le_of_mul_le_mul_left ?_ hα
    calc α * ((∫ θ in Work.Spaces.Iθ,
            AngBlk4 α (Work.FTS.StrongPersist.L3Rhs.VfsA1 α) θ)
          * (∫ z in Work.Spaces.Iz,
              SlotSum4 (fun z => Work.FTS.StrongPersist.L3Rhs.VfsRad z
                * Work.Construction.L12 w z) z))
        = (α * (∫ θ in Work.Spaces.Iθ,
              AngBlk4 α (Work.FTS.StrongPersist.L3Rhs.VfsA1 α) θ))
            * (∫ z in Work.Spaces.Iz,
                SlotSum4 (fun z => Work.FTS.StrongPersist.L3Rhs.VfsRad z
                  * Work.Construction.L12 w z) z) := by ring
      _ ≤ Ka * (Cr * (1 + Kr) ^ 2 * Work.Spaces.HkSq α 4 w) := h1
      _ = Ka * Cr * (1 + Kr) ^ 2 * Work.Spaces.HkSq α 4 w := by ring
      _ ≤ Ka * Cr * (1 + Kr) ^ 2 * (C₀ ^ 2 * α ^ 4) :=
          mul_le_mul_of_nonneg_left hw5
            (mul_nonneg (mul_nonneg hKapos.le hCrpos.le) (sq_nonneg _))
      _ = α * (Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 * α ^ 3) := by ring
  have hα3 : α ^ 3 ≤ 1 := pow_le_one₀ hα.le hα1
  have hHnn : (0 : ℝ) ≤ 1 + Work.Spaces.HkSq α 5 w := by
    have h := Work.Spaces.HkSq_nonneg α 5 w
    linarith
  have hone : (1 : ℝ) ≤ 1 + Work.Spaces.HkSq α 5 w := by
    have h := Work.Spaces.HkSq_nonneg α 5 w
    linarith
  calc Work.Spaces.HkSq α 4 (NP4a α w)
      = Work.Spaces.HkSq α 4 (fun z θ => Work.FTS.StrongPersist.L3Rhs.VfsA1 α θ
          * (Work.FTS.StrongPersist.L3Rhs.VfsRad z * Work.Construction.L12 w z)) := hcongr
    _ ≤ (∫ θ in Work.Spaces.Iθ, AngBlk4 α (Work.FTS.StrongPersist.L3Rhs.VfsA1 α) θ)
          * (∫ z in Work.Spaces.Iz,
              SlotSum4 (fun z => Work.FTS.StrongPersist.L3Rhs.VfsRad z
                * Work.Construction.L12 w z) z) := hsep
    _ ≤ Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 * α ^ 3 := hprod
    _ ≤ Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hα3 hK0nn
    _ ≤ (Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 + 1) * (1 + Work.Spaces.HkSq α 5 w) := by
        calc Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 * 1
            = Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 := by ring
          _ ≤ (Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2) * (1 + Work.Spaces.HkSq α 5 w) :=
              le_mul_of_one_le_right hK0nn hone
          _ ≤ (Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 + 1) * (1 + Work.Spaces.HkSq α 5 w) :=
              mul_le_mul_of_nonneg_right (by linarith) hHnn

theorem NP5a_HkSq4_le (C₀ : ℝ) : ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ w : Work.FTS.Galerkin.Fn,
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    Work.Spaces.HkSq α 4 (NP5a α w) ≤ K * (1 + Work.Spaces.HkSq α 5 w) := by
  obtain ⟨Ka, hKapos, hA⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.angBlk4_VfsA_mass
  obtain ⟨Cr, hCrpos, hrad⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.radBlk5
  obtain ⟨Kr, hKrpos, _hKrF, hKrH⟩ := Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.nzradZop_bound6
  have hK0nn : (0 : ℝ) ≤ Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg hKapos.le hCrpos.le) (sq_nonneg _)) (sq_nonneg _)
  refine ⟨Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 + 1, by linarith, ?_⟩
  intro α hαIoc w hw hXw
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hsmw : Work.FTS.EllipticEst.SmoothOpen w := hw.reg
  have hm4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 4 (by norm_num) hw.mem
  obtain ⟨_hAngInt, _hAngMass, hAngInt2, hAngMass2⟩ := hA α hαIoc
  -- the multiplier `Hz` and its jets
  have hHz5 : ContDiffOn ℝ 5 Work.FTS.Nonlinear.FstarPkg.Hz (Set.Ioi 0) :=
    (Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.nzsmoothOn_Hz).of_le (by norm_num)
  have hHzjet : ∀ b ≤ 4, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Spaces.Zop^[b] Work.FTS.Nonlinear.FstarPkg.Hz z| ≤ Kr :=
    fun b hb z hz => hKrH b (by omega) z hz
  have hradB := hrad α hαIoc Work.FTS.Nonlinear.FstarPkg.Hz w Kr hKrpos.le
    hHz5 hHzjet hsmw hm4 hw.l12
  have hcongr : Work.Spaces.HkSq α 4 (NP5a α w)
      = Work.Spaces.HkSq α 4 (fun z θ => Work.FTS.StrongPersist.L3Rhs.VfsA2 α θ
          * (Work.FTS.Nonlinear.FstarPkg.Hz z * Work.Construction.L12 w z)) :=
    Work.FTS.EllipticEst.HkSq_congr_open α 4 (NP5a_eq_sep4 w)
  have hsep := Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.sep_HkSq4_le
    (α := α) (C := Work.FTS.StrongPersist.L3Rhs.VfsA2 α)
    (B := fun z => Work.FTS.Nonlinear.FstarPkg.Hz z * Work.Construction.L12 w z)
    hAngInt2 hradB.1
  have hw5 : Work.Spaces.HkSq α 4 w ≤ C₀ ^ 2 * α ^ 4 := by
    rw [sq_xn w]
    calc (Work.FTS.Nonlin.Xn α w) ^ 2 ≤ (C₀ * α ^ 2) ^ 2 :=
          pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 w) hXw 2
      _ = C₀ ^ 2 * α ^ 4 := by ring
  have hIntnn : (0 : ℝ) ≤ ∫ z in Work.Spaces.Iz,
      SlotSum4 (fun z => Work.FTS.Nonlinear.FstarPkg.Hz z * Work.Construction.L12 w z) z :=
    integral_nonneg fun z => SlotSum4_nonneg _ z
  have h1 : (α * (∫ θ in Work.Spaces.Iθ,
        AngBlk4 α (Work.FTS.StrongPersist.L3Rhs.VfsA2 α) θ))
      * (∫ z in Work.Spaces.Iz,
          SlotSum4 (fun z => Work.FTS.Nonlinear.FstarPkg.Hz z
            * Work.Construction.L12 w z) z)
      ≤ Ka * (Cr * (1 + Kr) ^ 2 * Work.Spaces.HkSq α 4 w) :=
    mul_le_mul hAngMass2 hradB.2 hIntnn hKapos.le
  have hprod : (∫ θ in Work.Spaces.Iθ,
        AngBlk4 α (Work.FTS.StrongPersist.L3Rhs.VfsA2 α) θ)
      * (∫ z in Work.Spaces.Iz,
          SlotSum4 (fun z => Work.FTS.Nonlinear.FstarPkg.Hz z
            * Work.Construction.L12 w z) z)
      ≤ Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 * α ^ 3 := by
    refine le_of_mul_le_mul_left ?_ hα
    calc α * ((∫ θ in Work.Spaces.Iθ,
            AngBlk4 α (Work.FTS.StrongPersist.L3Rhs.VfsA2 α) θ)
          * (∫ z in Work.Spaces.Iz,
              SlotSum4 (fun z => Work.FTS.Nonlinear.FstarPkg.Hz z
                * Work.Construction.L12 w z) z))
        = (α * (∫ θ in Work.Spaces.Iθ,
              AngBlk4 α (Work.FTS.StrongPersist.L3Rhs.VfsA2 α) θ))
            * (∫ z in Work.Spaces.Iz,
                SlotSum4 (fun z => Work.FTS.Nonlinear.FstarPkg.Hz z
                  * Work.Construction.L12 w z) z) := by ring
      _ ≤ Ka * (Cr * (1 + Kr) ^ 2 * Work.Spaces.HkSq α 4 w) := h1
      _ = Ka * Cr * (1 + Kr) ^ 2 * Work.Spaces.HkSq α 4 w := by ring
      _ ≤ Ka * Cr * (1 + Kr) ^ 2 * (C₀ ^ 2 * α ^ 4) :=
          mul_le_mul_of_nonneg_left hw5
            (mul_nonneg (mul_nonneg hKapos.le hCrpos.le) (sq_nonneg _))
      _ = α * (Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 * α ^ 3) := by ring
  have hα3 : α ^ 3 ≤ 1 := pow_le_one₀ hα.le hα1
  have hHnn : (0 : ℝ) ≤ 1 + Work.Spaces.HkSq α 5 w := by
    have h := Work.Spaces.HkSq_nonneg α 5 w
    linarith
  have hone : (1 : ℝ) ≤ 1 + Work.Spaces.HkSq α 5 w := by
    have h := Work.Spaces.HkSq_nonneg α 5 w
    linarith
  calc Work.Spaces.HkSq α 4 (NP5a α w)
      = Work.Spaces.HkSq α 4 (fun z θ => Work.FTS.StrongPersist.L3Rhs.VfsA2 α θ
          * (Work.FTS.Nonlinear.FstarPkg.Hz z * Work.Construction.L12 w z)) := hcongr
    _ ≤ (∫ θ in Work.Spaces.Iθ, AngBlk4 α (Work.FTS.StrongPersist.L3Rhs.VfsA2 α) θ)
          * (∫ z in Work.Spaces.Iz,
              SlotSum4 (fun z => Work.FTS.Nonlinear.FstarPkg.Hz z
                * Work.Construction.L12 w z) z) := hsep
    _ ≤ Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 * α ^ 3 := hprod
    _ ≤ Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hα3 hK0nn
    _ ≤ (Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 + 1) * (1 + Work.Spaces.HkSq α 5 w) := by
        calc Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 * 1
            = Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 := by ring
          _ ≤ (Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2) * (1 + Work.Spaces.HkSq α 5 w) :=
              le_mul_of_one_le_right hK0nn hone
          _ ≤ (Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 + 1) * (1 + Work.Spaces.HkSq α 5 w) :=
              mul_le_mul_of_nonneg_right (by linarith) hHnn

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Nblock6.Tools.shiftProdDth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Nblock6.Tools.shiftProdDth` — the `D_θ` shift-product bound of the level-`6` `N`-block

`HkSq α 6 (A · D_θ f) ≤ C (MA² (1 + HkSq α 7 f) + (1 + (γ-1)⁻¹ (HkSq α 6 A + HkSq α 6 f))
  (HkSq α 6 A + HkSq α 6 f))`,

from the pointwise master bound `PtBdDth` (proved in `Tools/ptBoundDth.lean`) and the
exceptional-pair bound `N6Trans.T1SixAux.excDz5_mixed_pair_bound`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Nblock6.Tools

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

open Work.Spaces

/-- **The `D_θ` shift-product bound** from the pointwise master bound. -/
theorem shiftProdDth_of (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hB : PtBdDth α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A f : ℝ → ℝ → ℝ) (MA : ℝ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.HkMem α 6 A → Work.Spaces.HkMem α 6 f → Work.Spaces.HkMem α 7 f →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ MA) →
      Work.Spaces.HkSq α 6 (fun z θ => A z θ * Work.Spaces.Dth f z θ)
        ≤ C * (MA ^ 2 * Work.Spaces.HkSq α 7 f
            + (1 + (Work.Spaces.gam α - 1)⁻¹
                * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
              * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f)) := by
  obtain ⟨K, hK, hBd⟩ := hB
  obtain ⟨Csp, hCsppos, hsp⟩ :=
    Work.FTS.StrongPersist.N6Trans.T1SixAux.excDz5_mixed_pair_bound 0 2 (by norm_num)
      (by norm_num)
  have hγ : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hgnn10 : (10 : ℝ) ≤ (Work.Spaces.gam α - 1)⁻¹ := ten_le_inv_gam_sub_one hα hα1
  refine ⟨2 * (K + K * Csp * (Work.Spaces.gam α - 1)⁻¹) + 1, by positivity, ?_⟩
  intro A f MA hsmA hsmf hmA hmf hmf7 hMA
  have hA6 : 0 ≤ Work.Spaces.HkSq α 6 A := Work.Spaces.HkSq_nonneg α 6 A
  have hF6 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hF7 : 0 ≤ Work.Spaces.HkSq α 7 f := Work.Spaces.HkSq_nonneg α 7 f
  have hMA2 : 0 ≤ MA ^ 2 := sq_nonneg MA
  have hgnn : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ := inv_nonneg.mpr hγ.le
  obtain ⟨hspmem, hspbd⟩ := hsp α A f hα hα1 hsmA hmA hsmf hmf
  -- abbreviations
  set S : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 0 2 f z θ
      * Work.Spaces.Wt α z θ with hSdef
  -- the pointwise bound
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.HkIntegrand α 6 (fun z θ => A z θ * Work.Spaces.Dth f z θ) z θ
        ≤ K * MA ^ 2 * Work.Spaces.HkIntegrand α 7 f z θ
          + K * (1 + (Work.Spaces.gam α - 1)⁻¹
              * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
            * (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ)
          + K * (S z θ) ^ 2 := by
    intro z θ hz hθ hθ'
    have h := hBd A f MA hsmA hsmf hmA hmf hmf7 hMA z θ hz hθ hθ'
    have hS : S z θ = Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 0 2 f z θ
        * Work.Spaces.Wt α z θ := by rw [hSdef]
    rw [hS] at *
    rw [← hS]
    exact h
  -- the θ-slice integrability of the majorant at each positive `z`
  have hGint : ∀ z : ℝ, 0 < z → IntegrableOn (fun θ => K * MA ^ 2 * Work.Spaces.HkIntegrand α 7 f z θ
      + K * (1 + (Work.Spaces.gam α - 1)⁻¹
          * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
        * (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ)
      + K * (S z θ) ^ 2) Iθ := by
    intro z hz
    have hzI : z ∈ Iz := hz.le
    exact (((hmf7.1 z hzI).const_mul _).add
      (((hmA.1 z hzI).add (hmf.1 z hzI)).const_mul _)).add ((hspmem.1 z hzI).const_mul _)
  -- the θ-integral evaluated
  have hGeq : ∀ z : ℝ, 0 < z → (∫ θ in Iθ,
        (K * MA ^ 2 * Work.Spaces.HkIntegrand α 7 f z θ
          + K * (1 + (Work.Spaces.gam α - 1)⁻¹
              * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
            * (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ)
          + K * (S z θ) ^ 2))
      = K * MA ^ 2 * (∫ θ in Iθ, Work.Spaces.HkIntegrand α 7 f z θ)
        + K * (1 + (Work.Spaces.gam α - 1)⁻¹
            * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
          * ((∫ θ in Iθ, Work.Spaces.HkIntegrand α 6 A z θ)
            + (∫ θ in Iθ, Work.Spaces.HkIntegrand α 6 f z θ))
        + K * (∫ θ in Iθ, (S z θ) ^ 2) := by
    intro z hz
    have hzI : z ∈ Iz := hz.le
    have h1 : Integrable (fun θ => K * MA ^ 2 * Work.Spaces.HkIntegrand α 7 f z θ)
        (volume.restrict Iθ) := (hmf7.1 z hzI).const_mul _
    have h2 : Integrable (fun θ => K * (1 + (Work.Spaces.gam α - 1)⁻¹
        * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
        * (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ))
        (volume.restrict Iθ) := ((hmA.1 z hzI).add (hmf.1 z hzI)).const_mul _
    have h3 : Integrable (fun θ => K * (S z θ) ^ 2) (volume.restrict Iθ) :=
      (hspmem.1 z hzI).const_mul _
    rw [integral_add_three h1 h2 h3]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_add (hmA.1 z hzI) (hmf.1 z hzI)]
  -- the θ-bound at each positive `z`
  have hinner : ∀ z : ℝ, 0 < z → (∫ θ in Iθ,
        Work.Spaces.HkIntegrand α 6 (fun z θ => A z θ * Work.Spaces.Dth f z θ) z θ)
      ≤ K * MA ^ 2 * (∫ θ in Iθ, Work.Spaces.HkIntegrand α 7 f z θ)
        + K * (1 + (Work.Spaces.gam α - 1)⁻¹
            * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
          * ((∫ θ in Iθ, Work.Spaces.HkIntegrand α 6 A z θ)
            + (∫ θ in Iθ, Work.Spaces.HkIntegrand α 6 f z θ))
        + K * (∫ θ in Iθ, (S z θ) ^ 2) := by
    intro z hz
    rw [← hGeq z hz]
    refine integral_mono_of_nonneg
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)
      (hGint z hz) ?_
    filter_upwards [ae_mem_Ioo_Iθ_fts] with θ hθ
    exact hpt z θ hz hθ.1 hθ.2
  -- the exceptional-term bound
  have hsp' : Work.Spaces.L2Sq S ≤ Csp * (Work.Spaces.gam α - 1)⁻¹
      * Work.Spaces.HkSq α 6 A * Work.Spaces.HkSq α 6 f := by
    have hSe : S = fun z θ => Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 0 2 f z θ
        * Work.Spaces.Wt α z θ := by
      funext z θ; rw [hSdef]
    rw [hSe]
    calc Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter 5 A z θ
            * Work.Spaces.mixed 0 2 f z θ * Work.Spaces.Wt α z θ)
        ≤ Csp / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 A
            * Work.Spaces.HkSq α 6 f := hspbd
      _ = Csp * (Work.Spaces.gam α - 1)⁻¹ * Work.Spaces.HkSq α 6 A
            * Work.Spaces.HkSq α 6 f := by rw [div_eq_mul_inv]
  -- main inequality
  have hmain : Work.Spaces.HkSq α 6 (fun z θ => A z θ * Work.Spaces.Dth f z θ)
      ≤ K * MA ^ 2 * Work.Spaces.HkSq α 7 f
        + K * (1 + (Work.Spaces.gam α - 1)⁻¹
            * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
          * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f)
        + K * Work.Spaces.L2Sq S := by
    rw [Work.Spaces.HkSq, Work.Spaces.HkSq, Work.Spaces.HkSq, Work.Spaces.HkSq,
      Work.Spaces.L2Sq]
    have h1 : IntegrableOn (fun z => K * MA ^ 2
        * (∫ θ in Iθ, Work.Spaces.HkIntegrand α 7 f z θ)) Iz := hmf7.2.const_mul _
    have h2 : IntegrableOn (fun z => K * (1 + (Work.Spaces.gam α - 1)⁻¹
        * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
        * ((∫ θ in Iθ, Work.Spaces.HkIntegrand α 6 A z θ)
          + (∫ θ in Iθ, Work.Spaces.HkIntegrand α 6 f z θ))) Iz :=
      (hmA.2.add hmf.2).const_mul _
    have h3 : IntegrableOn (fun z => K * (∫ θ in Iθ, (S z θ) ^ 2)) Iz :=
      hspmem.2.const_mul _
    have hθ_int : IntegrableOn (fun z => K * MA ^ 2
        * (∫ θ in Iθ, Work.Spaces.HkIntegrand α 7 f z θ)
        + K * (1 + (Work.Spaces.gam α - 1)⁻¹
            * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
          * ((∫ θ in Iθ, Work.Spaces.HkIntegrand α 6 A z θ)
            + (∫ θ in Iθ, Work.Spaces.HkIntegrand α 6 f z θ))
        + K * (∫ θ in Iθ, (S z θ) ^ 2)) Iz := (h1.add h2).add h3
    have hstep : (∫ z in Iz, ∫ θ in Iθ,
          Work.Spaces.HkIntegrand α 6 (fun z θ => A z θ * Work.Spaces.Dth f z θ) z θ)
        ≤ ∫ z in Iz, (K * MA ^ 2 * (∫ θ in Iθ, Work.Spaces.HkIntegrand α 7 f z θ)
            + K * (1 + (Work.Spaces.gam α - 1)⁻¹
                * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
              * ((∫ θ in Iθ, Work.Spaces.HkIntegrand α 6 A z θ)
                + (∫ θ in Iθ, Work.Spaces.HkIntegrand α 6 f z θ))
            + K * (∫ θ in Iθ, (S z θ) ^ 2)) := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ) hθ_int ?_
      filter_upwards [ae_mem_Ioi_Iz_fts] with z hz
      exact hinner z hz
    calc (∫ z in Iz, ∫ θ in Iθ,
            Work.Spaces.HkIntegrand α 6 (fun z θ => A z θ * Work.Spaces.Dth f z θ) z θ)
        ≤ _ := hstep
      _ = K * MA ^ 2 * (∫ z in Iz, ∫ θ in Iθ, Work.Spaces.HkIntegrand α 7 f z θ)
          + K * (1 + (Work.Spaces.gam α - 1)⁻¹
              * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
            * ((∫ z in Iz, ∫ θ in Iθ, Work.Spaces.HkIntegrand α 6 A z θ)
              + (∫ z in Iz, ∫ θ in Iθ, Work.Spaces.HkIntegrand α 6 f z θ))
          + K * (∫ z in Iz, ∫ θ in Iθ, (S z θ) ^ 2) := by
        rw [integral_add_three_z h1 h2 h3]
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const_mul]
        rw [MeasureTheory.integral_add hmA.2 hmf.2]
  -- arithmetic
  have hspnn : 0 ≤ Work.Spaces.L2Sq S := by
    rw [Work.Spaces.L2Sq]
    exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  have hAF : Work.Spaces.HkSq α 6 A * Work.Spaces.HkSq α 6 f
      ≤ (1 + (Work.Spaces.gam α - 1)⁻¹
          * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
        * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f) := by
    have h1 : 4 * (Work.Spaces.HkSq α 6 A * Work.Spaces.HkSq α 6 f)
        ≤ (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f) ^ 2 := by
      nlinarith [sq_nonneg (Work.Spaces.HkSq α 6 A - Work.Spaces.HkSq α 6 f)]
    have h3 : 0 ≤ (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f) ^ 2 := sq_nonneg _
    have h4 : 40 * (Work.Spaces.HkSq α 6 A * Work.Spaces.HkSq α 6 f)
        ≤ (Work.Spaces.gam α - 1)⁻¹
          * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f) ^ 2 := by
      nlinarith [h1, hgnn10, h3, mul_nonneg (sub_nonneg.mpr hgnn10) h3]
    have h5 : (1 + (Work.Spaces.gam α - 1)⁻¹
          * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
        * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f)
        = (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f)
          + (Work.Spaces.gam α - 1)⁻¹
            * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f) ^ 2 := by ring
    have h6 : 0 ≤ Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f := by linarith
    nlinarith [h4, h5, h6]
  have hspnn' : 0 ≤ Csp * (Work.Spaces.gam α - 1)⁻¹ * Work.Spaces.HkSq α 6 A
      * Work.Spaces.HkSq α 6 f := by positivity
  have hmid : Work.Spaces.HkSq α 6 A * Work.Spaces.HkSq α 6 f
      ≤ (1 + (Work.Spaces.gam α - 1)⁻¹
          * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
        * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f) := hAF
  -- the two "cA"-terms bound
  set LB : ℝ := K * MA ^ 2 * Work.Spaces.HkSq α 7 f
      + K * (1 + (Work.Spaces.gam α - 1)⁻¹
          * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
        * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f)
      + K * Work.Spaces.L2Sq S with hLBdef
  have hkey : LB ≤ (K + K * Csp * (Work.Spaces.gam α - 1)⁻¹)
      * (MA ^ 2 * Work.Spaces.HkSq α 7 f
        + (1 + (Work.Spaces.gam α - 1)⁻¹
            * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
          * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f)) := by
    have hL2 : K * Work.Spaces.L2Sq S ≤ K * (Csp * (Work.Spaces.gam α - 1)⁻¹
        * Work.Spaces.HkSq α 6 A * Work.Spaces.HkSq α 6 f) :=
      mul_le_mul_of_nonneg_left hsp' hK.le
    have hKC : 0 ≤ K * Csp * (Work.Spaces.gam α - 1)⁻¹ := by positivity
    have hcA_nn : 0 ≤ (1 + (Work.Spaces.gam α - 1)⁻¹
        * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
        * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f) := by positivity
    have hAF' : Work.Spaces.HkSq α 6 A * Work.Spaces.HkSq α 6 f
        ≤ (1 + (Work.Spaces.gam α - 1)⁻¹
            * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
          * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f) := hAF
    have hmn : 0 ≤ MA ^ 2 * Work.Spaces.HkSq α 7 f := mul_nonneg hMA2 hF7
    rw [hLBdef]
    have hsum1 : K * MA ^ 2 * Work.Spaces.HkSq α 7 f
        ≤ (K + K * Csp * (Work.Spaces.gam α - 1)⁻¹)
          * (MA ^ 2 * Work.Spaces.HkSq α 7 f) := by
      nlinarith [hmn, hK.le, hKC]
    have hsum2 : K * (1 + (Work.Spaces.gam α - 1)⁻¹
          * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
        * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f)
        + K * (Csp * (Work.Spaces.gam α - 1)⁻¹ * Work.Spaces.HkSq α 6 A
            * Work.Spaces.HkSq α 6 f)
        ≤ (K + K * Csp * (Work.Spaces.gam α - 1)⁻¹)
          * ((1 + (Work.Spaces.gam α - 1)⁻¹
              * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
            * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f)) := by
      have hCspnn : 0 ≤ Csp * (Work.Spaces.gam α - 1)⁻¹ := by positivity
      have hstep : K * (Csp * (Work.Spaces.gam α - 1)⁻¹
          * (Work.Spaces.HkSq α 6 A * Work.Spaces.HkSq α 6 f))
          ≤ K * (Csp * (Work.Spaces.gam α - 1)⁻¹
            * ((1 + (Work.Spaces.gam α - 1)⁻¹
                * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
              * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))) := by
        refine mul_le_mul_of_nonneg_left ?_ hK.le
        exact mul_le_mul_of_nonneg_left hAF' hCspnn
      nlinarith [hstep, hcA_nn, hK.le, hKC]
    linarith [hsum1, hsum2]
  calc Work.Spaces.HkSq α 6 (fun z θ => A z θ * Work.Spaces.Dth f z θ) ≤ LB := hmain
    _ ≤ (K + K * Csp * (Work.Spaces.gam α - 1)⁻¹)
        * (MA ^ 2 * Work.Spaces.HkSq α 7 f
          + (1 + (Work.Spaces.gam α - 1)⁻¹
              * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
            * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f)) := hkey
    _ ≤ (2 * (K + K * Csp * (Work.Spaces.gam α - 1)⁻¹) + 1)
        * (MA ^ 2 * Work.Spaces.HkSq α 7 f
          + (1 + (Work.Spaces.gam α - 1)⁻¹
              * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
            * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f)) := by
        have hb : 0 ≤ MA ^ 2 * Work.Spaces.HkSq α 7 f
            + (1 + (Work.Spaces.gam α - 1)⁻¹
                * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
              * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f) := by positivity
        have hKC : 0 ≤ K + K * Csp * (Work.Spaces.gam α - 1)⁻¹ := by positivity
        nlinarith [hb, hKC]


/-- **The `D_θ` shift-product bound**, instantiated at `ptBoundDth`. -/
theorem shiftProdDth (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A f : ℝ → ℝ → ℝ) (MA : ℝ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.HkMem α 6 A → Work.Spaces.HkMem α 6 f → Work.Spaces.HkMem α 7 f →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ MA) →
      Work.Spaces.HkSq α 6 (fun z θ => A z θ * Work.Spaces.Dth f z θ)
        ≤ C * (MA ^ 2 * Work.Spaces.HkSq α 7 f
            + (1 + (Work.Spaces.gam α - 1)⁻¹
                * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
              * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f)) :=
  shiftProdDth_of α hα hα1 (ptBoundDth α hα hα1)

end Work.FTS.StrongEps.E4R3.Nblock6.Tools
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.Reduction =====
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
open Work.FTS.StrongGlobal (Xn6 concat)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The two inputs of `EpsE4Thr` -/





/-- **`EpsDatum` implies `EpsDatumP`**: the two classes differ only in that the class-`C` clause
of the latter is about the *projected* mollified profile, and the projection is the identity on a
profile whose `L₁₂`-zero-mode vanishes — which is the `l12` field of the former's class-`C`
clause. -/
theorem EpsDatum.toDatumP {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {h : Fn}
    (hd : EpsDatum α ρ ε h) : EpsDatumP α ρ ε h := by
  obtain ⟨hsm, hmem, hC⟩ := hd
  have hPz : Pz (Jeps ρ ε h) = Jeps ρ ε h :=
    Pz_self_of_l12 (Work.FTS.ClassC.ClassC.l12_zero hC)
  exact ⟨hsm, hmem, by rw [hPz]; exact hC⟩

/-! ## The restart-and-concatenate induction -/


/-! ## The assembly of `EpsUniformMem` -/


end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.TransO.ContDiffOn_E1_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TransO/ContDiffOn_E1_O` — `E1 α f` is `C³` on the open quadrant, on the *open* class

The transfer identity `D_θ(𝓛_Γ^T f) = 𝓛̂(D_θ f) + E1 α f` (`Transfer/Profiles.lean`)
introduces the defect

  `E1 α f z θ = (sin 2θ · Γ'(θ)) · radA α f z`,

a **separated** product of an angular factor of `θ` alone and a radial factor of `z` alone.
On the open coercivity class `CoerAdmO α f` (the class of the route's projected slices,
`EpsE4Thr/OpenClass.lean`) its two factors are of class `C³`:

* the angular factor `B(θ) = sin 2θ · Γ'(θ)` is `C³` on `(0,π/2)` because
  `Γ(θ) = (sin θ cos²θ)^{α/3}` is `C^∞` there (`Transfer.sinGam_contDiffOn_Ioo`);
* the radial factor `radA α f` is `C³` on `(0,∞)` because the nonlocal tail integral
  `L₁₂ f` is `C⁴` there — this is the *open* analogue
  `GalFields.Norm.radA_contDiffOn_four_of_smoothOpen` of the frozen
  `Transfer.radA_contDiffOn`, and it needs only `SmoothOpen f` and `HkMem α 5 f`, both of
  which `CoerAdmO α f` supplies.

The frozen twin of the present statement is `E1Parts.contDiffOn_uncurry_E1`, which is stated
on `CoerAdm` (hence demands `SmoothQuad`); that class is not reachable on the route
(`EpsE4Thr/OpenClass.lean`), which is exactly why this open-class version is needed.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.TransO

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The angular factor `B(θ) = sin 2θ·Γ'(θ)` of the transfer defect is `C³` on `(0,π/2)`.**

This is the angular half of `E1`; it is class-free (it does not involve the datum `f`).  The
proof is the one of `Work.FTS.CoercivityFix.Transfer.sinGam_contDiffOn_Ioo`: `Γ` is `C^∞` on
the open half-strip `z > 0, 0 < θ < π/2` (its base `sin θ · cos²θ` is positive there), so its
`D_θ`-derivative is `C^∞` as well, and it is recovered as the `z = 1` slice. -/
theorem contDiffOn_E1_ang (α : ℝ) :
    ContDiffOn ℝ 3
      (fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ) (Set.Ioo 0 (π / 2)) :=
  Work.FTS.CoercivityFix.Transfer.sinGam_contDiffOn_Ioo α

/-- **The radial factor `radA α f` of the transfer defect is `C³` on `(0,∞)`.**

`CoerAdmO α f` supplies `SmoothOpen f` (the class-`C`-clause regularity of the route) and
`HkMem α 5 f`, which on `radA`'s definition
`radA α f z = −a(z)·L₁₂ f(z) + (b(z)/c(α))·L₁₂(Transport f)(0)` reduce the statement to
`L₁₂ f ∈ C⁴((0,∞))` — the open twin
`Work.FTS.GalFields.Norm.radA_contDiffOn_four_of_smoothOpen`. -/
theorem contDiffOn_E1_rad (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hf : Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f) :
    ContDiffOn ℝ 3 (Work.FTS.CoercivityFix.Transfer.radA α f) (Set.Ioi (0 : ℝ)) :=
  (Work.FTS.GalFields.Norm.radA_contDiffOn_four_of_smoothOpen hα hα1 hf.1.1 hf.1.2.1).of_le
    (by norm_num)

/-- **The requested regularity**: the transfer defect `E1 α f` is `C³` on the open quadrant,
for every datum of the open coercivity class `CoerAdmO α f`.

`E1 α f z θ = B(θ)·radA α f z` is a separated product, so its joint `C³`-regularity on
`Qd = (0,∞) × (0,π/2)` follows from `contDiffOn_E1_ang` and `contDiffOn_E1_rad` by composing
with the two projections. -/
theorem ContDiffOn_E1_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f) :
    ContDiffOn ℝ 3 (Function.uncurry (Work.FTS.CoercivityFix.Transfer.E1 α f))
      Work.Construction.Qd := by
  have hB : ContDiffOn ℝ 3
      (fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ) (Set.Ioo 0 (π / 2)) :=
    contDiffOn_E1_ang α
  have hR : ContDiffOn ℝ 3 (Work.FTS.CoercivityFix.Transfer.radA α f) (Set.Ioi (0 : ℝ)) :=
    contDiffOn_E1_rad α hα hα1 hf
  have hfun : Function.uncurry (Work.FTS.CoercivityFix.Transfer.E1 α f)
      = (fun p : ℝ × ℝ => Real.sin (2 * p.2) * deriv (Work.Spaces.Gam α) p.2)
        * (fun p : ℝ × ℝ => Work.FTS.CoercivityFix.Transfer.radA α f p.1) := by
    funext p
    rcases p with ⟨z, θ⟩
    rfl
  rw [hfun]
  exact (hB.comp contDiffOn_snd (fun p hp => hp.2)).mul
    (hR.comp contDiffOn_fst (fun p hp => hp.1))

end Work.FTS.StrongEps.EpsE4Thr.TransO
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.ClassCDiffDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The bundle of open-quadrant facts about the difference `W₁ - W₂` of two `ClassC` profiles**
that the nine per-piece bounds of the `N₀`-difference consume.

Everything is stated for the difference `h = W₁ - W₂` (written out, so that the record can be
built without a `let`), and every field is a `SmoothOpen`-, `HkMem`- or `Xn`-statement about `h`
or about one of the two `D_θ`/`D_z`-derived fields `Dth W₂`, `Dz W₂` of the second profile. -/
structure ClassCDiffFacts (α : ℝ) (W₁ W₂ : Fn) : Prop where
  /-- `h = W₁ - W₂` is `C^∞` on the open quadrant -/
  hsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => W₁ z θ - W₂ z θ)
  /-- honesty of the `ℋ⁵`-integrand of `h` (used to reach `D_θh`, `D_zh`) -/
  hmem : Work.Spaces.HkMem α 5 (fun z θ => W₁ z θ - W₂ z θ)
  /-- the `ℋ⁴`-size of `h` is controlled by its `ℋ⁵`-size -/
  hXh : Work.FTS.Nonlin.Xn α (fun z θ => W₁ z θ - W₂ z θ)
    ≤ Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)
  /-- smoothness of `D_θh` -/
  hDthSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth (fun z θ => W₁ z θ - W₂ z θ))
  /-- honesty of the `ℋ⁴`-integrand of `D_θh` -/
  hDthMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dth (fun z θ => W₁ z θ - W₂ z θ))
  /-- the `ℋ⁴`-size of `D_θh` is controlled by the `ℋ⁵`-size of `h` -/
  hDthXn : Work.FTS.Nonlin.Xn α (Work.Spaces.Dth (fun z θ => W₁ z θ - W₂ z θ))
    ≤ Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)
  /-- smoothness of `D_zh` -/
  hDzSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz (fun z θ => W₁ z θ - W₂ z θ))
  /-- honesty of the `ℋ⁴`-integrand of `D_zh` -/
  hDzMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz (fun z θ => W₁ z θ - W₂ z θ))
  /-- the `ℋ⁴`-size of `D_zh` is controlled by the `ℋ⁵`-size of `h` -/
  hDzXn : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz (fun z θ => W₁ z θ - W₂ z θ))
    ≤ Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)
  /-- smoothness of the radial function `z ↦ L₁₂(h)(z)` -/
  hLhSm : Work.FTS.EllipticEst.SmoothOpen
    (fun z _ => Work.Construction.L12 (fun z θ => W₁ z θ - W₂ z θ) z)
  /-- the zero mode of `L₁₂(h)` vanishes -/
  hLh0 : Work.Construction.L12 (fun z θ => W₁ z θ - W₂ z θ) 0 = 0
  /-- smoothness of the radial function `z ↦ L₁₂(W₁)(z)` -/
  hLW₁Sm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 W₁ z)
  /-- the `ℋ⁴`-size of `W₁` is controlled by its `ℋ⁵`-size -/
  hXW₁ : Work.FTS.Nonlin.Xn α W₁ ≤ Work.FTS.GalFields.Xn5 α W₁
  /-- the `ℋ⁴`-size of `W₂` is controlled by its `ℋ⁵`-size -/
  hXW₂ : Work.FTS.Nonlin.Xn α W₂ ≤ Work.FTS.GalFields.Xn5 α W₂
  /-- smoothness of `D_θW₂` -/
  hDthW₂Sm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth W₂)
  /-- honesty of the `ℋ⁴`-integrand of `D_θW₂` -/
  hDthW₂Mem : Work.Spaces.HkMem α 4 (Work.Spaces.Dth W₂)
  /-- the `ℋ⁴`-size of `D_θW₂` is controlled by the `ℋ⁵`-size of `W₂` -/
  hDthW₂Xn : Work.FTS.Nonlin.Xn α (Work.Spaces.Dth W₂) ≤ Work.FTS.GalFields.Xn5 α W₂
  /-- smoothness of `D_zW₂` -/
  hDzW₂Sm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz W₂)
  /-- honesty of the `ℋ⁴`-integrand of `D_zW₂` -/
  hDzW₂Mem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz W₂)
  /-- the `ℋ⁴`-size of `D_zW₂` is controlled by the `ℋ⁵`-size of `W₂` -/
  hDzW₂Xn : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz W₂) ≤ Work.FTS.GalFields.Xn5 α W₂

end Work.FTS.StrongEps.EpsRLX
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.Atoms.W5DzFstar =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5.Atoms

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The one-dimensional product rule for `z ↦ z u'(z)`

The single analytic fact behind the whole lemma: on an open set where `u` is smooth,

  `(z u')^{(k)}(z) = z u^{(k+1)}(z) + k u^{(k)}(z)`,

from which both the separation identities for `D_z(D_zF_*)` resp. `D_θ(D_zF_*)` and the
weighted derivative bounds for the radial factor `z ↦ z H'(z)` follow. -/

/-- The `m`-th `deriv`-iterate of a function which is `C^{m+1}` on an open set is
differentiable at every point of that set.  (The ``iteratedDerivWithin`` is `C^{m+1}`, and on
the open set it agrees with the honest iterate `deriv^[m]`.) -/
theorem differentiableAt_deriv_iterate {u : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s) {m : ℕ}
    (hu : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) u s) {z : ℝ} (hz : z ∈ s) :
    DifferentiableAt ℝ (deriv^[m] u) z := by
  have hd : DifferentiableWithinAt ℝ (iteratedDeriv m u) s z := by
    have h0 : DifferentiableWithinAt ℝ (iteratedDerivWithin m u s) s z :=
      (hu.differentiableOn_iteratedDerivWithin (by exact_mod_cast Nat.lt_succ_self m)
        hs.uniqueDiffOn) z hz
    exact h0.congr (fun y hy => (iteratedDerivWithin_of_isOpen hs hy).symm)
      (iteratedDerivWithin_of_isOpen hs hz).symm
  rw [← iteratedDeriv_eq_iterate]
  exact hd.differentiableAt (hs.mem_nhds hz)

/-- **The product rule for the iterated `z`-derivative of `z ↦ z·u'(z)`.**  If `u` is `C^m` on
the open set `s` for every `m`, then for `z ∈ s`

  `(z u')^{(k)}(z) = z · u^{(k+1)}(z) + k · u^{(k)}(z)`. -/
theorem deriv_iter_zpz {u : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hu : ∀ m : ℕ, ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞) u s) :
    ∀ k : ℕ, ∀ z ∈ s,
      deriv^[k] (fun w => w * deriv u w) z = z * deriv^[k+1] u z + (k : ℝ) * deriv^[k] u z := by
  intro k
  induction k with
  | zero =>
      intro z _
      simp
  | succ k ih =>
      intro z hz
      have hev : deriv^[k] (fun w => w * deriv u w)
          =ᶠ[𝓝 z] (fun w => w * deriv^[k+1] u w + (k : ℝ) * deriv^[k] u w) := by
        filter_upwards [hs.mem_nhds hz] with w hw
        exact ih w hw
      rw [Function.iterate_succ_apply', hev.deriv_eq]
      have h1 : HasDerivAt (deriv^[k+1] u) (deriv^[k+2] u z) z := by
        have h := (differentiableAt_deriv_iterate hs (hu (k + 2)) hz).hasDerivAt
        rwa [show deriv (deriv^[k+1] u) z = deriv^[k+2] u z from
          (congrFun (Function.iterate_succ_apply' deriv (k + 1) u) z).symm] at h
      have h2 : HasDerivAt (deriv^[k] u) (deriv^[k+1] u z) z := by
        have h := (differentiableAt_deriv_iterate hs (hu (k + 1)) hz).hasDerivAt
        rwa [show deriv (deriv^[k] u) z = deriv^[k+1] u z from
          (congrFun (Function.iterate_succ_apply' deriv k u) z).symm] at h
      have hprod : HasDerivAt (fun w => w * deriv^[k+1] u w)
          (1 * deriv^[k+1] u z + z * deriv^[k+2] u z) z := (hasDerivAt_id z).mul h1
      have hcm : HasDerivAt (fun w => (k : ℝ) * deriv^[k] u w)
          ((k : ℝ) * deriv^[k+1] u z) z := h2.const_mul (k : ℝ)
      rw [show deriv (fun w => w * deriv^[k+1] u w + (k : ℝ) * deriv^[k] u w) z
          = 1 * deriv^[k+1] u z + z * deriv^[k+2] u z + (k : ℝ) * deriv^[k+1] u z
        from (hprod.add hcm).deriv]
      push_cast
      ring

/-! ## The radial factor `z ↦ z H'(z)` of `D_z(D_zF_*)` and its weighted derivative bounds -/

/-- `H = Hz = 2z(1-z)/(1+z)³` is `C^m` on `(-1,∞)` for every `m`. -/
theorem contDiffOn_Hz :
    ∀ m : ℕ, ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞)
      (Work.FTS.Nonlinear.FstarPkg.Hz) (Set.Ioi (-1 : ℝ)) := by
  intro m
  have hden : ∀ z ∈ Set.Ioi (-1 : ℝ), (1 + z) ^ 3 ≠ 0 := by
    intro z hz
    have hz' : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
    positivity
  show ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞) (fun z => 2 * z * (1 - z) / (1 + z) ^ 3)
    (Set.Ioi (-1 : ℝ))
  exact ((contDiffOn_const.mul contDiffOn_id).mul (contDiffOn_const.sub contDiffOn_id)).div
    ((contDiffOn_const.add contDiffOn_id).pow 3) hden

/-- **The weighted derivative bounds for the radial factor `z ↦ z H'(z)` of `D_z(D_zF_*)`.**
There is a sequence `B : ℕ → ℝ` of nonnegative constants with
`|(z+1)^k · (z H')^{(k)}(z)| ≤ B k` for all `k` and all `z ≥ 0`. -/
theorem HzDz_deriv_bound : ∃ B : ℕ → ℝ, (∀ k, 0 ≤ B k) ∧
    ∀ k : ℕ, ∀ z : ℝ, 0 ≤ z →
      |(z + 1) ^ k * deriv^[k] (fun w => w * deriv Work.FTS.Nonlinear.FstarPkg.Hz w) z|
        ≤ B k := by
  refine ⟨fun k => Work.FTS.Nonlinear.FstarPkg.HB (k + 1)
      + (k : ℝ) * Work.FTS.Nonlinear.FstarPkg.HB k, ?_, ?_⟩
  · intro k
    have h1 : 0 ≤ Work.FTS.Nonlinear.FstarPkg.HB (k + 1) :=
      Work.FTS.Nonlinear.FstarPkg.HB_nonneg (k + 1)
    have h2 : 0 ≤ Work.FTS.Nonlinear.FstarPkg.HB k := Work.FTS.Nonlinear.FstarPkg.HB_nonneg k
    positivity
  · intro k z hz
    have hz1 : (-1 : ℝ) < z := by linarith
    have hzp : (0 : ℝ) < z + 1 := by linarith
    rw [deriv_iter_zpz isOpen_Ioi contDiffOn_Hz k z hz1]
    have hA : |(z + 1) ^ k * z * deriv^[k+1] Work.FTS.Nonlinear.FstarPkg.Hz z|
        ≤ Work.FTS.Nonlinear.FstarPkg.HB (k + 1) := by
      have h := Work.FTS.Nonlinear.FstarPkg.Hz_deriv_bound (k + 1) z hz
      have hfac : z * ((z + 1) ^ k * deriv^[k+1] Work.FTS.Nonlinear.FstarPkg.Hz z)
          = (z / (z + 1)) * ((z + 1) ^ (k + 1)
              * deriv^[k+1] Work.FTS.Nonlinear.FstarPkg.Hz z) := by
        field_simp
        ring
      have h0 : 0 ≤ z / (z + 1) := div_nonneg hz hzp.le
      have h1 : z / (z + 1) ≤ 1 := by
        rw [div_le_one hzp]
        linarith
      rw [show (z + 1) ^ k * z * deriv^[k+1] Work.FTS.Nonlinear.FstarPkg.Hz z
            = z * ((z + 1) ^ k * deriv^[k+1] Work.FTS.Nonlinear.FstarPkg.Hz z) by ring,
        hfac, abs_mul, abs_of_nonneg h0]
      calc z / (z + 1) * |(z + 1) ^ (k + 1) * deriv^[k+1] Work.FTS.Nonlinear.FstarPkg.Hz z|
          ≤ 1 * Work.FTS.Nonlinear.FstarPkg.HB (k + 1) :=
            mul_le_mul h1 h (abs_nonneg _) zero_le_one
        _ = Work.FTS.Nonlinear.FstarPkg.HB (k + 1) := one_mul _
    have hB : |(z + 1) ^ k * ((k : ℝ) * deriv^[k] Work.FTS.Nonlinear.FstarPkg.Hz z)|
        ≤ (k : ℝ) * Work.FTS.Nonlinear.FstarPkg.HB k := by
      rw [show (z + 1) ^ k * ((k : ℝ) * deriv^[k] Work.FTS.Nonlinear.FstarPkg.Hz z)
            = (k : ℝ) * ((z + 1) ^ k * deriv^[k] Work.FTS.Nonlinear.FstarPkg.Hz z) by ring,
        abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
      exact mul_le_mul_of_nonneg_left (Work.FTS.Nonlinear.FstarPkg.Hz_deriv_bound k z hz)
        (Nat.cast_nonneg k)
    have hsplit : (z + 1) ^ k * (z * deriv^[k+1] Work.FTS.Nonlinear.FstarPkg.Hz z
          + (k : ℝ) * deriv^[k] Work.FTS.Nonlinear.FstarPkg.Hz z)
        = (z + 1) ^ k * z * deriv^[k+1] Work.FTS.Nonlinear.FstarPkg.Hz z
          + (z + 1) ^ k * ((k : ℝ) * deriv^[k] Work.FTS.Nonlinear.FstarPkg.Hz z) := by
      ring
    rw [hsplit]
    exact le_trans (abs_add_le _ _) (add_le_add hA hB)

/-! ## The separated form of `D_z(D_zF_*)` -/

/-- **`D_z(D_zF_*)` is the separated product `((α/c)·Γ) ⊗ (z·H')` on `z > -1`**, with
`H = Hz = 2z(1-z)/(1+z)³` the radial factor of `D_zF_*`. -/
lemma DzDzFstar_eq_sep {α : ℝ} (hα : 0 < α) :
    ∀ z : ℝ, -1 < z → ∀ θ : ℝ,
      Work.Spaces.Dz (Work.Spaces.Dz (Work.Construction.Fstar α)) z θ
        = (α / Work.Spaces.c α * Work.Spaces.Gam α θ)
            * (z * deriv Work.FTS.Nonlinear.FstarPkg.Hz z) := by
  intro z hz θ
  have hev : (fun z' : ℝ => Work.Spaces.Dz (Work.Construction.Fstar α) z' θ)
      =ᶠ[𝓝 z] fun z' : ℝ => α / Work.Spaces.c α
        * (Work.Spaces.Gam α θ * Work.FTS.Nonlinear.FstarPkg.Hz z') := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact Work.FTS.Nonlinear.FstarPkg.Dz_Fstar_eq_Hz (θ := θ) hα hz'
  show z * deriv (fun z' : ℝ => Work.Spaces.Dz (Work.Construction.Fstar α) z' θ) z
      = (α / Work.Spaces.c α * Work.Spaces.Gam α θ)
          * (z * deriv Work.FTS.Nonlinear.FstarPkg.Hz z)
  rw [hev.deriv_eq,
    Work.Spaces.deriv_const_mul' (α / Work.Spaces.c α) z
      (fun z' => Work.Spaces.Gam α θ * Work.FTS.Nonlinear.FstarPkg.Hz z'),
    Work.Spaces.deriv_const_mul' (Work.Spaces.Gam α θ) z Work.FTS.Nonlinear.FstarPkg.Hz]
  ring

/-- **The `W5` data of the fixed profile `D_zF_*`.**  Same shape as `W5DthFstar`, for
`F = Dz F_*`: the new facts are `WlInfMem α 4 (Dz (Dz F_*))` (`= WlInfMem α 4 (DzIter 2 F_*)`),
`WlInfMem α 4 (Dth (Dz F_*))` and the two corresponding `WlInf`-bounds.

Available: `Work.FTS.StrongPersist.DzFstar_W6` gives `WlInfMem α 6 (Dz F_*)` with norm `≤ Cα`, and
`Work.FTS.StrongPersist.H6Rows.Npair6BWork.fstarDat` gives `SmoothOpen` and `WlInfMem α 6 (F_*)`
with the pointwise slot bounds `|mixed j i F_* z θ| ≤ C α (z/(1+z)²)(…)` for `j + i ≤ 6`.

Direct slot route (recommended, and the only one needed): every slot of `WlInf α 4 (Dz (Dz F_*))`
or of `WlInf α 4 (Dth (Dz F_*))` is — after `pzIter k (Dz g) = z·pzIter (k+1) g + k·pzIter k g` and
`DthIter j (Dz g) = Dz (DthIter j g)` — a `pzIter`-iterate of `mixed b a F_*` with `a + b ≤ 6`,
hence dominated pointwise by the `fstarDat` slot bound; finish with `Work.Spaces.supAbs_le`.
`a` may depend on `α`. -/
theorem W5DzFstar : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∃ a : ℝ, 0 < a ∧
    Work.FTS.StrongEps.H5.W5 α (Work.Spaces.Dz (Work.Construction.Fstar α)) a := by
  obtain ⟨C, _hCpos, hdat⟩ := Work.FTS.StrongPersist.H6Rows.Npair6BWork.fstarDat
  obtain ⟨K, _hKpos, hKgam⟩ := Work.FTS.StrongPersist.W6Aux.dthGamWeightLe7
  obtain ⟨B, _hBnn, hB⟩ := HzDz_deriv_bound
  intro α hαIoc
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  obtain ⟨_hsmF, _hsmDth, hsmDz, _hFmem, _hFle, _hDthmem, _hDthle, hDzmem, hDzle, _hslot⟩ :=
    hdat α hαIoc
  -- ### the level-`4` and level-`5` data of `D_zF_*`
  have hDzmem4 : Work.Spaces.WlInfMem α 4 (Work.Spaces.Dz (Work.Construction.Fstar α)) :=
    (WlInfMem_mono (α := α) (l := 6) (l' := 4) (by norm_num) hDzmem).1
  have hDzle4 : Work.Spaces.WlInf α 4 (Work.Spaces.Dz (Work.Construction.Fstar α)) ≤ C * α :=
    le_trans (WlInfMem_mono (α := α) (l := 6) (l' := 4) (by norm_num) hDzmem).2 hDzle
  have hDzmem5 : Work.Spaces.WlInfMem α 5 (Work.Spaces.Dz (Work.Construction.Fstar α)) :=
    (WlInfMem_mono (α := α) (l := 6) (l' := 5) (by norm_num) hDzmem).1
  have hDzle5 : Work.Spaces.WlInf α 5 (Work.Spaces.Dz (Work.Construction.Fstar α)) ≤ C * α :=
    le_trans (WlInfMem_mono (α := α) (l := 6) (l' := 5) (by norm_num) hDzmem).2 hDzle
  -- ### `D_θ(D_zF_*)`: one `D_θ`-derivative costs one level of the `𝒲`-norm
  have hDthDz := Work.FTS.StrongEps.H5.WlInfMem_Dth (l := 4) hα hα1 hDzmem5
  -- ### `D_z(D_zF_*)`: the separated product `A ⊗ H`
  have hc1 : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hcoef : |α / Work.Spaces.c α| ≤ 10 * α := by
    rw [abs_of_nonneg (div_nonneg hα.le hcpos.le), div_le_iff₀ hcpos]
    nlinarith
  set A : ℝ → ℝ := fun θ => α / Work.Spaces.c α * Work.Spaces.Gam α θ with hAdef
  set H : ℝ → ℝ := fun z => z * deriv Work.FTS.Nonlinear.FstarPkg.Hz z with hHdef
  set Aj : ℕ → ℝ := fun _ => 10 * α * max (Work.Spaces.tBound 0 0) (K * α) with hAjdef
  have hA0 : ∀ θ ∈ Work.Spaces.Iθ, |A θ| ≤ 10 * α := by
    intro θ hθ
    have h2 := Work.Spaces.Gam_bounds α θ hα hθ
    rw [hAdef, abs_mul]
    calc |α / Work.Spaces.c α| * |Work.Spaces.Gam α θ|
        = |α / Work.Spaces.c α| * Work.Spaces.Gam α θ := by rw [abs_of_nonneg h2.1]
      _ ≤ (10 * α) * 1 := mul_le_mul hcoef h2.2 h2.1 (by positivity)
      _ = 10 * α := by ring
  have hAj : ∀ j : ℕ, 1 ≤ j → j ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |(Work.Spaces.dthU^[j]) A θ * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ| ≤ Aj j := by
    intro j hj1 hj4 θ hθ
    have hiter : (Work.Spaces.dthU^[j]) A θ
        = (α / Work.Spaces.c α) * (Work.Spaces.dthU^[j])
            (fun t => Work.Spaces.Gam α t) θ := by
      rw [hAdef, Work.Spaces.dthU_iter_const_mul j (α / Work.Spaces.c α)
        (fun t => Work.Spaces.Gam α t)]
    have hb : |(Work.Spaces.dthU^[j]) (fun t => Work.Spaces.Gam α t) θ
        * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ|
        ≤ max (Work.Spaces.tBound 0 0) (K * α) := by
      rcases lt_or_eq_of_le hj1 with hj2 | hj1'
      · have hw := Work.FTS.Nonlinear.FstarPkg.DthAux.Wt_nonneg hα hθ
        rw [abs_mul, abs_of_nonneg hw]
        exact le_trans (hKgam j (by omega) (by omega) α hα hα1 θ hθ) (le_max_right _ _)
      · have hjeq : j = 1 := hj1'.symm
        subst hjeq
        have h1 := Work.Spaces.dthU_Gam_le 1 (le_refl 1) α hα hα1 θ hθ
        have hw := Work.FTS.Nonlinear.FstarPkg.DthAux.Wt_nonneg hα hθ
        have h2 := Work.FTS.Nonlinear.FstarPkg.DthAux.alpha_Gam_Wt_le_one
          (α := α) (θ := θ) hα hθ
        have ht : 0 ≤ Work.Spaces.tBound 0 0 := Work.Spaces.tBound_nonneg 0 0
        have h3 : |(Work.Spaces.dthU^[1]) (fun t => Work.Spaces.Gam α t) θ
            * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ| ≤ Work.Spaces.tBound 0 0 := by
          rw [abs_mul, abs_of_nonneg hw]
          calc |(Work.Spaces.dthU^[1]) (fun t => Work.Spaces.Gam α t) θ|
                * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ
              ≤ (α * Work.Spaces.tBound 0 0 * Work.Spaces.Gam α θ)
                * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ :=
                mul_le_mul_of_nonneg_right h1 hw
            _ = Work.Spaces.tBound 0 0
                * (α * Work.Spaces.Gam α θ * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ) := by
                ring
            _ ≤ Work.Spaces.tBound 0 0 * 1 := mul_le_mul_of_nonneg_left h2 ht
            _ = Work.Spaces.tBound 0 0 := mul_one _
        exact le_trans h3 (le_max_left _ _)
    have hsplit : (α / Work.Spaces.c α) * (Work.Spaces.dthU^[j])
          (fun t => Work.Spaces.Gam α t) θ
        * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ
        = (α / Work.Spaces.c α) * ((Work.Spaces.dthU^[j])
            (fun t => Work.Spaces.Gam α t) θ
          * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ) := by ring
    rw [hiter, hsplit, abs_mul]
    calc |α / Work.Spaces.c α| * |(Work.Spaces.dthU^[j])
            (fun t => Work.Spaces.Gam α t) θ
          * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ|
        ≤ (10 * α) * max (Work.Spaces.tBound 0 0) (K * α) :=
          mul_le_mul hcoef hb (abs_nonneg _) (by positivity)
      _ = Aj j := by rw [hAjdef]
  have hH : ∀ k : ℕ, k ≤ 4 → ∀ z : ℝ, 0 ≤ z →
      |(z + 1) ^ k * deriv^[k] H z| ≤ B k := by
    intro k _ z hz
    rw [hHdef]
    exact hB k z hz
  have hsep : Work.Spaces.WlInfMem α 4 (fun z θ => A θ * H z) ∧
      Work.Spaces.WlInf α 4 (fun z θ => A θ * H z) ≤ sepBnd 4 (10 * α) Aj B :=
    WlInf_sep (l := 4) hA0 hAj hH
  have hcongr := Work.FTS.Nonlinear.FstarPkg.WlInf_congr (α := α) (l := 4)
    (f := Work.Spaces.Dz (Work.Spaces.Dz (Work.Construction.Fstar α)))
    (g := fun z θ => A θ * H z)
    (fun z hz θ => DzDzFstar_eq_sep hα z hz θ)
  set sb1 : ℝ := sepBnd 4 (10 * α) Aj B with hsb1
  set sb2 : ℝ := (α + 1) * (C * α) with hsb2
  refine ⟨max 1 (max (C * α) (max sb1 sb2)), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  refine ⟨hsmDz, hDzmem4, ?_, hsmDz.Dz, hcongr.2.mpr hsep.1, ?_, hsmDz.Dth, hDthDz.1, ?_⟩
  · calc Work.Spaces.WlInf α 4 (Work.Spaces.Dz (Work.Construction.Fstar α)) ≤ C * α := hDzle4
      _ ≤ max 1 (max (C * α) (max sb1 sb2)) :=
          le_trans (le_max_left (C * α) (max sb1 sb2))
            (le_max_right 1 (max (C * α) (max sb1 sb2)))
  · calc Work.Spaces.WlInf α 4 (Work.Spaces.Dz (Work.Spaces.Dz (Work.Construction.Fstar α)))
        = Work.Spaces.WlInf α 4 (fun z θ => A θ * H z) := hcongr.1
      _ ≤ sb1 := by rw [hsb1]; exact hsep.2
      _ ≤ max 1 (max (C * α) (max sb1 sb2)) :=
          le_trans (le_max_left sb1 sb2)
            (le_trans (le_max_right (C * α) (max sb1 sb2))
              (le_max_right 1 (max (C * α) (max sb1 sb2))))
  · calc Work.Spaces.WlInf α 4 (Work.Spaces.Dth (Work.Spaces.Dz (Work.Construction.Fstar α)))
        ≤ (α + 1) * Work.Spaces.WlInf α 5 (Work.Spaces.Dz (Work.Construction.Fstar α)) :=
          hDthDz.2
      _ ≤ (α + 1) * (C * α) := mul_le_mul_of_nonneg_left hDzle5 (by linarith)
      _ = sb2 := by rw [hsb2]
      _ ≤ max 1 (max (C * α) (max sb1 sb2)) :=
          le_trans (le_max_right sb1 sb2)
            (le_trans (le_max_right (C * α) (max sb1 sb2))
              (le_max_right 1 (max (C * α) (max sb1 sb2))))

end Work.FTS.StrongEps.H5.Atoms
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.Corr_HkSq6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux

/-- **The `ℋ⁶`-norm of the nonlocal correction `Corr α f`.**

`Corr α f = Γ(θ)·radA α f z` is a product of the angular function `Γ = Gam α` and the radial
profile `radA α f` (`CoercivityFix.Transfer.Corr_eq_radA`), so the separation bound
`L6Aux.HkIntegrandSepLeGen` at level six gives

`HkIntegrand α 6 (Corr α f) z θ ≤ c(α)²·Mth6 α θ·SlotSum (radA α f) z`  (`θ ∈ Iθ`),

and both one-dimensional factors are bounded uniformly in `α ∈ (0,1]`:

* `∫_θ Mth6 α ≤ Cang` (`H6Aux.Mth6_integral_bound`),
* `∫_z SlotSum (radA α f) ≤ Crad·HkSq α 6 f` (`H6Aux.Alt_SlotSum_radA_le'`),

whence `HkSq α 6 (Corr α f) ≤ 100·Cang·Crad·HkSq α 6 f` (`c(α) ≤ 10`, `Spaces.c_bounds`). -/
theorem Corr_HkSq6 : ∃ C α₂ : ℝ, 0 < C ∧ 0 < α₂ ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ f : ℝ → ℝ → ℝ,
    Work.FTS.StrongPersist.H6Adm α f → Work.Spaces.HkMem α 7 f →
      Work.Spaces.HkMem α 6 (Work.FTS.CoercivityFix.Corr α f) ∧
      Work.Spaces.HkSq α 6 (Work.FTS.CoercivityFix.Corr α f)
        ≤ C * Work.Spaces.HkSq α 6 f := by
  obtain ⟨Cang, hCangpos, hang⟩ := Mth6_integral_bound
  obtain ⟨Crad, _hCradpos, hrad⟩ := Alt_SlotSum_radA_le'
  refine ⟨100 * Cang * Crad, 1, by positivity, one_pos, ?_⟩
  intro α hαIoc f hf hmem7
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hf.reg.1
  have hmem := HkMem_Corr_of hα hα1 hsm hmem7 hang (hrad α hαIoc f hf hmem7)
  refine ⟨hmem, ?_⟩
  exact HkSq_Corr_le_of hα hα1 hmem (le_of_lt hCangpos) (hang α hαIoc)
    (hrad α hαIoc f hf hmem7)

end Work.FTS.StrongPersist.H6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.RStep =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux

open Work.FTS.Galerkin (Fn)
open Work.FTS.IPGen (IPnG IPnG_zero IPnG_succ)
open Work.FTS.CoercivityFix.Transfer (CommSm CSQ AddOKSm)

set_option autoImplicit false

/-- **One step of the commutator induction.** -/
theorem R_step (n : ℕ) (hn : n + 1 ≤ 5)
    (IH : ∃ r : ℝ, 0 < r ∧ ∀ α ∈ Set.Ioc 0 1, ∀ h : Fn,
      Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.HkMem α (n + 2) h →
      -r * IPnG 1 1 α n h h ≤ IPnG 1 1 α n (Work.FTS.CoercivityFix.Lhat h) h) :
    ∃ r : ℝ, 0 < r ∧ ∀ α ∈ Set.Ioc 0 1, ∀ h : Fn,
      Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.HkMem α (n + 3) h →
      -r * IPnG 1 1 α (n + 1) h h
        ≤ IPnG 1 1 α (n + 1) (Work.FTS.CoercivityFix.Lhat h) h := by
  obtain ⟨r, hr, IHr⟩ := IH
  obtain ⟨CC, hCC, hCSQunif⟩ := CSQ_IPnG_unif n
  obtain ⟨C₂, hC₂, hE2unif⟩ := HkSq_E2hat_le (m := n + 1) (by omega)
  refine ⟨r + CC * Real.sqrt C₂, by positivity, fun α hα h hs hm3 => ?_⟩
  have hα0 : 0 < α := hα.1
  have hCSQ := hCSQunif α hα
  have hE2 := hE2unif α (by linarith)
  -- ## the elementary facts
  obtain ⟨hm2', hm2dth, hm2dz⟩ := Work.FTS.IPGen.HkMem_descent (by linarith : -(1 / 10 : ℝ) ≤ α) hs hm3
  have hm2 : Work.Spaces.HkMem α (n + 2) h := hm2'
  have hm1dth : Work.Spaces.HkMem α (n + 1) (Work.Spaces.Dth h) :=
    Work.FTS.IPGen.HkMem_mono_le hs.Dth (n + 1) (by omega) hm2dth
  have hm1dz : Work.Spaces.HkMem α (n + 1) (Work.Spaces.Dz h) :=
    Work.FTS.IPGen.HkMem_mono_le hs.Dz (n + 1) (by omega) hm2dz
  have hm1E2 : Work.Spaces.HkMem α (n + 1) (Work.FTS.CoercivityFix.E2hat h) :=
    HkMem_E2hat α (by linarith) hα0 (m := n + 1) (by omega) hs hm2
  -- the smoothness facts
  have hsDth : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth h) := hs.Dth
  have hsDz : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz h) := hs.Dz
  have hsE2 : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.CoercivityFix.E2hat h) :=
    smoothOpen_E2hat hs
  -- the commutator identities
  obtain ⟨hcommθ, hcommz⟩ := LhatCommOpen hs
  have hcm : CommSm α (n + 1) (IPnG 1 1 α n) := commSm_IPnG α hα0 n
  -- ## the recursion
  have hcongr1 : IPnG 1 1 α n (Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat h))
        (Work.Spaces.Dth h)
      = IPnG 1 1 α n (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth h))
        (Work.Spaces.Dth h) :=
    hcm.congr _ _ _ hcommθ
  have hcongr2 : IPnG 1 1 α n (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat h))
        (Work.Spaces.Dz h)
      = IPnG 1 1 α n (fun z θ => Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz h) z θ
          + Work.FTS.CoercivityFix.E2hat h z θ) (Work.Spaces.Dz h) :=
    hcm.congr _ _ _ hcommz
  have hadd : IPnG 1 1 α n (fun z θ => Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz h) z θ
        + Work.FTS.CoercivityFix.E2hat h z θ) (Work.Spaces.Dz h)
      = IPnG 1 1 α n (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz h)) (Work.Spaces.Dz h)
        + IPnG 1 1 α n (Work.FTS.CoercivityFix.E2hat h) (Work.Spaces.Dz h) :=
    hcm.add _ _ _ ⟨q0Sm_Lhat hsDz (n + 1), q0Sm_of_smoothOpen hsE2 (n + 1),
      q0Sm_of_smoothOpen hsDz (n + 1), Lhat_mem α hα0 (n + 1) hsDz hm2dz, hm1E2, hm1dz⟩
  -- ## the induction hypotheses
  have hIH1 := IHr α hα h hs hm2
  have hIH2 := IHr α hα (Work.Spaces.Dth h) hsDth hm2dth
  have hIH3 := IHr α hα (Work.Spaces.Dz h) hsDz hm2dz
  -- ## the correction
  have hcorr : -CC * Real.sqrt C₂ * IPnG 1 1 α (n + 1) h h
      ≤ IPnG 1 1 α n (Work.FTS.CoercivityFix.E2hat h) (Work.Spaces.Dz h) := by
    have hcs := hCSQ (Work.FTS.CoercivityFix.E2hat h) (Work.Spaces.Dz h)
      (q0Sm_of_smoothOpen hsE2 (n + 1)) (q0Sm_of_smoothOpen hsDz (n + 1)) hm1E2 hm1dz
    have hE2b := hE2 h hs hm2
    have hDzb : Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dz h)
        ≤ Work.Spaces.HkSq α (n + 2) h := HkSq_Dz_le_succ' α (n + 1) hs hm2
    have hcover := lo_IPnG α hα0 (n + 1) h hs hm2
    -- the two norms are bounded by `√(C₂ · HkSq α (n+2) h)` and `√(HkSq α (n+2) h)`
    have hn1 : Work.Spaces.HkNorm α (n + 1) (Work.FTS.CoercivityFix.E2hat h)
        ≤ Real.sqrt C₂ * Real.sqrt (Work.Spaces.HkSq α (n + 2) h) := by
      rw [Work.Spaces.HkNorm, ← Real.sqrt_mul hC₂.le]
      exact Real.sqrt_le_sqrt hE2b
    have hn2 : Work.Spaces.HkNorm α (n + 1) (Work.Spaces.Dz h)
        ≤ Real.sqrt (Work.Spaces.HkSq α (n + 2) h) := by
      rw [Work.Spaces.HkNorm]
      exact Real.sqrt_le_sqrt hDzb
    have hprod := mul_le_mul hn1 hn2 (Real.sqrt_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg C₂) (Real.sqrt_nonneg _))
    have hkey : Real.sqrt C₂ * Real.sqrt (Work.Spaces.HkSq α (n + 2) h)
        * Real.sqrt (Work.Spaces.HkSq α (n + 2) h)
        = Real.sqrt C₂ * Work.Spaces.HkSq α (n + 2) h := by
      rw [mul_assoc, Real.mul_self_sqrt (Work.Spaces.HkSq_nonneg α (n + 2) h)]
    rw [hkey] at hprod
    have hfinal : CC * Work.Spaces.HkNorm α (n + 1) (Work.FTS.CoercivityFix.E2hat h)
          * Work.Spaces.HkNorm α (n + 1) (Work.Spaces.Dz h)
        ≤ CC * Real.sqrt C₂ * IPnG 1 1 α (n + 1) h h := by
      calc CC * Work.Spaces.HkNorm α (n + 1) (Work.FTS.CoercivityFix.E2hat h)
            * Work.Spaces.HkNorm α (n + 1) (Work.Spaces.Dz h)
          = CC * (Work.Spaces.HkNorm α (n + 1) (Work.FTS.CoercivityFix.E2hat h)
              * Work.Spaces.HkNorm α (n + 1) (Work.Spaces.Dz h)) := by ring
        _ ≤ CC * (Real.sqrt C₂ * Work.Spaces.HkSq α (n + 2) h) :=
            mul_le_mul_of_nonneg_left hprod hCC.le
        _ ≤ CC * (Real.sqrt C₂ * IPnG 1 1 α (n + 1) h h) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcover (Real.sqrt_nonneg C₂))
              hCC.le
        _ = CC * Real.sqrt C₂ * IPnG 1 1 α (n + 1) h h := by ring
    have hcs' := abs_le.mp hcs
    linarith [hcs'.1, hfinal]
  -- ## the recursion rewritten and the final arithmetic
  have hrec : IPnG 1 1 α (n + 1) (Work.FTS.CoercivityFix.Lhat h) h
      = IPnG 1 1 α n (Work.FTS.CoercivityFix.Lhat h) h
        + IPnG 1 1 α n (Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat h)) (Work.Spaces.Dth h)
        + IPnG 1 1 α n (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat h)) (Work.Spaces.Dz h) := by
    simp only [IPnG_succ, Work.Coercivity.HkIPStep, one_mul]
  have hdiag : IPnG 1 1 α (n + 1) h h
      = IPnG 1 1 α n h h + IPnG 1 1 α n (Work.Spaces.Dth h) (Work.Spaces.Dth h)
        + IPnG 1 1 α n (Work.Spaces.Dz h) (Work.Spaces.Dz h) := by
    simp only [IPnG_succ, Work.Coercivity.HkIPStep, one_mul]
  rw [hrec, hcongr1, hcongr2, hadd, hdiag]
  rw [hdiag] at hcorr
  nlinarith [hIH1, hIH2, hIH3, hcorr]

end Work.FTS.StrongPersist.H6Aux
end
end
