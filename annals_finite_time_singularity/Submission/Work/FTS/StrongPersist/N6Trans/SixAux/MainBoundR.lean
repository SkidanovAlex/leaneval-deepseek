import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.AeI1Fts.zibp_cut
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.OpenPkg.radialMul_field
import Submission.Work.FTS.PhiStar.Series.BslOp.Setup
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EpsE4Thr.WipEqIntegral
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Assembly6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Gmaj6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Majorant6
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.L3MulDzBackupM
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.FkSlots
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.NfkSmooth
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsSep
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.leibnizRem6
import Submission.Work.FTS.StrongPersist.N6_fkH
import Submission.Work.FTS.StrongPersist.N6_prod
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2Sup.GenSlot
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_EllLimOK.BoxDataH.BoxUniform
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
-- ===== merged: Submission.Work.FTS.ClassC.deriv_series_general =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Work
open Work.FTS.PhiStar
open Work.FTS.PhiStar.Series

theorem deriv_series_general (α : ℝ) (F : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hInt : (∀ m : ℕ, ContinuousOn (fun t => Work.FTS.PhiStar.Series.cmode m F t) (Set.Ioi 0)) ∧
      (∀ m : ℕ, MeasureTheory.IntegrableOn
        (fun t => Work.FTS.PhiStar.Series.cmode m F t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
        (Set.Ioo 0 1)) ∧
      (∀ m : ℕ, MeasureTheory.IntegrableOn
        (fun t => Work.FTS.PhiStar.Series.cmode m F t * t ^ (-(2 * (m : ℝ) / α) - 1))
        (Set.Ioi 1)))
    (hmaj : ∀ D : ℝ, Summable fun m : ℕ => D * Work.FTS.PhiStar.Series.majPow m)
    (z : ℝ) (hz : 0 < z) (θ : ℝ) (hθ : 0 < θ) (hθ2 : θ < π / 2) (D : ℝ)
    (hB0 : ∀ m : ℕ, ∀ y : ℝ, 0 < y →
      |Work.FTS.PhiStar.Series.acoeff α m F y| * |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ D * Work.FTS.PhiStar.Series.majPow m)
    (hB1 : ∀ m : ℕ, ∀ y : ℝ, 0 < y →
      |deriv (Work.FTS.PhiStar.Series.acoeff α m F) y| * |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ D * Work.FTS.PhiStar.Series.majPow m)
    (hB2 : ∀ m : ℕ, ∀ y : ℝ, 0 < y →
      |deriv (deriv (Work.FTS.PhiStar.Series.acoeff α m F)) y|
        * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ D * Work.FTS.PhiStar.Series.majPow m)
    (hB3 : ∀ m : ℕ, ∀ y : ℝ, 0 < y → y ≤ (θ + Real.pi / 2) / 2 →
      |Work.FTS.PhiStar.Series.acoeff α m F z| * |deriv (Work.FTS.PhiStar.Gegenbauer.eFam m) y|
        ≤ D * Work.FTS.PhiStar.Series.majPow m)
    (hB4 : ∀ m : ℕ, ∀ y : ℝ, 0 < y → y ≤ (θ + Real.pi / 2) / 2 →
      |Work.FTS.PhiStar.Series.acoeff α m F z|
        * |iteratedDeriv 2 (Work.FTS.PhiStar.Gegenbauer.eFam m) y|
        ≤ D * Work.FTS.PhiStar.Series.majPow m)
    (hB5 : ∀ m : ℕ, ∀ y : ℝ, 0 < y → y ≤ (θ + Real.pi / 2) / 2 →
      |Work.FTS.PhiStar.Series.acoeff α m F z|
        * |deriv (fun θ' => Real.tan θ' * Work.FTS.PhiStar.Gegenbauer.eFam m θ') y|
        ≤ D * Work.FTS.PhiStar.Series.majPow m) :
    Work.Spaces.pz (fun z θ => Work.FTS.PhiStar.Series.psiSeries α F z θ) z θ
        = ∑' m : ℕ, deriv (Work.FTS.PhiStar.Series.acoeff α m F) z
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ ∧
      Work.Spaces.pzIter 2 (fun z θ => Work.FTS.PhiStar.Series.psiSeries α F z θ) z θ
        = ∑' m : ℕ, deriv (deriv (Work.FTS.PhiStar.Series.acoeff α m F)) z
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ ∧
      Work.Spaces.pth (fun z θ => Work.FTS.PhiStar.Series.psiSeries α F z θ) z θ
        = ∑' m : ℕ, Work.FTS.PhiStar.Series.acoeff α m F z
            * deriv (Work.FTS.PhiStar.Gegenbauer.eFam m) θ ∧
      Work.Spaces.pthIter 2 (fun z θ => Work.FTS.PhiStar.Series.psiSeries α F z θ) z θ
        = ∑' m : ℕ, Work.FTS.PhiStar.Series.acoeff α m F z
            * iteratedDeriv 2 (Work.FTS.PhiStar.Gegenbauer.eFam m) θ ∧
      Work.Spaces.pth (fun z' θ' => Real.tan θ' * Work.FTS.PhiStar.Series.psiSeries α F z' θ') z θ
        = ∑' m : ℕ, Work.FTS.PhiStar.Series.acoeff α m F z
            * deriv (fun θ' => Real.tan θ' * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ ∧
      (Work.Elliptic.Lzero (fun z θ => Work.FTS.PhiStar.Series.psiSeries α F z θ) z θ
        = -Work.Spaces.pthIter 2 (fun z θ => Work.FTS.PhiStar.Series.psiSeries α F z θ) z θ
          + Work.Spaces.pth (fun z' θ' => Real.tan θ' * Work.FTS.PhiStar.Series.psiSeries α F z' θ') z θ
          - 6 * Work.FTS.PhiStar.Series.psiSeries α F z θ) := by
  have hθu_eq : (θ + Real.pi / 2) / 2 = (θ + π / 2) / 2 := rfl
  set θu : ℝ := (θ + π / 2) / 2 with hθu
  have hθu_lt : θu < π / 2 := by rw [hθu]; linarith [hθ2]
  have hcθ : 0 < Real.cos θu :=
    Real.cos_pos_of_mem_Ioo ⟨by rw [hθu]; linarith [Real.pi_pos], hθu_lt⟩
  have hderA : ∀ m : ℕ,
      (∀ y, 0 < y → HasDerivAt (acoeff α m F) (deriv (acoeff α m F) y) y) ∧
      (∀ y, 0 < y → HasDerivAt (deriv (acoeff α m F))
        (deriv (deriv (acoeff α m F)) y) y) := by
    intro m
    have hc : ContinuousOn (fun t => cmode m F t) (Set.Ioi 0) := hInt.1 m
    have h0 : MeasureTheory.IntegrableOn
        (fun t => cmode m F t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioo 0 1) := hInt.2.1 m
    have hinf : MeasureTheory.IntegrableOn
        (fun t => cmode m F t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1) := hInt.2.2 m
    have hd1 : ∀ y, 0 < y →
        HasDerivAt (Radial.radGreenI α m (fun t => cmode m F t))
          (rgiD1 α m (fun t => cmode m F t) y) y :=
      fun y hy => hasDerivAt_radGreenI hc h0 hinf y hy
    constructor
    · intro y hy
      exact (hd1 y hy).congr_deriv (hd1 y hy).deriv.symm
    · intro y hy
      have heq : deriv (acoeff α m F) =ᶠ[𝓝 y] rgiD1 α m (fun t => cmode m F t) := by
        filter_upwards [isOpen_Ioi.mem_nhds hy] with w hw
        exact (hd1 w hw).deriv
      have hd : DifferentiableAt ℝ (rgiD1 α m (fun t => cmode m F t)) y :=
        rgiD1_differentiableAt hc h0 hinf y hy
      exact ((heq.differentiableAt_iff).mpr hd).hasDerivAt
  -- summability of the majorant and of the mode families
  have hsum_maj : Summable fun m : ℕ => D * majPow m := hmaj D
  have hsum_of : ∀ (E : ℝ) (f : ℕ → ℝ), (∀ m, |f m| ≤ E * majPow m) → Summable f := by
    intro E f hf
    refine Summable.of_norm_bounded (hmaj E) fun m => ?_
    rw [Real.norm_eq_abs]
    exact hf m
  -- the derivative identities
  have hz_sub : Set.Ioo (z / 2) (2 * z) ⊆ Set.Ioi 0 := by
    intro y hy; exact lt_trans (by linarith [hz]) hy.1
  have hθ_sub : Set.Ioo (θ / 2) θu ⊆ Set.Ioi 0 := by
    intro y hy; exact lt_trans (by linarith [hθ]) hy.1
  have hθub : ∀ y ∈ Set.Ioo (θ / 2) θu, y ≤ θu := fun y hy => le_of_lt hy.2
  have hθle : θ ≤ (θ + π / 2) / 2 := by linarith [hθ2]
  have hZ1 : ∀ y ∈ Set.Ioo (z / 2) (2 * z),
      HasDerivAt (fun y' => psiSeries α F y' θ)
        (∑' m : ℕ, deriv (acoeff α m F) y * Gegenbauer.eFam m θ) y := by
    intro y hy
    have hmain : HasDerivAt
        (fun y' => ∑' m : ℕ, acoeff α m F y' * Gegenbauer.eFam m θ)
        (∑' m : ℕ, deriv (acoeff α m F) y * Gegenbauer.eFam m θ) y := by
      refine hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℝ)
        (u := fun m => D * majPow m)
        (g := fun m y' => acoeff α m F y' * Gegenbauer.eFam m θ)
        (g' := fun m y' => deriv (acoeff α m F) y' * Gegenbauer.eFam m θ)
        hsum_maj isOpen_Ioo isPreconnected_Ioo ?_ ?_
        (y₀ := z) ⟨by linarith [hz], by linarith [hz]⟩ ?_ hy
      · intro m y' hy'
        exact ((hderA m).1 y' (hz_sub hy')).mul_const (Gegenbauer.eFam m θ)
      · intro m y' hy'
        rw [Real.norm_eq_abs, abs_mul]
        exact hB1 m y' (hz_sub hy')
      · exact hsum_of D _ (fun m => by rw [abs_mul]; exact hB0 m z hz)
    have heq : (fun y' => psiSeries α F y' θ)
        = fun y' => ∑' m : ℕ, acoeff α m F y' * Gegenbauer.eFam m θ := rfl
    rw [heq]
    exact hmain
  have hZ2 : ∀ y ∈ Set.Ioo (z / 2) (2 * z),
      HasDerivAt (fun y' => ∑' m : ℕ,
          deriv (acoeff α m F) y' * Gegenbauer.eFam m θ)
        (∑' m : ℕ, deriv (deriv (acoeff α m F)) y
          * Gegenbauer.eFam m θ) y := by
    intro y hy
    refine hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℝ)
      (u := fun m => D * majPow m)
      (g := fun m y' => deriv (acoeff α m F) y' * Gegenbauer.eFam m θ)
      (g' := fun m y' => deriv (deriv (acoeff α m F)) y'
        * Gegenbauer.eFam m θ)
      hsum_maj isOpen_Ioo isPreconnected_Ioo ?_ ?_
      (y₀ := z) ⟨by linarith [hz], by linarith [hz]⟩ ?_ hy
    · intro m y' hy'
      exact ((hderA m).2 y' (hz_sub hy')).mul_const (Gegenbauer.eFam m θ)
    · intro m y' hy'
      rw [Real.norm_eq_abs, abs_mul]
      exact hB2 m y' (hz_sub hy')
    · exact hsum_of D _ (fun m => by rw [abs_mul]; exact hB1 m z hz)
  have hT1 : ∀ y ∈ Set.Ioo (θ / 2) θu,
      HasDerivAt (fun y' => psiSeries α F z y')
        (∑' m : ℕ, acoeff α m F z * deriv (Gegenbauer.eFam m) y) y := by
    intro y hy
    have hmain : HasDerivAt
        (fun y' => ∑' m : ℕ, acoeff α m F z * Gegenbauer.eFam m y')
        (∑' m : ℕ, acoeff α m F z * deriv (Gegenbauer.eFam m) y) y := by
      refine hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℝ)
        (u := fun m => D * majPow m)
        (g := fun m y' => acoeff α m F z * Gegenbauer.eFam m y')
        (g' := fun m y' => acoeff α m F z * deriv (Gegenbauer.eFam m) y')
        hsum_maj isOpen_Ioo isPreconnected_Ioo ?_ ?_
        (y₀ := θ) ⟨by linarith [hθ], by rw [hθu]; linarith [hθ2]⟩ ?_ hy
      · intro m y' hy'
        have hd : HasDerivAt (fun θ' => Gegenbauer.eFam m θ')
            (deriv (Gegenbauer.eFam m) y') y' :=
          ((contDiff_eFam m).differentiable (by norm_num)).differentiableAt.hasDerivAt
        exact hd.const_mul _
      · intro m y' hy'
        rw [Real.norm_eq_abs, abs_mul]
        exact hB3 m y' (hθ_sub hy') (hθub y' hy')
      · exact hsum_of D _ (fun m => by rw [abs_mul]; exact hB0 m z hz)
    have heq : (fun y' => psiSeries α F z y')
        = fun y' => ∑' m : ℕ, acoeff α m F z * Gegenbauer.eFam m y' := rfl
    rw [heq]
    exact hmain
  have hT2 : ∀ y ∈ Set.Ioo (θ / 2) θu,
      HasDerivAt (fun y' => ∑' m : ℕ,
          acoeff α m F z * deriv (Gegenbauer.eFam m) y')
        (∑' m : ℕ, acoeff α m F z * iteratedDeriv 2 (Gegenbauer.eFam m) y) y := by
    intro y hy
    refine hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℝ)
      (u := fun m => D * majPow m)
      (g := fun m y' => acoeff α m F z * deriv (Gegenbauer.eFam m) y')
      (g' := fun m y' => acoeff α m F z
        * iteratedDeriv 2 (Gegenbauer.eFam m) y')
      hsum_maj isOpen_Ioo isPreconnected_Ioo ?_ ?_
      (y₀ := θ) ⟨by linarith [hθ], by rw [hθu]; linarith [hθ2]⟩ ?_ hy
    · intro m y' hy'
      have hd : HasDerivAt (fun θ' => deriv (Gegenbauer.eFam m) θ')
          (deriv (deriv (Gegenbauer.eFam m)) y') y' :=
        ((ContDiff.deriv' (n := 2) (contDiff_eFam m)).differentiable
          (by norm_num)).differentiableAt.hasDerivAt
      have h := hd.const_mul (acoeff α m F z)
      simpa only [iteratedDeriv_two_apply, mul_comm] using h
    · intro m y' hy'
      rw [Real.norm_eq_abs, abs_mul]
      exact hB4 m y' (hθ_sub hy') (hθub y' hy')
    · exact hsum_of D _ (fun m => by
        rw [abs_mul]
        exact hB3 m θ (by linarith [hθ]) hθle)
  have hT3 : ∀ y ∈ Set.Ioo (θ / 2) θu,
      HasDerivAt (fun y' => ∑' m : ℕ,
          Real.tan y' * (acoeff α m F z * Gegenbauer.eFam m y'))
        (∑' m : ℕ, acoeff α m F z
          * deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') y) y := by
    intro y hy
    have hy0 : 0 < y := hθ_sub hy
    refine hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℝ)
      (u := fun m => D * majPow m)
      (g := fun m y' => Real.tan y' * (acoeff α m F z
        * Gegenbauer.eFam m y'))
      (g' := fun m y' => acoeff α m F z
        * deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') y')
      hsum_maj isOpen_Ioo isPreconnected_Ioo ?_ ?_
      (y₀ := θ) ⟨by linarith [hθ], by rw [hθu]; linarith [hθ2]⟩ ?_ hy
    · intro m y' hy'
      have hy0' : 0 < y' := hθ_sub hy'
      have hne' : Real.cos y' ≠ 0 := ne_of_gt (lt_of_lt_of_le hcθ
        (Real.cos_le_cos_of_nonneg_of_le_pi (le_of_lt hy0') (by linarith [Real.pi_pos, hθ2])
          (le_of_lt hy'.2)))
      have htan : HasDerivAt Real.tan (1 / Real.cos y' ^ 2) y' := Real.hasDerivAt_tan hne'
      have he : HasDerivAt (fun θ' => Gegenbauer.eFam m θ') (deriv (Gegenbauer.eFam m) y') y' :=
        ((contDiff_eFam m).differentiable (by norm_num)).differentiableAt.hasDerivAt
      have hdd : HasDerivAt (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ')
          (deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') y') y' :=
        (htan.mul he).differentiableAt.hasDerivAt
      have h := hdd.const_mul (acoeff α m F z)
      simpa only [mul_assoc, mul_comm, mul_left_comm] using h
    · intro m y' hy'
      rw [Real.norm_eq_abs, abs_mul]
      exact hB5 m y' (hθ_sub hy') (hθub y' hy')
    · refine hsum_of (|Real.tan θ| * D + 1) _ (fun m => ?_)
      rw [abs_mul, abs_mul]
      calc |Real.tan θ| * (|acoeff α m F z| * |Gegenbauer.eFam m θ|)
          ≤ |Real.tan θ| * (D * majPow m) :=
            mul_le_mul_of_nonneg_left (hB0 m z hz) (abs_nonneg _)
        _ ≤ (|Real.tan θ| * D + 1) * majPow m := by
            have h := majPow_nonneg m
            nlinarith [abs_nonneg (Real.tan θ)]
  have hzt' : z ∈ Set.Ioo (z / 2) (2 * z) := ⟨by linarith [hz], by linarith [hz]⟩
  have hθt' : θ ∈ Set.Ioo (θ / 2) θu := ⟨by linarith [hθ], by rw [hθu]; linarith [hθ2]⟩
  have hPz : Spaces.pz (fun z θ => psiSeries α F z θ) z θ
      = ∑' m : ℕ, deriv (acoeff α m F) z * Gegenbauer.eFam m θ :=
    (hZ1 z hzt').deriv
  have hPz2 : Spaces.pzIter 2 (fun z θ => psiSeries α F z θ) z θ
      = ∑' m : ℕ, deriv (deriv (acoeff α m F)) z * Gegenbauer.eFam m θ := by
    have hderiv : deriv (fun y => deriv (fun y' => psiSeries α F y' θ) y) z
        = deriv (fun y => ∑' m : ℕ,
            deriv (acoeff α m F) y * Gegenbauer.eFam m θ) z := by
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [isOpen_Ioo.mem_nhds hzt'] with y hy
      exact (hZ1 y hy).deriv
    show deriv (fun y => deriv (fun y' => psiSeries α F y' θ) y) z = _
    rw [hderiv]
    exact (hZ2 z hzt').deriv
  have hPt : Spaces.pth (fun z θ => psiSeries α F z θ) z θ
      = ∑' m : ℕ, acoeff α m F z * deriv (Gegenbauer.eFam m) θ :=
    (hT1 θ hθt').deriv
  have hPt2 : Spaces.pthIter 2 (fun z θ => psiSeries α F z θ) z θ
      = ∑' m : ℕ, acoeff α m F z * iteratedDeriv 2 (Gegenbauer.eFam m) θ := by
    have hderiv : deriv (fun y => deriv (fun y' => psiSeries α F z y') y) θ
        = deriv (fun y => ∑' m : ℕ,
            acoeff α m F z * deriv (Gegenbauer.eFam m) y) θ := by
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [isOpen_Ioo.mem_nhds hθt'] with y hy
      exact (hT1 y hy).deriv
    show deriv (fun y => deriv (fun y' => psiSeries α F z y') y) θ = _
    rw [hderiv]
    exact (hT2 θ hθt').deriv
  have hPtan : Spaces.pth (fun z' θ' => Real.tan θ' * psiSeries α F z' θ') z θ
      = ∑' m : ℕ, acoeff α m F z
          * deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') θ := by
    have hfun : (fun θ' => Real.tan θ' * psiSeries α F z θ')
        = fun θ' => ∑' m : ℕ,
            Real.tan θ' * (acoeff α m F z * Gegenbauer.eFam m θ') := by
      funext θ'
      rw [show psiSeries α F z θ'
          = ∑' m : ℕ, acoeff α m F z * Gegenbauer.eFam m θ' from rfl]
      exact (tsum_mul_left (a := Real.tan θ')
        (f := fun m : ℕ => acoeff α m F z * Gegenbauer.eFam m θ')).symm
    show deriv (fun θ' => Real.tan θ' * psiSeries α F z θ') θ = _
    rw [hfun]
    exact (hT3 θ hθt').deriv
  have hLzero : Elliptic.Lzero (fun z θ => psiSeries α F z θ) z θ
      = -Spaces.pthIter 2 (fun z θ => psiSeries α F z θ) z θ
        + Spaces.pth (fun z' θ' => Real.tan θ' * psiSeries α F z' θ') z θ
        - 6 * psiSeries α F z θ := by
    rw [Elliptic.Lzero_eq_deriv]
    rfl
  exact ⟨hPz, hPz2, hPt, hPt2, hPtan, hLzero⟩

end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.radial_identity =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeI1Fts

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "χ" => Work.FTS.EllipticEst.cut
local notation "ψ" => Work.FTS.EllipticEst.SliceMixedAux.cut



end

end Work.FTS.EllipticEst.AeI1Fts
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.radial_identity2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeI1Fts


end Work.FTS.EllipticEst.AeI1Fts
end
-- ===== merged: Submission.Work.FTS.GalFields.Norm.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.GalFields

open Work.FTS.Nonlin (RegQ GalClass CoerAdm UnifIP GalBasis Xn PsiCan)
open Work.FTS.Galerkin (Fn Fam galFun)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The `ℋ⁴`-size of `D_zg` is controlled by the `ℋ⁵`-size of `g`.** -/
theorem Xn_Dz_le_Xn5 {α : ℝ} (hα : 0 < α) {g : Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen g) (h : Work.Spaces.HkMem α 5 g) :
    Xn α (Work.Spaces.Dz g) ≤ Xn5 α g :=
  Real.sqrt_le_sqrt
    (Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm α 4
      (Work.FTS.StrongPersist.q0Sm_of_smoothOpen hsm 5) h)

/-- **The `ℋ⁴`-size of `D_θg` is controlled by the `ℋ⁵`-size of `g`.** -/
theorem Xn_Dth_le_Xn5 {α : ℝ} (hα : 0 < α) {g : Fn} (h : Work.Spaces.HkMem α 5 g) :
    Xn α (Work.Spaces.Dth g) ≤ Xn5 α g :=
  Real.sqrt_le_sqrt (Work.FTS.CoercivityStep.Norm.HkSq_Dth_le α hα 4 h)

end Work.FTS.GalFields
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.B4SepId =====
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

set_option autoImplicit false

open Work.FTS.StrongPersist.H6Pair6Aux (NA1 NA4 NA5 NA6 NP3 NP4a NP4b NP5a NP5b NP6)

/-- `Zop F_* = H` on `(0,∞)`: the radial factor of `D_zF_*` is the `Zop`-derivative of the
fundamental radial profile. -/
theorem Zop_Fstar_eq_Hz {z : ℝ} (hz : 0 < z) :
    Work.Spaces.Zop Work.FM.Fstar z = Work.FTS.Nonlinear.FstarPkg.Hz z := by
  rw [Work.Spaces.Zop, Work.FM.deriv_Fstar z (by linarith)]
  simp only [Work.FTS.Nonlinear.FstarPkg.Hz]
  field_simp <;> ring

/-- `VfsRadZ` is `H` on `(0,∞)`. -/
theorem VfsRadZ_eq_Hz {z : ℝ} (hz : 0 < z) :
    Work.FTS.StrongPersist.L3Rhs.VfsRadZ z = Work.FTS.Nonlinear.FstarPkg.Hz z := by
  have h : Work.FTS.StrongPersist.L3Rhs.VfsRadZ z
      = Work.Spaces.Zop Work.FM.Fstar z := rfl
  rw [h, Zop_Fstar_eq_Hz hz]

/-- **The separated form of `NP4a` on the open quadrant.** -/
theorem NP4a_eq_sep4 {α : ℝ} (hα : 0 < α) (w : ℝ → ℝ → ℝ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      NP4a α w z θ = Work.FTS.StrongPersist.L3Rhs.VfsA1 α θ
        * (Work.FTS.StrongPersist.L3Rhs.VfsRad z * Work.Construction.L12 w z) := by
  intro z θ _ _ _
  simp only [NP4a, NA4, Work.Spaces.Dth, Work.FTS.StrongPersist.L3Rhs.VfsA1,
    Work.Spaces.dthU]
  rw [Work.FTS.StrongPersist.L3Rhs.pth_Fstar_sep]
  have hαne : α ≠ 0 := ne_of_gt hα
  field_simp <;> ring

/-- **The separated form of `NP5a` on the open quadrant.** -/
theorem NP5a_eq_sep4 {α : ℝ} (w : ℝ → ℝ → ℝ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      NP5a α w z θ = Work.FTS.StrongPersist.L3Rhs.VfsA2 α θ
        * (Work.FTS.Nonlinear.FstarPkg.Hz z * Work.Construction.L12 w z) := by
  intro z θ hz _ _
  rw [NP5a, NA5, Work.FTS.StrongPersist.L3Rhs.Dz_Fstar_sep, VfsRadZ_eq_Hz hz]
  simp only [Work.FTS.StrongPersist.L3Rhs.VfsA2]
  ring

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.EnergyIP4 =====
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
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.H1IP_upper_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

theorem H1IP_upper_open {α : ℝ} {f : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 1 f)
    (hef : Work.Coercivity.Ef f ≤ Work.Coercivity.EfEta f) :
    Work.Coercivity.H1IP α f f ≤ (10 : ℝ) ^ 22 * Work.Spaces.HkSq α 1 f := by
  -- `sin(2θ) ≥ 0` on the angular interval, so the angular weights are nonnegative.
  have hsin : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    simp only [Work.Spaces.Iθ, mem_Icc] at hθ
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  -- The `ℋ¹` norm is the sum of three of the four inner-product terms (open class).
  have hshape : Work.Spaces.HkSq α 1 f
      = Work.Coercivity.EfEta f + Work.Coercivity.EDz f + Work.Coercivity.EDth α f :=
    Work.FTS.StrongPersist.HkSq_one_eq_SO α hs hm
  -- The unweighted term is dominated by the `η`-weighted one.
  have hle3 : Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) f f
      ≤ Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) f f := by
    rw [← Work.Coercivity.Ef_eq_wip f, ← Work.Coercivity.EfEta_eq_wip f]
    exact hef
  -- Nonnegativity of the three `wip`-terms that make up `HkSq α 1 f`.
  have hA : 0 ≤ Work.Coercivity.wip
      (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      (Work.Spaces.Dz f) (Work.Spaces.Dz f) :=
    Work.Coercivity.wip_self_nonneg
      (fun z θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin θ hθ) _))
  have hB : 0 ≤ Work.Coercivity.wip
      (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) f f :=
    Work.Coercivity.wip_self_nonneg
      (fun z θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin θ hθ) _))
  have hD : 0 ≤ Work.Coercivity.wip
      (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (Work.Spaces.Dth f) (Work.Spaces.Dth f) :=
    Work.Coercivity.wip_self_nonneg
      (fun z θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin θ hθ) _))
  rw [hshape, Work.Coercivity.EDz_eq_wip f, Work.Coercivity.EDth_eq_wip α f,
    Work.Coercivity.EfEta_eq_wip f]
  unfold Work.Coercivity.H1IP
  linarith [hle3, hA, hB, hD]

end Work.FTS.StrongEps.EpsE4Thr
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.LedgerO =====
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

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The ledger**: the four slot estimates, rescaled by the coefficients of `H1IP`, dominate
the `ℋ¹`-energy. -/
theorem ledger_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14) {f : Fn}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm1 : Work.Spaces.HkMem α 1 f)
    (hED : Work.Coercivity.EDthW f ≤ Work.Coercivity.EDth α f)
    (hEL : Work.Coercivity.EL12z f ≤ 16 * Work.Coercivity.Ef f)
    (hP : (1 / 5) * Work.Coercivity.EDz f - 100 * Work.Coercivity.EfEta f
        - 100 * Work.Coercivity.EDth α f - 10 ^ 12 * Work.Coercivity.Ef f
      ≤ Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          (Work.Spaces.Dz (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dz f))
    (hQ : (1 / 5) * Work.Coercivity.EfEta f
        - 100000 * (Work.Coercivity.EL12z f + Work.Coercivity.EDthW f + Work.Coercivity.Ef f)
      ≤ Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          (Work.Coercivity.LGammaT α f) f)
    (hR : (1 / 5) * Work.Coercivity.Ef f - 1000 * Work.Coercivity.EDthW f
      ≤ Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
          (Work.Coercivity.LGammaT α f) f)
    (hS : (17 / 40 - 1 / 100) * Work.Coercivity.EDth α f
        - (1 / 10 ^ 6) * Work.Coercivity.Ef f
      ≤ Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          (Work.Spaces.Dth (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dth f)) :
    Work.Spaces.HkSq α 1 f ≤ Work.Coercivity.H1IP α (Work.Coercivity.LGammaT α f) f := by
  have hHk' := Work.FTS.StrongPersist.HkSq_one_eq_SO α hso hm1
  have hHk : Work.Spaces.HkSq α 1 f
      = Work.Coercivity.EDz f + Work.Coercivity.EfEta f + Work.Coercivity.EDth α f := by
    rw [hHk']; ring
  rw [hHk, Work.Coercivity.H1IP]
  -- the four slot bounds, rescaled by the coefficients of `H1IP`
  have h1 : (2 : ℝ) * Work.Coercivity.EDz f - 1000 * Work.Coercivity.EfEta f
        - 1000 * Work.Coercivity.EDth α f - 10 ^ 13 * Work.Coercivity.Ef f
      ≤ 10 * Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          (Work.Spaces.Dz (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dz f) := by
    have := mul_le_mul_of_nonneg_left hP (show (0 : ℝ) ≤ 10 by norm_num)
    linarith [this]
  have h2 : 2 * 10 ^ 9 * Work.Coercivity.EfEta f
        - 17 * 10 ^ 15 * Work.Coercivity.Ef f - 10 ^ 15 * Work.Coercivity.EDth α f
      ≤ (10 : ℝ) ^ 10 * Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          (Work.Coercivity.LGammaT α f) f := by
    have hb := mul_le_mul_of_nonneg_left hQ (show (0 : ℝ) ≤ (10 : ℝ) ^ 10 by norm_num)
    have hEL' : (10 : ℝ) ^ 15 * Work.Coercivity.EL12z f
        ≤ 16 * 10 ^ 15 * Work.Coercivity.Ef f := by
      have := mul_le_mul_of_nonneg_left hEL (show (0 : ℝ) ≤ (10 : ℝ) ^ 15 by norm_num)
      linarith [this]
    have hED' : (10 : ℝ) ^ 15 * Work.Coercivity.EDthW f
        ≤ (10 : ℝ) ^ 15 * Work.Coercivity.EDth α f :=
      mul_le_mul_of_nonneg_left hED (by norm_num)
    have hEfnn : 0 ≤ Work.Coercivity.Ef f := by
      rw [Work.FTS.CoercivityFix.Coer1.Ef_eq_EnOne]; exact Work.FTS.CoercivityFix.Coer1.EnOne_nonneg f
    linarith [hb, hEL', hED', hEfnn]
  have h3 : 2 * 10 ^ 16 * Work.Coercivity.Ef f - 10 ^ 20 * Work.Coercivity.EDth α f
      ≤ (10 : ℝ) ^ 17 * Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
          (Work.Coercivity.LGammaT α f) f := by
    have hb := mul_le_mul_of_nonneg_left hR (show (0 : ℝ) ≤ (10 : ℝ) ^ 17 by norm_num)
    have hED' : (10 : ℝ) ^ 20 * Work.Coercivity.EDthW f
        ≤ (10 : ℝ) ^ 20 * Work.Coercivity.EDth α f :=
      mul_le_mul_of_nonneg_left hED (by norm_num)
    linarith [hb, hED']
  have h4 : ((17 / 40 - 1 / 100) * 10 ^ 21) * Work.Coercivity.EDth α f
        - 10 ^ 15 * Work.Coercivity.Ef f
      ≤ (10 : ℝ) ^ 21 * Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          (Work.Spaces.Dth (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dth f) := by
    have hb := mul_le_mul_of_nonneg_left hS (show (0 : ℝ) ≤ (10 : ℝ) ^ 21 by norm_num)
    linarith [hb]
  have e1 : 0 ≤ Work.Coercivity.EDz f := by
    rw [Work.FTS.CoercivityFix.Coer1.EDz_eq_En]; exact Work.FTS.CoercivityFix.Coer1.En_nonneg _ _
  have e2 : 0 ≤ Work.Coercivity.EfEta f := by
    rw [Work.FTS.CoercivityFix.Coer1.EfEta_eq_En]; exact Work.FTS.CoercivityFix.Coer1.En_nonneg _ _
  have e3 : 0 ≤ Work.Coercivity.Ef f := by
    rw [Work.FTS.CoercivityFix.Coer1.Ef_eq_EnOne]; exact Work.FTS.CoercivityFix.Coer1.EnOne_nonneg f
  have e4 : 0 ≤ Work.Coercivity.EDth α f := by
    rw [Work.FTS.CoercivityFix.Coer1.EDth_eq_En]; exact Work.FTS.CoercivityFix.Coer1.En_nonneg _ _
  linarith [h1, h2, h3, h4, e1, e2, e3, e4]

end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.LoFourOpen =====
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

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "IP4" => Work.FTS.CoercivityFix.Assembly.IP4

/-! ## The recursion step on the open class -/

/-- **One step of the lower comparison, on the open class** (the `RegQo` analogue of
`V_bounds.lo_step`).  If the level-`n` pairing dominates `cst·|v|²_{ℋⁿ}` on the open class, then
the level-`n+1` pairing `HkIPStep c₁ c₂ IP` dominates `(cst·min 1 (min c₁ c₂))·|v|²_{ℋ^{n+1}}`
there. -/
theorem lo_step_SO_min {α : ℝ} (hα : 0 < α) {n : ℕ}
    {IP : Fn → Fn → ℝ} {c₁ c₂ cst : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hcst : 0 < cst)
    (h : ∀ v : Fn, Work.FTS.EllipticEst.SmoothOpen v → Work.Spaces.HkMem α (n + 1) v →
      cst * Work.Spaces.HkSq α (n + 1) v ≤ IP v v) :
    ∀ v : Fn, Work.FTS.EllipticEst.SmoothOpen v → Work.Spaces.HkMem α (n + 2) v →
      (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 2) v
        ≤ Work.Coercivity.HkIPStep c₁ c₂ IP v v := by
  intro v hs hm
  obtain ⟨hmv, hmd, hmz⟩ :=
    Work.FTS.CoercivityFix.Transfer.HkMem_descent_Q0Sm α hα (n + 1)
      (Work.FTS.StrongPersist.q0Sm_of_smoothOpen hs (n + 1 + 1)) hm
  have h0 := h v hs hmv
  have h1 := h (Work.Spaces.Dth v) hs.Dth hmd
  have h2 := h (Work.Spaces.Dz v) hs.Dz hmz
  have hsucc := Work.FTS.StrongPersist.HkSq_succ_le_SO (α := α) hα (n + 1) (by omega)
    (Work.FTS.StrongPersist.q0Sm_of_smoothOpen hs (n + 2)) hm
  have hA0 := Work.Spaces.HkSq_nonneg α (n + 1) v
  have hA1 := Work.Spaces.HkSq_nonneg α (n + 1) (Work.Spaces.Dth v)
  have hA2 := Work.Spaces.HkSq_nonneg α (n + 1) (Work.Spaces.Dz v)
  have hm1 : min 1 (min c₁ c₂) ≤ 1 := min_le_left _ _
  have hm2 : min 1 (min c₁ c₂) ≤ c₁ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hm3 : min 1 (min c₁ c₂) ≤ c₂ := le_trans (min_le_right _ _) (min_le_right _ _)
  have hcm : 0 ≤ cst * min 1 (min c₁ c₂) :=
    (mul_pos hcst (lt_min one_pos (lt_min hc₁ hc₂))).le
  have e0 : (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 1) v ≤ IP v v := by
    calc (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 1) v
        ≤ (cst * 1) * Work.Spaces.HkSq α (n + 1) v :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm1 hcst.le) hA0
      _ = cst * Work.Spaces.HkSq α (n + 1) v := by ring
      _ ≤ IP v v := h0
  have e1 : (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dth v)
      ≤ c₁ * IP (Work.Spaces.Dth v) (Work.Spaces.Dth v) := by
    calc (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dth v)
        ≤ (cst * c₁) * Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dth v) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm2 hcst.le) hA1
      _ = c₁ * (cst * Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dth v)) := by ring
      _ ≤ c₁ * IP (Work.Spaces.Dth v) (Work.Spaces.Dth v) :=
          mul_le_mul_of_nonneg_left h1 hc₁.le
  have e2 : (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dz v)
      ≤ c₂ * IP (Work.Spaces.Dz v) (Work.Spaces.Dz v) := by
    calc (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dz v)
        ≤ (cst * c₂) * Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dz v) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm3 hcst.le) hA2
      _ = c₂ * (cst * Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dz v)) := by ring
      _ ≤ c₂ * IP (Work.Spaces.Dz v) (Work.Spaces.Dz v) :=
          mul_le_mul_of_nonneg_left h2 hc₂.le
  have hsum : (cst * min 1 (min c₁ c₂))
        * (Work.Spaces.HkSq α (n + 1) v + Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dth v)
          + Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dz v))
      = (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 1) v
        + (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dth v)
        + (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 1) (Work.Spaces.Dz v) := by
    ring
  rw [Work.Coercivity.HkIPStep]
  have hmain : (cst * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α (n + 2) v
      ≤ IP v v + c₁ * IP (Work.Spaces.Dth v) (Work.Spaces.Dth v)
        + c₂ * IP (Work.Spaces.Dz v) (Work.Spaces.Dz v) := by
    refine le_trans (mul_le_mul_of_nonneg_left hsucc hcm) ?_
    rw [hsum]; linarith [e0, e1, e2]
  exact hmain

/-! ## The level-four lower comparison -/

/-- **The `lo` clause of the level-four coercivity on the open class** — the open analogue of
`V_bounds.lo_four`: for arbitrary *positive* coefficients, the squared `ℋ⁴`-norm of a `RegQo α 4`
profile is dominated by the diagonal of `IP4`. -/
theorem lo_four_open {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ}
    (h₁ : 0 < c₁) (h₂ : 0 < c₂) (h₁' : 0 < c₁') (h₂' : 0 < c₂')
    (h₁'' : 0 < c₁'') (h₂'' : 0 < c₂'') :
    ∃ clo : ℝ, 0 < clo ∧ ∀ (α : ℝ), 0 < α → ∀ f : Fn,
      RegQo α 4 f →
        clo * Work.Spaces.HkSq α 4 f
          ≤ IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f f := by
  refine ⟨((1 * min 1 (min c₁ c₂)) * min 1 (min c₁' c₂')) * min 1 (min c₁'' c₂''),
    mul_pos (mul_pos (mul_pos one_pos (lt_min one_pos (lt_min h₁ h₂)))
      (lt_min one_pos (lt_min h₁' h₂'))) (lt_min one_pos (lt_min h₁'' h₂'')), ?_⟩
  intro α hα f hf
  have b1 : ∀ g : Fn, Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 1 g →
      (1 : ℝ) * Work.Spaces.HkSq α 1 g ≤ Work.Coercivity.H1IP α g g :=
    fun g hg hmg => by simpa using Work.FTS.StrongPersist.H1IP_le_self_SO hg hmg
  have b2 : ∀ g : Fn, Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 2 g →
      (1 * min 1 (min c₁ c₂)) * Work.Spaces.HkSq α 2 g
        ≤ Work.Coercivity.HkIPStep c₁ c₂ (Work.Coercivity.H1IP α) g g :=
    lo_step_SO_min (n := 0) hα h₁ h₂ one_pos b1
  have b3 : ∀ g : Fn, Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 3 g →
      ((1 * min 1 (min c₁ c₂)) * min 1 (min c₁' c₂')) * Work.Spaces.HkSq α 3 g
        ≤ Work.Coercivity.HkIPStep c₁' c₂'
            (Work.Coercivity.HkIPStep c₁ c₂ (Work.Coercivity.H1IP α)) g g :=
    lo_step_SO_min (n := 1) hα h₁' h₂'
      (mul_pos one_pos (lt_min one_pos (lt_min h₁ h₂))) b2
  have b4 : ∀ g : Fn, Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      (((1 * min 1 (min c₁ c₂)) * min 1 (min c₁' c₂')) * min 1 (min c₁'' c₂''))
          * Work.Spaces.HkSq α 4 g
        ≤ Work.Coercivity.HkIPStep c₁'' c₂''
            (Work.Coercivity.HkIPStep c₁' c₂'
              (Work.Coercivity.HkIPStep c₁ c₂ (Work.Coercivity.H1IP α))) g g :=
    lo_step_SO_min (n := 2) hα h₁'' h₂''
      (mul_pos (mul_pos one_pos (lt_min one_pos (lt_min h₁ h₂)))
        (lt_min one_pos (lt_min h₁' h₂'))) b3
  have h := b4 f hf.1 hf.2.1
  simpa only [Work.FTS.CoercivityFix.Assembly.IP4] using h

end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.WordCongr =====
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

/-- **`wip` only sees its two profiles on the open quadrant** (first argument). -/
theorem wip_congr_Q0_fst {ρ A A' B : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → A z θ = A' z θ) :
    Work.Coercivity.wip ρ A B = Work.Coercivity.wip ρ A' B :=
  Work.FTS.CoercivityStep.Base.wip_congr_Qd h

/-- **`wip` only sees its two profiles on the open quadrant** (second argument), from the symmetry
of `wip`. -/
theorem wip_congr_Q0_snd {ρ A B B' : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → B z θ = B' z θ) :
    Work.Coercivity.wip ρ A B = Work.Coercivity.wip ρ A B' := by
  rw [Work.FTS.CoercivityStep.Base.wip_comm ρ A B,
    Work.FTS.CoercivityStep.Base.wip_comm ρ A B']
  exact Work.FTS.CoercivityStep.Base.wip_congr_Qd
    (ρ := ρ) (A := B) (A' := B') (B := A) h

/-- **`wip` only sees its two profiles on the open quadrant** (both arguments). -/
theorem wip_congr_Q0_both {ρ A A' B B' : ℝ → ℝ → ℝ}
    (hA : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → A z θ = A' z θ)
    (hB : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → B z θ = B' z θ) :
    Work.Coercivity.wip ρ A B = Work.Coercivity.wip ρ A' B' := by
  rw [wip_congr_Q0_fst (ρ := ρ) hA, wip_congr_Q0_snd (ρ := ρ) (A := A') hB]

/-- **`H1IP` only sees its two profiles on the open quadrant** (both arguments at once). -/
theorem H1IP_congr_Q0 (α : ℝ) {f f' g g' : ℝ → ℝ → ℝ}
    (hf : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → f z θ = f' z θ)
    (hg : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → g z θ = g' z θ) :
    Work.Coercivity.H1IP α f g = Work.Coercivity.H1IP α f' g' := by
  have hDz := Work.FTS.CoercivityStep.Base.Dz_congr_Qd hf
  have hDz' := Work.FTS.CoercivityStep.Base.Dz_congr_Qd hg
  have hDth := Work.FTS.CoercivityStep.Base.Dth_congr_Qd hf
  have hDth' := Work.FTS.CoercivityStep.Base.Dth_congr_Qd hg
  simp only [Work.Coercivity.H1IP]
  have h1 := wip_congr_Q0_both
    (ρ := fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) hDz hDz'
  have h2 := wip_congr_Q0_both
    (ρ := fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) hf hg
  have h3 := wip_congr_Q0_both (ρ := fun z _ => Work.Spaces.w z ^ 2) hf hg
  have h4 := wip_congr_Q0_both
    (ρ := fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.gam α)) hDth hDth'
  rw [h1, h2, h3, h4]


end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.normSub_SO =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

/-- The three `H^n → H^{n+1}` domination facts for a function which is `C^∞` on the open
quadrant and honestly in `ℋ^{n+1}`.

* the first conjunct is the plain monotonicity of `HkSq` in the regularity index
  (`HkIntegrand` is a sum of squares over a range that grows with `k`);
* the second is the `D_θ`-shift `HkSq α n (D_θ f) ≤ HkSq α (n+1) f`: the `(n)`-summands of
  `D_θ f` become mixed summands of `f` at level `n+1` with the heavier weight `W`;
* the third is the `D_z`-shift `HkSq α n (D_z f) ≤ HkSq α (n+1) f`, which is only needed on
  the open quadrant and hence only requires `SmoothOpen f` (via `Q0Sm (n+1) f`). -/
theorem normSub_SO {α : ℝ} {n : ℕ} {f : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α (n + 1) f) :
    Work.Spaces.HkSq α n f ≤ Work.Spaces.HkSq α (n + 1) f ∧
      Work.Spaces.HkSq α n (Work.Spaces.Dth f) ≤ Work.Spaces.HkSq α (n + 1) f ∧
      Work.Spaces.HkSq α n (Work.Spaces.Dz f) ≤ Work.Spaces.HkSq α (n + 1) f :=
  ⟨Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (Nat.le_succ n) hm,
    Work.FTS.CoercivityStep.Norm.HkSq_Dth_le α hα n hm,
    Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm α n
      (Work.FTS.StrongPersist.q0Sm_of_smoothOpen hs (n + 1)) hm⟩

end Work.FTS.StrongEps.EpsE4Thr
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.IPChains =====
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
open Work.FTS.CoercivityFix.Transfer (CommSm CSQ CommSm_L1 CommSm_succ CSQ_one CSQ_succ)

set_option autoImplicit false

/-- **Additivity of the `n`-fold pairing.**  `CommSm α (n+1) (IPnG 1 1 α n)`, i.e. `IPnG 1 1 α n`
is additive on `C^{n+1}`-on-the-open-quadrant arguments in `ℋ^{n+1}`, for every `n`. -/
theorem commSm_IPnG (α : ℝ) (hα : 0 < α) (n : ℕ) :
    CommSm α (n + 1) (IPnG 1 1 α n) := by
  induction n with
  | zero => exact CommSm_L1 α hα
  | succ n ih =>
      have h := CommSm_succ α hα (n + 1) (c₁ := (1 : ℝ)) (c₂ := (1 : ℝ)) ih
      have he : Work.Coercivity.HkIPStep 1 1 (IPnG 1 1 α n) = IPnG 1 1 α (n + 1) := by
        rw [← IPnG_succ]
      rwa [he] at h


/-- **The slot cover of the `n`-fold pairing.**  `HkSq α (n+1) f ≤ IPnG 1 1 α n f f` for every
`f` smooth on the open quadrant with honest `ℋ^{n+1}`-integral. -/
theorem lo_IPnG (α : ℝ) (hα : 0 < α) (n : ℕ) :
    ∀ f : Fn, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α (n + 1) f →
      Work.Spaces.HkSq α (n + 1) f ≤ IPnG 1 1 α n f f := by
  induction n with
  | zero =>
      intro f hs hm
      simpa only [IPnG_zero] using Work.FTS.StrongPersist.H1IP_le_self_SO (α := α) hs hm
  | succ n ih =>
      have h := Work.FTS.StrongPersist.lo_step_SO (α := α) hα (k := n + 1) (IP := IPnG 1 1 α n)
        (c₁ := (1 : ℝ)) (c₂ := (1 : ℝ)) (by omega) le_rfl le_rfl ih
      intro f hs hm
      have he : Work.Coercivity.HkIPStep 1 1 (IPnG 1 1 α n) = IPnG 1 1 α (n + 1) := by
        rw [← IPnG_succ]
      rw [← he]
      exact h f hs hm

/-! ## The uniform-in-`α` versions -/

/-- **Cauchy–Schwarz for the `n`-fold pairing, uniformly in `α ∈ (0,1]`.** -/
theorem CSQ_IPnG_unif (n : ℕ) :
    ∃ CC : ℝ, 0 < CC ∧ ∀ α ∈ Set.Ioc 0 1, CSQ α (n + 1) (IPnG 1 1 α n) CC := by
  induction n with
  | zero =>
      refine ⟨(10 : ℝ) ^ 22, by norm_num, fun α hα => ?_⟩
      exact fun X Y _ _ hX hY =>
        Work.FTS.CoercivityFix.Transfer.H1IP_cs_of_mem α hα.1 X Y hX hY
  | succ n ih =>
      obtain ⟨CC, hCC, h⟩ := ih
      refine ⟨3 * max 1 (max 1 1) * CC, by positivity, fun α hα => ?_⟩
      have hstep := Work.FTS.CoercivityFix.Transfer.CSQ_succ α hα.1 (n + 1)
        (c₁ := (1 : ℝ)) (c₂ := (1 : ℝ)) hCC.le zero_le_one zero_le_one (h α hα)
      rwa [show Work.Coercivity.HkIPStep 1 1 (IPnG 1 1 α n) = IPnG 1 1 α (n + 1) from by
        rw [← IPnG_succ]] at hstep

end Work.FTS.StrongPersist.H6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.RadialSlots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

theorem slots_radial_mul {X r : ℝ → ℝ} {M : ℝ}
    (hX : ContDiffOn ℝ 6 X (Set.Ioi 0)) (hr : ContDiffOn ℝ 6 r (Set.Ioi 0))
    (hXint : ∀ b : ℕ, b ≤ 6 → MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter b X z * Work.Spaces.w z) ^ 2) Work.Spaces.Iz)
    (hM : ∀ m : ℕ, m ≤ 6 → ∀ z : ℝ, 0 < z → |Work.Elliptic.DzdIter m r z| ≤ M) :
    ∀ j : ℕ, j ≤ 6 → MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter j (fun z => X z * r z) z * Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz := by
  have hXc : ∀ b ≤ 6, ContinuousOn (fun z : ℝ => Work.Elliptic.DzdIter b X z) (Set.Ioi 0) :=
    fun b hb => (Work.FTS.StrongPersist.L3Rhs.NfkAux.contDiffOn_DzdIter_of_radial (r := X) (n := 6)
      (fun m hm => hX.of_le (by exact_mod_cast hm)) (a := b) (t := 0) (by omega)).continuousOn
  have hrc : ∀ b ≤ 6, ContinuousOn (fun z : ℝ => Work.Elliptic.DzdIter b r z) (Set.Ioi 0) :=
    fun b hb => (Work.FTS.StrongPersist.L3Rhs.NfkAux.contDiffOn_DzdIter_of_radial (r := r) (n := 6)
      (fun m hm => hr.of_le (by exact_mod_cast hm)) (a := b) (t := 0) (by omega)).continuousOn
  have hwc : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
    simp only [Work.Spaces.w]
    exact ((continuousOn_const.add continuousOn_id).pow 2).div (continuousOn_id.pow 2)
      (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
  intro j hj
  -- the Leibniz identity on `(0,∞)`
  have hleib : ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.DzdIter j (fun z => X z * r z) z
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b X z * Work.Elliptic.DzdIter (j - b) r z) :=
    fun z hz => Work.FTS.StrongPersist.H6Aux.DzdIter_mul_of_diff j X r
      (fun b hb => (Work.FTS.StrongPersist.L3Rhs.NfkAux.contDiffOn_DzdIter_of_radial (r := X)
        (n := 6) (fun m hm => hX.of_le (by exact_mod_cast hm)) (a := b) (t := 1)
        (by omega)).differentiableOn (by norm_num))
      (fun b hb => (Work.FTS.StrongPersist.L3Rhs.NfkAux.contDiffOn_DzdIter_of_radial (r := r)
        (n := 6) (fun m hm => hr.of_le (by exact_mod_cast hm)) (a := b) (t := 1)
        (by omega)).differentiableOn (by norm_num)) z hz
  have hXc : ∀ b ≤ 6, ContinuousOn (fun z : ℝ => Work.Elliptic.DzdIter b X z) (Set.Ioi 0) :=
    fun b hb => (Work.FTS.StrongPersist.L3Rhs.NfkAux.contDiffOn_DzdIter_of_radial (r := X) (n := 6)
      (fun m hm => hX.of_le (by exact_mod_cast hm)) (a := b) (t := 0) (by omega)).continuousOn
  have hrc : ∀ b ≤ 6, ContinuousOn (fun z : ℝ => Work.Elliptic.DzdIter b r z) (Set.Ioi 0) :=
    fun b hb => (Work.FTS.StrongPersist.L3Rhs.NfkAux.contDiffOn_DzdIter_of_radial (r := r) (n := 6)
      (fun m hm => hr.of_le (by exact_mod_cast hm)) (a := b) (t := 0) (by omega)).continuousOn
  have hwc : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
    simp only [Work.Spaces.w]
    exact ((continuousOn_const.add continuousOn_id).pow 2).div (continuousOn_id.pow 2)
      (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
  -- the (continuous) representative of the integrand on `(0,∞)`
  have hcont : ContinuousOn (fun z : ℝ =>
      (Work.Elliptic.DzdIter j (fun z => X z * r z) z * Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    refine ContinuousOn.congr ?_ (fun z hz => by rw [hleib z hz])
    show ContinuousOn (fun z : ℝ => ((∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
      * (Work.Elliptic.DzdIter b X z * Work.Elliptic.DzdIter (j - b) r z))
      * Work.Spaces.w z) ^ 2) (Set.Ioi 0)
    refine ContinuousOn.pow ?_ 2
    refine ContinuousOn.mul (continuousOn_finsetSum _ fun b hb => ?_) hwc
    have hbj : b ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    exact ContinuousOn.mul continuousOn_const
      ((hXc b (by omega)).mul (hrc (j - b) (by omega)))
  -- the majorant
  have hmaj : MeasureTheory.IntegrableOn (fun z : ℝ =>
      (7 * 4096 * M ^ 2 + 1) * ∑ b ∈ Finset.range 7,
        (Work.Elliptic.DzdIter b X z * Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    (MeasureTheory.integrable_finsetSum (Finset.range 7) (fun b hb =>
      hXint b (Nat.le_of_lt_succ (Finset.mem_range.mp hb)))).const_mul _
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => (Work.Elliptic.DzdIter j (fun z => X z * r z) z * Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h1 : MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ => (Work.Elliptic.DzdIter j (fun z => X z * r z) z * Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      hcont.aestronglyMeasurable isOpen_Ioi.measurableSet
    rwa [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))] at h1
  refine hmaj.mono' haesm ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with z hz
  have hz0 : (0 : ℝ) ≤ z := hz
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  rcases eq_or_lt_of_le hz0 with hz00 | hzpos
  · rw [← hz00]
    simp only [Work.Spaces.w]
    norm_num
  · have hkey : ((∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
        * (Work.Elliptic.DzdIter b X z * Work.Elliptic.DzdIter (j - b) r z))
        * Work.Spaces.w z)
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Elliptic.DzdIter (j - b) r z * Work.Spaces.w z)) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [hleib z hzpos, hkey]
    set f : ℕ → ℝ := fun b => (j.choose b : ℝ) * (Work.Elliptic.DzdIter b X z
      * (Work.Elliptic.DzdIter (j - b) r z * Work.Spaces.w z)) with hf
    have hch : ∀ b ∈ Finset.range (j + 1), (((j.choose b : ℕ) : ℝ)) ^ 2 ≤ 4096 := by
      intro b _
      have h1 : (((j.choose b : ℕ) : ℝ)) ≤ 64 := by
        have h2 : j.choose b ≤ 2 ^ j := Nat.choose_le_two_pow j b
        have h3 : 2 ^ j ≤ 64 := by
          calc 2 ^ j ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hj
            _ = 64 := by norm_num
        exact_mod_cast le_trans h2 h3
      have h0 : (0 : ℝ) ≤ (((j.choose b : ℕ) : ℝ)) := by positivity
      nlinarith [h1, h0]
    have hterm : ∀ b ∈ Finset.range (j + 1),
        (f b) ^ 2 ≤ 4096 * M ^ 2 * (Work.Elliptic.DzdIter b X z * Work.Spaces.w z) ^ 2 := by
      intro b hb
      have hM' : (Work.Elliptic.DzdIter (j - b) r z) ^ 2 ≤ M ^ 2 := by
        have h := hM (j - b) (by omega) z hzpos
        have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
        rwa [sq_abs] at h2
      have hstep2 : (((j.choose b : ℕ) : ℝ)) ^ 2
          * ((Work.Elliptic.DzdIter (j - b) r z) ^ 2) ≤ 4096 * M ^ 2 :=
        mul_le_mul (hch b hb) hM' (sq_nonneg _) (by norm_num)
      have hgoal : (f b) ^ 2 = (((j.choose b : ℕ) : ℝ)) ^ 2
          * ((Work.Elliptic.DzdIter (j - b) r z) ^ 2)
          * ((Work.Elliptic.DzdIter b X z * Work.Spaces.w z) ^ 2) := by
        simp only [hf]
        push_cast
        ring
      rw [hgoal]
      exact mul_le_mul_of_nonneg_right hstep2 (sq_nonneg _)
    have hstep : (∑ b ∈ Finset.range (j + 1), (f b) ^ 2)
        ≤ ∑ b ∈ Finset.range (j + 1),
            4096 * M ^ 2 * (Work.Elliptic.DzdIter b X z * Work.Spaces.w z) ^ 2 :=
      Finset.sum_le_sum hterm
    have hstepM : (∑ b ∈ Finset.range (j + 1), (f b) ^ 2)
        ≤ 4096 * M ^ 2 * (∑ b ∈ Finset.range (j + 1),
            (Work.Elliptic.DzdIter b X z * Work.Spaces.w z) ^ 2) := by
      refine hstep.trans (le_of_eq ?_)
      rw [Finset.mul_sum]
    have hsq := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1)) (f := f)
    have hcard : (((Finset.range (j + 1)).card : ℕ) : ℝ) ≤ 7 := by
      rw [Finset.card_range]; exact_mod_cast (by omega : j + 1 ≤ 7)
    have hsum7 : (∑ b ∈ Finset.range (j + 1),
          (Work.Elliptic.DzdIter b X z * Work.Spaces.w z) ^ 2)
        ≤ ∑ b ∈ Finset.range 7, (Work.Elliptic.DzdIter b X z * Work.Spaces.w z) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun b hb => Finset.mem_range.mpr
          (lt_of_lt_of_le (Finset.mem_range.mp hb) (by omega)))
        (fun b _ _ => sq_nonneg _)
    have hnn7 : 0 ≤ ∑ b ∈ Finset.range 7, (Work.Elliptic.DzdIter b X z * Work.Spaces.w z) ^ 2 :=
      Finset.sum_nonneg fun b _ => sq_nonneg _
    have hM2 : (0 : ℝ) ≤ M ^ 2 := sq_nonneg M
    calc (∑ b ∈ Finset.range (j + 1), f b) ^ 2
        ≤ (((Finset.range (j + 1)).card : ℕ) : ℝ) * (∑ b ∈ Finset.range (j + 1), (f b) ^ 2) :=
          hsq
      _ ≤ 7 * (∑ b ∈ Finset.range (j + 1), (f b) ^ 2) :=
          mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg fun b _ => sq_nonneg _)
      _ ≤ 7 * (4096 * M ^ 2 * (∑ b ∈ Finset.range (j + 1),
            (Work.Elliptic.DzdIter b X z * Work.Spaces.w z) ^ 2)) :=
          mul_le_mul_of_nonneg_left hstepM (by norm_num)
      _ ≤ 7 * (4096 * M ^ 2 * (∑ b ∈ Finset.range 7,
            (Work.Elliptic.DzdIter b X z * Work.Spaces.w z) ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsum7 (by positivity)) (by norm_num)
      _ ≤ (7 * 4096 * M ^ 2 + 1) * (∑ b ∈ Finset.range 7,
            (Work.Elliptic.DzdIter b X z * Work.Spaces.w z) ^ 2) := by
          nlinarith [hnn7, hM2]

end Work.FTS.StrongPersist.H6Pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.rowDthWlInf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

set_option maxHeartbeats 1600000

/-- The two angular endpoints of `Iθ` are null. -/
theorem restrict_Iθ_eq_Ioo :
    volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
  Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo

/-- `Iz = [0,∞)` agrees with `(0,∞)` up to a null set. -/
theorem restrict_Iz_eq_Ioi :
    volume.restrict Work.Spaces.Iz = volume.restrict (Set.Ioi (0 : ℝ)) := by
  have h : Set.Ioi (0 : ℝ) =ᵐ[volume] Set.Ici (0 : ℝ) := Ioi_ae_eq_Ici
  simpa [Work.Spaces.Iz] using (MeasureTheory.Measure.restrict_congr_set h).symm


end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.assembly =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Constant multiples of open-quadrant-smooth data -/

/-- A constant multiple of an open-quadrant-smooth datum is open-quadrant-smooth. -/
theorem smoothOpen_const_mul_loc (c : ℝ) {f : Fn}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have h : Function.uncurry (fun z θ => c * f z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry f p := by
    funext p; rfl
  rw [h]
  exact contDiffOn_const.mul (hf.forall n)

/-! ## The four summands of `dynRHS` -/

/-- The modulation summand `-μ̄·AK α` of `dynRHS`. -/
def P1 (α : ℝ) (g Φ : Fam) (τ : ℝ) : Fn :=
  fun z θ => -Work.Construction.mubar
      (Work.Construction.N0 α (Work.Construction.Ftau α g τ) (slice g τ))
      (Work.Construction.N α (Work.Construction.Ftau α g τ) (slice Φ τ))
    * Work.Construction.AK α z θ

/-- The `N₀`-summand of `dynRHS`. -/
def P2 (α : ℝ) (g : Fam) (τ : ℝ) : Fn :=
  Work.Construction.N0 α (Work.Construction.Ftau α g τ) (slice g τ)

/-- The `N`-summand of `dynRHS`. -/
def P3 (α : ℝ) (g Φ : Fam) (τ : ℝ) : Fn :=
  Work.Construction.N α (Work.Construction.Ftau α g τ) (slice Φ τ)

/-- The `N*`-summand of `dynRHS`, at the dynamic modulation constants. -/
def P4 (α : ℝ) (Φ g : Fam) (τ : ℝ) : Fn :=
  Work.Construction.Nstar (Work.FTS.Galerkin.muDyn α Φ g τ)
    (Work.FTS.Galerkin.lamDyn α Φ g τ) (slice g τ)

/-- **`dynRHS` is the four-fold sum of the pieces**, with the association of `gRHS`. -/
theorem dynRHS_eq_sum (α : ℝ) (Φ g : Fam) (τ : ℝ) :
    Work.FTS.Galerkin.dynRHS α Φ g τ
      = fun z θ => ((P1 α g Φ τ z θ + P2 α g τ z θ) + P3 α g Φ τ z θ) + P4 α Φ g τ z θ := rfl

/-- `P4` is the `N*`-form `-μ f - (μ + λ + μλ) D_z f` of the pieces of `nstar_pair_le`. -/
theorem P4_eq (α : ℝ) (Φ g : Fam) (τ : ℝ) :
    P4 α Φ g τ = fun z θ => -(Work.FTS.Galerkin.muDyn α Φ g τ) * slice g τ z θ
      - (Work.FTS.Galerkin.muDyn α Φ g τ + Work.FTS.Galerkin.lamDyn α Φ g τ
          + Work.FTS.Galerkin.muDyn α Φ g τ * Work.FTS.Galerkin.lamDyn α Φ g τ)
        * Work.Spaces.Dz (slice g τ) z θ := rfl

/-! ## Membership of the pieces -/

/-- **Membership of the `N*`-piece.**  `P4 = -μ f - (μ+λ+μλ) D_z f` is `C^∞` on the open
quadrant and `ℋ⁶`, from the smoothness/`ℋ⁶`-membership of `f`, of `D_z f`
(`IPGen.HkMem_Dz_le`, which consumes `HkMem α 7 f`) and the closure under constant multiples. -/
theorem P4_smooth_mem {α : ℝ} {g Φ : Fam} {τ : ℝ}
    (hsmf : Work.FTS.EllipticEst.SmoothOpen (slice g τ))
    (h6 : Work.Spaces.HkMem α 6 (slice g τ))
    (h7 : Work.Spaces.HkMem α 7 (slice g τ)) :
    Work.FTS.EllipticEst.SmoothOpen (P4 α Φ g τ) ∧ Work.Spaces.HkMem α 6 (P4 α Φ g τ) := by
  have he : P4 α Φ g τ = fun z θ =>
      (-(Work.FTS.Galerkin.muDyn α Φ g τ)) * slice g τ z θ
      + (-(Work.FTS.Galerkin.muDyn α Φ g τ + Work.FTS.Galerkin.lamDyn α Φ g τ
          + Work.FTS.Galerkin.muDyn α Φ g τ * Work.FTS.Galerkin.lamDyn α Φ g τ))
        * Work.Spaces.Dz (slice g τ) z θ := by
    funext z θ
    rw [P4_eq]
    ring
  rw [he]
  have hsm1 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-(Work.FTS.Galerkin.muDyn α Φ g τ)) * slice g τ z θ) :=
    smoothOpen_const_mul_loc (-(Work.FTS.Galerkin.muDyn α Φ g τ)) hsmf
  have hsm2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-(Work.FTS.Galerkin.muDyn α Φ g τ + Work.FTS.Galerkin.lamDyn α Φ g τ
          + Work.FTS.Galerkin.muDyn α Φ g τ * Work.FTS.Galerkin.lamDyn α Φ g τ))
        * Work.Spaces.Dz (slice g τ) z θ) :=
    smoothOpen_const_mul_loc _ hsmf.Dz
  have hm1 : Work.Spaces.HkMem α 6
      (fun z θ => (-(Work.FTS.Galerkin.muDyn α Φ g τ)) * slice g τ z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 6 _ h6
  have hm2 : Work.Spaces.HkMem α 6
      (fun z θ => (-(Work.FTS.Galerkin.muDyn α Φ g τ + Work.FTS.Galerkin.lamDyn α Φ g τ
          + Work.FTS.Galerkin.muDyn α Φ g τ * Work.FTS.Galerkin.lamDyn α Φ g τ))
        * Work.Spaces.Dz (slice g τ) z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 6 _ (Work.FTS.IPGen.HkMem_Dz_le hsmf h7)
  exact ⟨smoothOpen_add' hsm1 hsm2, HkMem_add_of_HkMem α 6 hsm1 hsm2 hm1 hm2⟩


/-! ## The right-hand side shape of the rows -/

/-- The right-hand side shared by the four rows and by `H6Pair.pair`:
`(1+|Ce|+|Cs|)⁴ α^{-10} (1+M)⁴ (1 + |f|²_{ℋ⁶})`. -/
def RowRHS (α M Ce Cs : ℝ) (f : Fn) : ℝ :=
  (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f)

theorem RowRHS_nonneg {α M Ce Cs : ℝ} {f : Fn} (hα : 0 < α) : 0 ≤ RowRHS α M Ce Cs f := by
  have h1 : (0 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 := by
    apply pow_nonneg
    have := abs_nonneg Ce; have := abs_nonneg Cs; linarith
  have h2 : (0 : ℝ) ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα.le _
  have h3 : (0 : ℝ) ≤ (1 + M) ^ 4 := by positivity
  have h4 : (0 : ℝ) ≤ 1 + Sq6 α f := by have := Sq6_nonneg α f; linarith
  exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4

/-- The `M`-only version of `RowRHS` (no `ℋ⁶` factor): the shape of the scalar bound on the
modulation constant `μ`. -/
def ScalRHS (α M Ce Cs : ℝ) : ℝ :=
  (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4

theorem ScalRHS_nonneg {α M Ce Cs : ℝ} (hα : 0 < α) : 0 ≤ ScalRHS α M Ce Cs := by
  have h1 : (0 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 := by
    apply pow_nonneg
    have := abs_nonneg Ce; have := abs_nonneg Cs; linarith
  have h2 : (0 : ℝ) ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα.le _
  have h3 : (0 : ℝ) ≤ (1 + M) ^ 4 := by positivity
  exact mul_nonneg (mul_nonneg h1 h2) h3


/-- **The `N*`-coefficient identity at the paper's second modulation constant**:
`|μ + λ(μ) + μ·λ(μ)| = |μ|`.  For `μ ≠ -1` this is `Nonlin.lamfun_add`; for `μ = -1` the value
`lamfun (-1)` is `0` by the totalised division, and the identity is `rfl`-level. -/
theorem abs_add_lamfun (μ : ℝ) :
    |μ + Work.Construction.lamfun μ + μ * Work.Construction.lamfun μ| = |μ| := by
  rcases eq_or_ne μ (-1) with h | h
  · subst h
    have h0 : Work.Construction.lamfun (-1) = 0 := by
      rw [Work.Construction.lamfun]; norm_num
    rw [h0]
    norm_num
  · rw [Work.FTS.Nonlin.lamfun_add h]
    exact abs_neg μ

end Work.FTS.StrongPersist.H6Pair6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.AK6Row =====
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

open Work.FTS.Galerkin (Fn Fam slice dynRHS)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The block `AK α` is `ℋ⁶` with an absolute bound

The `-μ̄·AK α` piece of `dynRHS` is the one piece whose coefficient is a *fixed* function, so
its size is a constant and only the `ℋ⁶`-membership and norm of `AK α` are needed.  `AK α` is
the separable datum `(Γ(θ)/c α)·2z²/(1+z)³`; the radial jets are `AK6/akRho_jet_bound6` and the
angular ones `LocData6.DthIter_Gam_abs_le6`, assembled in `AK6/Sharp6` and `AK6/HkMem_AK6`. -/

/-- `AK α = (Γ(θ)/c α)·(2z²/(1+z)³)` is `C^∞` on the open quadrant (a product of the angular
factor `Γ` — `C^∞` by `row23_smoothOpen_Gam` — and the radial rational profile). -/
theorem AK_smoothO (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.AK α z θ) := by
  have hG : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Work.Spaces.Gam α θ) :=
    Work.FTS.Nonlinear.Open.row23_smoothOpen_Gam α
  have h1 : Work.FTS.EllipticEst.SmoothOpen
      (fun (_ : ℝ) (θ : ℝ) => Work.Spaces.Gam α θ / Work.Spaces.c α) := by
    have he : (fun (_ : ℝ) (θ : ℝ) => Work.Spaces.Gam α θ / Work.Spaces.c α)
        = fun (_ : ℝ) (θ : ℝ) => (1 / Work.Spaces.c α) * Work.Spaces.Gam α θ := by
      funext z θ
      ring
    rw [he]
    exact smoothOpen_const_mul' (1 / Work.Spaces.c α) hG
  have h3 : Work.FTS.EllipticEst.SmoothOpen (fun (z : ℝ) (_ : ℝ) => 2 * z ^ 2 / (1 + z) ^ 3) := by
    refine Work.FTS.Nonlinear.Open.row23_smoothOpen_radial
      (r := fun z : ℝ => 2 * z ^ 2 / (1 + z) ^ 3) (fun n => ?_)
    have he : (fun z : ℝ => 2 * z ^ 2 / (1 + z) ^ 3)
        = fun z : ℝ => 2 * z ^ 2 * ((1 + z) ^ 3)⁻¹ := by
      funext z
      rw [div_eq_mul_inv]
    rw [he]
    refine ContDiffOn.mul (contDiffOn_const.mul (contDiffOn_id.pow 2)) ?_
    refine ((contDiffOn_const.add contDiffOn_id).pow 3).inv (fun z hz => ?_)
    have hz' : (0 : ℝ) < 1 + z := by
      have h := hz
      rw [Set.mem_Ioi] at h
      linarith
    simpa only [id_eq] using pow_ne_zero 3 (ne_of_gt hz')
  have h4 : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (fun z θ =>
        (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)))
      Work.FTS.EllipticEst.Q0 := h1.mul h3
  have heq : (fun z θ => Work.Construction.AK α z θ)
      = fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) := rfl
  rw [heq]
  exact h4

/-- **`AK α ∈ ℋ⁶` with an `α`-uniform norm bound.**  From the radial jet bound `hrad` of
`2z²/(1+z)³` (`akRho_jet_bound6`) and the pointwise domination `AK_integrand_le6`, the
integration criterion `hkSq_le_of_integrand_le6` gives `HkSq α 6 (AK α) ≤ 2(700R·10⁴ +
49·10¹²R·700)`, and `HkMem_AK6` gives the membership. -/
theorem AK6_mem_norm : ∃ K : ℝ, 0 < K ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    Work.Spaces.HkMem α 6 (Work.Construction.AK α) ∧
      Work.Spaces.HkNorm α 6 (Work.Construction.AK α) ≤ K := by
  obtain ⟨R, hR0, hR⟩ := Work.FTS.StrongPersist.AK6.akRho_jet_bound6
  refine ⟨Real.sqrt (2 * (700 * R * 10 ^ 4 + 49 * 10 ^ 12 * R * 700)) + 1,
    by positivity, ?_⟩
  intro α hα hα1
  have hA0 : (0 : ℝ) ≤ 700 * R := by linarith
  have hB0 : (0 : ℝ) ≤ 49 * 10 ^ 12 * R := by linarith
  refine ⟨Work.FTS.StrongPersist.AK6.HkMem_AK6 α hα hα1 hR0 hR, ?_⟩
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (Work.Construction.AK α) z θ
        ≤ (1 / (1 + z) ^ 2) * ((700 * R) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            + (49 * 10 ^ 12 * R) * ((α + Real.sin (2 * θ)) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) :=
    Work.FTS.StrongPersist.AK6.AK_integrand_le6 hR0 hR α hα hα1
  have hsq : Work.Spaces.HkSq α 6 (Work.Construction.AK α)
      ≤ 2 * (700 * R * 10 ^ 4 + 49 * 10 ^ 12 * R * 700) :=
    Work.FTS.StrongPersist.AK6.hkSq_le_of_integrand_le6 (f := Work.Construction.AK α)
      hα hα1 hA0 hB0 hpt
  have hmono : Work.Spaces.HkNorm α 6 (Work.Construction.AK α)
      ≤ Real.sqrt (2 * (700 * R * 10 ^ 4 + 49 * 10 ^ 12 * R * 700)) := Real.sqrt_le_sqrt hsq
  linarith [Real.sqrt_nonneg (2 * (700 * R * 10 ^ 4 + 49 * 10 ^ 12 * R * 700))]



end Work.FTS.StrongPersist
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.contDiffOn6_FK =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

/-- The datum data of the level-six coefficient rows records only *finite-order* smoothness
(`SmoothOpen f` is `C^∞` on the open quadrant) together with `HkMem α 7 f`, so the radial
angular moment `z ↦ FK f z` is `C^6` on the open quadrant: this is exactly
`H6Rows.co6_FK_radial`.  (The `C^∞`-strength statement `SmoothOpen (FK f)` is false for honest
data, see `Npair6BWork/NOTES_coefData_FK_FALSE.md`; order six is the right interface.) -/
theorem contDiffOn6_FK : ∀ α ∈ Set.Ioc 0 1, ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ),
    Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
    ContDiffOn ℝ 6
      (Function.uncurry (fun z _ => Work.Construction.FK f z))
      Work.FTS.EllipticEst.Q0 := by
  intro α hα f M hD
  obtain ⟨hα0, hα1⟩ := Set.mem_Ioc.mp hα
  exact Work.FTS.StrongPersist.H6Rows.co6_FK_radial hα0 hα1 hD.sm hD.h7

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The level-6 `T2` slot: the Leibniz remainder `R` and its bound

`D_z^bD_θ^a(f·D_z g) = f·D_z(D_z^bD_θ^a g) + R`, where `R` collects the Leibniz summands with
at least one derivative on `f` (`SixAux.leibR`).  `leibR_bound` bounds the `canonW q`-weighted
pairing of `R` with `D_z^bD_θ^a g` by `64·(a+1)(b+1)·Λ·|g|²_{ℋ⁶}`, by summing the per-summand
`term_bound`.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixAux

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z canonW_mono)
open Work.FTS.StrongPersist.N6Trans.T1SixAux (SlotW6 slotW6_z slotW6_mixed)

set_option autoImplicit false
set_option maxHeartbeats 3200000






end Work.FTS.StrongPersist.N6Trans.SixAux
end
end
