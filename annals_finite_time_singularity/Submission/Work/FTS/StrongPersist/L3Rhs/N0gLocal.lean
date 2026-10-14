import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.EllipticEst.remov.SourceBound.sliceMomentIdentity
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.Pgs
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.Pieces4
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.RadialWAux.radPsi_contDiffOn
import Submission.Work.FTS.PhiStar.RadialWAux.radPsi_iteratedDeriv
import Submission.Work.FTS.RegPkgGal.St1Class
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.H6Aux.RadialAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.SlotDataOpen
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.leibnizRem6
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS.StrongPersist.hasDerivAt_wip_family
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.T2Sup.GenSlot
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_RegExport.RXR5L.L12fAux.C1Jet_L12f_of_support
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.RPFresh.slice_sq_le
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.ClassC.lintegral_modeSum_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "w" => Work.Spaces.w
local notation "eFam" => Work.FTS.PhiStar.Gegenbauer.eFam
local notation "sEta" => Work.FTS.EllipticEst.sEta

/-- The radial weight `w z = (1+z)²/z²` is nonnegative. -/
theorem lms_w_nonneg (z : ℝ) : 0 ≤ w z := by
  rw [Work.Spaces.w]; positivity

/-- **Integrability of the dominating radial function of the mode-sum bound.**  If every
weighted square `z ↦ a_m(z)² w(z)²` (`m ≤ N`) is integrable on `Iz`, and `0 ≤ c`, then

  `z ↦ c · (Σ_{m≤N} (m+1)|a_m(z)|)² · w(z)²`

is integrable on `Iz`.  The majorant is the `m`-Cauchy–Schwarz bound
`(Σ_m (m+1)|a_m|)² ≤ (N+1)·Σ_m (m+1)²·(a_m² w²)`, divided by `w²`. -/
theorem integrableOn_modeSum_maj (a : ℕ → ℝ → ℝ) (N : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hint : ∀ m, m ≤ N → MeasureTheory.IntegrableOn
      (fun z => (a m z) ^ 2 * (w z) ^ 2) Iz) :
    MeasureTheory.IntegrableOn
      (fun z => c * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2
        * (w z) ^ 2) Iz := by
  classical
  have hw_nn : ∀ z : ℝ, 0 ≤ w z := lms_w_nonneg
  have hmaj_int : MeasureTheory.IntegrableOn (fun z =>
      c * ((N : ℝ) + 1) * (∑ m ∈ Finset.range (N + 1),
        ((m : ℝ) + 1) ^ 2 * ((a m z) ^ 2 * (w z) ^ 2))) Iz :=
    (MeasureTheory.integrable_finsetSum _ fun m hm =>
      (hint m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))).const_mul _).const_mul _
  have hP_asm : AEStronglyMeasurable (fun z => ∑ m ∈ Finset.range (N + 1),
      ((m : ℝ) + 1) * Real.sqrt ((a m z) ^ 2 * (w z) ^ 2)) (volume.restrict Iz) := by
    have h := Finset.aestronglyMeasurable_sum (Finset.range (N + 1))
      (f := fun (m : ℕ) => fun (z : ℝ) => ((m : ℝ) + 1) * Real.sqrt ((a m z) ^ 2 * (w z) ^ 2))
      (fun m hm => aestronglyMeasurable_const.mul
        (Real.continuous_sqrt.comp_aestronglyMeasurable
          (hint m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))).aestronglyMeasurable))
    have h2 : (∑ i ∈ Finset.range (N + 1),
          (fun z : ℝ => ((i : ℝ) + 1) * Real.sqrt ((a i z) ^ 2 * (w z) ^ 2)))
        = (fun z : ℝ => ∑ i ∈ Finset.range (N + 1),
            ((i : ℝ) + 1) * Real.sqrt ((a i z) ^ 2 * (w z) ^ 2)) := by
      funext z
      rw [Finset.sum_apply]
    rwa [h2] at h
  have hasm : AEStronglyMeasurable (fun z => c * (∑ m ∈ Finset.range (N + 1),
      ((m : ℝ) + 1) * |a m z|) ^ 2 * (w z) ^ 2) (volume.restrict Iz) :=
    (aestronglyMeasurable_const.mul (hP_asm.pow 2)).congr (by
      filter_upwards with z
      show c * (∑ m ∈ Finset.range (N + 1),
              ((m : ℝ) + 1) * Real.sqrt ((a m z) ^ 2 * (w z) ^ 2)) ^ 2
          = c * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2 * (w z) ^ 2
      have hsq : ∀ m : ℕ, Real.sqrt ((a m z) ^ 2 * (w z) ^ 2) = |a m z| * w z := by
        intro m
        rw [← mul_pow, Real.sqrt_sq_eq_abs, abs_mul, abs_of_nonneg (hw_nn z)]
      have hsum : (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * (|a m z| * w z))
          = (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) * w z := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun m _ => by ring
      rw [Finset.sum_congr rfl (fun m _ => by rw [hsq m]), hsum]
      ring)
  have hae : ∀ z : ℝ, ‖c * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2
        * (w z) ^ 2‖ ≤ c * ((N : ℝ) + 1)
        * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) ^ 2
            * ((a m z) ^ 2 * (w z) ^ 2)) := by
    intro z
    have hCS : (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2
        ≤ ((N : ℝ) + 1) * ∑ m ∈ Finset.range (N + 1), (((m : ℝ) + 1) * |a m z|) ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq
        (s := Finset.range (N + 1)) (f := fun m => ((m : ℝ) + 1) * |a m z|)
      simpa [Finset.card_range, Nat.cast_add, Nat.cast_one] using h
    have hnonneg : 0 ≤ c * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2
        * (w z) ^ 2 :=
      mul_nonneg (mul_nonneg hc (sq_nonneg _)) (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    have hstep : (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2 * (w z) ^ 2
        ≤ ((N : ℝ) + 1) * ∑ m ∈ Finset.range (N + 1),
            ((m : ℝ) + 1) ^ 2 * ((a m z) ^ 2 * (w z) ^ 2) := by
      have h1 := mul_le_mul_of_nonneg_right hCS (sq_nonneg (w z))
      have h2 : ((N : ℝ) + 1) * (∑ m ∈ Finset.range (N + 1), (((m : ℝ) + 1) * |a m z|) ^ 2)
            * (w z) ^ 2
          = ((N : ℝ) + 1) * ∑ m ∈ Finset.range (N + 1),
              ((m : ℝ) + 1) ^ 2 * ((a m z) ^ 2 * (w z) ^ 2) := by
        rw [mul_assoc, Finset.sum_mul]
        congr 1
        exact Finset.sum_congr rfl fun m _ => by rw [mul_pow, sq_abs]; ring
      exact h2 ▸ h1
    calc c * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2 * (w z) ^ 2
        = c * ((∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2 * (w z) ^ 2) := by
          ring
      _ ≤ c * (((N : ℝ) + 1) * ∑ m ∈ Finset.range (N + 1),
              ((m : ℝ) + 1) ^ 2 * ((a m z) ^ 2 * (w z) ^ 2)) :=
          mul_le_mul_of_nonneg_left hstep hc
      _ = c * ((N : ℝ) + 1) * (∑ m ∈ Finset.range (N + 1),
              ((m : ℝ) + 1) ^ 2 * ((a m z) ^ 2 * (w z) ^ 2)) := by ring
  exact hmaj_int.mono' hasm (Filter.Eventually.of_forall fun z => hae z)

/-- **The level-`0` mode-sum bound in `lintegral` form.**

  `∫⁻_z ∫⁻_θ ofReal ((Σ_{m≤N} a_m(z) e_m(θ))² · w(z)² · σ(θ))
     ≤ ofReal (9·(∫_θ σ)·(Σ_{m≤N} (m+1)·√(∫_z a_m² w²))²)`,

where `e_m = Gegenbauer.eFam m` is the Dirichlet eigenfamily and `σ = sEta`. -/
theorem lintegral_modeSum_le (a : ℕ → ℝ → ℝ) (N : ℕ)
    (hint : ∀ m, m ≤ N → MeasureTheory.IntegrableOn
      (fun z => (a m z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((∑ m ∈ Finset.range (N + 1),
            a m z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      ≤ ENNReal.ofReal (9 * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ)
          * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1)
              * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2)) ^ 2) := by
  classical
  set K : ℝ := ∫ θ in Iθ, sEta θ with hK
  set P : ℝ → ℝ := fun z => ∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z| with hP
  set Q : ℝ → ℝ := fun z => 9 * (P z) ^ 2 * (w z) ^ 2 with hQ
  have hKnn : 0 ≤ K := by
    rw [hK]
    exact setIntegral_nonneg measurableSet_Icc fun θ hθ => Work.FTS.EllipticEst.Honest.sEta_nonneg hθ
  have hPnn : ∀ z, 0 ≤ P z := by
    intro z
    rw [hP]
    exact Finset.sum_nonneg fun m _ => mul_nonneg (by positivity) (abs_nonneg _)
  have hQnn : ∀ z, 0 ≤ Q z := by
    intro z
    rw [hQ]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  -- the `θ`-integral of `ofReal σ`
  have hσ : ∫⁻ θ in Iθ, ENNReal.ofReal (sEta θ) = ENNReal.ofReal K := by
    rw [hK]
    refine (MeasureTheory.ofReal_integral_eq_lintegral_ofReal Work.FTS.EllipticEst.Honest.sEta_integrableOn ?_).symm
    exact (MeasureTheory.ae_restrict_iff' measurableSet_Icc).2
      (Filter.Eventually.of_forall fun θ hθ => Work.FTS.EllipticEst.Honest.sEta_nonneg hθ)
  -- the pointwise angular bound `(Σ a_m e_m)² ≤ 9 P²` on `Iθ`
  have hpt : ∀ z θ, θ ∈ Iθ →
      (∑ m ∈ Finset.range (N + 1), a m z * eFam m θ) ^ 2 * (w z) ^ 2 * sEta θ
        ≤ Q z * sEta θ := by
    intro z θ hθ
    have hsup := abs_sum_eFam_le (N := N) (b := fun m => a m z) hθ
    have hPz : P z = ∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z| := by rw [hP]
    have hsq : (∑ m ∈ Finset.range (N + 1), a m z * eFam m θ) ^ 2 ≤ 9 * (P z) ^ 2 := by
      rw [hPz]
      calc (∑ m ∈ Finset.range (N + 1), a m z * eFam m θ) ^ 2
          = |∑ m ∈ Finset.range (N + 1), a m z * eFam m θ| ^ 2 := (sq_abs _).symm
        _ ≤ (3 * ∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hsup 2
        _ = 9 * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2 := by ring
    have h1 : (∑ m ∈ Finset.range (N + 1), a m z * eFam m θ) ^ 2 * (w z) ^ 2
        ≤ (9 * (P z) ^ 2) * (w z) ^ 2 :=
      mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    have h2 : (∑ m ∈ Finset.range (N + 1), a m z * eFam m θ) ^ 2 * (w z) ^ 2 * sEta θ
        ≤ (9 * (P z) ^ 2 * (w z) ^ 2) * sEta θ := by
      calc (∑ m ∈ Finset.range (N + 1), a m z * eFam m θ) ^ 2 * (w z) ^ 2 * sEta θ
          = ((∑ m ∈ Finset.range (N + 1), a m z * eFam m θ) ^ 2 * (w z) ^ 2) * sEta θ := by
            ring
        _ ≤ ((9 * (P z) ^ 2) * (w z) ^ 2) * sEta θ :=
            mul_le_mul_of_nonneg_right h1 (Work.FTS.EllipticEst.Honest.sEta_nonneg hθ)
        _ = (9 * (P z) ^ 2 * (w z) ^ 2) * sEta θ := by ring
    rw [hQ]
    exact h2
  -- the inner `θ`-bound, for `z ∈ Iz`
  have hinner : ∀ z ∈ Iz, (∫⁻ θ in Iθ,
      ENNReal.ofReal ((∑ m ∈ Finset.range (N + 1), a m z * eFam m θ) ^ 2
        * (w z) ^ 2 * sEta θ))
      ≤ ENNReal.ofReal (Q z) * ENNReal.ofReal K := by
    intro z hz
    have h1 : (∫⁻ θ in Iθ,
        ENNReal.ofReal ((∑ m ∈ Finset.range (N + 1), a m z * eFam m θ) ^ 2
          * (w z) ^ 2 * sEta θ))
        ≤ ∫⁻ θ in Iθ, ENNReal.ofReal (Q z * sEta θ) :=
      MeasureTheory.setLIntegral_mono' measurableSet_Icc fun θ hθ =>
        ENNReal.ofReal_le_ofReal (hpt z θ hθ)
    have h2 : (∫⁻ θ in Iθ, ENNReal.ofReal (Q z * sEta θ))
        = ∫⁻ θ in Iθ, ENNReal.ofReal (Q z) * ENNReal.ofReal (sEta θ) :=
      MeasureTheory.setLIntegral_congr_fun measurableSet_Icc fun θ hθ =>
        ENNReal.ofReal_mul (hQnn z)
    have h3 : (∫⁻ θ in Iθ, ENNReal.ofReal (Q z) * ENNReal.ofReal (sEta θ))
        = ENNReal.ofReal (Q z) * ∫⁻ θ in Iθ, ENNReal.ofReal (sEta θ) :=
      MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (Q z))
        (fun θ => ENNReal.ofReal (sEta θ)) ENNReal.ofReal_ne_top
    rw [h2] at h1
    rw [h3, hσ] at h1
    exact h1
  -- integrability of the dominating radial function
  have hQint : MeasureTheory.IntegrableOn Q Iz := by
    have h := integrableOn_modeSum_maj a N (c := 9) (by norm_num) hint
    simpa only [hQ, hP] using h
  have hQae : 0 ≤ᵐ[volume.restrict Iz] Q :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ici).2
      (Filter.Eventually.of_forall fun z hz => hQnn z)
  have hQlin : (∫⁻ z in Iz, ENNReal.ofReal (Q z)) = ENNReal.ofReal (∫ z in Iz, Q z) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hQint hQae).symm
  -- the radial part, by finite-sum Minkowski
  have hM_le : (∫ z in Iz, Q z) ≤ 9 * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1)
      * Real.sqrt (∫ z in Iz, (a m z) ^ 2 * (w z) ^ 2)) ^ 2 := by
    have hweighted := weighted_l2_modeSum (N := N) (a := a) (c := fun m => ((m : ℝ) + 1))
      (fun m => by positivity) hint
    have hfunext : Q = fun z => 9 * ((w z) ^ 2 * (P z) ^ 2) := by
      funext z
      rw [hQ]
      ring
    rw [hfunext, MeasureTheory.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    simpa only [hP] using hweighted
  calc (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((∑ m ∈ Finset.range (N + 1),
            a m z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      ≤ ∫⁻ z in Iz, ENNReal.ofReal (Q z) * ENNReal.ofReal K :=
        MeasureTheory.setLIntegral_mono' measurableSet_Ici hinner
    _ = ENNReal.ofReal K * ∫⁻ z in Iz, ENNReal.ofReal (Q z) := by
        rw [show (fun z => ENNReal.ofReal (Q z) * ENNReal.ofReal K)
            = fun z => ENNReal.ofReal K * ENNReal.ofReal (Q z) from by
          funext z; rw [mul_comm]]
        exact MeasureTheory.lintegral_const_mul' (ENNReal.ofReal K)
          (fun z => ENNReal.ofReal (Q z)) ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal K * ENNReal.ofReal (∫ z in Iz, Q z) := by rw [hQlin]
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal (9 * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1)
          * Real.sqrt (∫ z in Iz, (a m z) ^ 2 * (w z) ^ 2)) ^ 2) :=
        mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hM_le)
          (by positivity : (0 : ℝ≥0∞) ≤ ENNReal.ofReal K)
    _ = ENNReal.ofReal (9 * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ)
          * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1)
              * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2)) ^ 2) := by
        rw [← ENNReal.ofReal_mul hKnn]
        congr 1
        rw [hK]
        ring

end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.ClassCHon.Hcoef.cmode_L2_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.Hcoef

open MeasureTheory Set Filter
open scoped Real Topology

/-- The radial weight `w` is continuous on the open half-line: needed only for the a.e. strong
measurability of `z ↦ w z`. -/
theorem continuousOn_w_Ioi : ContinuousOn Work.Spaces.w (Set.Ioi (0 : ℝ)) := by
  have h : Work.Spaces.w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := rfl
  rw [h]
  exact ((continuous_const.add continuous_id).pow 2).continuousOn.div
    (continuous_id.pow 2).continuousOn (fun z hz => pow_ne_zero 2 (ne_of_gt hz))

/-- **The `L²(w²)` bound for a single angular mode.**

For `F` in the honest `ℋ⁰` class (`HkMem α 0 F`) and `C^∞` on the open quadrant, the weighted
square of the `m`-th mode coefficient is integrable on `(0,∞)` and its `eNorm m`-weighted
integral is dominated by `HkSq α 0 F`:

  `∫_0^∞ (cmode m F z · w z)² dz < ∞`,   `eNorm m · ∫_0^∞ (cmode m F z · w z)² dz ≤ HkSq α 0 F`.

This is the *sharp* (Bessel-type) per-mode bound
`eNorm m * (cmode m F z)² ≤ ∫_θ (F z θ)² sin(2θ)^{-η}` (proved in
`eNorm_mul_cmode_sq_le_sliceMass`) integrated against `w²`; at level `k = 0` the `ℋ⁰`-integrand
is `w z² · ∫_θ (F z θ)² sin(2θ)^{-η}`, so the right-hand side is exactly `HkSq α 0 F`. -/
theorem cmode_L2_bound {α : ℝ} {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hF0 : Work.Spaces.HkMem α 0 F) (m : ℕ) :
    MeasureTheory.IntegrableOn
        (fun z : ℝ => (Work.FTS.PhiStar.Series.cmode m F z * Work.Spaces.w z) ^ 2)
        (Set.Ioi 0) ∧
      Work.EllipticEst.ModalSolution.eNorm m
          * (∫ z in Set.Ioi (0 : ℝ),
              (Work.FTS.PhiStar.Series.cmode m F z * Work.Spaces.w z) ^ 2)
        ≤ Work.Spaces.HkSq α 0 F := by
  -- the per-slice `η`-weighted mass, as an abbreviation
  set M : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hM
  have hEpos : 0 < Work.EllipticEst.ModalSolution.eNorm m :=
    Work.EllipticEst.ModalSolution.eNorm_pos m
  -- the slice is `Iθ`-integrable at every `z > 0` (honesty of the `ℋ⁰` class)
  have hslice : ∀ z ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn
      (fun θ : ℝ => (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ := fun z hz => Work.FTS.PhiStar.Honesty.integrableOn_sq_sEta_of_HkMem hF0 hz
  -- the sharp per-mode slice bound, integrated against the radial weight
  have hbound : ∀ z : ℝ, 0 < z →
      Work.EllipticEst.ModalSolution.eNorm m
          * (Work.FTS.PhiStar.Series.cmode m F z * Work.Spaces.w z) ^ 2
        ≤ (Work.Spaces.w z) ^ 2 * M z := by
    intro z hz
    have h := Work.FTS.PhiStar.Honesty.eNorm_mul_cmode_sq_le_sliceMass
      (m := m) (F := F) (z := z) (hslice z hz)
    rw [hM]
    calc Work.EllipticEst.ModalSolution.eNorm m
            * (Work.FTS.PhiStar.Series.cmode m F z * Work.Spaces.w z) ^ 2
        = (Work.Spaces.w z) ^ 2 * (Work.EllipticEst.ModalSolution.eNorm m
            * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2) := by ring
      _ ≤ (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
          mul_le_mul_of_nonneg_left h (sq_nonneg _)
  -- the `z`-slice of `HkIntegrand α 0 F` is `w z² · M z`
  have hId : ∀ z : ℝ, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ)
      = (Work.Spaces.w z) ^ 2 * M z := by
    intro z
    rw [hM]
    rw [show (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ)
          = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
              * ((F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) from
        MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => by
          rw [Work.FTS.EllipticEst.AngAWeak.HkIntegrand_zero_eq_w α F z hθ,
            Work.FTS.EllipticEst.sEta]
          ring)]
    rw [MeasureTheory.integral_const_mul]
  -- the majorant `w² · M` is integrable: it is the `z`-slice function of `HkIntegrand α 0 F`
  have hmaj : MeasureTheory.IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * M z)
      (Set.Ioi (0 : ℝ)) := by
    have hsub : Set.Ioi (0 : ℝ) ⊆ Work.Spaces.Iz := by
      intro z hz
      simp only [Work.Spaces.Iz, Set.mem_Ici]
      exact le_of_lt hz
    have h1 : MeasureTheory.IntegrableOn
        (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ)
        (Set.Ioi (0 : ℝ)) := hF0.2.mono_set hsub
    refine h1.congr_fun ?_ measurableSet_Ioi
    intro z _
    exact hId z
  -- hence the target function is integrable as well
  have hT : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.PhiStar.Series.cmode m F z * Work.Spaces.w z) ^ 2)
      (Set.Ioi (0 : ℝ)) := by
    have hdom : MeasureTheory.IntegrableOn
        (fun z : ℝ => (Work.EllipticEst.ModalSolution.eNorm m)⁻¹
          * ((Work.Spaces.w z) ^ 2 * M z)) (Set.Ioi (0 : ℝ)) := hmaj.const_mul _
    refine hdom.mono' ?_ ?_
    · have hcm : MeasureTheory.AEStronglyMeasurable
          (fun z : ℝ => Work.FTS.PhiStar.Series.cmode m F z)
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
        Work.EllipticEst.ModalSolution.aesm_cmode hsm m
      have hw : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => Work.Spaces.w z)
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
        (continuousOn_w_Ioi.aemeasurable measurableSet_Ioi).aestronglyMeasurable
      exact (hcm.mul hw).pow 2
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
      have hcm2 : (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
          ≤ (Work.EllipticEst.ModalSolution.eNorm m)⁻¹ * M z := by
        have h := Work.FTS.PhiStar.Honesty.eNorm_mul_cmode_sq_le_sliceMass
          (m := m) (F := F) (z := z) (hslice z hz)
        rw [hM]
        rw [← div_eq_inv_mul, le_div_iff₀ hEpos]
        calc (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
              * Work.EllipticEst.ModalSolution.eNorm m
            = Work.EllipticEst.ModalSolution.eNorm m
                * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 := by ring
          _ ≤ ∫ θ in Work.Spaces.Iθ,
                (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := h
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      calc (Work.FTS.PhiStar.Series.cmode m F z * Work.Spaces.w z) ^ 2
          = (Work.Spaces.w z) ^ 2 * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 := by ring
        _ ≤ (Work.Spaces.w z) ^ 2 * ((Work.EllipticEst.ModalSolution.eNorm m)⁻¹ * M z) :=
              mul_le_mul_of_nonneg_left hcm2 (sq_nonneg _)
        _ = (Work.EllipticEst.ModalSolution.eNorm m)⁻¹
              * ((Work.Spaces.w z) ^ 2 * M z) := by ring
  -- the integral of the majorant is `HkSq α 0 F`
  have hmaj_eq : (∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * M z)
      = Work.Spaces.HkSq α 0 F := by
    have h1 : (∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * M z)
        = ∫ z in Set.Ioi (0 : ℝ),
            ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => (hId z).symm)
    have h2 : (∫ z in Set.Ioi (0 : ℝ),
          ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ)
        = Work.Spaces.HkSq α 0 F := by
      rw [Work.Spaces.HkSq, show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl]
      exact (MeasureTheory.integral_Ici_eq_integral_Ioi (μ := MeasureTheory.volume)
        (x := (0 : ℝ))).symm
    rw [h1, h2]
  refine ⟨hT, ?_⟩
  rw [← MeasureTheory.integral_const_mul]
  calc (∫ z in Set.Ioi (0 : ℝ), Work.EllipticEst.ModalSolution.eNorm m
          * (Work.FTS.PhiStar.Series.cmode m F z * Work.Spaces.w z) ^ 2)
      ≤ ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * M z :=
        MeasureTheory.setIntegral_mono_on (hT.const_mul _) hmaj measurableSet_Ioi
          (fun z hz => hbound z hz)
    _ = Work.Spaces.HkSq α 0 F := hmaj_eq

end Work.FTS.ClassCHon.Hcoef
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E2_norm =====
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

/-- `√(X+Y) ≤ √X + √Y` for nonnegative `X`, `Y`. -/
private theorem sqrt_add_le_sqrt_add_sqrt {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    Real.sqrt (X + Y) ≤ Real.sqrt X + Real.sqrt Y := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX
  have h2 : Real.sqrt Y ^ 2 = Y := Real.sq_sqrt hY
  have hexp : (Real.sqrt X + Real.sqrt Y) ^ 2
      = X + 2 * (Real.sqrt X * Real.sqrt Y) + Y := by
    rw [add_sq, h1, h2]; ring
  nlinarith [hexp, mul_nonneg (Real.sqrt_nonneg X) (Real.sqrt_nonneg Y)]


end Work.FTS.CoercivityFix.Transfer
end
end
-- ===== merged: Submission.Work.FTS.GalFields.Norm.ang_fac_integrable_bound =====
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

/-- **The angular factor of the `ℋⁿ`-integrand of `Γ(θ)·r(z)` is `θ`-integrable with an
`α`-uniform bound.**

The angular weight that appears when the sharp profile `G θ = sin(2θ)^{α/5}` is folded into the
heavy weight `τ = sin(2θ)^{-γ}` is

  `smE θ + 4·(10^5 α)²·sin(2θ)^{2(α/5) - γ}`,

with `smE θ = sin(2θ)^{-η}` (`η = 99/100`) and `γ = 1 + α/10`.  Both exponents
`-η ∈ (-1,0)` and `2α/5 - γ = -1 + 3α/10 ∈ (-1,0)` for `α ∈ (0,1]` are `> -1`, so each
summand is integrable on `Iθ`; quantitatively `sin_two_rpow` gives

  `∫_{Iθ} sin(2θ)^{-η} ≤ 10^4`  and  `∫_{Iθ} sin(2θ)^{2α/5-γ} ≤ 10^3/(3α)`,

and the second bound, whose divergence as `α → 0⁺` is `~ 1/α`, is multiplied by the `α²` of
the coefficient `4·(10^5 α)²` and by `α ≤ 1`, giving the `α`-independent constant `K`.

This is the `RintN = 1` (trivial radial density) case of `E2norm.gam_rad_integral_le`. -/
theorem ang_fac_integrable_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
      MeasureTheory.IntegrableOn (fun θ : ℝ =>
          Work.FTS.Nonlinear.RadialProd.smE θ
            + 4 * (100000 * α) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ,
          (Work.FTS.Nonlinear.RadialProd.smE θ
            + 4 * (100000 * α) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α))) ≤ K := by
  refine ⟨10000 + 40000000000000 / 3, by norm_num, ?_⟩
  intro α hα hα1
  -- Integrability of the two summands.
  have hIe : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.Nonlinear.RadialProd.smE θ)
      Work.Spaces.Iθ := by
    have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
      (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_pos])).1
    simpa [Work.FTS.Nonlinear.RadialProd.smE] using h
  have hp1 : -1 < 2 * (α / 5) - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hp2 : 2 * (α / 5) - Work.Spaces.gam α ≤ 0 := by rw [Work.Spaces.gam]; linarith
  have hIex : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)) Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow _ hp1 hp2).1
  constructor
  · exact hIe.add (hIex.const_mul _)
  · -- The two numerical bounds for the `θ`-integrals.
    have hIe_le : (∫ θ in Work.Spaces.Iθ, Work.FTS.Nonlinear.RadialProd.smE θ) ≤ 10000 := by
      have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
        (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_pos])).2
      have hexp : -(Work.Spaces.eta) + 1 = (1 : ℝ) / 100 := by rw [Work.Spaces.eta]; norm_num
      rw [hexp] at h
      have h2 : (100 : ℝ) / ((1 : ℝ) / 100) = 10000 := by norm_num
      rw [h2] at h
      simpa [Work.FTS.Nonlinear.RadialProd.smE] using h
    have hIex_le : (∫ θ in Work.Spaces.Iθ,
        (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)) ≤ 1000 / (3 * α) := by
      have h := (Work.Spaces.sin_two_rpow _ hp1 hp2).2
      have hexp : 2 * (α / 5) - Work.Spaces.gam α + 1 = 3 * α / 10 := by
        rw [Work.Spaces.gam]; ring
      rw [hexp] at h
      have heq : (100 : ℝ) / (3 * α / 10) = 1000 / (3 * α) := by
        have h1 : (3 : ℝ) * α ≠ 0 := by positivity
        have h2 : (3 : ℝ) * α / 10 ≠ 0 := by positivity
        field_simp
        ring
      calc (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α))
          ≤ 100 / (3 * α / 10) := h
        _ = 1000 / (3 * α) := heq
    have h4 : (0 : ℝ) ≤ 4 * (100000 * α) ^ 2 := by positivity
    have hkey : 10000 + 4 * (100000 * α) ^ 2 * (1000 / (3 * α))
        ≤ 10000 + 40000000000000 / 3 := by
      have heq : 4 * (100000 * α) ^ 2 * (1000 / (3 * α)) = (40000000000000 / 3) * α := by
        have h1 : α ≠ 0 := ne_of_gt hα
        field_simp
        ring
      rw [heq]
      nlinarith [hα1]
    have hsplit : (∫ θ in Work.Spaces.Iθ,
          (Work.FTS.Nonlinear.RadialProd.smE θ
            + 4 * (100000 * α) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)))
        = (∫ θ in Work.Spaces.Iθ, Work.FTS.Nonlinear.RadialProd.smE θ)
          + 4 * (100000 * α) ^ 2
            * ∫ θ in Work.Spaces.Iθ,
                (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α) := by
      rw [MeasureTheory.integral_add hIe (hIex.const_mul _), MeasureTheory.integral_const_mul]
    rw [hsplit]
    linarith [hIe_le, mul_le_mul_of_nonneg_left hIex_le h4, hkey]

end Work.FTS.GalFields.Norm
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.rl1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

theorem rl1 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.NonlinRows.Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
      |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ)) 0|
        ≤ K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
            + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
  -- ## the twenty per-piece constants
  obtain ⟨K1, hK1, hb1⟩ := Work.FTS.NonlinRows.Rl1.ggBounds (Ce := Ce)
  obtain ⟨K1', hK1', hb1'⟩ := Work.FTS.NonlinRows.Rl1.ggRows45
  obtain ⟨K2, hK2, hb2⟩ := Work.FTS.NonlinRows.Rl1.gsBounds (Ce := Ce)
  obtain ⟨K2', hK2', hb2'⟩ := Work.FTS.NonlinRows.Rl1.gsRows45 (Ce := Ce)
  obtain ⟨K3, hK3, hb3⟩ := Work.FTS.NonlinRows.Rl1.sgBounds (Cs := Cs)
  obtain ⟨K3', hK3', hb3'⟩ := Work.FTS.NonlinRows.Rl1.sgRows45 (Cs := Cs)
  obtain ⟨K4, hK4, hb4⟩ := Work.FTS.NonlinRows.Rl1.ssBounds (Cs := Cs)
  refine ⟨20 * (K1 + K1' + K2 + K2' + K3 + K3' + K4 + 1),
    by linarith [hK1, hK1', hK2, hK2', hK3, hK3', hK4], ?_⟩
  intro α g Φs Φg hctx
  obtain ⟨hα, hα1, hαα₂, hgal, hs, hell⟩ := hctx
  have hEnv : 0 ≤ Work.FTS.NonlinRows.Rl1.Env α g :=
    Work.FTS.NonlinRows.Rl1.Env_nonneg g hα.le
  -- ## the twenty per-piece bounds, at the common constant
  have hpiece : ∀ k : Fin 20, Work.FTS.Nonlinear.Pieces.Fa
      (Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Φg k)
        ≤ ENNReal.ofReal ((K1 + K1' + K2 + K2' + K3 + K3' + K4 + 1)
            * Work.FTS.NonlinRows.Rl1.Env α g) := by
    have h1 := hb1 hα hα1 hgal hell
    have h1' := hb1' hα hα1 hgal
    have h2 := hb2 hα hα1 hgal hell
    have h2' := hb2' hα hα1 hgal hell
    have h3 := hb3 hα hα1 hgal hs
    have h3' := hb3' hα hα1 hgal hs
    have h4 := hb4 hα hα1 hgal hs
    have e1 : ∀ {F : Work.FTS.Galerkin.Fn}, Work.FTS.Nonlinear.Pieces.Fa F
        ≤ ENNReal.ofReal (K1 * Work.FTS.NonlinRows.Rl1.Env α g) →
        Work.FTS.Nonlinear.Pieces.Fa F ≤ ENNReal.ofReal
          ((K1 + K1' + K2 + K2' + K3 + K3' + K4 + 1)
            * Work.FTS.NonlinRows.Rl1.Env α g) :=
      fun h => h.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (by linarith) hEnv))
    have e1' : ∀ {F : Work.FTS.Galerkin.Fn}, Work.FTS.Nonlinear.Pieces.Fa F
        ≤ ENNReal.ofReal (K1' * Work.FTS.NonlinRows.Rl1.Env α g) →
        Work.FTS.Nonlinear.Pieces.Fa F ≤ ENNReal.ofReal
          ((K1 + K1' + K2 + K2' + K3 + K3' + K4 + 1)
            * Work.FTS.NonlinRows.Rl1.Env α g) :=
      fun h => h.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (by linarith) hEnv))
    have e2 : ∀ {F : Work.FTS.Galerkin.Fn}, Work.FTS.Nonlinear.Pieces.Fa F
        ≤ ENNReal.ofReal (K2 * Work.FTS.NonlinRows.Rl1.Env α g) →
        Work.FTS.Nonlinear.Pieces.Fa F ≤ ENNReal.ofReal
          ((K1 + K1' + K2 + K2' + K3 + K3' + K4 + 1)
            * Work.FTS.NonlinRows.Rl1.Env α g) :=
      fun h => h.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (by linarith) hEnv))
    have e2' : ∀ {F : Work.FTS.Galerkin.Fn}, Work.FTS.Nonlinear.Pieces.Fa F
        ≤ ENNReal.ofReal (K2' * Work.FTS.NonlinRows.Rl1.Env α g) →
        Work.FTS.Nonlinear.Pieces.Fa F ≤ ENNReal.ofReal
          ((K1 + K1' + K2 + K2' + K3 + K3' + K4 + 1)
            * Work.FTS.NonlinRows.Rl1.Env α g) :=
      fun h => h.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (by linarith) hEnv))
    have e3 : ∀ {F : Work.FTS.Galerkin.Fn}, Work.FTS.Nonlinear.Pieces.Fa F
        ≤ ENNReal.ofReal (K3 * Work.FTS.NonlinRows.Rl1.Env α g) →
        Work.FTS.Nonlinear.Pieces.Fa F ≤ ENNReal.ofReal
          ((K1 + K1' + K2 + K2' + K3 + K3' + K4 + 1)
            * Work.FTS.NonlinRows.Rl1.Env α g) :=
      fun h => h.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (by linarith) hEnv))
    have e3' : ∀ {F : Work.FTS.Galerkin.Fn}, Work.FTS.Nonlinear.Pieces.Fa F
        ≤ ENNReal.ofReal (K3' * Work.FTS.NonlinRows.Rl1.Env α g) →
        Work.FTS.Nonlinear.Pieces.Fa F ≤ ENNReal.ofReal
          ((K1 + K1' + K2 + K2' + K3 + K3' + K4 + 1)
            * Work.FTS.NonlinRows.Rl1.Env α g) :=
      fun h => h.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (by linarith) hEnv))
    have e4 : ∀ {F : Work.FTS.Galerkin.Fn}, Work.FTS.Nonlinear.Pieces.Fa F
        ≤ ENNReal.ofReal (K4 * Work.FTS.NonlinRows.Rl1.Env α g) →
        Work.FTS.Nonlinear.Pieces.Fa F ≤ ENNReal.ofReal
          ((K1 + K1' + K2 + K2' + K3 + K3' + K4 + 1)
            * Work.FTS.NonlinRows.Rl1.Env α g) :=
      fun h => h.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (by linarith) hEnv))
    intro k
    fin_cases k
    · exact e1 h1.1
    · exact e2 h2.1
    · exact e3 h3.1
    · exact e4 h4.1
    · exact e1 h1.2.1
    · exact e2 h2.2.1
    · exact e3 h3.2.1
    · exact e4 h4.2.1
    · exact e1 h1.2.2
    · exact e2 h2.2.2
    · exact e3 h3.2.2
    · exact e4 h4.2.2.1
    · exact e1' h1'.1
    · exact e2' h2'.1
    · exact e3' h3'.1
    · exact e4 h4.2.2.2.1
    · exact e1' h1'.2
    · exact e2' h2'.2
    · exact e3' h3'.2
    · exact e4 h4.2.2.2.2
  -- ## the measurability of the twenty pieces
  have hmeas := Work.FTS.NonlinRows.Rl1.PvecMeasOpen hα hα1 hgal hs hell
  -- ## the exact split of `N` into its twenty summands
  have hsmg : Work.FTS.EllipticEst.SmoothOpen g :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hgal.reg.1
  have hmemg : Work.Spaces.HkMem α 4 g := (Work.FTS.Nonlin.galClass_regQ4 hgal).2.1
  have hL12 : ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z :=
    fun z hz => hN.l12diff α ⟨hα, hαα₂⟩ g ⟨hsmg, hmemg⟩ z hz
  have hsp := Work.FTS.NonlinRows.Rl1.splitOpen hα hα1 hsmg hs.smooth hell.smooth
    (fun z hz => (Work.FTS.Nonlinear.Pieces.L12FK_add_ge0 hα hα1 hgal).1 z hz.le)
    (fun z hz => (Work.FTS.Nonlinear.Pieces.L12FK_add_ge0 hα hα1 hgal).2 z hz.le) hL12
  have hsplit : ∀ r θ : ℝ, (r, θ) ∈ Work.Construction.Qd →
      Work.Construction.N α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) r θ
        = ∑ k : Fin 20, Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Φg k r θ := by
    intro r θ hq
    rw [hsp r θ hq]
    simp only [Work.FTS.Nonlinear.Pieces.rl1Tools.pv, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.reduceFinMk]
    ring
  -- ## the `L¹(r⁻¹dr)`-triangle inequality
  have htri := Work.FTS.Nonlinear.Pieces.rl1Tools.FaSumAE
    (N := Work.Construction.N α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ))
    (p := Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Φg) hsplit hmeas.1 hmeas.2
  -- ## adding the twenty constants
  have hsum : (∑ k : Fin 20, Work.FTS.Nonlinear.Pieces.Fa
        (Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Φg k))
      ≤ ENNReal.ofReal ((20 * (K1 + K1' + K2 + K2' + K3 + K3' + K4 + 1))
          * Work.FTS.NonlinRows.Rl1.Env α g) := by
    refine (Finset.sum_le_sum fun k _ => hpiece k).trans ?_
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
      show ((20 : ℕ) : ENNReal) = ENNReal.ofReal 20 from (ENNReal.ofReal_natCast 20).symm,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 20)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_assoc]
  -- ## assembling
  have hglue := Work.FTS.Nonlinear.Pieces.ofReal_L12_le
    (Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ))
  have hkey : ENNReal.ofReal |Work.Construction.L12 (Work.Construction.N α
      (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ)) 0|
      ≤ ENNReal.ofReal ((20 * (K1 + K1' + K2 + K2' + K3 + K3' + K4 + 1))
          * Work.FTS.NonlinRows.Rl1.Env α g) := hglue.trans (htri.trans hsum)
  have hfin := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (by positivity) hEnv)).mp hkey
  simpa only [Work.FTS.NonlinRows.Rl1.Env] using hfin

end Work.FTS.NonlinRows
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.gs_open_rows =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)

/-- `√2 ≤ 2`. -/
private theorem sqrt_two_le_two : Real.sqrt 2 ≤ 2 := by
  have h : Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
  rwa [show Real.sqrt (4 : ℝ) = 2 from by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h

/-- `√16 = 4`. -/
private theorem sqrt_sixteen : Real.sqrt (16 : ℝ) = 4 := by
  rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `|FK f r| ≤ 4√(Φ₀ f r)`, from the slot integrability and strong measurability. -/
private theorem FK_abs_le_four_sqrt {f : Fn} {r : ℝ} (hr : 0 < r)
    (hint : MeasureTheory.IntegrableOn (fun θ => (f r θ) ^ 2) Work.Spaces.Iθ)
    (haesm : MeasureTheory.AEStronglyMeasurable (fun θ => f r θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    |Work.Construction.FK f r|
      ≤ 4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r) := by
  have hFK := Real.abs_le_sqrt
    (Work.FTS.NonlinRows.Rl1.FK_sq_le_sixteen_Phi0 (g := f) hr hint haesm)
  rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16), sqrt_sixteen] at hFK

theorem gs_open_rows : ∃ K : ℝ, 0 < K ∧
    ∀ {α : ℝ} {f : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N4gs α f)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N5gs α f)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) := by
  refine ⟨1000 * Real.pi + 1, by positivity, ?_⟩
  intro α f hα hα1 hso hmem
  have s0 : Work.FTS.NonlinRows.Rl1.SlotData α f
      (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f) (Work.Spaces.HkSq α 4 f) :=
    slotData_open_g (α := α) (f := f) hα hso hmem
  have hEnvn : 0 ≤ Work.FTS.NonlinRows.Rl1.Env α f :=
    Work.FTS.NonlinRows.Rl1.Env_nonneg f hα.le
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
  have hsqrtX : Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
      Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r) ≤ Work.FTS.Nonlin.Xn α f :=
    Real.sqrt_le_sqrt s0.le
  have hrad2 : Real.sqrt 2 ≤ 2 := sqrt_two_le_two
  have hα2X := Work.FTS.NonlinRows.Rl1.alpha_sq_mul_Xn_le_Env (g := f) hα hα1
  have hαX := Work.FTS.NonlinRows.Rl1.alpha_mul_Xn_le_Env (g := f) hα hα1
  have hKbig : (240 : ℝ) * Real.pi ≤ 1000 * Real.pi + 1 := by nlinarith [Real.pi_pos]
  constructor
  · -- `N₄^{gs} = -(1/2)·sin2θ·FK f·∂_θF_*`
    have hp := Work.FTS.NonlinRows.Rl1.profile_data_sq (d := 40 * α ^ 2) (by positivity)
    have hmain := Work.FTS.NonlinRows.Rl1.Fa_le_of_profile
      (N := Work.FTS.Nonlin.N4gs α f)
      (c := fun r => 40 * α ^ 2 * r / (1 + r) ^ 2)
      (M := fun r => 4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r))
      (Ψ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f) (C := 16)
      (by norm_num)
      (fun r hr => by positivity)
      (fun r => by positivity)
      s0.nonneg s0.meas s0.int hp.1 hp.2.1
      (fun r hr => le_of_eq (by
        rw [mul_pow, Real.sq_sqrt (s0.nonneg r)]
        norm_num))
      (fun r hr θ hθ => by
        have hFKabs := FK_abs_le_four_sqrt (f := f) hr (s0.sqint r hr) (s0.aesm r hr)
        have h1 := Work.FTS.NonlinRows.Rl1.N4gs_pt (α := α) (g := f) hα hα1 r hr θ hθ
        have h2 : 40 * α ^ 2 * (r / (1 + r) ^ 2) * |Work.Construction.FK f r|
            ≤ 40 * α ^ 2 * (r / (1 + r) ^ 2)
              * (4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r)) :=
          mul_le_mul_of_nonneg_left hFKabs (by positivity)
        have h3 : 40 * α ^ 2 * (r / (1 + r) ^ 2)
              * (4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r))
            = (40 * α ^ 2 * r / (1 + r) ^ 2)
              * (4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r)) := by ring
        exact h1.trans (h2.trans (le_of_eq h3)))
    refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [sqrt_sixteen]
    have h40 : Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
        (r⁻¹ * (40 * α ^ 2 * r / (1 + r) ^ 2)) ^ 2) ≤ 40 * α ^ 2 * 2 :=
      hp.2.2.2.trans (by nlinarith [Real.sqrt_nonneg 2, hrad2, sq_nonneg α])
    have hAB : Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r)
        * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          (r⁻¹ * (40 * α ^ 2 * r / (1 + r) ^ 2)) ^ 2)
        ≤ Work.FTS.Nonlin.Xn α f * (40 * α ^ 2 * 2) :=
      mul_le_mul hsqrtX h40 (Real.sqrt_nonneg _) hX0
    have hstep : Real.pi / 2 * (4 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r)
        * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          (r⁻¹ * (40 * α ^ 2 * r / (1 + r) ^ 2)) ^ 2))
        ≤ Real.pi / 2 * (4 * Work.FTS.Nonlin.Xn α f * (40 * α ^ 2 * 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc 4 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
              Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r)
            * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
              (r⁻¹ * (40 * α ^ 2 * r / (1 + r) ^ 2)) ^ 2)
          = 4 * (Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
                Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r)
              * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
                (r⁻¹ * (40 * α ^ 2 * r / (1 + r) ^ 2)) ^ 2)) := by ring
        _ ≤ 4 * (Work.FTS.Nonlin.Xn α f * (40 * α ^ 2 * 2)) :=
            mul_le_mul_of_nonneg_left hAB (by norm_num)
        _ = 4 * Work.FTS.Nonlin.Xn α f * (40 * α ^ 2 * 2) := by ring
    refine hstep.trans ?_
    have h1 : Real.pi / 2 * (4 * Work.FTS.Nonlin.Xn α f * (40 * α ^ 2 * 2))
        = (160 * Real.pi) * (α ^ 2 * Work.FTS.Nonlin.Xn α f) := by ring
    rw [h1]
    calc (160 * Real.pi) * (α ^ 2 * Work.FTS.Nonlin.Xn α f)
        ≤ (160 * Real.pi) * Work.FTS.NonlinRows.Rl1.Env α f :=
          mul_le_mul_of_nonneg_left hα2X (by positivity)
      _ ≤ (1000 * Real.pi + 1) * Work.FTS.NonlinRows.Rl1.Env α f :=
          mul_le_mul_of_nonneg_right (by nlinarith [Real.pi_pos]) hEnvn
  · -- `N₅^{gs} = -sin²θ·FK f·F_*`
    have hp := Work.FTS.NonlinRows.Rl1.profile_data_sq (d := 60 * α) (by positivity)
    have hmain := Work.FTS.NonlinRows.Rl1.Fa_le_of_profile
      (N := Work.FTS.Nonlin.N5gs α f)
      (c := fun r => 60 * α * r / (1 + r) ^ 2)
      (M := fun r => 4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r))
      (Ψ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f) (C := 16)
      (by norm_num)
      (fun r hr => by positivity)
      (fun r => by positivity)
      s0.nonneg s0.meas s0.int hp.1 hp.2.1
      (fun r hr => le_of_eq (by
        rw [mul_pow, Real.sq_sqrt (s0.nonneg r)]
        norm_num))
      (fun r hr θ hθ => by
        have hFKabs := FK_abs_le_four_sqrt (f := f) hr (s0.sqint r hr) (s0.aesm r hr)
        have h1 := Work.FTS.NonlinRows.Rl1.N5gs_pt (α := α) (g := f) hα hα1 r hr θ hθ
        have h2 : 60 * α * (r / (1 + r) ^ 2) * |Work.Construction.FK f r|
            ≤ 60 * α * (r / (1 + r) ^ 2)
              * (4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r)) :=
          mul_le_mul_of_nonneg_left hFKabs (by positivity)
        have h3 : 60 * α * (r / (1 + r) ^ 2)
              * (4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r))
            = (60 * α * r / (1 + r) ^ 2)
              * (4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r)) := by ring
        exact h1.trans (h2.trans (le_of_eq h3)))
    refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [sqrt_sixteen]
    have h60 : Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
        (r⁻¹ * (60 * α * r / (1 + r) ^ 2)) ^ 2) ≤ 60 * α * 2 :=
      hp.2.2.2.trans (by nlinarith [Real.sqrt_nonneg 2, hrad2, hα.le])
    have hAB : Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r)
        * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          (r⁻¹ * (60 * α * r / (1 + r) ^ 2)) ^ 2)
        ≤ Work.FTS.Nonlin.Xn α f * (60 * α * 2) :=
      mul_le_mul hsqrtX h60 (Real.sqrt_nonneg _) hX0
    have hstep : Real.pi / 2 * (4 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r)
        * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          (r⁻¹ * (60 * α * r / (1 + r) ^ 2)) ^ 2))
        ≤ Real.pi / 2 * (4 * Work.FTS.Nonlin.Xn α f * (60 * α * 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc 4 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
              Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r)
            * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
              (r⁻¹ * (60 * α * r / (1 + r) ^ 2)) ^ 2)
          = 4 * (Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
                Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f r)
              * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
                (r⁻¹ * (60 * α * r / (1 + r) ^ 2)) ^ 2)) := by ring
        _ ≤ 4 * (Work.FTS.Nonlin.Xn α f * (60 * α * 2)) :=
            mul_le_mul_of_nonneg_left hAB (by norm_num)
        _ = 4 * Work.FTS.Nonlin.Xn α f * (60 * α * 2) := by ring
    refine hstep.trans ?_
    have h1 : Real.pi / 2 * (4 * Work.FTS.Nonlin.Xn α f * (60 * α * 2))
        = (240 * Real.pi) * (α * Work.FTS.Nonlin.Xn α f) := by ring
    rw [h1]
    calc (240 * Real.pi) * (α * Work.FTS.Nonlin.Xn α f)
        ≤ (240 * Real.pi) * Work.FTS.NonlinRows.Rl1.Env α f :=
          mul_le_mul_of_nonneg_left hαX (by positivity)
      _ ≤ (1000 * Real.pi + 1) * Work.FTS.NonlinRows.Rl1.Env α f :=
          mul_le_mul_of_nonneg_right hKbig hEnvn

end

end Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.N0gL12Sup =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

open Work.FTS.GalBasis.cc (Gaz Sw Wlam BK W2 BK_nonneg Wlam_nonneg continuous_sw)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000


/-! ## The pointwise bound on the `L₁₂`-density -/


/-! ## The main bound -/


/-! ## The target -/


end Work.FTS.StrongPersist.L3Rhs
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.N0gLocal =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The factored form of `Wf` -/

/-- `Wf α f = c₂(θ) · (L₁₂(F_*(α))(z) · D_z f)` — the association of the product
`(c₂ · L₁₂(F_*)) · D_z f` in the form in which the two multipliers are applied successively. -/
private theorem Wf_factor (α : ℝ) (f : Fn) :
    Wf α f = fun z θ => Work.Construction.c2m θ
      * (Work.Construction.L12 (Work.Construction.Fstar α) z * Work.Spaces.Dz f z θ) := by
  funext z θ
  simp only [Wf]
  ring

/-! ## The `D_z`-shift -/

/-- **`D_z` costs exactly one `ℋ`-order**: for `SmoothOpen f ∈ ℋ⁴`, the radial derivative
`D_z f` is in `ℋ³` and its `ℋ³`-square is dominated by the `ℋ⁴`-square of `f`.  This is the
pair `Work.FTS.IPGen.HkMem_Dz_le` (membership) and
`Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm` (integrated pointwise domination of the
integrands). -/
private theorem HkMem_HkSq_Dz_shift {α : ℝ} {f : Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 4 f) :
    Work.Spaces.HkMem α 3 (Work.Spaces.Dz f) ∧
      Work.Spaces.HkSq α 3 (Work.Spaces.Dz f) ≤ Work.Spaces.HkSq α 4 f := by
  have hq : Work.FTS.CoercivityFix.Transfer.Q0Sm 4 f := by
    rw [Work.FTS.CoercivityFix.Transfer.q0Sm_iff]
    exact (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hsm 4
  exact ⟨Work.FTS.IPGen.HkMem_Dz_le hsm hm,
    Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm α 3 hq hm⟩

/-! ## Smoothness of the radial coefficient -/

/-- `L₁₂(F_*(α))` is `C^∞` on `(-1,∞)`: there it is the explicit rational function
`z ↦ 2α/(1+z)` (`Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one`). -/
private theorem contDiffOn_smoothOrder_L12Fstar {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => Work.Construction.L12 (Work.Construction.Fstar α) z)
      (Set.Ioi (-1)) := by
  have hbase : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => 2 * α / (1 + z))
      (Set.Ioi (-1)) := by
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => (1 : ℝ) + z)
        (Set.Ioi (-1)) := contDiffOn_const.add contDiffOn_id
    have h2 := (contDiffOn_const (c := 2 * α) :
      ContDiffOn ℝ Work.Stability.smoothOrder (fun _ : ℝ => 2 * α) (Set.Ioi (-1))).div h1
      (fun z hz => by
        have hz' : (-1 : ℝ) < z := hz
        have : (0 : ℝ) < 1 + z := by linarith
        linarith)
    exact h2
  refine hbase.congr (fun z hz => ?_)
  exact Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one hα hα1 hz

/-! ## The assembly -/

/-- **The assembly of `N0gLocal`** from the two multiplier estimates.  `CA` bounds the radial
multiplier `L₁₂(F_*(α))` and `CB` the angular one `c₂`; both are universal (independent of
`α ∈ (0,1]`), and the final constant is `√(CA·CB) + 1`. -/
private theorem N0gLocal_assembly (CA CB : ℝ) (hCA : 0 < CA) (hCB : 0 < CB)
    (hA : ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ g : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 3 g →
      Work.Spaces.HkMem α 3
          (fun z θ => Work.Construction.L12 (Work.Construction.Fstar α) z * g z θ) ∧
      Work.Spaces.HkSq α 3
          (fun z θ => Work.Construction.L12 (Work.Construction.Fstar α) z * g z θ)
        ≤ CA * Work.Spaces.HkSq α 3 g)
    (hB : ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ g : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 3 g →
      Work.Spaces.HkMem α 3 (fun z θ => Work.Construction.c2m θ * g z θ) ∧
      Work.Spaces.HkSq α 3 (fun z θ => Work.Construction.c2m θ * g z θ)
        ≤ CB * Work.Spaces.HkSq α 3 g) :
    ∃ C α₂ : ℝ, 0 < C ∧ 0 < α₂ ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ (f : Fn) (M : ℝ),
        H6Adm α f → Work.FTS.Nonlin.Xn α f ≤ M →
        Work.Spaces.HkMem α 3 (Wf α f) ∧
        Work.Spaces.HkNorm α 3 (Wf α f) ≤ C * (1 + M) := by
  refine ⟨Real.sqrt (CA * CB) + 1, 1, by positivity, one_pos, ?_⟩
  intro α hα f M hadm hM
  obtain ⟨hα0, hα1⟩ := hα
  have hαIoc : α ∈ Set.Ioc (0 : ℝ) 1 := ⟨hα0, hα1⟩
  -- the honest regularity of the datum
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hadm.reg.1
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm 4 (by norm_num) hadm.reg.2
  -- the `D_z`-shift
  obtain ⟨hUmem, hUshift⟩ := HkMem_HkSq_Dz_shift hsm hmem4
  -- the radial multiplier
  have hV : Work.Spaces.HkMem α 3
        (fun z θ => Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz f z θ) ∧
      Work.Spaces.HkSq α 3
        (fun z θ => Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz f z θ)
        ≤ CA * Work.Spaces.HkSq α 3 (Work.Spaces.Dz f) :=
    hA α hαIoc (Work.Spaces.Dz f) hsm.Dz hUmem
  -- the angular multiplier
  have hVsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.L12 (Work.Construction.Fstar α) z * Work.Spaces.Dz f z θ) :=
    Work.FTS.StrongPersist.L3Aux.smoothOpen_zmul
      (contDiffOn_smoothOrder_L12Fstar hα0 hα1) hsm.Dz
  have hW : Work.Spaces.HkMem α 3 (fun z θ => Work.Construction.c2m θ
        * (Work.Construction.L12 (Work.Construction.Fstar α) z * Work.Spaces.Dz f z θ)) ∧
      Work.Spaces.HkSq α 3 (fun z θ => Work.Construction.c2m θ
        * (Work.Construction.L12 (Work.Construction.Fstar α) z * Work.Spaces.Dz f z θ))
        ≤ CB * Work.Spaces.HkSq α 3
          (fun z θ => Work.Construction.L12 (Work.Construction.Fstar α) z
            * Work.Spaces.Dz f z θ) :=
    hB α hαIoc (fun z θ => Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.Dz f z θ) hVsm hV.1
  refine ⟨?_, ?_⟩
  · rw [Wf_factor]
    exact hW.1
  · -- the squared estimate
    have hsq : Work.Spaces.HkSq α 3 (Wf α f) ≤ CA * CB * Work.Spaces.HkSq α 4 f := by
      rw [Wf_factor]
      calc Work.Spaces.HkSq α 3 (fun z θ => Work.Construction.c2m θ
              * (Work.Construction.L12 (Work.Construction.Fstar α) z * Work.Spaces.Dz f z θ))
          ≤ CB * Work.Spaces.HkSq α 3 (fun z θ => Work.Construction.L12
              (Work.Construction.Fstar α) z * Work.Spaces.Dz f z θ) := hW.2
        _ ≤ CB * (CA * Work.Spaces.HkSq α 3 (Work.Spaces.Dz f)) :=
              mul_le_mul_of_nonneg_left hV.2 hCB.le
        _ ≤ CB * (CA * Work.Spaces.HkSq α 4 f) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hUshift hCA.le) hCB.le
        _ = CA * CB * Work.Spaces.HkSq α 4 f := by ring
    have hM0 : 0 ≤ M := le_trans (Real.sqrt_nonneg _) hM
    have hroot : Work.Spaces.HkNorm α 3 (Wf α f) ≤ Real.sqrt (CA * CB) * M := by
      have hkey : Real.sqrt (Work.Spaces.HkSq α 3 (Wf α f)) ≤ Real.sqrt (CA * CB) * M := by
        calc Real.sqrt (Work.Spaces.HkSq α 3 (Wf α f))
            ≤ Real.sqrt (CA * CB * Work.Spaces.HkSq α 4 f) := Real.sqrt_le_sqrt hsq
          _ = Real.sqrt (CA * CB) * Real.sqrt (Work.Spaces.HkSq α 4 f) :=
                Real.sqrt_mul (mul_nonneg hCA.le hCB.le) _
          _ ≤ Real.sqrt (CA * CB) * M :=
                mul_le_mul_of_nonneg_left (by simpa only [Work.Spaces.HkNorm] using hM)
                  (Real.sqrt_nonneg _)
      simpa only [Work.Spaces.HkNorm] using hkey
    refine le_trans hroot ?_
    nlinarith [Real.sqrt_nonneg (CA * CB), hM0]

theorem N0gLocal : ∃ C α₂ : ℝ, 0 < C ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ),
      Work.FTS.StrongPersist.H6Adm α f → Work.FTS.Nonlin.Xn α f ≤ M →
      Work.Spaces.HkMem α 3 (Work.FTS.StrongPersist.L3Rhs.Wf α f) ∧
      Work.Spaces.HkNorm α 3 (Work.FTS.StrongPersist.L3Rhs.Wf α f) ≤ C * (1 + M) := by
  obtain ⟨CA, hCA, hA⟩ := L12F_mul_HkSq_le
  obtain ⟨CB, hCB, hB⟩ := c2m_mul_HkSq_le
  exact N0gLocal_assembly CA CB hCA hCB hA hB

end Work.FTS.StrongPersist.L3Rhs
end
end
