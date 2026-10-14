import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.PhiStar.Honesty.smoothCptQ_hkMem
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartAux
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.N0SlotSplitAux
import Submission.Work.FTS.StrongPersist.H6Rows.H6Pair_of_rows_C6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkMomentJetSq
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumGamSin
import Submission.Work.FTS.StrongPersist.StarPkg6Assembly
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.H2W.FstarDzIterFourPsiAe
import Submission.Work.Spaces.sin_two_rpow
-- ===== merged: Submission.Work.FTS.PhiStar.RouteB.psiSeries_L2_of_approx =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.FTS.PhiStar.RouteB

local notation "SMO" => Work.FTS.EllipticEst.SmoothOpen
local notation "HK" => Work.Spaces.HkMem
local notation "HKS" => Work.Spaces.HkSq
local notation "Q0" => Work.FTS.EllipticEst.Q0
local notation "Iz" => Work.Spaces.Iz
local notation "Iθ" => Work.Spaces.Iθ
local notation "psiSeries" => Work.FTS.PhiStar.Series.psiSeries
local notation "Mprod" => MeasureTheory.Measure.prod
  (MeasureTheory.volume.restrict Work.Spaces.Iz)
  (MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-- `SmoothOpen` is closed under differences. -/
theorem smoothOpen_diff {X Y : ℝ → ℝ → ℝ} (hX : SMO X) (hY : SMO Y) :
    SMO (fun z θ => X z θ - Y z θ) := by
  have hfun : Function.uncurry (fun z θ => X z θ - Y z θ)
      = Function.uncurry X - Function.uncurry Y := by
    funext p; rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, hfun]
  exact ContDiffOn.sub hX hY

/-- `HkMem` is closed under differences of `SmoothOpen` data. -/
theorem hkMem_diff_of_smoothOpen {α : ℝ} {k : ℕ} {X Y : ℝ → ℝ → ℝ}
    (hX : SMO X) (hY : SMO Y) (hmX : HK α k X) (hmY : HK α k Y) :
    HK α k (fun z θ => X z θ - Y z θ) :=
  Work.FTS.PhiStar.Honesty.EllWeakAux.HkMem_sub_of_eqOn_Q0 α k hX hY hmX hmY
    (fun z _ θ _ _ => rfl)

/-- The open quadrant is measurable. -/
theorem measurableSet_Q0 : MeasurableSet Q0 :=
  (isOpen_Ioi.prod isOpen_Ioo).measurableSet


/-- The angular weight `sin θ cos²θ` is continuous. -/
theorem continuous_sinCos2 : Continuous Work.Elliptic.sinCos2 := by
  unfold Work.Elliptic.sinCos2
  fun_prop

/-- The angular moment of a difference of two globally continuous sources splits. -/
theorem Fstar_diff {X Y : ℝ → ℝ → ℝ}
    (hX : ∀ z : ℝ, Continuous (fun θ : ℝ => X z θ))
    (hY : ∀ z : ℝ, Continuous (fun θ : ℝ => Y z θ)) (z : ℝ) :
    Work.Elliptic.Fstar (fun z θ => X z θ - Y z θ) z
      = Work.Elliptic.Fstar X z - Work.Elliptic.Fstar Y z := by
  have h1 : IntegrableOn (fun θ : ℝ => X z θ * Work.Elliptic.sinCos2 θ) Iθ :=
    ((hX z).mul continuous_sinCos2).continuousOn.integrableOn_compact isCompact_Icc
  have h2 : IntegrableOn (fun θ : ℝ => Y z θ * Work.Elliptic.sinCos2 θ) Iθ :=
    ((hY z).mul continuous_sinCos2).continuousOn.integrableOn_compact isCompact_Icc
  simp only [Work.Elliptic.Fstar]
  rw [← MeasureTheory.integral_sub h1 h2]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)

/-- The main assembly, with the three analytic inputs (`psiSeries` additivity, the `∫⁻`-domination
by `HkSq`, and the uniform level-`0` estimate for `psiSeries`) taken as hypotheses. -/
theorem psiSeries_L2_of_approx_aux {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hL2bd : ∀ {Y : ℝ → ℝ → ℝ}, HK α 0 Y →
        AEMeasurable (Function.uncurry Y) Mprod →
        (∫⁻ p in Q0, ENNReal.ofReal ((Y p.1 p.2) ^ 2)) ≤ ENNReal.ofReal (HKS α 0 Y))
    (C : ℝ) (hCpos : 0 < C)
    (hbdu : ∀ {X : ℝ → ℝ → ℝ}, SMO X → HK α 1 X →
      (∀ z : ℝ, 0 < z → Work.Elliptic.Fstar X z = 0) →
      HKS α 0 (psiSeries α X) ≤ C * HKS α 0 X)
    (K : ℕ) (hK : 2 ≤ K) {F : ℝ → ℝ → ℝ} (hsmF : SMO F) (hF : HK α K F)
    (G : ℕ → ℝ → ℝ → ℝ) (hG : ∀ n : ℕ, Work.FTS.PhiStar.Honesty.SmoothCptQ (G n))
    (hGs : ∀ n : ℕ, ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (G n) z = 0)
    (hconv : Tendsto (fun n : ℕ => HKS α K (fun z θ => G n z θ - F z θ)) atTop (nhds 0))
    {Φ : ℝ → ℝ → ℝ}
    (hΦ : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → Φ z θ = psiSeries α F z θ) :
    (∀ n : ℕ, IntegrableOn (fun p : ℝ × ℝ =>
        (psiSeries α (G n) p.1 p.2 - Φ p.1 p.2) ^ 2) Q0) ∧
    Tendsto (fun n : ℕ => ∫ p in Q0,
        (psiSeries α (G n) p.1 p.2 - Φ p.1 p.2) ^ 2) atTop (nhds 0) := by
  have hα1 : α ≤ 1 := by linarith
  -- ## sources, their smoothness, honesty and moments
  have hGsm : ∀ n, SMO (G n) := fun n => (hG n).smoothOpen
  have hGmem : ∀ n k, HK α k (G n) :=
    fun n k => Work.FTS.PhiStar.Honesty.smoothCptQ_hkMem (hG n) k
  have hFmem : ∀ l, l ≤ K → HK α l F :=
    fun l hl => Work.FTS_EllLimOK.PkgJets.HkMem_mono_le hsmF hl hF
  have hDsm : ∀ n, SMO (fun z θ => G n z θ - F z θ) :=
    fun n => smoothOpen_diff (hGsm n) hsmF
  have hDmem : ∀ n l, l ≤ K → HK α l (fun z θ => G n z θ - F z θ) :=
    fun n l hl => hkMem_diff_of_smoothOpen (hGsm n) hsmF (hGmem n l) (hFmem l hl)
  have hEsm : ∀ n m, SMO (fun z θ => G n z θ - G m z θ) :=
    fun n m => smoothOpen_diff (hGsm n) (hGsm m)
  have hEmem : ∀ n m l, HK α l (fun z θ => G n z θ - G m z θ) :=
    fun n m l => hkMem_diff_of_smoothOpen (hGsm n) (hGsm m) (hGmem n l) (hGmem m l)
  have hGcont : ∀ n z, Continuous (fun θ : ℝ => G n z θ) := fun n z =>
    ((hG n).smooth 0).continuous.comp (continuous_const.prodMk continuous_id)
  have hEor : ∀ n m z, 0 < z → Work.Elliptic.Fstar (fun z θ => G n z θ - G m z θ) z = 0 := by
    intro n m z hz
    rw [Fstar_diff (fun z => hGcont n z) (fun z => hGcont m z) z,
      hGs n z hz, hGs m z hz, sub_zero]
  have hGsq : ∀ n, IntegrableOn (fun p : ℝ × ℝ => G n p.1 p.2 ^ 2) Q0 :=
    fun n => Work.FTS.PhiStar.integrableOn_sq_Q0_of_HkMem (hGmem n 0) (hGsm n)
  have hEsq : ∀ n m, IntegrableOn (fun p : ℝ × ℝ => (G n p.1 p.2 - G m p.1 p.2) ^ 2) Q0 :=
    fun n m => Work.FTS.PhiStar.integrableOn_sq_Q0_of_HkMem (hEmem n m 0) (hEsm n m)
  -- ## (1) pointwise convergence of the approximating series to `Φ`
  have hconv0 : Tendsto (fun n : ℕ => HKS α 0 (fun z θ => G n z θ - F z θ)) atTop (nhds 0) := by
    refine squeeze_zero (fun n => Work.Spaces.HkSq_nonneg α 0 _) (fun n => ?_) hconv
    exact Work.FTS_EllLimOK.PkgJets.HkSq_mono_le (Nat.zero_le K) (hDmem n K le_rfl)
  have hPt : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      Tendsto (fun n : ℕ => psiSeries α (G n) z θ) atTop (nhds (Φ z θ)) := by
    intro z hz θ hθ0 hθ2
    have h := Work.FTS.PhiStar.Honesty.psiSeries_tendsto_of_HkSq hα hα4 hGsm hsmF
      (fun n => hGmem n 0) (hFmem 0 (Nat.zero_le K)) hconv0 z hz θ hθ0 hθ2
    rwa [hΦ z hz θ hθ0 hθ2]
  -- ## (2) the `∫⁻`-estimate for the difference of two solutions
  have hmono : MeasureTheory.volume.restrict Q0 ≤ Mprod := by
    have hsub : Q0 ⊆ Iz ×ˢ Iθ := by
      rw [Work.FTS.EllipticEst.Q0, Work.Spaces.Iz, Work.Spaces.Iθ]
      exact Set.prod_mono Set.Ioi_subset_Ici_self Set.Ioo_subset_Icc_self
    rw [MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.Measure.restrict_mono_set volume hsub
  have hSmeas : ∀ {X : ℝ → ℝ → ℝ}, SMO X → HK α 0 X → HK α 1 X →
      AEMeasurable (fun p : ℝ × ℝ => psiSeries α X p.1 p.2) Mprod :=
    fun hsm hm0 hm1 => Work.FTS.ClassCHon.CmpSupp.aemeasurable_psiSeries_uncurry
      (fun m => Work.FTS.ClassCHon.aemeasurable_acoeff_of_source hα hα4 hsm hm0 hm1 m)
  have hpair_meas : ∀ n m : ℕ, AEMeasurable (fun p : ℝ × ℝ =>
      (psiSeries α (G n) p.1 p.2 - psiSeries α (G m) p.1 p.2) ^ 2)
      (MeasureTheory.volume.restrict Q0) := by
    intro n m
    have h1 := (hSmeas (hGsm n) (hGmem n 0) (hGmem n 1)).sub
      (hSmeas (hGsm m) (hGmem m 0) (hGmem m 1))
    exact (h1.pow_const 2).mono_measure hmono
  have hseq_meas : ∀ n m : ℕ, AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
      ((psiSeries α (G n) p.1 p.2 - psiSeries α (G m) p.1 p.2) ^ 2))
      (MeasureTheory.volume.restrict Q0) :=
    fun n m => (hpair_meas n m).ennreal_ofReal
  have hEhk : ∀ n m, HK α 0 (psiSeries α (fun z θ => G n z θ - G m z θ)) :=
    fun n m => (Work.FTS.ClassCHon.hkMem_zero_psiSeries_of_source hα hα4 (hEsm n m)
      (hEmem n m 1) (hEor n m)).1
  have hpair : ∀ n m : ℕ,
      (∫⁻ p in Q0, ENNReal.ofReal
        ((psiSeries α (G n) p.1 p.2 - psiSeries α (G m) p.1 p.2) ^ 2))
        ≤ ENNReal.ofReal (C * (2 * (HKS α K (fun z θ => G n z θ - F z θ)
            + HKS α K (fun z θ => G m z θ - F z θ)))) := by
    intro n m
    -- additivity of the series in the source, on the open quadrant
    have hlin : (fun p : ℝ × ℝ => ENNReal.ofReal
          ((psiSeries α (G n) p.1 p.2 - psiSeries α (G m) p.1 p.2) ^ 2))
        =ᵐ[MeasureTheory.volume.restrict Q0]
        (fun p : ℝ × ℝ => ENNReal.ofReal
          ((psiSeries α (fun z θ => G n z θ - G m z θ) p.1 p.2) ^ 2)) :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Q0 fun p hp =>
        congrArg (fun t : ℝ => ENNReal.ofReal (t ^ 2))
          (psiSeries_sub_eqOn hα hα4 (hGsm n) (hGsm m) (hGmem n 0) (hGmem m 0)
            (hGmem n 1) (hGmem m 1) (hGs n) (hGs m) (hGsq n) (hGsq m)
            (hEsm n m) (hEor n m) (hEsq n m) p.1 hp.1 p.2 hp.2.1 hp.2.2)
    rw [MeasureTheory.lintegral_congr_ae hlin]
    -- the source estimate and the subadditivity in the levels
    have h2 : HKS α 0 (fun z θ => G n z θ - G m z θ)
        ≤ 2 * (HKS α K (fun z θ => G n z θ - F z θ)
            + HKS α K (fun z θ => G m z θ - F z θ)) := by
      have hsub := Work.FTS.PhiStar.Honesty.SlotsLimit.HkSq_sub_le_open α 0 (hDsm n) (hDsm m)
        (hDmem n 0 (Nat.zero_le K)) (hDmem m 0 (Nat.zero_le K))
      have heq : (fun z θ => (G n z θ - F z θ) - (G m z θ - F z θ))
          = fun z θ => G n z θ - G m z θ := by funext z θ; ring
      rw [heq] at hsub
      have h1' := Work.FTS_EllLimOK.PkgJets.HkSq_mono_le (m := 0) (k := K)
        (Nat.zero_le K) (hDmem n K le_rfl)
      have h2' := Work.FTS_EllLimOK.PkgJets.HkSq_mono_le (m := 0) (k := K)
        (Nat.zero_le K) (hDmem m K le_rfl)
      linarith
    refine le_trans (hL2bd (hEhk n m)
      (hSmeas (hEsm n m) (hEmem n m 0) (hEmem n m 1))) ?_
    refine ENNReal.ofReal_le_ofReal ?_
    calc HKS α 0 (psiSeries α (fun z θ => G n z θ - G m z θ))
        ≤ C * HKS α 0 (fun z θ => G n z θ - G m z θ) :=
          hbdu (hEsm n m) (hEmem n m 1) (hEor n m)
      _ ≤ C * (2 * (HKS α K (fun z θ => G n z θ - F z θ)
            + HKS α K (fun z θ => G m z θ - F z θ))) :=
          mul_le_mul_of_nonneg_left h2 hCpos.le
  -- ## (3) Fatou: the limit is controlled by the pairwise estimates
  have hbound : ∀ n : ℕ,
      (∫⁻ p in Q0, ENNReal.ofReal ((psiSeries α (G n) p.1 p.2 - Φ p.1 p.2) ^ 2))
        ≤ ENNReal.ofReal (C * (2 * HKS α K (fun z θ => G n z θ - F z θ))) := by
    intro n
    have hfat := MeasureTheory.lintegral_liminf_le' (μ := MeasureTheory.volume.restrict Q0)
      (u := Filter.atTop)
      (f := fun m (p : ℝ × ℝ) => ENNReal.ofReal
        ((psiSeries α (G n) p.1 p.2 - psiSeries α (G m) p.1 p.2) ^ 2)) (hseq_meas n)
    have hlim_eq : (fun p : ℝ × ℝ => liminf (fun m : ℕ => ENNReal.ofReal
          ((psiSeries α (G n) p.1 p.2 - psiSeries α (G m) p.1 p.2) ^ 2)) Filter.atTop)
        =ᵐ[MeasureTheory.volume.restrict Q0]
        (fun p : ℝ × ℝ => ENNReal.ofReal ((psiSeries α (G n) p.1 p.2 - Φ p.1 p.2) ^ 2)) := by
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Q0 fun p hp => ?_
      have htend : Tendsto (fun m : ℕ => psiSeries α (G m) p.1 p.2) Filter.atTop
          (nhds (Φ p.1 p.2)) := hPt p.1 hp.1 p.2 hp.2.1 hp.2.2
      have hcont : Continuous (fun x : ℝ =>
          ENNReal.ofReal ((psiSeries α (G n) p.1 p.2 - x) ^ 2)) :=
        ENNReal.continuous_ofReal.comp ((continuous_const.sub continuous_id).pow 2)
      exact (hcont.continuousAt.tendsto.comp htend).liminf_eq
    rw [MeasureTheory.lintegral_congr_ae hlim_eq] at hfat
    refine hfat.trans ?_
    refine Filter.liminf_le_of_le
      (Filter.isBoundedUnder_of ⟨0, fun m => bot_le⟩) fun b hb => ?_
    refine le_of_tendsto_of_tendsto tendsto_const_nhds ?_
      (hb.mono fun m hm => le_trans hm (hpair n m))
    have h2 : Tendsto (fun m : ℕ => 2 * (HKS α K (fun z θ => G n z θ - F z θ)
        + HKS α K (fun z θ => G m z θ - F z θ))) Filter.atTop
        (nhds (2 * HKS α K (fun z θ => G n z θ - F z θ))) := by
      have h := (tendsto_const_nhds (x := HKS α K (fun z θ => G n z θ - F z θ))
        (f := Filter.atTop)).add hconv
      have h' := h.const_mul 2
      simpa using h'
    have h3 : Tendsto (fun m : ℕ => C * (2 * (HKS α K (fun z θ => G n z θ - F z θ)
        + HKS α K (fun z θ => G m z θ - F z θ)))) Filter.atTop
        (nhds (C * (2 * HKS α K (fun z θ => G n z θ - F z θ)))) := h2.const_mul C
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp h3
  -- ## (4) integrability and convergence
  have hmeas_tend : ∀ n : ℕ, AEMeasurable (fun p : ℝ × ℝ =>
      (psiSeries α (G n) p.1 p.2 - Φ p.1 p.2) ^ 2) (MeasureTheory.volume.restrict Q0) := by
    intro n
    refine aemeasurable_of_tendsto_metrizable_ae'
      (f := fun m (p : ℝ × ℝ) =>
        (psiSeries α (G n) p.1 p.2 - psiSeries α (G m) p.1 p.2) ^ 2)
      (hpair_meas n) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Q0 fun p hp => ?_
    have htend : Tendsto (fun m : ℕ => psiSeries α (G m) p.1 p.2) Filter.atTop
        (nhds (Φ p.1 p.2)) := hPt p.1 hp.1 p.2 hp.2.1 hp.2.2
    exact ((continuous_const.sub continuous_id).pow 2).continuousAt.tendsto.comp htend
  have hfin_int : ∀ n : ℕ, IntegrableOn (fun p : ℝ × ℝ =>
      (psiSeries α (G n) p.1 p.2 - Φ p.1 p.2) ^ 2) Q0 := by
    intro n
    have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
        (psiSeries α (G n) p.1 p.2 - Φ p.1 p.2) ^ 2) (MeasureTheory.volume.restrict Q0) :=
      (hmeas_tend n).aestronglyMeasurable
    refine ⟨haesm, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun p => sq_nonneg _)]
    exact lt_of_le_of_lt (hbound n) ENNReal.ofReal_lt_top
  refine ⟨hfin_int, ?_⟩
  have hint_eq : ∀ n : ℕ, (∫ p in Q0, (psiSeries α (G n) p.1 p.2 - Φ p.1 p.2) ^ 2)
      = ((∫⁻ p in Q0, ENNReal.ofReal
          ((psiSeries α (G n) p.1 p.2 - Φ p.1 p.2) ^ 2))).toReal :=
    fun n => MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun p => sq_nonneg _) (hfin_int n).1
  have hlim : Tendsto (fun n : ℕ =>
      C * (2 * HKS α K (fun z θ => G n z θ - F z θ))) Filter.atTop (nhds 0) := by
    have h := hconv.const_mul (C * 2)
    simpa only [mul_zero, mul_assoc] using h
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hlim
  · rw [hint_eq n]; exact ENNReal.toReal_nonneg
  · rw [hint_eq n]
    have hnn : 0 ≤ C * (2 * HKS α K (fun z θ => G n z θ - F z θ)) :=
      mul_nonneg hCpos.le (mul_nonneg (by norm_num) (Work.Spaces.HkSq_nonneg α K _))
    exact le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbound n))
      (le_of_eq (ENNReal.toReal_ofReal hnn))

/-- **R3 of the `RouteB` node**: the approximating mode series converge to the witness `Φ` in
`L²(Q0)`, from `H^K`-convergence of the sources. -/
theorem psiSeries_L2_of_approx (K : ℕ) (hK : 2 ≤ K) {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {F : ℝ → ℝ → ℝ} (hsmF : Work.FTS.EllipticEst.SmoothOpen F)
    (hF : Work.Spaces.HkMem α K F)
    (G : ℕ → ℝ → ℝ → ℝ) (hG : ∀ n : ℕ, Work.FTS.PhiStar.Honesty.SmoothCptQ (G n))
    (hGs : ∀ n : ℕ, ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (G n) z = 0)
    (hconv : Filter.Tendsto (fun n : ℕ => Work.Spaces.HkSq α K (fun z θ => G n z θ - F z θ))
      Filter.atTop (nhds 0))
    {Φ : ℝ → ℝ → ℝ}
    (hΦ : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      Φ z θ = Work.FTS.PhiStar.Series.psiSeries α F z θ) :
    (∀ n : ℕ, MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.FTS.PhiStar.Series.psiSeries α (G n) p.1 p.2 - Φ p.1 p.2) ^ 2)
      Work.FTS.EllipticEst.Q0) ∧
    Filter.Tendsto (fun n : ℕ => ∫ p in Work.FTS.EllipticEst.Q0,
        (Work.FTS.PhiStar.Series.psiSeries α (G n) p.1 p.2 - Φ p.1 p.2) ^ 2)
      Filter.atTop (nhds 0) := by
  obtain ⟨C, hCpos, hbdu⟩ := Work.FTS.PhiStar.RouteB.exists_uniform_HkSq_psiSeries_le hα hα4
  exact psiSeries_L2_of_approx_aux hα hα4
    (fun hm hmeas => Work.FTS.PhiStar.RouteB.lintegral_sq_le_HkSq_zero hm hmeas)
    C hCpos hbdu K hK hsmF hF G hG hGs hconv hΦ

end Work.FTS.PhiStar.RouteB
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.Congr =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The `ℋ^k`-integrand only depends on the values of the function on the *closed* domain
`Iz × Iθ`. -/
theorem hkIntegrand_congr_Izθ {α : ℝ} {k : ℕ} {f f' : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, f z θ = f' z θ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k f z θ = Work.Spaces.HkIntegrand α k f' z θ := by
  intro z hz θ hθ
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
  · rw [← hz0, Work.FTS.LocData.HkIntegrand_zero_fst α k f,
      Work.FTS.LocData.HkIntegrand_zero_fst α k f']
  · by_cases hθi : θ ∈ Set.Ioo 0 (π / 2)
    · refine Work.FTS.StrongPersist.H6Pair6Aux.HkIntegrand_congr_Qd (f := f) (f' := f')
        (fun z' θ' hzθ' => ?_) z θ ⟨hzpos, hθi⟩
      have hz' : (0 : ℝ) < z' := hzθ'.1
      have hθ' : θ' ∈ Work.Spaces.Iθ := ⟨le_of_lt hzθ'.2.1, le_of_lt hzθ'.2.2⟩
      exact h z' (show z' ∈ Work.Spaces.Iz from le_of_lt hz') θ' hθ'
    · have hs : Real.sin (2 * θ) = 0 :=
        Work.Spaces.sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hθi
      rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k f z θ hs,
        Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k f' z θ hs]

/-- Honesty in `ℋ^k` transports along an equality on `Iz × Iθ`. -/
theorem hkMem_congr_Izθ {α : ℝ} {k : ℕ} {f f' : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, f z θ = f' z θ)
    (hf : Work.Spaces.HkMem α k f) : Work.Spaces.HkMem α k f' := by
  have hgoal := hkIntegrand_congr_Izθ (α := α) (k := k) (f := f) (f' := f') h
  obtain ⟨h1, h2⟩ := hf
  constructor
  · intro z hz
    exact (h1 z hz).congr (ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => hgoal z hz θ hθ))
  · refine h2.congr (ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_))
    exact setIntegral_congr_fun measurableSet_Icc (fun θ hθ => hgoal z hz θ hθ)

/-- The squared `ℋ^k`-norm transports along an equality on `Iz × Iθ`. -/
theorem hkSq_congr_Izθ {α : ℝ} {k : ℕ} {f f' : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, f z θ = f' z θ) :
    Work.Spaces.HkSq α k f = Work.Spaces.HkSq α k f' := by
  have hgoal := hkIntegrand_congr_Izθ (α := α) (k := k) (f := f) (f' := f') h
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  exact setIntegral_congr_fun measurableSet_Ici (fun z hz =>
    setIntegral_congr_fun measurableSet_Icc (fun θ hθ => hgoal z hz θ hθ))

/-- The `ℋ^k`-norm transports along an equality on `Iz × Iθ`. -/
theorem hkNorm_congr_Izθ {α : ℝ} {k : ℕ} {f f' : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, f z θ = f' z θ) :
    Work.Spaces.HkNorm α k f = Work.Spaces.HkNorm α k f' := by
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, hkSq_congr_Izθ h]

end

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
end
