import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.RegPkgGal.R5Parts
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.regFromVolterra
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.bump_mixed_EpsSq_le
import Submission.Work.FTS.StrongEps.RhsCont
import Submission.Work.FTS.StrongEps.epsWP_abs_le_on_compact
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.radialSupMul_cd6
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNstarBlock
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.SmainHon
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.ExcPairBranches
import Submission.Work.FTS.StrongPersist.SP6.F0SixYblk
import Submission.Work.FTS.StrongPersist.SP6.WlInf6OfFlatW
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.T2Sup.GenSlot
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.TransportS.t2SlotGuarded
import Submission.Work.FTS_MuLamOK.Conversion
import Submission.Work.FTS_MuLamOK.Defs
import Submission.Work.FTS_MuLamOK.RowReduction
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.R1G.vecResid_eq_scalar_smul
import Submission.Work.Stability.CutFactorFderivZero
-- ===== merged: Submission.Work.FTS.EpsEngine.VolterraV4Main =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongEps
open Work.FTS.StrongEps.EpsLocalPStar

namespace Work.FTS.EpsEngine

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The engine -/

theorem exists_volterra_v4 {α : ℝ} {F : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {h₀ : Work.FTS.Galerkin.Fn} {P : Work.FTS.Galerkin.Fn → Prop} {Cpt L δ : ℝ}
    (hδ : 0 < δ) (hL : 0 < L) (hδL : δ * Real.sqrt L < 1) (hCpt : 0 ≤ Cpt) (hP₀ : P h₀)
    (hbd : ∀ u : Work.FTS.Galerkin.Fn, P u →
      Work.FTS.StrongEps.EpsMem α (F u) ∧ Work.FTS.StrongEps.EpsSq α (F u) ≤ L)
    (hlip : ∀ u v : Work.FTS.Galerkin.Fn, P u → P v →
      Work.FTS.StrongEps.EpsMem α (fun z θ => u z θ - v z θ) →
      Work.FTS.StrongEps.EpsSq α (fun z θ => F u z θ - F v z θ)
        ≤ L * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ))
    (hpt : ∀ u v : Work.FTS.Galerkin.Fn, P u → P v → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F u z θ - F v z θ| ≤ Cpt * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)))
    (hcontP : ∀ u : Work.FTS.Galerkin.Fn, P u → ContinuousOn (fun q : ℝ × ℝ => F u q.1 q.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hzeroP : ∀ u : Work.FTS.Galerkin.Fn, P u → ∀ q : ℝ × ℝ,
      q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) → F u q.1 q.2 = 0)
    (hkeepIter : ∀ n : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      P (fun z θ => h₀ z θ + ∫ s in (0 : ℝ)..τ,
        F (Work.FTS.Galerkin.slice (iter F h₀ n) s) z θ))
    (hlimP : ∀ τ, τ ∈ Set.Icc 0 δ → P (Work.FTS.Galerkin.slice (limFam F h₀) τ)) :
    (∀ z θ, limFam F h₀ z θ 0 = h₀ z θ) ∧
      ∀ z θ τ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) → τ ∈ Set.Icc 0 δ →
        HasDerivWithinAt (fun s => limFam F h₀ z θ s)
          (F (Work.FTS.Galerkin.slice (limFam F h₀) τ) z θ) (Set.Icc 0 δ) τ := by
  classical  classical
  -- ## 0. numerical set-up
  have hδ0 : 0 ≤ δ := hδ.le
  have hL0 : 0 ≤ L := hL.le
  set q : ℝ := δ ^ 2 * L with hqdef
  have hq0 : 0 ≤ q := by rw [hqdef]; positivity
  have hqsq : q = (δ * Real.sqrt L) ^ 2 := by
    rw [hqdef, mul_pow, Real.sq_sqrt hL0]
  have hq1 : q < 1 := by
    rw [hqsq]
    exact pow_lt_one₀ (mul_nonneg hδ0 (Real.sqrt_nonneg L)) hδL (by norm_num)
  set r : ℝ := Real.sqrt q with hrdef
  have hr0 : 0 ≤ r := Real.sqrt_nonneg q
  have hr2 : r ^ 2 = q := by rw [hrdef]; exact Real.sq_sqrt hq0
  have hr1 : r < 1 := by nlinarith [hr0, hr2, hq1]
  have hrpow : ∀ n : ℕ, Real.sqrt (q ^ n) = r ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Real.sqrt_mul hq0, ← hrdef, ih, pow_succ']
  -- ## 0'. the a priori bounds (proved in `Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.IterBounds`)
  obtain ⟨hP, hB0, hBK, hwsq, hwpt⟩ :=
    iter_bounds_v4 (α := α) (F := F) (h₀ := h₀) (P := P) (Cpt := Cpt) (L := L)
      (δ := δ) (q := q) (r := r) hδ hL hδL hqdef hrdef hq0 hq1 hr0 hrpow hCpt hP₀ hbd hlip
      hpt hcontP hzeroP hkeepIter
  -- the two iterate-indexed hypotheses of the sibling engine, *derived* from the class data
  obtain ⟨hcontIter, hmeasIter⟩ :=
    iter_cont_meas (α := α) (Cpt := Cpt) (L := L) (δ := δ) (F := F) (h₀ := h₀) (P := P)
      hδ hL0 hCpt hP hcontP hzeroP hbd hpt

  -- ## 6. summability and convergence of the iterates
  have hsum : ∀ τ, τ ∈ Set.Icc 0 δ → ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Summable (fun n : ℕ => wseq F h₀ (n + 1) τ z θ) := by
    intro τ hτ z θ hz hθ0 hθ1
    have hgeo : Summable (fun n : ℕ => δ * Cpt * r ^ (n + 1)) := by
      have h := (summable_geometric_of_norm_lt_one
        (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)).mul_left (δ * Cpt * r)
      refine h.congr (fun n => ?_)
      rw [pow_succ']
      ring
    refine Summable.of_norm_bounded hgeo ?_
    intro n
    rw [Real.norm_eq_abs]
    exact hwpt (n + 1) τ hτ (by omega) z θ hz hθ0 hθ1
  have htsum : ∀ τ, τ ∈ Set.Icc 0 δ → ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HasSum (fun n : ℕ => wseq F h₀ (n + 1) τ z θ)
        (limFam F h₀ z θ τ - (h₀ z θ + wseq F h₀ 0 τ z θ)) := by
    intro τ hτ z θ hz hθ0 hθ1
    have h := (hsum τ hτ z θ hz hθ0 hθ1).hasSum
    have h2 : limFam F h₀ z θ τ - (h₀ z θ + wseq F h₀ 0 τ z θ)
        = ∑' n, wseq F h₀ (n + 1) τ z θ := by
      simp only [limFam]
      ring
    rw [h2]
    exact h
  have hconv : ∀ τ, τ ∈ Set.Icc 0 δ → ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun N : ℕ => slice (iter F h₀ N) τ z θ) Filter.atTop
        (nhds (limFam F h₀ z θ τ)) := by
    intro τ hτ z θ hz hθ0 hθ1
    have h1 := (htsum τ hτ z θ hz hθ0 hθ1).tendsto_sum_nat
    have h3 : Filter.Tendsto
        (fun N : ℕ => (∑ n ∈ Finset.range N, wseq F h₀ (n + 1) τ z θ)
          + (h₀ z θ + wseq F h₀ 0 τ z θ)) Filter.atTop
        (nhds (limFam F h₀ z θ τ)) := by
      have h := h1.add_const (h₀ z θ + wseq F h₀ 0 τ z θ)
      have h4 : (limFam F h₀ z θ τ - (h₀ z θ + wseq F h₀ 0 τ z θ))
          + (h₀ z θ + wseq F h₀ 0 τ z θ) = limFam F h₀ z θ τ := by ring
      rw [h4] at h
      exact h
    have heq : (fun N : ℕ => (∑ n ∈ Finset.range N, wseq F h₀ (n + 1) τ z θ)
          + (h₀ z θ + wseq F h₀ 0 τ z θ))
        =ᶠ[Filter.atTop] (fun N : ℕ => slice (iter F h₀ (N + 1)) τ z θ) := by
      filter_upwards with N
      rw [sum_wseq_shift]
      ring
    have htend : Filter.Tendsto (fun N : ℕ => slice (iter F h₀ (N + 1)) τ z θ) Filter.atTop
        (nhds (limFam F h₀ z θ τ)) := (Filter.tendsto_congr' heq).mp h3
    exact (Filter.tendsto_add_atTop_iff_nat 1).mp htend
  -- ## 7. `F` along the iterates converges to `FlimM`
  have hFsum : ∀ τ, τ ∈ Set.Icc 0 δ → ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Summable (fun n : ℕ => F (slice (iter F h₀ (n + 1)) τ) z θ
        - F (slice (iter F h₀ n) τ) z θ) := by
    intro τ hτ z θ hz hθ0 hθ1
    have hgeo : Summable (fun n : ℕ => Cpt * r ^ (n + 1)) := by
      have h := (summable_geometric_of_norm_lt_one
        (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)).mul_left (Cpt * r)
      refine h.congr (fun n => ?_)
      rw [pow_succ']
      ring
    refine Summable.of_norm_bounded hgeo ?_
    intro n
    rw [Real.norm_eq_abs]
    have hw : wseq F h₀ n τ
        = fun z θ => slice (iter F h₀ (n + 1)) τ z θ - slice (iter F h₀ n) τ z θ := rfl
    calc |F (slice (iter F h₀ (n + 1)) τ) z θ - F (slice (iter F h₀ n) τ) z θ|
        ≤ Cpt * Real.sqrt (EpsSq α (fun z θ => slice (iter F h₀ (n + 1)) τ z θ
            - slice (iter F h₀ n) τ z θ)) :=
          hpt _ _ (hP (n + 1) τ hτ) (hP n τ hτ) z θ hz hθ0 hθ1
      _ = Cpt * Real.sqrt (EpsSq α (wseq F h₀ n τ)) := by rw [hw]
      _ ≤ Cpt * r ^ (n + 1) := by
          rw [← hrpow (n + 1)]
          exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hwsq n τ hτ)) hCpt
  have hFlim : ∀ τ, τ ∈ Set.Icc 0 δ → ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun N : ℕ => F (slice (iter F h₀ N) τ) z θ) Filter.atTop
        (nhds (FlimM F h₀ z θ τ)) := by
    intro τ hτ z θ hz hθ0 hθ1
    have h1 := (hFsum τ hτ z θ hz hθ0 hθ1).hasSum
    have h2 : Filter.Tendsto
        (fun N : ℕ => (∑ n ∈ Finset.range N,
            (F (slice (iter F h₀ (n + 1)) τ) z θ - F (slice (iter F h₀ n) τ) z θ))
          + F h₀ z θ) Filter.atTop
        (nhds ((∑' n, (F (slice (iter F h₀ (n + 1)) τ) z θ
            - F (slice (iter F h₀ n) τ) z θ)) + F h₀ z θ)) :=
      h1.tendsto_sum_nat.add_const (F h₀ z θ)
    have h3 : (∑' n, (F (slice (iter F h₀ (n + 1)) τ) z θ
        - F (slice (iter F h₀ n) τ) z θ)) + F h₀ z θ = FlimM F h₀ z θ τ := by
      simp only [FlimM]
      ring
    rw [h3] at h2
    have heq : (fun N : ℕ => (∑ n ∈ Finset.range N,
            (F (slice (iter F h₀ (n + 1)) τ) z θ - F (slice (iter F h₀ n) τ) z θ))
          + F h₀ z θ)
        =ᶠ[Filter.atTop] (fun N : ℕ => F (slice (iter F h₀ N) τ) z θ) := by
      filter_upwards with N
      rw [sum_FlimM]
      ring
    exact (Filter.tendsto_congr' heq).mp h2
  have hFcauchy : ∀ M N τ, τ ∈ Set.Icc 0 δ → N ≤ M → ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F (slice (iter F h₀ M) τ) z θ - F (slice (iter F h₀ N) τ) z θ| ≤ Cpt * r ^ (N + 1) := by
    intro M N τ hτ hNM z θ hz hθ0 hθ1
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      rcases Nat.eq_zero_or_pos M with hM | hM
      · subst hM
        have h0 : slice (iter F h₀ 0) τ = h₀ := rfl
        rw [h0, sub_self, abs_zero]
        exact mul_nonneg hCpt (pow_nonneg hr0 1)
      · have hsq : EpsSq α (fun z θ => slice (iter F h₀ M) τ z θ - h₀ z θ) ≤ q :=
          (hB0 M τ hτ hM).2
        have h0 : slice (iter F h₀ 0) τ = h₀ := rfl
        calc |F (slice (iter F h₀ M) τ) z θ - F (slice (iter F h₀ 0) τ) z θ|
            = |F (slice (iter F h₀ M) τ) z θ - F h₀ z θ| := by rw [h0]
          _ ≤ Cpt * Real.sqrt (EpsSq α (fun z θ => slice (iter F h₀ M) τ z θ - h₀ z θ)) :=
              hpt _ _ (hP M τ hτ) hP₀ z θ hz hθ0 hθ1
          _ ≤ Cpt * r ^ (0 + 1) := by
              have hq1 : q ^ (0 + 1) = q := pow_one q
              rw [← hrpow (0 + 1), hq1]
              exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsq) hCpt
    · have hsq : EpsSq α (fun z θ => slice (iter F h₀ M) τ z θ
          - slice (iter F h₀ N) τ z θ) ≤ q ^ (N + 1) :=
        (hBK M N hN hNM τ hτ).2
      calc |F (slice (iter F h₀ M) τ) z θ - F (slice (iter F h₀ N) τ) z θ|
          ≤ Cpt * Real.sqrt (EpsSq α (fun z θ => slice (iter F h₀ M) τ z θ
              - slice (iter F h₀ N) τ z θ)) :=
            hpt _ _ (hP M τ hτ) (hP N τ hτ) z θ hz hθ0 hθ1
        _ ≤ Cpt * r ^ (N + 1) := by
            rw [← hrpow (N + 1)]
            exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsq) hCpt
  have hFbound : ∀ N τ, τ ∈ Set.Icc 0 δ → ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F (slice (iter F h₀ N) τ) z θ - FlimM F h₀ z θ τ| ≤ Cpt * r ^ (N + 1) := by
    intro N τ hτ z θ hz hθ0 hθ1
    have hlim := hFlim τ hτ z θ hz hθ0 hθ1
    have htend : Filter.Tendsto
        (fun M : ℕ => F (slice (iter F h₀ M) τ) z θ - F (slice (iter F h₀ N) τ) z θ)
        Filter.atTop (nhds (FlimM F h₀ z θ τ - F (slice (iter F h₀ N) τ) z θ)) :=
      hlim.sub_const _
    have hup : FlimM F h₀ z θ τ - F (slice (iter F h₀ N) τ) z θ ≤ Cpt * r ^ (N + 1) :=
      le_of_tendsto htend (Filter.eventually_atTop.2 ⟨N, fun M hM => by
        have h := hFcauchy M N τ hτ hM z θ hz hθ0 hθ1
        rw [abs_le] at h
        exact h.2⟩)
    have hlow : -(Cpt * r ^ (N + 1)) ≤ FlimM F h₀ z θ τ - F (slice (iter F h₀ N) τ) z θ :=
      ge_of_tendsto htend (Filter.eventually_atTop.2 ⟨N, fun M hM => by
        have h := hFcauchy M N τ hτ hM z θ hz hθ0 hθ1
        rw [abs_le] at h
        exact h.1⟩)
    rw [abs_sub_comm, abs_le]
    exact ⟨by linarith, by linarith⟩
  have hFcont : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ContinuousOn (fun s => FlimM F h₀ z θ s) (Set.Icc 0 δ) := by
    intro z θ hz hθ0 hθ1
    have hunif : TendstoUniformlyOn (fun N s => F (slice (iter F h₀ N) s) z θ)
        (fun s => FlimM F h₀ z θ s) Filter.atTop (Set.Icc 0 δ) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      have h0 : Filter.Tendsto (fun N : ℕ => Cpt * r ^ (N + 1)) Filter.atTop (nhds 0) := by
        have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp
          (tendsto_add_atTop_nat 1)
        simpa using h.const_mul Cpt
      obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 (h0.eventually (Iio_mem_nhds hε))
      filter_upwards [Filter.eventually_ge_atTop N₀] with N hN s hs
      rw [Real.dist_eq, abs_sub_comm]
      exact lt_of_le_of_lt (hFbound N s hs z θ hz hθ0 hθ1) (hN₀ N hN)
    exact hunif.continuousOn (Filter.frequently_atTop.2 fun a => ⟨a, le_refl a,
      hcontIter a z θ hz hθ0 hθ1⟩)
  -- ## 8. the integral (Volterra) identity for the limit family
  have hvol : ∀ τ, τ ∈ Set.Icc 0 δ → ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      limFam F h₀ z θ τ = h₀ z θ + ∫ s in (0 : ℝ)..τ, FlimM F h₀ z θ s := by
    intro τ hτ z θ hz hθ0 hθ1
    have h1 : ∀ N : ℕ, slice (iter F h₀ (N + 1)) τ z θ
        = h₀ z θ + ∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ N) s) z θ := by
      intro N
      rw [iter_succ F h₀ N]
      simp only [Work.FTS.Galerkin.slice_apply]
    have hd : ∀ N : ℕ, |(∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ N) s) z θ)
        - (∫ s in (0 : ℝ)..τ, FlimM F h₀ z θ s)| ≤ δ * Cpt * r ^ (N + 1) := by
      intro N
      have hint1 : IntervalIntegrable (fun s => F (slice (iter F h₀ N) s) z θ) volume 0 τ :=
        ContinuousOn.intervalIntegrable_of_Icc hτ.1
          ((hcontIter N z θ hz hθ0 hθ1).mono
            (Set.Icc_subset_Icc_right hτ.2))
      have hint2 : IntervalIntegrable (fun s => FlimM F h₀ z θ s) volume 0 τ :=
        ContinuousOn.intervalIntegrable_of_Icc hτ.1
          ((hFcont z θ hz hθ0 hθ1).mono (Set.Icc_subset_Icc_right hτ.2))
      have hb : ∀ s ∈ Set.uIoc (0 : ℝ) τ,
          ‖F (slice (iter F h₀ N) s) z θ - FlimM F h₀ z θ s‖ ≤ Cpt * r ^ (N + 1) := by
        intro s hs
        rw [Real.norm_eq_abs]
        have hsIcc : s ∈ Set.Icc 0 δ := by
          rw [Set.uIoc_of_le hτ.1] at hs
          exact ⟨le_of_lt hs.1, le_trans hs.2 hτ.2⟩
        exact hFbound N s hsIcc z θ hz hθ0 hθ1
      rw [← intervalIntegral.integral_sub hint1 hint2, ← Real.norm_eq_abs]
      have h3 := intervalIntegral.norm_integral_le_of_norm_le_const (C := Cpt * r ^ (N + 1))
        (a := (0 : ℝ)) (b := τ) hb
      rw [sub_zero, abs_of_nonneg hτ.1] at h3
      refine h3.trans ?_
      nlinarith [hτ.1, hτ.2, mul_nonneg hCpt (pow_nonneg hr0 (N + 1))]
    have h3 : Filter.Tendsto (fun N : ℕ => |(∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ N) s) z θ)
        - (∫ s in (0 : ℝ)..τ, FlimM F h₀ z θ s)|) Filter.atTop (nhds 0) := by
      refine squeeze_zero (fun N => abs_nonneg _) hd ?_
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp
        (tendsto_add_atTop_nat 1)
      simpa using h.const_mul (δ * Cpt)
    have h2 : Filter.Tendsto (fun N : ℕ => ∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ N) s) z θ)
        Filter.atTop (nhds (∫ s in (0 : ℝ)..τ, FlimM F h₀ z θ s)) :=
      tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa [Real.norm_eq_abs] using h3)
    have h4 : Filter.Tendsto (fun N : ℕ => slice (iter F h₀ (N + 1)) τ z θ) Filter.atTop
        (nhds (h₀ z θ + ∫ s in (0 : ℝ)..τ, FlimM F h₀ z θ s)) := by
      have h5 := h2.const_add (h₀ z θ)
      refine (Filter.tendsto_congr' ?_).mp h5
      filter_upwards with N
      exact (h1 N).symm
    refine tendsto_nhds_unique ?_ h4
    have h6 := (hconv τ hτ z θ hz hθ0 hθ1).comp (tendsto_add_atTop_nat 1)
    rw [show ((fun N : ℕ => slice (iter F h₀ N) τ z θ) ∘ fun a => a + 1)
        = fun N : ℕ => slice (iter F h₀ (N + 1)) τ z θ from rfl] at h6
    exact h6
  -- ## 9. the Fatou tail bound
  have htail : ∀ K : ℕ, 1 ≤ K → ∀ τ ∈ Set.Icc 0 δ,
      EpsMem α (fun z θ => slice (limFam F h₀) τ z θ - slice (iter F h₀ K) τ z θ) ∧
      EpsSq α (fun z θ => slice (limFam F h₀) τ z θ - slice (iter F h₀ K) τ z θ)
        ≤ q ^ (K + 1) := by
    intro K hK τ hτ
    have hAK : ∀ m : ℕ, AK2 α (fun z θ => slice (iter F h₀ (m + K)) τ z θ
        - slice (iter F h₀ K) τ z θ) := by
      intro m
      have heq : ∀ᵐ p ∂DomM,
          (slice (iter F h₀ (m + K)) τ p.1 p.2 - slice (iter F h₀ K) τ p.1 p.2)
          = ∫ s in (0 : ℝ)..τ, (F (slice (iter F h₀ (m + K - 1)) s) p.1 p.2
              - F (slice (iter F h₀ (K - 1)) s) p.1 p.2) :=
        ae_of_forall_open (fun z hz θ hθ0 hθ1 =>
          diff_eq_integral_v4 hP hcontIter hτ (by omega) hK hz hθ0 hθ1)
      have hAK2 : AK2 α (fun z θ => ∫ s in (0 : ℝ)..τ,
          (F (slice (iter F h₀ (m + K - 1)) s) z θ - F (slice (iter F h₀ (K - 1)) s) z θ)) := by
        refine AK2_intervalIntegral hτ.1 ?_
        have h1 := aesm_weighted_uIoc_of_restrict (α := α)
          (Φ := fun s => F (slice (iter F h₀ (m + K - 1)) s)) hτ (hmeasIter (m + K - 1))
        have h2 := aesm_weighted_uIoc_of_restrict (α := α)
          (Φ := fun s => F (slice (iter F h₀ (K - 1)) s)) hτ (hmeasIter (K - 1))
        exact (h1.sub h2).congr (by filter_upwards with p; simp only [Pi.sub_apply]; ring)
      exact AK2_congr_ae heq hAK2
    have hbd : ∀ m : ℕ, epsL2 α (fun z θ => slice (iter F h₀ (m + K)) τ z θ
        - slice (iter F h₀ K) τ z θ) ≤ ENNReal.ofReal (q ^ (K + 1)) := by
      intro m
      exact epsL2_le_ofReal_of_mem (hBK (m + K) K hK (by omega) τ hτ).1
        (hBK (m + K) K hK (by omega) τ hτ).2
    have hlim : ∀ᵐ p ∂DomM, Filter.Tendsto (fun m : ℕ =>
        (fun z θ => slice (iter F h₀ (m + K)) τ z θ - slice (iter F h₀ K) τ z θ) p.1 p.2)
        Filter.atTop (nhds ((fun z θ => slice (limFam F h₀) τ z θ
          - slice (iter F h₀ K) τ z θ) p.1 p.2)) := by
      have hpt : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
          Filter.Tendsto (fun m : ℕ => slice (iter F h₀ (m + K)) τ z θ - slice (iter F h₀ K) τ z θ)
            Filter.atTop (nhds (slice (limFam F h₀) τ z θ - slice (iter F h₀ K) τ z θ)) := by
        intro z hz θ hθ0 hθ1
        exact ((hconv τ hτ z θ hz hθ0 hθ1).comp (tendsto_add_atTop_nat K)).sub
          tendsto_const_nhds
      exact ae_of_forall_open hpt
    exact Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.EpsMem_and_EpsSq_le_of_tendsto_ae (pow_nonneg hq0 (K + 1))
      hAK hbd hlim
  -- ## 10. identification of the limit of `F` with `F` of the limit
  have hidentify : ∀ τ, τ ∈ Set.Icc 0 δ → ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      FlimM F h₀ z θ τ = F (slice (limFam F h₀) τ) z θ := by
    intro τ hτ z θ hz hθ0 hθ1
    have hlim0 : Filter.Tendsto (fun m : ℕ => EpsSq α (fun z θ =>
        slice (iter F h₀ (m + 1)) τ z θ - slice (limFam F h₀) τ z θ))
        Filter.atTop (nhds 0) := by
      have hle : ∀ m : ℕ, EpsSq α (fun z θ =>
          slice (iter F h₀ (m + 1)) τ z θ - slice (limFam F h₀) τ z θ) ≤ q ^ (m + 2) := by
        intro m
        rw [EpsSq_sub_comm]
        exact (htail (m + 1) (by omega) τ hτ).2
      have hg : Filter.Tendsto (fun m : ℕ => q ^ (m + 2)) Filter.atTop (nhds 0) := by
        have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp
          (tendsto_add_atTop_nat 2)
        rw [show ((fun n : ℕ => q ^ n) ∘ fun a => a + 2) = fun m : ℕ => q ^ (m + 2) from rfl] at h
        exact h
      exact squeeze_zero (fun m => EpsSq_nonneg α _) hle hg
    have hF0 : Filter.Tendsto (fun m : ℕ => F (slice (iter F h₀ (m + 1)) τ) z θ
        - F (slice (limFam F h₀) τ) z θ) Filter.atTop (nhds 0) := by
      have h0 : Filter.Tendsto (fun m : ℕ => Cpt * Real.sqrt (EpsSq α (fun z θ =>
          slice (iter F h₀ (m + 1)) τ z θ - slice (limFam F h₀) τ z θ)))
          Filter.atTop (nhds 0) := by
        simpa using hlim0.sqrt.const_mul Cpt
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using h0.neg) h0 ?_ ?_
      · intro m
        have hm := abs_le.mp (hpt _ _ (hP (m + 1) τ hτ) (hlimP τ hτ) z θ hz hθ0 hθ1)
        simpa only [Work.FTS.Galerkin.slice_apply] using hm.1
      · intro m
        have hm := abs_le.mp (hpt _ _ (hP (m + 1) τ hτ) (hlimP τ hτ) z θ hz hθ0 hθ1)
        simpa only [Work.FTS.Galerkin.slice_apply] using hm.2
    have hF : Filter.Tendsto (fun m : ℕ => F (slice (iter F h₀ (m + 1)) τ) z θ)
        Filter.atTop (nhds (F (slice (limFam F h₀) τ) z θ)) := by
      simpa using hF0.add_const (F (slice (limFam F h₀) τ) z θ)
    refine tendsto_nhds_unique ?_ hF
    have h6 := (hFlim τ hτ z θ hz hθ0 hθ1).comp (tendsto_add_atTop_nat 1)
    rw [show ((fun n : ℕ => F (slice (iter F h₀ n) τ) z θ) ∘ fun a => a + 1)
        = fun n : ℕ => F (slice (iter F h₀ (n + 1)) τ) z θ from rfl] at h6
    exact h6
  -- ## 11. conclusion: the fundamental theorem of calculus
  refine ⟨fun z θ => limFam_zero F h₀ z θ, ?_⟩
  intro z θ τ hz hθ hτ
  haveI : Fact (τ ∈ Set.Icc 0 δ) := ⟨hτ⟩
  rw [← hidentify τ hτ z θ hz hθ.1 hθ.2]
  have hInt : IntervalIntegrable (fun s => FlimM F h₀ z θ s) volume 0 τ :=
    ContinuousOn.intervalIntegrable_of_Icc hτ.1
      ((hFcont z θ hz hθ.1 hθ.2).mono (Set.Icc_subset_Icc_right hτ.2))
  have hFTC : HasDerivWithinAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, FlimM F h₀ z θ s)
      (FlimM F h₀ z θ τ) (Set.Icc 0 δ) τ :=
    intervalIntegral.integral_hasDerivWithinAt_right hInt
      ((hFcont z θ hz hθ.1 hθ.2).stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc τ)
      ((hFcont z θ hz hθ.1 hθ.2).continuousWithinAt hτ)
  refine (hFTC.const_add (h₀ z θ)).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact hvol s hs z θ hz hθ.1 hθ.2
  · exact hvol τ hτ z θ hz hθ.1 hθ.2

end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.Open3.HQoAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.Open3

open Work.FTS.Nonlin
open Work.FTS.VocabO (HQo)
open Work.FTS.Galerkin (Fn Fam)

set_option autoImplicit false

/-- `SmoothOpen` is preserved by multiplication by a constant. -/
theorem smoothOpen_const_mul {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f) (c : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  have h : Function.uncurry (fun z θ => c * f z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry f p := rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, h]
  exact hf.const_smul c

/-- `HQo` is closed under multiplication by a constant. -/
theorem HQo_const_mul {α : ℝ} {k : ℕ} {f : Fn} (hf : HQo α k f) (c : ℝ) :
    HQo α k (fun z θ => c * f z θ) :=
  ⟨smoothOpen_const_mul hf.1 c, Work.FTS.LocData.HkMem_const_mul α k c hf.2⟩

/-- `HQo` is closed under negation. -/
theorem HQo_neg {α : ℝ} {k : ℕ} {f : Fn} (hf : HQo α k f) : HQo α k (fun z θ => -f z θ) := by
  have hfun : (fun z θ => -f z θ) = fun z θ => (-1 : ℝ) * f z θ := by funext z θ; ring
  rw [hfun]
  exact HQo_const_mul hf (-1)

/-- `HQo` is closed under addition. -/
theorem HQo_add {α : ℝ} {k : ℕ} {f g : Fn} (hf : HQo α k f) (hg : HQo α k g) :
    HQo α k (fun z θ => f z θ + g z θ) :=
  ⟨Work.FTS.EllipticEst.smoothOpen_add hf.1 hg.1,
   Work.FTS.CoercivityFix.Assembly.HkMem_add_open α k hf.1 hg.1 hf.2 hg.2⟩

/-- `HQo` is closed under subtraction. -/
theorem HQo_sub {α : ℝ} {k : ℕ} {f g : Fn} (hf : HQo α k f) (hg : HQo α k g) :
    HQo α k (fun z θ => f z θ - g z θ) := by
  have hfun : (fun z θ => f z θ - g z θ) = fun z θ => f z θ + -g z θ := by funext z θ; ring
  rw [hfun]
  exact HQo_add hf (HQo_neg hg)


end Work.FTS.Open3
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.R5Parts_of_pieces =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.Der

/-- **Monotonicity of the `C1Jet`-constant**: weakening the constant is free, both in the `Jet`
and in the `z`-derivative bound.  Needed to feed two `C1Jet`-hypotheses with *different* constants
into a lemma that asks for a common one (the `D_z`-slots of `zderiv_N0`). -/
theorem c1Jet_mono_N {α S M N : ℝ} {h : Work.FTS.RegPkgGal.Fam} (hMN : M ≤ N)
    (H : Work.FTS.RegPkgGal.C1Jet α S M h) : Work.FTS.RegPkgGal.C1Jet α S N h :=
  ⟨jet_mono_N hMN H.1, fun τ hτ θ hθ z hz => by
    obtain ⟨d, hd, hb⟩ := H.2 τ hτ θ hθ z hz
    exact ⟨d, hd, le_trans hb hMN⟩⟩


end Work.FTS.RegPkgGal.Der
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsConvAllH =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsConvH

set_option autoImplicit false

/-- **A uniformly Cauchy sequence that has a convergent subsequence converges** (to the same
limit).  The index map `A` is the subsequence; it only has to tend to infinity. -/
theorem of_uniform_cauchy {X β : Type*} [PseudoMetricSpace β]
    {s : Set X} {F : ℕ → X → β} {f : X → β} {A : ℕ → ℕ}
    (hA : Tendsto A atTop atTop)
    (hc : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ x ∈ s, dist (F m x) (F n x) < ε)
    (hs : TendstoUniformlyOn (F ∘ A) f atTop s) :
    TendstoUniformlyOn F f atTop s := by
  rw [Metric.tendstoUniformlyOn_iff] at hs ⊢
  intro ε hε
  have hε2 : (0:ℝ) < ε/2 := by linarith
  obtain ⟨N, hN⟩ := hc (ε/2) hε2
  have h1 : ∀ᶠ n in atTop, ∀ x ∈ s, dist (f x) (F (A n) x) < ε/2 := hs (ε/2) hε2
  filter_upwards [h1, eventually_ge_atTop N, hA.eventually (eventually_ge_atTop N)]
    with n hn hnN hAn
  intro x hx
  calc dist (f x) (F n x)
      ≤ dist (f x) (F (A n) x) + dist (F (A n) x) (F n x) := dist_triangle _ _ _
    _ < ε/2 + ε/2 := add_lt_add (hn x hx) (hN (A n) hAn n hnN x hx)
    _ = ε := by ring

/-- **Uniform Cauchy from convergence on a dense set of parameters.**  Let `u σ n p` be a family
of `ℝ`-valued sequences indexed by `n`, depending on a real parameter `σ`.  If

* `u · n p` is `C`-Lipschitz in `σ`, uniformly in `n` and `p ∈ s`,
* `u σ · p` converges for every `σ` in `Icc 0 T ∩ D`, `D` dense in `Icc 0 T` in the sense of
  `hdense`,

then `u τ · p` is uniformly (in `p ∈ s`) Cauchy for every `τ ∈ Icc 0 T`. -/
theorem uniform_cauchy_of_dense_lipschitz {X : Type*} {s : Set X} {T : ℝ} {D : Set ℝ}
    {u : ℝ → ℕ → X → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hdense : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ δ : ℝ, 0 < δ →
      ∃ σ ∈ Set.Icc (0 : ℝ) T ∩ D, |σ - τ| ≤ δ)
    (hlip : ∀ σ ∈ Set.Icc (0 : ℝ) T, ∀ σ' ∈ Set.Icc (0 : ℝ) T, ∀ n : ℕ, ∀ p ∈ s,
      |u σ n p - u σ' n p| ≤ C * |σ - σ'|)
    (hconv : ∀ σ ∈ Set.Icc (0 : ℝ) T ∩ D, ∃ L : X → ℝ, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∀ p ∈ s, |u σ n p - L p| < ε) :
    ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ p ∈ s,
      |u τ m p - u τ n p| < ε := by
  intro τ hτ ε hε
  have hC1 : (0:ℝ) < C + 1 := by linarith
  have hδpos : (0:ℝ) < ε / (8 * (C + 1)) := by positivity
  obtain ⟨σ, hσ, hστ⟩ := hdense τ hτ (ε / (8 * (C + 1))) hδpos
  obtain ⟨L, hL⟩ := hconv σ hσ
  have hε4 : (0:ℝ) < ε/4 := by linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hL (ε/4) hε4)
  have key : C * (ε / (8 * (C + 1))) ≤ ε / 8 := by
    have h3 : C / (C + 1) ≤ 1 := by rw [div_le_one hC1]; linarith
    calc C * (ε / (8 * (C + 1))) = (C / (C + 1)) * (ε / 8) := by field_simp
      _ ≤ 1 * (ε / 8) := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = ε / 8 := by ring
  refine ⟨N, fun m hm n hn p hp => ?_⟩
  have hm' : |u σ m p - L p| < ε/4 := hN m hm p hp
  have hn' : |u σ n p - L p| < ε/4 := hN n hn p hp
  have hmτ : |u τ m p - u σ m p| ≤ ε/8 := by
    have h := hlip τ hτ σ hσ.1 m p hp
    refine le_trans h (le_trans (mul_le_mul_of_nonneg_left ?_ hC) key)
    rw [abs_sub_comm]; exact hστ
  have hnτ : |u σ n p - u τ n p| ≤ ε/8 := by
    have h := hlip σ hσ.1 τ hτ n p hp
    refine le_trans h (le_trans (mul_le_mul_of_nonneg_left ?_ hC) key)
    exact hστ
  have hmid : |u σ m p - u σ n p| < ε/2 := by
    have h1 : u σ m p - u σ n p = (u σ m p - L p) - (u σ n p - L p) := by ring
    rw [h1]
    have htri : |(u σ m p - L p) - (u σ n p - L p)|
        ≤ |u σ m p - L p| + |u σ n p - L p| :=
      abs_sub_le_iff.mpr
        ⟨by linarith [le_abs_self (u σ m p - L p), neg_le_abs (u σ n p - L p)],
         by linarith [le_abs_self (u σ n p - L p), neg_le_abs (u σ m p - L p)]⟩
    linarith
  have htri2 : |u τ m p - u σ m p + (u σ m p - u σ n p) + (u σ n p - u τ n p)|
      ≤ |u τ m p - u σ m p| + |u σ m p - u σ n p| + |u σ n p - u τ n p| :=
    abs_add_three _ _ _
  calc |u τ m p - u τ n p|
      = |(u τ m p - u σ m p) + (u σ m p - u σ n p) + (u σ n p - u τ n p)| := by ring_nf
    _ ≤ |u τ m p - u σ m p| + |u σ m p - u σ n p| + |u σ n p - u τ n p| := htri2
    _ < ε := by linarith

/-- The rationals are dense in `Icc 0 T`: every `τ ∈ Icc 0 T` is within `δ` of a *rational*
point of `Icc 0 T`. -/
theorem exists_rat_mem_Icc_close {T τ : ℝ} (hτ : τ ∈ Set.Icc (0:ℝ) T) {δ : ℝ} (hδ : 0 < δ) :
    ∃ σ ∈ Set.Icc (0:ℝ) T ∩ Set.range (fun q : ℚ => (q:ℝ)), |σ - τ| ≤ δ := by
  rcases lt_or_eq_of_le (le_trans hτ.1 hτ.2) with hT | hT
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (x := max 0 (τ - δ)) (y := min T (τ + δ))
      (max_lt (lt_min hT (by linarith [hτ.1])) (lt_min (by linarith [hτ.2]) (by linarith)))
    refine ⟨(q:ℝ), ⟨?_, ⟨q, rfl⟩⟩, ?_⟩
    · rw [Set.mem_Icc]
      exact ⟨le_of_lt (lt_of_le_of_lt (le_max_left _ _) hq1),
             le_of_lt (lt_of_lt_of_le hq2 (min_le_left _ _))⟩
    · rw [abs_le]
      exact ⟨by linarith [lt_of_le_of_lt (le_max_right _ _) hq1],
             by linarith [lt_of_lt_of_le hq2 (min_le_right _ _)]⟩
  · have hτ0 : τ = 0 := le_antisymm (le_trans hτ.2 (le_of_eq hT.symm)) hτ.1
    refine ⟨0, ⟨?_, ⟨0, by norm_num⟩⟩, ?_⟩
    · rw [Set.mem_Icc]; exact ⟨le_rfl, le_of_eq hT⟩
    · rw [hτ0, sub_zero, abs_zero]; exact le_of_lt hδ

end Work.FTS.StrongEps.EpsConvH

namespace Work.FTS.StrongEps

open Work.FTS.StrongEps.EpsConvH

-- the statement carries the hypothesis `hφ`, which the proof does not need

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsMemRegP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false



end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.zeroTermDth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth

/-! ## The `(i,j) = (0,0)` transport summand of the `D_θ`-row

The integrand `ρ·A·D_θ(D_z^bD_θ^a f)·D_z^bD_θ^af` carries *no* derivative on the coefficient
`A`, so it is controlled by the slice-level transport inequality
`N6Trans.T1SixAux.hardSlotSliceSixZero`, which is stated for a coefficient `F` with *both*
`|F| ≤ Kf` and `|D_θF| ≤ Kf`.  The `CoefData` of this row does not give a pointwise bound on
`D_θA` directly, but the `α`-uniform pointwise bound of mixed slots of order `≤ 2`
(`TransportS.T2SupB2.mixed_pointwise_le_Xn`, at `(i,j) = (1,0)`) gives
`|D_θA| ≤ Cm·|A|_{ℋ⁴} ≤ Cm·K4`, so the slice inequality may be applied with
`Kf := max K0 (Cm·K4)`.  Everything else (the three leaf weights, the `z`-integration, the two
integrability conjuncts, the energy bound `∫∫ρ(D_z^bD_θ^af)² ≤ HkSq α 6 f`) is exactly the
sibling lemma `Npair6Aux.zeroTerm`, which already performs this assembly for the coefficient
hypotheses `CoefHyp`/`DatHyp` (field-for-field the `CoefData`/`DatData` of this row). -/

/-- `D_θ` is the `(i,j) = (1,0)` mixed slot. -/
theorem dth_eq_mixed_zero_one (g : ℝ → ℝ → ℝ) : Work.Spaces.Dth g = Work.Spaces.mixed 0 1 g := rfl

theorem zeroTermDth : ∃ C : ℝ, 0 < C ∧
    ∀ α ∈ Set.Ioc 0 1, ∀ (A f : Work.FTS.Galerkin.Fn) (K0 K4 K6 M : ℝ) (a b : ℕ)
      (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M → a + b ≤ 6 →
      Work.FTS.TransportS.IsLeafW α a ρ →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ => ρ z θ * A z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
          * Work.Spaces.mixed b a f z θ) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, ρ z θ * A z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
          * Work.Spaces.mixed b a f z θ) Work.Spaces.Iz ∧
      |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * A z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
          * Work.Spaces.mixed b a f z θ|
        ≤ C * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) * (1 + Work.Spaces.HkSq α 6 f) := by
  -- the two proved ingredients: the pointwise bound on the angular slot of the coefficient
  -- (with an `α`-independent constant) and the assembled sibling row `zeroTerm`
  obtain ⟨Cm, hCmpos, hCm⟩ := Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
  obtain ⟨Cz, hCzpos, hCz⟩ := Work.FTS.StrongPersist.H6Rows.Npair6Aux.zeroTerm
  set C : ℝ := Cz * max 1 Cm with hCdef
  have hCpos : 0 < C := by
    rw [hCdef]
    exact mul_pos hCzpos (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  refine ⟨C, hCpos, ?_⟩
  intro α hαmem A f K0 K4 K6 M a b ρ hcoef hdat hab hleaf
  obtain ⟨hα, hα1⟩ := hαmem
  -- the coefficient is priced pointwise by `K0` and its angular slot by `Cm · K4`
  have hlt : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hK0 : 0 ≤ K0 :=
    le_trans (abs_nonneg (A 1 1)) (hcoef.val 1 1 (by norm_num) (by norm_num) hlt)
  have hK4 : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hcoef.n4
  have hdbA : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed 0 1 A z θ| ≤ Cm * K4 := by
    intro z θ hz hθ hθ2
    refine le_trans (hCm α A hα hα1 hcoef.sm hcoef.h4 0 1 (by norm_num) (by norm_num)
      z θ hz hθ hθ2) ?_
    exact mul_le_mul_of_nonneg_left hcoef.n4 hCmpos.le
  -- the coefficient price for the slice inequality
  set Kf : ℝ := max K0 (Cm * K4) with hKfdef
  have hKf0 : 0 ≤ Kf := by rw [hKfdef]; exact le_trans hK0 (le_max_left _ _)
  have hvalKf : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ Kf := by
    intro z θ hz hθ hθ2
    rw [hKfdef]
    exact le_trans (hcoef.val z θ hz hθ hθ2) (le_max_left _ _)
  have hdbKf : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.Dth A z θ| ≤ Kf := by
    intro z θ hz hθ hθ2
    rw [hKfdef, dth_eq_mixed_zero_one]
    exact le_trans (hdbA z θ hz hθ hθ2) (le_max_right _ _)
  -- the sibling row `zeroTerm`, with the coefficient data transported to `CoefHyp`/`DatHyp`
  have hcoefH : Work.FTS.StrongPersist.H6Rows.Npair6Aux.CoefHyp α A K0 K4 K6 :=
    ⟨hcoef.sm, hcoef.h4, hcoef.h6, hcoef.val, hcoef.n4, hcoef.n6⟩
  have hdatH : Work.FTS.StrongPersist.H6Rows.Npair6Aux.DatHyp α f M :=
    ⟨hdat.sm, hdat.h6, hdat.h7, hdat.vanish, hdat.axis, hdat.bdd⟩
  obtain ⟨h1, h2, h3⟩ := hCz α ⟨hα, hα1⟩ A f Kf M a b ρ
    hcoefH.sm hKf0 hvalKf hdbKf hdatH hab hleaf
  refine ⟨h1, h2, ?_⟩
  -- `max K0 (Cm·K4) ≤ max 1 Cm · (K0 + K4)`
  have hsum0 : 0 ≤ K0 + K4 := add_nonneg hK0 hK4
  have hM0 : 0 ≤ max 1 Cm := le_trans zero_le_one (le_max_left _ _)
  have hKf_le : Kf ≤ max 1 Cm * (K0 + K4) := by
    rw [hKfdef]
    refine max_le ?_ ?_
    · calc K0 ≤ 1 * (K0 + K4) := by rw [one_mul]; exact le_add_of_nonneg_right hK4
        _ ≤ max 1 Cm * (K0 + K4) := mul_le_mul_of_nonneg_right (le_max_left _ _) hsum0
    · calc Cm * K4 ≤ max 1 Cm * K4 := mul_le_mul_of_nonneg_right (le_max_right _ _) hK4
        _ ≤ max 1 Cm * (K0 + K4) := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hK0) hM0
  have hCK : Cz * Kf ≤ C * (K0 + K4) := by
    rw [hCdef]
    calc Cz * Kf ≤ Cz * (max 1 Cm * (K0 + K4)) :=
          mul_le_mul_of_nonneg_left hKf_le hCzpos.le
      _ = Cz * max 1 Cm * (K0 + K4) := by ring
  -- `α^{-1/2} ≥ 1` and `HkSq ≥ 0`
  have hS0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hαr : (1 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := one_le_alpha_rpow_neg_half hα hα1
  have hSle : Work.Spaces.HkSq α 6 f
      ≤ α ^ (-(1 / 2 : ℝ)) * (1 + Work.Spaces.HkSq α 6 f) := by
    have h1' : Work.Spaces.HkSq α 6 f ≤ α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkSq α 6 f := by
      simpa using mul_le_mul_of_nonneg_right hαr hS0
    have h2' : α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkSq α 6 f
        ≤ α ^ (-(1 / 2 : ℝ)) * (1 + Work.Spaces.HkSq α 6 f) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one)
        (le_trans zero_le_one hαr)
    linarith
  refine le_trans h3 ?_
  calc Cz * Kf * Work.Spaces.HkSq α 6 f
      ≤ (C * (K0 + K4)) * Work.Spaces.HkSq α 6 f :=
        mul_le_mul_of_nonneg_right hCK hS0
    _ ≤ (C * (K0 + K4)) * (α ^ (-(1 / 2 : ℝ)) * (1 + Work.Spaces.HkSq α 6 f)) :=
        mul_le_mul_of_nonneg_left hSle (mul_nonneg hCpos.le hsum0)
    _ = C * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) * (1 + Work.Spaces.HkSq α 6 f) := by ring

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth
end
