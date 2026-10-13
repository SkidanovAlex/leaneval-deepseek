/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/VolterraV4Main.lean` — the *applicable* abstract
# Volterra–Picard engine

`exists_volterra_v4`: the abstract Picard/Volterra engine of
`Work.FTS.StrongEps.EpsLocalPStar.exists_volterra_v3`, with the curve-level hypotheses replaced by
iterate-indexed ones (see the companion file `VolterraV4Iter.lean` for the rationale and for the
a-priori bounds `iter_bounds_v4`).

Hypotheses (all profile- or iterate-level, hence instantiable):

* `hδ, hL, hδL, hCpt` — the numerical set-up (`δ √L < 1` is the contraction condition);
* `hP₀ : P h₀`;
* `hbd, hlip, hpt` — the right-hand side is bounded in `X = (EpsMem, EpsSq)`, `X`-Lipschitz and
  pointwise controlled on `P`;
* `hcontIter`, `hmeasIter` — continuity in the fake time and joint measurability of the
  `F`-images of the *explicit* Picard iterates `slice (iter F h₀ n) ·`;
* `hkeep` — the class `P` is preserved by the short-time integral over any `P`-curve;
* `hlimP` — the limit family's slices are in `P` (this is the closedness content; with `hpt` it
  yields the identification of the limit of `F` along the iteration with `F` of the limit).

The conclusion is a family `h` with `h · · 0 = h₀` and `∂_τ h = F (slice h τ)` on `Icc 0 δ`, i.e.
exactly the Volterra solution of the local step.  Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.StrongEps.EpsSpace
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.Defs
import Submission.Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.Iter
import Submission.Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.EpsMem_and_EpsSq_intervalIntegral_le
import Submission.Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.EpsMem_and_EpsSq_le_of_tendsto_ae
import Submission.Work.FTS.EpsEngine.VolterraV4Iter

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
