/-
# `ModalSol/Basic` — the elementary facts about the modal weak solution

This module proves, for the witness `Psi α F` of `ModalSol/Defs.lean` (the limit of the partial
sums `psiTrunc α F N` of the mode series `Σ_m acoeff α m F z · eFam m θ`), the facts used by the
assembly of `ModalSol/weakSolExists_slice.lean`:

* `acoeff_zero_of_orth`: the `m = 0` coefficient vanishes when the source moment does;
* `continuous_eFam`, `continuousOn_acoeff_mul_eFam`, `continuousOn_uncurry_psiTrunc`: the partial
  sums are continuous on the quadrant (the radial coefficient is continuous by
  `Aux/radGreen_continuousOn`);
* `psiTrunc_bound`, `psiTrunc_tendsto_Psi`: the uniform-in-`N` pointwise bound on the partial
  sums, and their convergence to `Psi`, both with the same weight `z ^ (-1/2)` (from the tail
  bounds `TailBound/psiTrunc_tail`);
* `tendstoUniformlyOn_psiTrunc_box`: uniform convergence of the partial sums on a rectangular
  box inside the quadrant, hence `continuousOn_uncurry_Psi`: the uncurried witness is continuous
  on the quadrant;
* `Psi_bound`, `Psi_tendsto_atTop_zero`, `continuousOn_slice_Psi`: the pointwise bound on the
  witness, its decay at `z → ∞`, and the continuity of its angular slices.

The final weak identity is assembled in `ModalSol/weakSolExists_slice.lean`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.H2.ModalSol.Defs
import Submission.Work.FTS.H2.ModalSol.Prelim.support
import Submission.Work.FTS.H2.ModalSol.TailBound.psiTrunc_tail
import Submission.Work.EllipticEst.ModalSolution.cmode_memLp
import Submission.Work.EllipticEst.ModalSolution.bslOp_ibp
import Submission.Work.EllipticEst.ModalSolution.box_of_compactSupport
import Submission.Work.FTS.PhiStar.Series.eFam_zero_moment
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSol

set_option maxHeartbeats 1000000

local notation "Q0" => Work.FTS.EllipticEst.Q0
local notation "Iθ" => Work.Spaces.Iθ

/-! ## The `m = 0` coefficient -/

/-- `radGreen` of the zero source vanishes. -/
theorem radGreen_const_zero (α : ℝ) (m : ℕ) :
    Work.FTS.PhiStar.Radial.radGreen α m (fun _ => (0 : ℝ)) = fun _ => 0 := by
  funext z
  simp only [Work.FTS.PhiStar.Radial.radGreen]
  simp only [zero_mul, mul_zero, add_zero, zero_add,
    intervalIntegral.integral_zero, MeasureTheory.integral_zero]

theorem acoeff_zero_of_orth {F : ℝ → ℝ → ℝ} (horth : Work.Elliptic.OrthCond F) (α : ℝ) (z : ℝ) :
    Work.FTS.PhiStar.Series.acoeff α 0 F z = 0 := by
  have hcm : (fun t => Work.FTS.PhiStar.Series.cmode 0 F t) = fun _ => (0 : ℝ) :=
    funext (fun t => Work.FTS.PhiStar.Series.eFam_zero_moment F (horth t))
  show Work.FTS.PhiStar.Radial.radGreen α 0
    (fun t => Work.FTS.PhiStar.Series.cmode 0 F t) z = 0
  rw [hcm, radGreen_const_zero]

/-! ## Continuity -/

/-- The angular modes are continuous. -/
theorem continuous_eFam (m : ℕ) : Continuous (Work.FTS.PhiStar.Gegenbauer.eFam m) := by
  change Continuous (fun θ : ℝ =>
    Real.cos θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ))
  exact Real.continuous_cos.mul
    (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).comp
      Real.continuous_sin)

/-- A finite sum of continuous functions of the plane, over `Finset.range`. -/
theorem continuousOn_sum_range (f : ℕ → ℝ × ℝ → ℝ) (n : ℕ)
    (hf : ∀ m : ℕ, ContinuousOn (f m) Q0) :
    ContinuousOn (fun p : ℝ × ℝ => ∑ m ∈ Finset.range n, f m p) Q0 := by
  induction n with
  | zero => simpa using (continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ => (0 : ℝ)) Q0)
  | succ n ih =>
      show ContinuousOn (fun p : ℝ × ℝ => ∑ m ∈ Finset.range (n + 1), f m p) Q0
      have h2 : (fun p : ℝ × ℝ => ∑ m ∈ Finset.range (n + 1), f m p)
          = fun p : ℝ × ℝ => (∑ m ∈ Finset.range n, f m p) + f n p := by
        funext p
        rw [Finset.sum_range_succ]
      rw [h2]
      exact ih.add (hf n)

/-- Each mode term `acoeff α m F z · eFam m θ` is continuous on the open quadrant, provided the
radial coefficient is square integrable (its continuity being `radGreen_continuousOn`). -/
theorem continuousOn_acoeff_mul_eFam (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (hc : ∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun t => Work.FTS.PhiStar.Series.cmode m F t ^ 2) (Set.Ioi 0)) (m : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.PhiStar.Series.acoeff α m F p.1 *
      Work.FTS.PhiStar.Gegenbauer.eFam m p.2) Q0 := by
  have h1 : ContinuousOn (fun z => Work.FTS.PhiStar.Series.acoeff α m F z) (Set.Ioi 0) :=
    radGreen_continuousOn α hα hα1 m (hc m)
  have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m p.2) Q0 :=
    (continuous_eFam m).comp_continuousOn continuous_snd.continuousOn
  exact (h1.comp continuous_fst.continuousOn
    (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)).mul h2

/-- The partial sums of the mode series are continuous on the open quadrant. -/
theorem continuousOn_uncurry_psiTrunc (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (hc : ∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun t => Work.FTS.PhiStar.Series.cmode m F t ^ 2) (Set.Ioi 0)) (N : ℕ) :
    ContinuousOn (Function.uncurry (Work.FTS.PhiStar.Series.psiTrunc α F N)) Q0 := by
  have hfun : Function.uncurry (Work.FTS.PhiStar.Series.psiTrunc α F N)
      = fun p : ℝ × ℝ => ∑ m ∈ Finset.range (N + 1),
          Work.FTS.PhiStar.Series.acoeff α m F p.1 *
            Work.FTS.PhiStar.Gegenbauer.eFam m p.2 := by
    funext p
    simp only [Function.uncurry, Work.FTS.PhiStar.Series.psiTrunc, Finset.sum_apply]
  rw [hfun]
  exact continuousOn_sum_range (fun m p => Work.FTS.PhiStar.Series.acoeff α m F p.1 *
    Work.FTS.PhiStar.Gegenbauer.eFam m p.2) (N + 1)
    (fun m => continuousOn_acoeff_mul_eFam α hα hα1 hc m)

/-! ## The pointwise bounds on the partial sums -/

/-- **The partial sums are bounded by `z ^ (-1/2)`**, uniformly in the summation index. -/
theorem psiTrunc_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (horth : Work.Elliptic.OrthCond F) (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < π / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (z : ℝ), 0 < z → ∀ θ ∈ Set.Icc δ (π / 2 - δ),
      |Work.FTS.PhiStar.Series.psiTrunc α F N z θ| ≤ C * z ^ (-(1 / 2) : ℝ) := by
  obtain ⟨C, b, hC0, hb0, hbT, hEst⟩ := Work.FTS.H2.ModalSol.TailBound.psiTrunc_tail α hα hα1 horth hsm hL2 δ hδ0 hδ1
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ N ≥ N₀, b N ≤ 1 := by
    have h : ∀ᶠ N in Filter.atTop, b N < 1 := hbT.eventually (eventually_lt_nhds zero_lt_one)
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h
    exact ⟨N₀, fun N hN => le_of_lt (hN₀ N hN)⟩
  set B : ℝ := max 1 (∑ N ∈ Finset.range (N₀ + 1), b N) with hBdef
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hBb : ∀ N : ℕ, b N ≤ B := by
    intro N
    rcases le_total N₀ N with hN | hN
    · exact le_trans (hN₀ N hN) (le_max_left _ _)
    · refine le_trans (Finset.single_le_sum (fun m _ => hb0 m)
        (Finset.mem_range.mpr (by omega))) (le_max_right _ _)
  refine ⟨C * (B + B), mul_pos hC0 (by linarith), fun N z hz θ hθ => ?_⟩
  have h0 : Work.FTS.PhiStar.Series.psiTrunc α F 0 z θ = 0 := by
    rw [Work.FTS.PhiStar.Series.psiTrunc, Finset.range_one, Finset.sum_singleton,
      acoeff_zero_of_orth horth α z]
    ring
  have h := hEst N 0 z hz θ hθ
  rw [h0, sub_zero] at h
  have hz' : 0 ≤ z ^ (-(1 / 2) : ℝ) := le_of_lt (Real.rpow_pos_of_pos hz _)
  calc |Work.FTS.PhiStar.Series.psiTrunc α F N z θ|
      ≤ C * z ^ (-(1 / 2) : ℝ) * (b N + b 0) := h
    _ ≤ C * z ^ (-(1 / 2) : ℝ) * (B + B) :=
        mul_le_mul_of_nonneg_left (add_le_add (hBb N) (hBb 0))
          (mul_nonneg (le_of_lt hC0) hz')
    _ = C * (B + B) * z ^ (-(1 / 2) : ℝ) := by ring

/-- **The partial sums converge to `Psi`**, with the same `z ^ (-1/2)` weight. -/
theorem psiTrunc_tendsto_Psi (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (horth : Work.Elliptic.OrthCond F) (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < π / 2) :
    ∀ z, 0 < z → ∀ θ ∈ Set.Icc δ (π / 2 - δ),
      Filter.Tendsto (fun N : ℕ => Work.FTS.PhiStar.Series.psiTrunc α F N z θ) Filter.atTop
        (nhds (Psi α F z θ)) := by
  obtain ⟨C, b, hC0, hb0, hbT, hEst⟩ := Work.FTS.H2.ModalSol.TailBound.psiTrunc_tail α hα hα1 horth hsm hL2 δ hδ0 hδ1
  intro z hz θ hθ
  apply Psi_tendsto_of_cauchy
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hz' : 0 < z ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hz _
  have hCz : 0 < C * z ^ (-(1 / 2) : ℝ) := mul_pos hC0 hz'
  have hne : C * z ^ (-(1 / 2) : ℝ) ≠ 0 := ne_of_gt hCz
  have hε' : 0 < ε / (4 * (C * z ^ (-(1 / 2) : ℝ))) := by positivity
  have hev : ∀ᶠ N in Filter.atTop, b N < ε / (4 * (C * z ^ (-(1 / 2) : ℝ))) :=
    hbT.eventually (eventually_lt_nhds hε')
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨N₀, fun m hm n hn => ?_⟩
  rw [Real.dist_eq]
  have hmn := hEst m n z hz θ hθ
  have h1 : b m < ε / (4 * (C * z ^ (-(1 / 2) : ℝ))) := hN₀ m hm
  have h2 : b n < ε / (4 * (C * z ^ (-(1 / 2) : ℝ))) := hN₀ n hn
  have h3 : C * z ^ (-(1 / 2) : ℝ) * (b m + b n) < ε / 2 := by
    have hadd : b m + b n < ε / (4 * (C * z ^ (-(1 / 2) : ℝ)))
        + ε / (4 * (C * z ^ (-(1 / 2) : ℝ))) := add_lt_add h1 h2
    have h4 : C * z ^ (-(1 / 2) : ℝ) * (ε / (4 * (C * z ^ (-(1 / 2) : ℝ)))
        + ε / (4 * (C * z ^ (-(1 / 2) : ℝ)))) = ε / 2 := by
      field_simp
      ring
    calc C * z ^ (-(1 / 2) : ℝ) * (b m + b n)
        < C * z ^ (-(1 / 2) : ℝ) * (ε / (4 * (C * z ^ (-(1 / 2) : ℝ)))
            + ε / (4 * (C * z ^ (-(1 / 2) : ℝ)))) := mul_lt_mul_of_pos_left hadd hCz
      _ = ε / 2 := h4
  linarith

/-! ## Uniform convergence on a box, and continuity of the witness -/

/-- **Uniform convergence of the partial sums on a rectangular box inside the quadrant.** -/
theorem tendstoUniformlyOn_psiTrunc_box (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (horth : Work.Elliptic.OrthCond F) (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc0 : 0 < c) (hcd : c ≤ d) (hd : d < π / 2) :
    TendstoUniformlyOn
      (fun N : ℕ => fun p : ℝ × ℝ => Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2)
      (fun p : ℝ × ℝ => Psi α F p.1 p.2) Filter.atTop (Set.Icc a b ×ˢ Set.Icc c d) := by
  set δ : ℝ := min c (π / 2 - d) with hδdef
  have hδ0 : 0 < δ := lt_min hc0 (by linarith)
  have hδ1 : δ < π / 2 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδc : δ ≤ c := min_le_left _ _
  have hδd : δ ≤ π / 2 - d := min_le_right _ _
  obtain ⟨C, β, hC0, hβ0, hβT, hEst⟩ := Work.FTS.H2.ModalSol.TailBound.psiTrunc_tail α hα hα1 horth hsm hL2 δ hδ0 hδ1
  have hconv : ∀ z, 0 < z → ∀ θ ∈ Set.Icc δ (π / 2 - δ),
      Filter.Tendsto (fun N : ℕ => Work.FTS.PhiStar.Series.psiTrunc α F N z θ) Filter.atTop
        (nhds (Psi α F z θ)) := psiTrunc_tendsto_Psi α hα hα1 horth hsm hL2 δ hδ0 hδ1
  have hkey : ∀ (N : ℕ) (p : ℝ × ℝ), p ∈ Set.Icc a b ×ˢ Set.Icc c d →
      |Psi α F p.1 p.2 - Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2|
        ≤ C * a ^ (-(1 / 2) : ℝ) * β N := by
    intro N p hp
    have hp1 : 0 < p.1 := lt_of_lt_of_le ha hp.1.1
    have hpl : δ ≤ p.2 := le_trans hδc hp.2.1
    have hpr : p.2 ≤ π / 2 - δ := le_trans hp.2.2 (by linarith)
    have hp2 : p.2 ∈ Set.Icc δ (π / 2 - δ) := ⟨hpl, hpr⟩
    have hlim := hconv p.1 hp1 p.2 hp2
    have hdiff : Filter.Tendsto
        (fun M : ℕ => |Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2
          - Work.FTS.PhiStar.Series.psiTrunc α F M p.1 p.2|) Filter.atTop
        (nhds |Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2 - Psi α F p.1 p.2|) :=
      ((tendsto_const_nhds.sub hlim).abs)
    have hbd : Filter.Tendsto
        (fun M : ℕ => C * p.1 ^ (-(1 / 2) : ℝ) * (β N + β M)) Filter.atTop
        (nhds (C * p.1 ^ (-(1 / 2) : ℝ) * (β N + 0))) :=
      ((tendsto_const_nhds.add hβT).const_mul _)
    have hle : |Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2 - Psi α F p.1 p.2|
        ≤ C * p.1 ^ (-(1 / 2) : ℝ) * β N := by
      have := le_of_tendsto_of_tendsto' hdiff hbd (fun M => hEst N M p.1 hp1 p.2 hp2)
      simpa using this
    have hp1a : a ^ (-(1 / 2) : ℝ) ≥ p.1 ^ (-(1 / 2) : ℝ) := by
      refine Real.rpow_le_rpow_of_nonpos ha hp.1.1 (by norm_num)
    have hbz : 0 ≤ β N := hβ0 N
    have hCpos : 0 ≤ C := le_of_lt hC0
    calc |Psi α F p.1 p.2 - Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2|
        = |Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2 - Psi α F p.1 p.2| :=
            abs_sub_comm _ _
      _ ≤ C * p.1 ^ (-(1 / 2) : ℝ) * β N := hle
      _ ≤ C * a ^ (-(1 / 2) : ℝ) * β N := by
          refine mul_le_mul_of_nonneg_right ?_ hbz
          exact mul_le_mul_of_nonneg_left hp1a hCpos
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hCa : 0 < C * a ^ (-(1 / 2) : ℝ) := mul_pos hC0 (Real.rpow_pos_of_pos ha _)
  have hε' : 0 < ε / (C * a ^ (-(1 / 2) : ℝ)) := by positivity
  have hev : ∀ᶠ N in Filter.atTop, β N < ε / (C * a ^ (-(1 / 2) : ℝ)) :=
    hβT.eventually (eventually_lt_nhds hε')
  filter_upwards [hev] with N hN
  intro p hp
  rw [Real.dist_eq]
  have h := hkey N p hp
  have h2 : C * a ^ (-(1 / 2) : ℝ) * β N < ε := by
    rw [lt_div_iff₀ hCa] at hN
    linarith
  linarith

/-- **The witness is continuous on the open quadrant.** -/
theorem continuousOn_uncurry_Psi (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (horth : Work.Elliptic.OrthCond F) (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    ContinuousOn (Function.uncurry (Psi α F)) Q0 := by
  have hc : ∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun t => Work.FTS.PhiStar.Series.cmode m F t ^ 2) (Set.Ioi 0) :=
    fun m => Work.EllipticEst.ModalSolution.cmode_memLp hsm hL2 m
  refine continuousOn_of_forall_continuousAt (fun p hp => ?_)
  obtain ⟨hz0, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  set ε : ℝ := min (p.1 / 2) (min (p.2 / 2) ((π / 2 - p.2) / 2)) with hεdef
  have hε0 : 0 < ε := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hεz : ε ≤ p.1 / 2 := min_le_left _ _
  have hεθ : ε ≤ p.2 / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hεπ : ε ≤ (π / 2 - p.2) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hbox : Set.Icc (p.1 - ε) (p.1 + ε) ×ˢ Set.Icc (p.2 - ε) (p.2 + ε) ⊆ Q0 := by
    intro q hq
    rw [Work.FTS.EllipticEst.mem_Q0]
    exact ⟨by linarith [hq.1.1, hεz, hz0], by linarith [hq.2.1, hεθ, hθ0],
      by linarith [hq.2.2, hεπ, hθ1]⟩
  have hunif := tendstoUniformlyOn_psiTrunc_box α hα hα1 horth hsm hL2
    (a := p.1 - ε) (b := p.1 + ε) (c := p.2 - ε) (d := p.2 + ε)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  have hcont : ContinuousOn (Function.uncurry (Psi α F))
      (Set.Icc (p.1 - ε) (p.1 + ε) ×ˢ Set.Icc (p.2 - ε) (p.2 + ε)) :=
    hunif.continuousOn (Filter.Eventually.of_forall
      (fun N => (continuousOn_uncurry_psiTrunc α hα hα1 hc N).mono hbox)).frequently
  have hnb : Set.Ioo (p.1 - ε) (p.1 + ε) ×ˢ Set.Ioo (p.2 - ε) (p.2 + ε) ∈ 𝓝 p :=
    (isOpen_Ioo.prod isOpen_Ioo).mem_nhds
      ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hbox_nhds : Set.Icc (p.1 - ε) (p.1 + ε) ×ˢ Set.Icc (p.2 - ε) (p.2 + ε) ∈ 𝓝 p :=
    Filter.mem_of_superset hnb (fun q hq =>
      ⟨⟨le_of_lt hq.1.1, le_of_lt hq.1.2⟩, ⟨le_of_lt hq.2.1, le_of_lt hq.2.2⟩⟩)
  exact hcont.continuousAt hbox_nhds

/-! ## The pointwise bound on the witness, and its decay -/

/-- **The witness is bounded by `z ^ (-1/2)`** on any closed angular subinterval. -/
theorem Psi_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (horth : Work.Elliptic.OrthCond F) (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < π / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ z, 0 < z → ∀ θ ∈ Set.Icc δ (π / 2 - δ),
      |Psi α F z θ| ≤ C * z ^ (-(1 / 2) : ℝ) := by
  obtain ⟨C, hC0, hbnd⟩ := psiTrunc_bound α hα hα1 horth hsm hL2 δ hδ0 hδ1
  refine ⟨C, hC0, fun z hz θ hθ => ?_⟩
  have hlim := psiTrunc_tendsto_Psi α hα hα1 horth hsm hL2 δ hδ0 hδ1 z hz θ hθ
  have := le_of_tendsto_of_tendsto' (hlim.abs) tendsto_const_nhds (fun N => hbnd N z hz θ hθ)
  simpa using this

/-- **The witness decays at `z → ∞` in every direction of `Iθ`.** -/
theorem Psi_tendsto_atTop_zero (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (horth : Work.Elliptic.OrthCond F) (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    ∀ θ ∈ Iθ, Filter.Tendsto (fun z => Psi α F z θ) Filter.atTop (nhds 0) := by
  intro θ hθ
  rcases lt_or_eq_of_le hθ.1 with hθ0 | rfl
  · rcases lt_or_eq_of_le hθ.2 with hθ1 | rfl
    · set δ : ℝ := min θ (π / 2 - θ) / 2 with hδdef
      have hδ0 : 0 < δ := by
        refine div_pos (lt_min hθ0 (sub_pos.mpr hθ1)) (by norm_num)
      have hδ1 : δ < π / 2 := by
        have : δ ≤ θ / 2 := by
          rw [hδdef]
          exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
        linarith
      have hmem : θ ∈ Set.Icc δ (π / 2 - δ) := by
        refine ⟨?_, ?_⟩
        · rw [hδdef]
          exact le_trans (div_le_self (le_of_lt (lt_min hθ0 (sub_pos.mpr hθ1)))
            (by norm_num : (1 : ℝ) ≤ 2)) (min_le_left _ _)
        · rw [hδdef]
          have : min θ (π / 2 - θ) ≤ π / 2 - θ := min_le_right _ _
          linarith
      obtain ⟨C, hC0, hbnd⟩ := Psi_bound α hα hα1 horth hsm hL2 δ hδ0 hδ1
      have h1 : Filter.Tendsto (fun z : ℝ => C * z ^ (-(1 / 2) : ℝ)) Filter.atTop (nhds 0) := by
        simpa using tendsto_const_nhds.mul
          (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 2 by norm_num))
      have h0 : Filter.Tendsto (fun _ : ℝ => (0 : ℝ)) Filter.atTop (nhds 0) := tendsto_const_nhds
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero' (Filter.Eventually.of_forall (fun z => norm_nonneg _)) ?_ h1
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
      rw [Real.norm_eq_abs]
      exact hbnd z hz θ hmem
    · exact tendsto_const_nhds.congr' (Filter.Eventually.of_forall
        (fun z => (Psi_apply_pi_half α F z).symm))
  · exact tendsto_const_nhds.congr' (Filter.Eventually.of_forall
      (fun z => (Psi_apply_zero α F z).symm))

/-- **The angular slices of the witness are continuous.** -/
theorem continuousOn_slice_Psi (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (horth : Work.Elliptic.OrthCond F) (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ => Psi α F z θ) (Set.Ioo 0 (π / 2)) := by
  have hc : ∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun t => Work.FTS.PhiStar.Series.cmode m F t ^ 2) (Set.Ioi 0) :=
    fun m => Work.EllipticEst.ModalSolution.cmode_memLp hsm hL2 m
  refine continuousOn_of_forall_continuousAt (fun θ hθ => ?_)
  set ε : ℝ := min θ (π / 2 - θ) / 2 with hεdef
  have hε0 : 0 < ε := by
    refine div_pos (lt_min hθ.1 (sub_pos.mpr hθ.2)) (by norm_num)
  have hεθ : ε ≤ θ / 2 := by
    rw [hεdef]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hεπ : ε ≤ (π / 2 - θ) / 2 := by
    rw [hεdef]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hI : Set.Icc (θ - ε) (θ + ε) ⊆ Set.Ioo (0 : ℝ) (π / 2) := fun t ht =>
    ⟨by linarith [ht.1, hεθ, hθ.1], by linarith [ht.2, hεπ, hθ.2]⟩
  have hunif := tendstoUniformlyOn_psiTrunc_box α hα hα1 horth hsm hL2
    (a := z / 2) (b := 2 * z) (c := θ - ε) (d := θ + ε)
    (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith [hθ.2])
  have hunifθ : TendstoUniformlyOn
      (fun N : ℕ => fun t : ℝ => Work.FTS.PhiStar.Series.psiTrunc α F N z t)
      (fun t : ℝ => Psi α F z t) Filter.atTop (Set.Icc (θ - ε) (θ + ε)) := by
    rw [Metric.tendstoUniformlyOn_iff] at hunif ⊢
    intro η hη
    filter_upwards [hunif η hη] with N hN
    intro t ht
    exact hN (z, t) ⟨⟨by linarith, by linarith⟩, ht⟩
  have hcontI : ContinuousOn (fun t : ℝ => Psi α F z t) (Set.Icc (θ - ε) (θ + ε)) :=
    hunifθ.continuousOn (Filter.Eventually.of_forall (fun N =>
      ((continuousOn_uncurry_psiTrunc α hα hα1 hc N).comp
        (continuous_const.prodMk continuous_id).continuousOn
        (fun t ht => by
          rw [Work.FTS.EllipticEst.mem_Q0]
          exact ⟨hz, hI ht⟩)))).frequently
  have hnb : Set.Ioo (θ - ε) (θ + ε) ∈ 𝓝 θ :=
    isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  exact hcontI.continuousAt (Filter.mem_of_superset hnb (fun t ht =>
    ⟨le_of_lt ht.1, le_of_lt ht.2⟩))

end Work.FTS.H2.ModalSol
