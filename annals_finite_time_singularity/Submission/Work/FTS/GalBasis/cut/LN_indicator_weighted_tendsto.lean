import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.GalBasis.cc.Subcut.Defs
import Submission.Work.FTS.GalBasis.cc.Subcut.upper_inv_layer_le
import Submission.Work.FTS.GalBasis.cc.wwBasic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cut

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The two angular layers of `LN N`, and the majorant weight

Everything below is stated in terms of the two closed intervals that make up `cc.LN N`; the
identifications `LN N = layA N ∪ layB N` (immediate from the definitions) and
`layA N, layB N ⊆ Iθ` (for `N ≥ 1`) are collected first, together with the pointwise bound
`ε/(sin 2θ) ≥ 1_{LN N}·G²·sin(2θ)^{-γ}` that the trace hypotheses supply. -/

/-- The lower angular layer `[1/(N+1), 2/(N+1)]` of `cc.LN N`. -/
private def layA (N : ℕ) : Set ℝ := Set.Icc (1 / ((N : ℝ) + 1)) (2 * (1 / ((N : ℝ) + 1)))

/-- The upper angular layer `[π/2 - 2/(N+1), π/2 - 1/(N+1)]` of `cc.LN N`. -/
private def layB (N : ℕ) : Set ℝ :=
  Set.Icc (Real.pi / 2 - 2 * (1 / ((N : ℝ) + 1))) (Real.pi / 2 - 1 / ((N : ℝ) + 1))

/-- The majorant: `wgt ε θ = ε · sin(2θ)^{-1}`. -/
private def wgt (ε : ℝ) (θ : ℝ) : ℝ := ε * (Real.sin (2 * θ)) ^ (-1 : ℝ)

private lemma LN_eq_layers (N : ℕ) :
    Work.FTS.GalBasis.cc.LN N = layA N ∪ layB N := by
  have hupd : 2 / ((N : ℝ) + 1) = 2 * (1 / ((N : ℝ) + 1)) := by ring
  rw [Work.FTS.GalBasis.cc.LN, Work.FTS.GalBasis.cc.tlo, Work.FTS.GalBasis.cc.thi, hupd,
    layA, layB]

private lemma layA_subset_LN (N : ℕ) : layA N ⊆ Work.FTS.GalBasis.cc.LN N := by
  rw [LN_eq_layers N]; exact Set.subset_union_left

private lemma layB_subset_LN (N : ℕ) : layB N ⊆ Work.FTS.GalBasis.cc.LN N := by
  rw [LN_eq_layers N]; exact Set.subset_union_right

/-- For `N ≥ 1` the layer `cc.LN N` avoids the two endpoints of `Iθ`. -/
private lemma LN_subset_Ioo {N : ℕ} (hN : 1 ≤ N) :
    Work.FTS.GalBasis.cc.LN N ⊆ Set.Ioo 0 (Real.pi / 2) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h2 : 2 / ((N : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hpos]; linarith
  have h1 : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
  intro θ hθ
  rw [Work.FTS.GalBasis.cc.LN, Work.FTS.GalBasis.cc.tlo, Work.FTS.GalBasis.cc.thi,
    Set.mem_union, Set.mem_Icc, Set.mem_Icc] at hθ
  rcases hθ with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact ⟨by linarith, by linarith [h2, Real.pi_gt_three]⟩
  · exact ⟨by linarith [h2, Real.pi_gt_three], by linarith [h1]⟩

/-! ## The trace hypotheses as pointwise smallness -/

private lemma exists_lt_near_zero {g : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (h : Tendsto g (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0)) :
    ∃ δ > 0, ∀ θ, 0 < θ → θ < δ → g θ < c := by
  have hP : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Ioi 0), g θ < c :=
    h.eventually (Filter.eventually_iff.mpr (isOpen_Iio.mem_nhds hc))
  obtain ⟨δ, hδ0, hδ⟩ := Metric.mem_nhdsWithin_iff.mp (Filter.eventually_iff.mp hP)
  refine ⟨δ, hδ0, fun θ hθ0 hθδ => ?_⟩
  exact hδ ⟨by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hθ0]; exact hθδ, hθ0⟩

private lemma exists_lt_near_pi_half {g : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (h : Tendsto g (nhdsWithin (Real.pi / 2) (Iio (Real.pi / 2))) (nhds 0)) :
    ∃ δ > 0, ∀ θ, Real.pi / 2 - δ < θ → θ < Real.pi / 2 → g θ < c := by
  have hP : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Iio (Real.pi / 2)), g θ < c :=
    h.eventually (Filter.eventually_iff.mpr (isOpen_Iio.mem_nhds hc))
  obtain ⟨δ, hδ0, hδ⟩ := Metric.mem_nhdsWithin_iff.mp (Filter.eventually_iff.mp hP)
  refine ⟨δ, hδ0, fun θ h1 h2 => ?_⟩
  refine hδ ⟨?_, h2⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (by linarith)]
  linarith

/-- **The pointwise bound on the layer.**  If `Ξ θ = sin(2θ)^{1-γ}·G θ²` is below `ε` on the two
endpoint neighbourhoods, then on `cc.LN N` (for `N` large enough that `2/(N+1) < min δ δ'`) the
weighted integrand is below `ε·sin(2θ)^{-1}`. -/
private lemma layer_ptwise {γ : ℝ} {G : ℝ → ℝ} {ε δ δ' : ℝ}
    (hδ : ∀ θ, 0 < θ → θ < δ → Real.sin (2 * θ) ^ (1 - γ) * G θ ^ 2 < ε)
    (hδ' : ∀ θ, Real.pi / 2 - δ' < θ → θ < Real.pi / 2 →
      Real.sin (2 * θ) ^ (1 - γ) * G θ ^ 2 < ε)
    {N : ℕ} (hN : 1 ≤ N) (h2t : 2 * (1 / ((N : ℝ) + 1)) < min δ δ') {θ : ℝ}
    (hθ : θ ∈ Work.FTS.GalBasis.cc.LN N) :
    G θ ^ 2 * Real.sin (2 * θ) ^ (-γ) ≤ wgt ε θ := by
  have hpos : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
  have hmem : θ ∈ layA N ∪ layB N := by
    rw [← LN_eq_layers N]; exact hθ
  rw [Set.mem_union, layA, layB, Set.mem_Icc, Set.mem_Icc] at hmem
  have hsub := LN_subset_Ioo hN hθ
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hsub.1]) (by linarith [hsub.2, Real.pi_pos])
  have hΞ : Real.sin (2 * θ) ^ (1 - γ) * G θ ^ 2 < ε := by
    rcases hmem with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact hδ θ (by linarith) (by linarith [hb, h2t, min_le_left δ δ'])
    · exact hδ' θ (by linarith [ha, h2t, min_le_right δ δ']) (by linarith [hb, hpos])
  have hkey : Real.sin (2 * θ) ^ (-γ)
      = Real.sin (2 * θ) ^ (1 - γ) * Real.sin (2 * θ) ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hs]
    congr 1
    ring
  rw [wgt, hkey]
  calc G θ ^ 2 * (Real.sin (2 * θ) ^ (1 - γ) * Real.sin (2 * θ) ^ (-1 : ℝ))
      = (Real.sin (2 * θ) ^ (1 - γ) * G θ ^ 2) * Real.sin (2 * θ) ^ (-1 : ℝ) := by ring
    _ ≤ ε * Real.sin (2 * θ) ^ (-1 : ℝ) :=
        mul_le_mul_of_nonneg_right (le_of_lt hΞ) (Real.rpow_nonneg hs.le _)

/-! ## The two layer integrals -/

/-- The lower layer `[t, 2t]` carries at most `ε·π/4` of `ε/sin(2θ)` (Jordan's inequality, via
`layer_int_pow_le` at `γ = 1`). -/
private lemma layerA_int {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t) (ht2 : 2 * t ≤ Real.pi / 4) :
    ∫ θ in t..(2 * t), wgt ε θ ≤ ε * (Real.pi / 4) := by
  have hbase := Work.FTS.GalBasis.cc.layer_int_pow_le (γ := 1) (t := t) (by norm_num) ht ht2
  rw [Real.rpow_one] at hbase
  have hfun : (fun θ : ℝ => Real.sin (2 * θ) ^ (-1 : ℝ) * θ ^ ((1 : ℝ) - 1))
      = fun θ : ℝ => Real.sin (2 * θ) ^ (-1 : ℝ) := by
    funext θ
    rw [show (1 : ℝ) - 1 = 0 by norm_num, Real.rpow_zero, mul_one]
  rw [hfun] at hbase
  change ∫ θ in t..(2 * t), ε * Real.sin (2 * θ) ^ (-1 : ℝ) ≤ ε * (Real.pi / 4)
  calc ∫ θ in t..(2 * t), ε * Real.sin (2 * θ) ^ (-1 : ℝ)
      = ε * ∫ θ in t..(2 * t), Real.sin (2 * θ) ^ (-1 : ℝ) := by
        rw [intervalIntegral.integral_const_mul]
    _ ≤ ε * (Real.pi / 4) := mul_le_mul_of_nonneg_left hbase hε

/-- The upper layer `[π/2-2t, π/2-t]` carries at most `ε·π/4` of `ε/sin(2θ)` (the mirror of
`layer_int_pow_le`, already available as `upper_inv_layer_le`). -/
private lemma layerB_int {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t) (ht2 : 2 * t ≤ Real.pi / 4) :
    ∫ θ in (Real.pi / 2 - 2 * t)..(Real.pi / 2 - t), wgt ε θ ≤ ε * (Real.pi / 4) := by
  have hbase := Work.FTS.GalBasis.cc.Subcut.upper_inv_layer_le t ht ht2
  change ∫ θ in (Real.pi / 2 - 2 * t)..(Real.pi / 2 - t), ε * Real.sin (2 * θ) ^ (-1 : ℝ)
      ≤ ε * (Real.pi / 4)
  calc ∫ θ in (Real.pi / 2 - 2 * t)..(Real.pi / 2 - t), ε * Real.sin (2 * θ) ^ (-1 : ℝ)
      = ε * ∫ θ in (Real.pi / 2 - 2 * t)..(Real.pi / 2 - t), Real.sin (2 * θ) ^ (-1 : ℝ) := by
        rw [intervalIntegral.integral_const_mul]
    _ = ε * ∫ θ in (Real.pi / 2 - 2 * t)..(Real.pi / 2 - t), (Real.sin (2 * θ))⁻¹ := by
        congr 1
        refine intervalIntegral.integral_congr (fun x _ => ?_)
        rw [Real.rpow_neg_one]
    _ ≤ ε * (Real.pi / 4) := mul_le_mul_of_nonneg_left hbase hε

/-! ## Continuity and integrability of the majorant -/

private lemma continuousOn_wgt_of_subset {ε : ℝ} {s : Set ℝ}
    (hs : s ⊆ Set.Ioo 0 (Real.pi / 2)) : ContinuousOn (wgt ε) s := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) s :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hne : ∀ θ ∈ s, Real.sin (2 * θ) ≠ 0 := fun θ hθ =>
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [(hs hθ).1])
      (by linarith [(hs hθ).2, Real.pi_pos]))
  exact continuousOn_const.mul (hsin.rpow_const fun θ hθ => Or.inl (hne θ hθ))

/-- `wgt ε` is integrable on the layer `cc.LN N` for `N ≥ 1`. -/
private lemma integrableOn_wgt_LN {ε : ℝ} {N : ℕ} (hN : 1 ≤ N) :
    IntegrableOn (wgt ε) (Work.FTS.GalBasis.cc.LN N) := by
  have hA : IntegrableOn (wgt ε) (layA N) :=
    ContinuousOn.integrableOn_compact isCompact_Icc
      (continuousOn_wgt_of_subset (fun θ hθ => LN_subset_Ioo hN (layA_subset_LN N hθ)))
  have hB : IntegrableOn (wgt ε) (layB N) :=
    ContinuousOn.integrableOn_compact isCompact_Icc
      (continuousOn_wgt_of_subset (fun θ hθ => LN_subset_Ioo hN (layB_subset_LN N hθ)))
  rw [LN_eq_layers N]
  exact IntegrableOn.union hA hB

/-! ## The layer mass is at most `2ε` -/

/-- **The angular layer mass.**  For `N ≥ 2`, `∫_{Iθ} 1_{LN N}(θ)·ε·sin(2θ)^{-1} ≤ 2ε`. -/
private lemma LN_indicator_wgt_eval {ε : ℝ} (hε : 0 ≤ ε) {N : ℕ} (hN : 2 ≤ N)
    (h2t : 2 * (1 / ((N : ℝ) + 1)) ≤ Real.pi / 4) :
    ∫ θ in Work.Spaces.Iθ, (Work.FTS.GalBasis.cc.LN N).indicator (wgt ε) θ ≤ 2 * ε := by
  have hN1 : 1 ≤ N := le_trans (by norm_num : (1 : ℕ) ≤ 2) hN
  have hLNsub : Work.FTS.GalBasis.cc.LN N ⊆ Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact (LN_subset_Ioo hN1).trans Set.Ioo_subset_Icc_self
  have hpos : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
  have hle : 1 / ((N : ℝ) + 1) ≤ 2 * (1 / ((N : ℝ) + 1)) := by linarith
  have hAint : IntegrableOn (wgt ε) (layA N) :=
    ContinuousOn.integrableOn_compact isCompact_Icc
      (continuousOn_wgt_of_subset (fun θ hθ => LN_subset_Ioo hN1 (layA_subset_LN N hθ)))
  have hBint : IntegrableOn (wgt ε) (layB N) :=
    ContinuousOn.integrableOn_compact isCompact_Icc
      (continuousOn_wgt_of_subset (fun θ hθ => LN_subset_Ioo hN1 (layB_subset_LN N hθ)))
  have hIntA : ∫ θ in layA N, wgt ε θ ≤ ε * (Real.pi / 4) := by
    rw [layA, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle]
    exact layerA_int hε hpos h2t
  have hIntB : ∫ θ in layB N, wgt ε θ ≤ ε * (Real.pi / 4) := by
    have hle' : Real.pi / 2 - 2 * (1 / ((N : ℝ) + 1)) ≤ Real.pi / 2 - 1 / ((N : ℝ) + 1) := by
      linarith
    rw [layB, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle']
    exact layerB_int hε hpos h2t
  have hdisj : Disjoint (layA N) (layB N) := by
    rw [Set.disjoint_left]
    intro θ hθA hθB
    rw [layA, Set.mem_Icc] at hθA
    rw [layB, Set.mem_Icc] at hθB
    have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h3 : (3 : ℝ) ≤ (N : ℝ) + 1 := by linarith
    have h13 : 1 / ((N : ℝ) + 1) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) h3
    have h4 : 4 * (1 / ((N : ℝ) + 1)) ≤ 4 / 3 := by
      have := mul_le_mul_of_nonneg_left h13 (by norm_num : (0 : ℝ) ≤ 4)
      linarith
    have h43 : (4 : ℝ) / 3 < Real.pi / 2 := by linarith [Real.pi_gt_three]
    linarith [hθA.2, hθB.1, h4, h43]
  calc ∫ θ in Work.Spaces.Iθ, (Work.FTS.GalBasis.cc.LN N).indicator (wgt ε) θ
      = ∫ θ in Work.Spaces.Iθ ∩ Work.FTS.GalBasis.cc.LN N, wgt ε θ :=
        MeasureTheory.setIntegral_indicator (μ := volume) (f := wgt ε)
          (Work.FTS.GalBasis.cc.measurableSet_LN N)
    _ = ∫ θ in Work.FTS.GalBasis.cc.LN N, wgt ε θ := by rw [Set.inter_eq_right.mpr hLNsub]
    _ = ∫ θ in layA N ∪ layB N, wgt ε θ := by rw [LN_eq_layers N]
    _ = (∫ θ in layA N, wgt ε θ) + (∫ θ in layB N, wgt ε θ) :=
        MeasureTheory.setIntegral_union hdisj measurableSet_Icc hAint hBint
    _ ≤ (ε * (Real.pi / 4)) + (ε * (Real.pi / 4)) := add_le_add hIntA hIntB
    _ = 2 * ε * (Real.pi / 4) := by ring
    _ ≤ 2 * ε := by
        have hπ : Real.pi / 4 ≤ 1 := by linarith [Real.pi_lt_four]
        have h2ε : (0 : ℝ) ≤ 2 * ε := by linarith
        have hstep := mul_le_mul_of_nonneg_left hπ h2ε
        linarith

/-! ## The main theorem -/

/-- **The shrinking angular layers `LN N` carry no `s^{-γ}`-weighted mass.**

`LN N = [1/(N+1), 2/(N+1)] ∪ [π/2 - 2/(N+1), π/2 - 1/(N+1)]` shrinks to the two endpoints of
`Iθ = [0, π/2]`; the hypothesis is that the `(1-γ)`-trace `Ξ θ = sin(2θ)^(1-γ)·G(θ)²` vanishes at
both endpoints, and the conclusion is that the weighted mass on the layer tends to `0`.

Route.  Fix `ε > 0`.  From the two trace hypotheses obtain `δ, δ' > 0` with `Ξ θ ≤ ε` for
`θ ∈ (0,δ)` and for `θ ∈ (π/2-δ', π/2)` (`Ξ ≥ 0`, so the limit statement gives this pointwise
smallness; `Metric.tendsto_nhdsWithin_nhds`).  For `N` large enough that `2/(N+1) < min δ δ'`
(and `N ≥ 2`) and `θ ∈ LN N ⊆ Iθ`, the point `θ` lies in `(0,δ) ∪ (π/2-δ',π/2)` (lower layer:
`0 < tlo N ≤ θ ≤ 2/(N+1) < δ`; upper layer: `π/2 - 2/(N+1) ≤ θ ≤ thi N < π/2` and
`θ > π/2 - δ'`), hence `Ξ θ ≤ ε`.  Therefore
`1_{LN N}(θ)·G(θ)²·sin(2θ)^{-γ} = 1_{LN N}(θ)·Ξ θ·sin(2θ)^{-1} ≤ 1_{LN N}(θ)·ε·sin(2θ)^{-1}`
pointwise on `Iθ`, and so the integral of the left side is at most `ε·∫_{Iθ} 1_{LN N}(θ)·sin(2θ)^{-1}`
(if the left integrand is not integrable its Bochner integral is `0`, so `MeasureTheory.integral_undef`
plus `integral_mono_ae` with both sides integrable handles it).

The remaining angular bound is `∫_{Iθ} 1_{LN N}(θ)·sin(2θ)^{-1} ≤ π/2`: on each of the two layers
the length is `1/(N+1)` and `sin(2θ) ≥ 4/(π(N+1))` there (Jordan's inequality `4x/π ≤ sin(2x)` for
`0 ≤ x ≤ π/4`, applied to `x = θ` on the lower layer and to `x = π/2 - θ` on the upper one, using
`sin(2(π/2-θ)) = sin(2θ)`); so each layer contributes at most `π/4`.  Equivalently use
`Work.FTS.GalBasis.cc.layer_int_pow_le` at `γ = 1` (`∫_t^{2t} sin(2θ)^{-1} ≤ π/4` for `2t ≤ π/4`)
together with `intervalIntegral.integral_comp_sub_left` for the reflected layer.

Only continuity of `G` on the two layers (compact subsets of `(0,π/2)`) enters, via integrability of
the two bounded integrands there; note however that the statement must be proved *without* assuming
anything about `G` beyond the two traces (the junk-value case is handled as above). -/
theorem LN_indicator_weighted_tendsto {γ : ℝ} (hγ : 1 < γ) {G : ℝ → ℝ}
    (ht0 : Filter.Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - γ) * G θ ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htπ : Filter.Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - γ) * G θ ^ 2)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    Filter.Tendsto (fun N : ℕ => ∫ θ in Work.Spaces.Iθ,
        (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ
          * (G θ ^ 2 * Real.sin (2 * θ) ^ (-γ)))
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε₁ hε₁
  set ε : ℝ := ε₁ / 3 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hεnn : 0 ≤ ε := le_of_lt hε
  obtain ⟨δ, hδ0, hδ⟩ := exists_lt_near_zero hε ht0
  obtain ⟨δ', hδ'0, hδ'⟩ := exists_lt_near_pi_half hε htπ
  have hminpos : (0 : ℝ) < min δ δ' / 2 := by
    have : (0 : ℝ) < min δ δ' := lt_min hδ0 hδ'0
    linarith
  have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hev : ∀ᶠ N : ℕ in atTop, 1 / ((N : ℝ) + 1) < min δ δ' / 2 :=
    hlim.eventually (Filter.eventually_iff.mpr (isOpen_Iio.mem_nhds hminpos))
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max 2 N₁, fun N hN => ?_⟩
  have hNge2 : 2 ≤ N := le_trans (le_max_left _ _) hN
  have hNge1 : 1 ≤ N := le_trans (by norm_num : (1 : ℕ) ≤ 2) hNge2
  have h1div : 1 / ((N : ℝ) + 1) < min δ δ' / 2 := hN₁ N (le_trans (le_max_right _ _) hN)
  have h2tlt : 2 * (1 / ((N : ℝ) + 1)) < min δ δ' := by
    have h := mul_lt_mul_of_pos_left h1div (by norm_num : (0 : ℝ) < 2)
    linarith
  have h2tpi : 2 * (1 / ((N : ℝ) + 1)) ≤ Real.pi / 4 := by
    have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNge2
    have h3 : (3 : ℝ) ≤ (N : ℝ) + 1 := by linarith
    have h13 : 1 / ((N : ℝ) + 1) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) h3
    have h23 : 2 * (1 / ((N : ℝ) + 1)) ≤ 2 * (1 / 3) :=
      mul_le_mul_of_nonneg_left h13 (by norm_num)
    have h34 : 2 * (1 / 3 : ℝ) ≤ Real.pi / 4 := by linarith [Real.pi_gt_three]
    linarith
  have hpoint : ∀ θ : ℝ, (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ
        * (G θ ^ 2 * Real.sin (2 * θ) ^ (-γ))
      ≤ (Work.FTS.GalBasis.cc.LN N).indicator (wgt ε) θ := by
    intro θ
    by_cases h : θ ∈ Work.FTS.GalBasis.cc.LN N
    · rw [Set.indicator_of_mem h, one_mul, Set.indicator_of_mem h]
      exact layer_ptwise hδ hδ' hNge1 h2tlt h
    · rw [Set.indicator_of_notMem h, zero_mul, Set.indicator_of_notMem h]
  have hFnn : ∀ θ : ℝ, 0 ≤ (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ
        * (G θ ^ 2 * Real.sin (2 * θ) ^ (-γ)) := by
    intro θ
    by_cases h : θ ∈ Work.FTS.GalBasis.cc.LN N
    · rw [Set.indicator_of_mem h, one_mul]
      have hsub := LN_subset_Ioo hNge1 h
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [hsub.1])
          (by linarith [hsub.2, Real.pi_pos]))) _)
    · rw [Set.indicator_of_notMem h, zero_mul]
  have hHint : IntegrableOn ((Work.FTS.GalBasis.cc.LN N).indicator (wgt ε)) Work.Spaces.Iθ := by
    have h := (integrable_indicator_iff (Work.FTS.GalBasis.cc.measurableSet_LN N)).mpr
      (integrableOn_wgt_LN (ε := ε) hNge1)
    exact h.mono_measure MeasureTheory.Measure.restrict_le_self
  have hHeval : ∫ θ in Work.Spaces.Iθ, (Work.FTS.GalBasis.cc.LN N).indicator (wgt ε) θ ≤ 2 * ε :=
    LN_indicator_wgt_eval hεnn hNge2 h2tpi
  have hmono : ∫ θ in Work.Spaces.Iθ, (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ
        * (G θ ^ 2 * Real.sin (2 * θ) ^ (-γ))
      ≤ ∫ θ in Work.Spaces.Iθ, (Work.FTS.GalBasis.cc.LN N).indicator (wgt ε) θ :=
    MeasureTheory.integral_mono_of_nonneg (μ := volume.restrict Work.Spaces.Iθ)
      (Filter.Eventually.of_forall hFnn) hHint (Filter.Eventually.of_forall hpoint)
  have hFint : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ
        * (G θ ^ 2 * Real.sin (2 * θ) ^ (-γ)) :=
    MeasureTheory.integral_nonneg hFnn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hFint]
  calc ∫ θ in Work.Spaces.Iθ, (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ
        * (G θ ^ 2 * Real.sin (2 * θ) ^ (-γ))
      ≤ ∫ θ in Work.Spaces.Iθ, (Work.FTS.GalBasis.cc.LN N).indicator (wgt ε) θ := hmono
    _ ≤ 2 * ε := hHeval
    _ < ε₁ := by rw [hεdef]; linarith

end Work.FTS.GalBasis.cut
