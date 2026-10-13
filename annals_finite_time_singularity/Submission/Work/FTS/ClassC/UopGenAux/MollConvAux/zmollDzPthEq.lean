import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_Gquad_eq_zmoll
import Submission.Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_Gquad_eq_conv
import Submission.Work.FTS.EllSol.EllPkgAux.MollSmooth.Hxy_quad_locallyIntegrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC.UopGenAux.MollConvAux

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Elementary facts about the mollifying kernels -/

/-- `sKer δ` is continuous. -/
private lemma sKer_cont (δ : ℝ) : Continuous (Work.FTS.EllSol.PkgK5.K5c.sKer δ) := by
  have h : (fun t : ℝ => (δ * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ *
      Work.FTS.EllSol.PkgK5.K5c.sBump (t / δ)) = Work.FTS.EllSol.PkgK5.K5c.sKer δ := by
    funext t; simp only [Work.FTS.EllSol.PkgK5.K5c.sKer]
  rw [← h]
  exact continuous_const.mul (Work.FTS.EllSol.PkgK5.K5c.sBump_continuous.comp
    (continuous_id.div_const δ))

/-- `sKer δ` is compactly supported (in `[-δ, δ]`). -/
private lemma sKer_cs (δ : ℝ) (hδ : 0 < δ) :
    HasCompactSupport (Work.FTS.EllSol.PkgK5.K5c.sKer δ) := by
  refine HasCompactSupport.intro (K := Set.Icc (-δ) δ) isCompact_Icc ?_
  intro t ht
  refine Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ ?_
  rw [Set.mem_Icc, not_and_or] at ht
  rcases ht with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-- `sKerd ε = deriv (sKer ε)` is continuous. -/
private lemma sKerd_cont (ε : ℝ) : Continuous (Work.FTS.EllSol.EllPkgAux.sKerd ε) := by
  have h : ContDiff ℝ 1 (Work.FTS.EllSol.PkgK5.K5c.sKer ε) :=
    Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 1)
  simpa [Work.FTS.EllSol.EllPkgAux.sKerd] using h.continuous_deriv_one

/-- `sKerd ε = deriv (sKer ε)` vanishes outside `[-ε, ε]`. -/
private lemma sKerd_eq_zero_of_lt_abs {ε t : ℝ} (hε : 0 < ε) (ht : ε < |t|) :
    Work.FTS.EllSol.EllPkgAux.sKerd ε t = 0 := by
  have hev : Work.FTS.EllSol.PkgK5.K5c.sKer ε =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) := by
    show ∀ᶠ y in 𝓝 t, Work.FTS.EllSol.PkgK5.K5c.sKer ε y = 0
    rw [Metric.eventually_nhds_iff]
    refine ⟨(|t| - ε) / 2, by linarith, ?_⟩
    intro y hy
    have h1 : |y - t| < (|t| - ε) / 2 := by simpa [Real.dist_eq] using hy
    have h2 : ε < |y| := by
      have h3 : |t| ≤ |y| + |y - t| := by simpa [abs_sub_comm] using abs_sub_le y 0 (y - t)
      linarith
    exact Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε (le_of_lt h2)
  rw [Work.FTS.EllSol.EllPkgAux.sKerd, hev.deriv_eq, deriv_const]

/-- `sKerd ε` is compactly supported (in `[-ε, ε]`). -/
private lemma sKerd_cs (ε : ℝ) (hε : 0 < ε) :
    HasCompactSupport (Work.FTS.EllSol.EllPkgAux.sKerd ε) := by
  refine HasCompactSupport.intro (K := Set.Icc (-ε) ε) isCompact_Icc ?_
  intro t ht
  refine sKerd_eq_zero_of_lt_abs hε ?_
  rw [Set.mem_Icc, not_and_or] at ht
  rcases ht with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-- A global bound for `sKer δ`. -/
private lemma exists_bound_sKer (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ t : ℝ, ‖Work.FTS.EllSol.PkgK5.K5c.sKer δ t‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -δ) (b := δ)).exists_bound_of_continuousOn
    (sKer_cont δ).continuousOn
  refine ⟨max C 0, fun t => ?_⟩
  by_cases ht : t ∈ Set.Icc (-δ) δ
  · exact le_trans (hC t ht) (le_max_left _ _)
  · rw [Set.mem_Icc, not_and_or] at ht
    have hz : Work.FTS.EllSol.PkgK5.K5c.sKer δ t = 0 := by
      refine Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ ?_
      rcases ht with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [hz, norm_zero]
    exact le_max_right _ _

/-- A global bound for `sKerd ε`. -/
private lemma exists_bound_sKerd (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ t : ℝ, ‖Work.FTS.EllSol.EllPkgAux.sKerd ε t‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -ε) (b := ε)).exists_bound_of_continuousOn
    (sKerd_cont ε).continuousOn
  refine ⟨max C 0, fun t => ?_⟩
  by_cases ht : t ∈ Set.Icc (-ε) ε
  · exact le_trans (hC t ht) (le_max_left _ _)
  · rw [Set.mem_Icc, not_and_or] at ht
    have hz : Work.FTS.EllSol.EllPkgAux.sKerd ε t = 0 := by
      refine sKerd_eq_zero_of_lt_abs hε ?_
      rcases ht with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [hz, norm_zero]
    exact le_max_right _ _

/-- `sKer δ (c - t) = 0` when `t` lies outside the interval `[c - δ, c + δ]`. -/
private lemma sKer_eq_zero_of_notMem_Icc {δ c t : ℝ} (hδ : 0 < δ)
    (h : t ∉ Set.Icc (c - δ) (c + δ)) : Work.FTS.EllSol.PkgK5.K5c.sKer δ (c - t) = 0 := by
  refine Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ (le_of_lt ?_)
  rw [Set.mem_Icc, not_and_or] at h
  rcases h with h | h
  · rw [abs_of_pos (by linarith)]; linarith
  · rw [abs_of_neg (by linarith)]; linarith

/-- `sKerd ε (c - t) = 0` when `t` lies outside the interval `[c - ε, c + ε]`. -/
private lemma sKerd_eq_zero_of_notMem_Icc {ε c t : ℝ} (hε : 0 < ε)
    (h : t ∉ Set.Icc (c - ε) (c + ε)) : Work.FTS.EllSol.EllPkgAux.sKerd ε (c - t) = 0 := by
  refine sKerd_eq_zero_of_lt_abs hε ?_
  rw [Set.mem_Icc, not_and_or] at h
  rcases h with h | h
  · rw [abs_of_pos (by linarith)]; linarith
  · rw [abs_of_neg (by linarith)]; linarith

/-- `sKerd ε (y - p) = 0` when `y` is within distance `1` of `c` while `p` is farther than
`1 + ε` from `c`. -/
private lemma sKerd_eq_zero_of_notMem_Icc_shift {ε y p c : ℝ} (hε : 0 < ε)
    (hy : y ∈ Set.Icc (c - 1) (c + 1)) (h : p ∉ Set.Icc (c - 1 - ε) (c + 1 + ε)) :
    Work.FTS.EllSol.EllPkgAux.sKerd ε (y - p) = 0 := by
  refine sKerd_eq_zero_of_lt_abs hε ?_
  rw [Set.mem_Icc] at hy
  rw [Set.mem_Icc, not_and_or] at h
  rcases h with h | h
  · rw [abs_of_pos (by linarith)]; linarith
  · rw [abs_of_neg (by linarith)]; linarith

/-! ## The two partial derivatives of the doubly-mollified convolution -/

/-- **The `θ`-derivative.**  For a locally integrable `H`, the `θ`-partial of the doubly
mollified convolution `∫ p, H p · sKer δ (x₁ - p₁) · sKer ε (θ - p₂)` is obtained by moving
the derivative onto the *inner* kernel. -/
private lemma hasDerivAt_slice_snd (H : ℝ × ℝ → ℝ)
    (hH : MeasureTheory.LocallyIntegrable H MeasureTheory.volume)
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (x : ℝ × ℝ) :
    HasDerivAt (fun y : ℝ => ∫ p : ℝ × ℝ,
        H p * (Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)
          * Work.FTS.EllSol.PkgK5.K5c.sKer ε (y - p.2)))
      (∫ p : ℝ × ℝ, H p * (Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)
          * Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2))) x.2 := by
  obtain ⟨C₁, hC₁⟩ := exists_bound_sKer δ hδ
  obtain ⟨C₂, hC₂⟩ := exists_bound_sKerd ε hε
  have hδc : Continuous (Work.FTS.EllSol.PkgK5.K5c.sKer δ) := sKer_cont δ
  have hεc : Continuous (Work.FTS.EllSol.PkgK5.K5c.sKer ε) := sKer_cont ε
  have hεdc : Continuous (Work.FTS.EllSol.EllPkgAux.sKerd ε) := sKerd_cont ε
  set Kbox : Set (ℝ × ℝ) :=
    Set.Icc (x.1 - δ) (x.1 + δ) ×ˢ Set.Icc (x.2 - 1 - ε) (x.2 + 1 + ε) with hKbox
  have hKc : IsCompact Kbox := isCompact_Icc.prod isCompact_Icc
  have hKmeas : MeasurableSet Kbox := measurableSet_Icc.prod measurableSet_Icc
  have hbnd_int : Integrable
      (fun p : ℝ × ℝ => C₁ * C₂ * Kbox.indicator (fun q : ℝ × ℝ => ‖H q‖) p)
      MeasureTheory.volume := by
    have h1 : Integrable (Kbox.indicator (fun q : ℝ × ℝ => ‖H q‖)) MeasureTheory.volume := by
      have h2 : Integrable (fun q : ℝ × ℝ => ‖Kbox.indicator H q‖) MeasureTheory.volume :=
        ((integrable_indicator_iff hKmeas).mpr (hH.integrableOn_isCompact hKc)).norm
      refine h2.congr ?_
      filter_upwards with q
      by_cases hq : q ∈ Kbox
      · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
      · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq, norm_zero]
    exact h1.const_mul (C₁ * C₂)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := MeasureTheory.volume)
    (F := fun y : ℝ => fun p : ℝ × ℝ => H p * (Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)
        * Work.FTS.EllSol.PkgK5.K5c.sKer ε (y - p.2)))
    (F' := fun y : ℝ => fun p : ℝ × ℝ => H p * (Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)
        * Work.FTS.EllSol.EllPkgAux.sKerd ε (y - p.2)))
    (bound := fun p : ℝ × ℝ => C₁ * C₂ * Kbox.indicator (fun q : ℝ × ℝ => ‖H q‖) p)
    (x₀ := x.2) (s := Set.Ioo (x.2 - 1) (x.2 + 1))
    (Ioo_mem_nhds (by linarith) (by linarith)) ?_ ?_ ?_ ?_ hbnd_int ?_).2
  · refine Filter.Eventually.of_forall fun y => ?_
    have hc : Continuous (fun p : ℝ × ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)
        * Work.FTS.EllSol.PkgK5.K5c.sKer ε (y - p.2)) :=
      (hδc.comp (continuous_const.sub continuous_fst)).mul
        (hεc.comp (continuous_const.sub continuous_snd))
    exact hH.aestronglyMeasurable.mul hc.aestronglyMeasurable
  · have hc : Continuous (fun p : ℝ × ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)
        * Work.FTS.EllSol.PkgK5.K5c.sKer ε (x.2 - p.2)) :=
      (hδc.comp (continuous_const.sub continuous_fst)).mul
        (hεc.comp (continuous_const.sub continuous_snd))
    have hcs : HasCompactSupport (fun p : ℝ × ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)
        * Work.FTS.EllSol.PkgK5.K5c.sKer ε (x.2 - p.2)) := by
      refine HasCompactSupport.intro
        (K := Set.Icc (x.1 - δ) (x.1 + δ) ×ˢ Set.Icc (x.2 - ε) (x.2 + ε))
        (isCompact_Icc.prod isCompact_Icc) ?_
      intro p hp
      rw [Set.mem_prod, not_and_or] at hp
      rcases hp with hp | hp
      · rw [sKer_eq_zero_of_notMem_Icc hδ hp, zero_mul]
      · rw [sKer_eq_zero_of_notMem_Icc hε hp, mul_zero]
    have h := hH.integrable_smul_left_of_hasCompactSupport hc hcs
    refine h.congr ?_
    filter_upwards with p
    rw [smul_eq_mul]; ring
  · have hc : Continuous (fun p : ℝ × ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)
        * Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2)) :=
      (hδc.comp (continuous_const.sub continuous_fst)).mul
        (hεdc.comp (continuous_const.sub continuous_snd))
    exact hH.aestronglyMeasurable.mul hc.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun p => ?_
    intro y hy
    by_cases hp : p ∈ Kbox
    · rw [Set.indicator_of_mem hp]
      have hA : ‖Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)‖ ≤ C₁ := hC₁ _
      have hB : ‖Work.FTS.EllSol.EllPkgAux.sKerd ε (y - p.2)‖ ≤ C₂ := hC₂ _
      have hAnn : (0 : ℝ) ≤ ‖Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)‖ := norm_nonneg _
      have hBnn : (0 : ℝ) ≤ ‖Work.FTS.EllSol.EllPkgAux.sKerd ε (y - p.2)‖ := norm_nonneg _
      have hC₁nn : (0 : ℝ) ≤ C₁ := le_trans hAnn hA
      have hprod : ‖Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)‖
          * ‖Work.FTS.EllSol.EllPkgAux.sKerd ε (y - p.2)‖ ≤ C₁ * C₂ :=
        mul_le_mul hA hB hBnn hC₁nn
      calc ‖H p * (Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)
            * Work.FTS.EllSol.EllPkgAux.sKerd ε (y - p.2))‖
          = ‖H p‖ * ‖Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)
              * Work.FTS.EllSol.EllPkgAux.sKerd ε (y - p.2)‖ := norm_mul _ _
        _ = ‖H p‖ * (‖Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)‖
              * ‖Work.FTS.EllSol.EllPkgAux.sKerd ε (y - p.2)‖) := by rw [norm_mul]
        _ ≤ ‖H p‖ * (C₁ * C₂) := mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
        _ = C₁ * C₂ * ‖H p‖ := by ring
    · rw [Set.indicator_of_notMem hp]
      rw [hKbox] at hp
      rw [Set.mem_prod, not_and_or] at hp
      rcases hp with hp | hp
      · have hz : Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1) = 0 :=
          sKer_eq_zero_of_notMem_Icc hδ hp
        simp [hz]
      · have hz : Work.FTS.EllSol.EllPkgAux.sKerd ε (y - p.2) = 0 :=
          sKerd_eq_zero_of_notMem_Icc_shift hε
            (Set.mem_Icc.mpr ⟨le_of_lt hy.1, le_of_lt hy.2⟩) hp
        simp [hz]
  · refine Filter.Eventually.of_forall fun p => ?_
    intro y _
    have hsm : HasDerivAt (fun y : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer ε (y - p.2))
        (Work.FTS.EllSol.EllPkgAux.sKerd ε (y - p.2)) y :=
      (show HasDerivAt (Work.FTS.EllSol.PkgK5.K5c.sKer ε)
          (Work.FTS.EllSol.EllPkgAux.sKerd ε (y - p.2)) (y - p.2) from
        (((Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 1)).differentiable_one)
          (y - p.2)).hasDerivAt).comp_sub_const y p.2
    exact (hsm.const_mul (Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1))).const_mul (H p)

/-- **The `z`-derivative.**  For a locally integrable `H`, the first partial of
`∫ p, H p · sKer δ (x₁ - p₁) · sKerd ε (x₂ - p₂)` is obtained by moving the derivative onto
the *outer* kernel. -/
private lemma hasDerivAt_slice_fst (H : ℝ × ℝ → ℝ)
    (hH : MeasureTheory.LocallyIntegrable H MeasureTheory.volume)
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (x : ℝ × ℝ) :
    HasDerivAt (fun y : ℝ => ∫ p : ℝ × ℝ,
        H p * (Work.FTS.EllSol.PkgK5.K5c.sKer δ (y - p.1)
          * Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2)))
      (∫ p : ℝ × ℝ, H p * (Work.FTS.EllSol.EllPkgAux.sKerd δ (x.1 - p.1)
          * Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2))) x.1 := by
  obtain ⟨C₁, hC₁⟩ := exists_bound_sKerd δ hδ
  obtain ⟨C₂, hC₂⟩ := exists_bound_sKerd ε hε
  have hδc : Continuous (Work.FTS.EllSol.PkgK5.K5c.sKer δ) := sKer_cont δ
  have hδdc : Continuous (Work.FTS.EllSol.EllPkgAux.sKerd δ) := sKerd_cont δ
  have hεdc : Continuous (Work.FTS.EllSol.EllPkgAux.sKerd ε) := sKerd_cont ε
  set Kbox : Set (ℝ × ℝ) :=
    Set.Icc (x.1 - 1 - δ) (x.1 + 1 + δ) ×ˢ Set.Icc (x.2 - ε) (x.2 + ε) with hKbox
  have hKc : IsCompact Kbox := isCompact_Icc.prod isCompact_Icc
  have hKmeas : MeasurableSet Kbox := measurableSet_Icc.prod measurableSet_Icc
  have hbnd_int : Integrable
      (fun p : ℝ × ℝ => C₁ * C₂ * Kbox.indicator (fun q : ℝ × ℝ => ‖H q‖) p)
      MeasureTheory.volume := by
    have h1 : Integrable (Kbox.indicator (fun q : ℝ × ℝ => ‖H q‖)) MeasureTheory.volume := by
      have h2 : Integrable (fun q : ℝ × ℝ => ‖Kbox.indicator H q‖) MeasureTheory.volume :=
        ((integrable_indicator_iff hKmeas).mpr (hH.integrableOn_isCompact hKc)).norm
      refine h2.congr ?_
      filter_upwards with q
      by_cases hq : q ∈ Kbox
      · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
      · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq, norm_zero]
    exact h1.const_mul (C₁ * C₂)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := MeasureTheory.volume)
    (F := fun t : ℝ => fun p : ℝ × ℝ => H p * (Work.FTS.EllSol.PkgK5.K5c.sKer δ (t - p.1)
        * Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2)))
    (F' := fun t : ℝ => fun p : ℝ × ℝ => H p * (Work.FTS.EllSol.EllPkgAux.sKerd δ (t - p.1)
        * Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2)))
    (bound := fun p : ℝ × ℝ => C₁ * C₂ * Kbox.indicator (fun q : ℝ × ℝ => ‖H q‖) p)
    (x₀ := x.1) (s := Set.Ioo (x.1 - 1) (x.1 + 1))
    (Ioo_mem_nhds (by linarith) (by linarith)) ?_ ?_ ?_ ?_ hbnd_int ?_).2
  · refine Filter.Eventually.of_forall fun t => ?_
    have hc : Continuous (fun p : ℝ × ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (t - p.1)
        * Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2)) :=
      (hδc.comp (continuous_const.sub continuous_fst)).mul
        (hεdc.comp (continuous_const.sub continuous_snd))
    exact hH.aestronglyMeasurable.mul hc.aestronglyMeasurable
  · have hc : Continuous (fun p : ℝ × ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)
        * Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2)) :=
      (hδc.comp (continuous_const.sub continuous_fst)).mul
        (hεdc.comp (continuous_const.sub continuous_snd))
    have hcs : HasCompactSupport (fun p : ℝ × ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)
        * Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2)) := by
      refine HasCompactSupport.intro
        (K := Set.Icc (x.1 - δ) (x.1 + δ) ×ˢ Set.Icc (x.2 - ε) (x.2 + ε))
        (isCompact_Icc.prod isCompact_Icc) ?_
      intro p hp
      rw [Set.mem_prod, not_and_or] at hp
      rcases hp with hp | hp
      · rw [sKer_eq_zero_of_notMem_Icc hδ hp, zero_mul]
      · rw [sKerd_eq_zero_of_notMem_Icc hε hp, mul_zero]
    have h := hH.integrable_smul_left_of_hasCompactSupport hc hcs
    refine h.congr ?_
    filter_upwards with p
    rw [smul_eq_mul]; ring
  · have hc : Continuous (fun p : ℝ × ℝ => Work.FTS.EllSol.EllPkgAux.sKerd δ (x.1 - p.1)
        * Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2)) :=
      (hδdc.comp (continuous_const.sub continuous_fst)).mul
        (hεdc.comp (continuous_const.sub continuous_snd))
    exact hH.aestronglyMeasurable.mul hc.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun p => ?_
    intro t ht
    by_cases hp : p ∈ Kbox
    · rw [Set.indicator_of_mem hp]
      have hA : ‖Work.FTS.EllSol.EllPkgAux.sKerd δ (t - p.1)‖ ≤ C₁ := hC₁ _
      have hB : ‖Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2)‖ ≤ C₂ := hC₂ _
      have hAnn : (0 : ℝ) ≤ ‖Work.FTS.EllSol.EllPkgAux.sKerd δ (t - p.1)‖ := norm_nonneg _
      have hBnn : (0 : ℝ) ≤ ‖Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2)‖ := norm_nonneg _
      have hC₁nn : (0 : ℝ) ≤ C₁ := le_trans hAnn hA
      have hprod : ‖Work.FTS.EllSol.EllPkgAux.sKerd δ (t - p.1)‖
          * ‖Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2)‖ ≤ C₁ * C₂ :=
        mul_le_mul hA hB hBnn hC₁nn
      calc ‖H p * (Work.FTS.EllSol.EllPkgAux.sKerd δ (t - p.1)
            * Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2))‖
          = ‖H p‖ * ‖Work.FTS.EllSol.EllPkgAux.sKerd δ (t - p.1)
              * Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2)‖ := norm_mul _ _
        _ = ‖H p‖ * (‖Work.FTS.EllSol.EllPkgAux.sKerd δ (t - p.1)‖
              * ‖Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2)‖) := by rw [norm_mul]
        _ ≤ ‖H p‖ * (C₁ * C₂) := mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
        _ = C₁ * C₂ * ‖H p‖ := by ring
    · rw [Set.indicator_of_notMem hp]
      rw [hKbox] at hp
      rw [Set.mem_prod, not_and_or] at hp
      rcases hp with hp | hp
      · have hz : Work.FTS.EllSol.EllPkgAux.sKerd δ (t - p.1) = 0 :=
          sKerd_eq_zero_of_notMem_Icc_shift hδ
            (Set.mem_Icc.mpr ⟨le_of_lt ht.1, le_of_lt ht.2⟩) hp
        simp [hz]
      · have hz : Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2) = 0 :=
          sKerd_eq_zero_of_notMem_Icc hε hp
        simp [hz]
  · refine Filter.Eventually.of_forall fun p => ?_
    intro t _
    have hsm : HasDerivAt (fun y : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (y - p.1))
        (Work.FTS.EllSol.EllPkgAux.sKerd δ (t - p.1)) t :=
      (show HasDerivAt (Work.FTS.EllSol.PkgK5.K5c.sKer δ)
          (Work.FTS.EllSol.EllPkgAux.sKerd δ (t - p.1)) (t - p.1) from
        (((Work.FTS.EllSol.EllPkgAux.contDiff_sKer δ (n := 1)).differentiable_one)
          (t - p.1)).hasDerivAt).comp_sub_const t p.1
    exact (hsm.mul_const (Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2))).const_mul (H p)

theorem zmollDzPthEq (G : ℝ → ℝ → ℝ)
    (hloc : MeasureTheory.LocallyIntegrable
      (Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G)) MeasureTheory.volume)
    (h0 : ∀ z : ℝ, G z 0 = 0) (hπ : ∀ z : ℝ, G z (Real.pi / 2) = 0)
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (z : ℝ) (hz : 0 < z) (θ : ℝ) (hθ : θ ∈ Set.Ioo (-(1:ℝ) / 2) (Real.pi / 2 + 1 / 2)) :
    Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)) z θ
      = ∫ u : ℝ, ∫ v : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ u
          * Work.FTS.EllSol.EllPkgAux.sKerd ε v
          * Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G)
              (Real.log z - u, θ - v) := by
  have hθ' : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  -- ## Step 1: the doubly-mollified datum, as an integral against the two kernels
  have hA : ∀ z' θ' : ℝ, 0 < z' → θ' ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) →
      Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε z' θ'
        = ∫ p : ℝ × ℝ, Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G) p
            * (Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z' - p.1)
              * Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ' - p.2)) := by
    intro z' θ' hz' hθ''
    rw [← Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_Gquad_eq_zmoll G h0 hπ δ ε hε hε2 z' θ' hθ'']
    rw [Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_Gquad_eq_conv G hloc δ ε hδ hε z' θ' hz']
    rw [MeasureTheory.convolution_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [Work.FTS.EllSol.EllPkgAux.Kd, Prod.fst_sub, Prod.snd_sub]
  -- ## Step 2: the `θ`-derivative of the slice
  have hinner : ∀ z' : ℝ, 0 < z' →
      Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z' θ
        = ∫ p : ℝ × ℝ, Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G) p
            * (Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z' - p.1)
              * Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - p.2)) := by
    intro z' hz'
    rw [Work.Spaces.pth]
    have hev : (fun θ'' : ℝ => Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε z' θ'') =ᶠ[𝓝 θ]
        (fun θ'' : ℝ => ∫ p : ℝ × ℝ,
            Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G) p
            * (Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z' - p.1)
              * Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ'' - p.2))) :=
      Filter.Eventually.mono
        (IsOpen.mem_nhds (isOpen_Ioo : IsOpen (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1))) hθ')
        fun θ'' hθ'' => hA z' θ'' hz' hθ''
    rw [hev.deriv_eq]
    exact (hasDerivAt_slice_snd
      (H := Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G))
      hloc δ ε hδ hε (Real.log z', θ)).deriv
  -- ## Step 3: the `z`-derivative
  have houter : deriv (fun z' : ℝ =>
        deriv (fun θ'' : ℝ => Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε z' θ'') θ) z
      = (∫ p : ℝ × ℝ, Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G) p
            * (Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - p.1)
              * Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - p.2))) * z⁻¹ := by
    have h1 : (fun z' : ℝ =>
          deriv (fun θ'' : ℝ => Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε z' θ'') θ) =ᶠ[𝓝 z]
        (fun z' : ℝ => ∫ p : ℝ × ℝ,
            Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G) p
            * (Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z' - p.1)
              * Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - p.2))) :=
      Filter.Eventually.mono (IsOpen.mem_nhds isOpen_Ioi hz) fun z' hz' => hinner z' hz'
    rw [h1.deriv_eq]
    change deriv ((fun y : ℝ => ∫ p : ℝ × ℝ,
        Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G) p
        * (Work.FTS.EllSol.PkgK5.K5c.sKer δ (y - p.1)
          * Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - p.2))) ∘ Real.log) z
      = (∫ p : ℝ × ℝ, Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G) p
            * (Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - p.1)
              * Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - p.2))) * z⁻¹
    exact (hasDerivAt_slice_fst
      (H := Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G))
      hloc δ ε hδ hε (Real.log z, θ)).comp z (Real.hasDerivAt_log (ne_of_gt hz)) |>.deriv
  -- ## Step 4: change of variables and Fubini
  have hstep : (∫ p : ℝ × ℝ, Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G) p
            * (Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - p.1)
              * Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - p.2)))
      = ∫ u : ℝ, ∫ v : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ u
          * Work.FTS.EllSol.EllPkgAux.sKerd ε v
          * Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G)
              (Real.log z - u, θ - v) := by
    have hgg : Integrable (fun q : ℝ × ℝ =>
        Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G) q
          * (Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - q.1)
            * Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - q.2))) MeasureTheory.volume := by
      have hc : Continuous (fun q : ℝ × ℝ =>
          Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - q.1)
            * Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - q.2)) :=
        ((sKerd_cont δ).comp (continuous_const.sub continuous_fst)).mul
          ((sKerd_cont ε).comp (continuous_const.sub continuous_snd))
      have hcs : HasCompactSupport (fun q : ℝ × ℝ =>
          Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - q.1)
            * Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - q.2)) := by
        refine HasCompactSupport.intro
          (K := Set.Icc (Real.log z - δ) (Real.log z + δ) ×ˢ Set.Icc (θ - ε) (θ + ε))
          (isCompact_Icc.prod isCompact_Icc) ?_
        intro q hq
        rw [Set.mem_prod, not_and_or] at hq
        rcases hq with hq | hq
        · rw [sKerd_eq_zero_of_notMem_Icc hδ hq, zero_mul]
        · rw [sKerd_eq_zero_of_notMem_Icc hε hq, mul_zero]
      have h := hloc.integrable_smul_left_of_hasCompactSupport hc hcs
      refine h.congr ?_
      filter_upwards with q
      rw [smul_eq_mul]; ring
    have hint : Integrable (fun p : ℝ × ℝ =>
        Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G) ((Real.log z, θ) - p)
          * (Work.FTS.EllSol.EllPkgAux.sKerd δ p.1
            * Work.FTS.EllSol.EllPkgAux.sKerd ε p.2)) MeasureTheory.volume := by
      have h := hgg.comp_sub_left (Real.log z, θ)
      refine h.congr ?_
      filter_upwards with q
      simp only [Prod.fst_sub, Prod.snd_sub, sub_sub_cancel]
    have hshift : (∫ p : ℝ × ℝ,
        Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G) p
          * (Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - p.1)
            * Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - p.2)))
        = ∫ p : ℝ × ℝ,
            Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G) ((Real.log z, θ) - p)
            * (Work.FTS.EllSol.EllPkgAux.sKerd δ p.1
              * Work.FTS.EllSol.EllPkgAux.sKerd ε p.2) :=
      (MeasureTheory.integral_sub_left_eq_self (μ := MeasureTheory.volume)
        (fun q : ℝ × ℝ => Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G) q
          * (Work.FTS.EllSol.EllPkgAux.sKerd δ ((Real.log z, θ).1 - q.1)
            * Work.FTS.EllSol.EllPkgAux.sKerd ε ((Real.log z, θ).2 - q.2)))
        (Real.log z, θ)).symm.trans
        (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun q => by
          simp only [Prod.fst_sub, Prod.snd_sub, sub_sub_cancel]))
    have hvol : (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
        = MeasureTheory.volume.prod MeasureTheory.volume := rfl
    rw [hshift, hvol]
    rw [MeasureTheory.integral_prod (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)
      (f := fun p : ℝ × ℝ =>
        Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G) ((Real.log z, θ) - p)
          * (Work.FTS.EllSol.EllPkgAux.sKerd δ p.1
            * Work.FTS.EllSol.EllPkgAux.sKerd ε p.2)) hint]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    dsimp only
    rw [show ((Real.log z, θ) - (u, v) : ℝ × ℝ) = (Real.log z - u, θ - v) from rfl]
    ring
  -- ## Step 5: assembly
  have hmain : Work.Spaces.Dz (Work.Spaces.pth
        (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)) z θ
      = ∫ p : ℝ × ℝ, Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G) p
            * (Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - p.1)
              * Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - p.2)) := by
    change z * deriv (fun z' : ℝ =>
        deriv (fun θ'' : ℝ => Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε z' θ'') θ) z
      = ∫ p : ℝ × ℝ, Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G) p
            * (Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - p.1)
              * Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - p.2))
    rw [houter]
    rw [← mul_assoc, mul_comm z _, mul_assoc, mul_inv_cancel₀ (ne_of_gt hz), mul_one]
  rw [hmain, hstep]

end

end Work.FTS.ClassC.UopGenAux.MollConvAux
