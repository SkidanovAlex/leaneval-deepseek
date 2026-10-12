import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Submission.Work.BoseFixR.LatGreen.LGFormDefs
import Submission.Work.BoseFixR.LatGreen.PoissonTheta
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatGreen.LGFormAux` — the heat-kernel/θ inputs of `latticeSum_eq_latGreen_form`

The periodised heat kernel `heatPeriod t u = Σ_n heatK3 t (u − n)` is the Fourier series

`heatPeriod t u = Σ_{k∈ℤ³} e^{−t‖q_k‖²} cos⟪q_k,u⟫`,   `q_k = 2πk`   (`heatPeriod_eq_tsum`),

by `PoissonTheta` in the `q_k` normalisation of `LGFormDefs`; its mean over the unit cube is `1`
(`integral_unitCell_heatPeriod`, from `Work.BoseB4.integral_unitCell_cos_lattice`), and, since
`heatPeriod t` is `ℤ³`-periodic with cell mean `1`, its integral over the ball of radius `2`
(which contains the support of the autocorrelation) is bounded uniformly in `t`
(`setIntegral_ball_heatPeriod_le` via `ball 0 2 ⊆ ⋃_{|n_i| ≤ 2} (n + unitCell)`).
-/

set_option maxHeartbeats 2000000
noncomputable section
open scoped Real BigOperators
open MeasureTheory

namespace Work.BoseFixR.LatGreen

theorem heatPeriod_eq_tsum (t : ℝ) (ht : 0 < t) (u : ℝ³) :
    heatPeriod t u = ∑' k : Fin 3 → ℤ,
      Real.exp (-t * ‖Work.BoseB4.vec k‖ ^ 2) * Real.cos (inner ℝ (Work.BoseB4.vec k) u) := by
  rw [PoissonTheta ht u]
  refine tsum_congr fun k => ?_
  rw [norm_sq_vec, inner_vec_eq]
  congr 2
  · ring

theorem heatPeriod_nonneg (t : ℝ) (ht : 0 < t) (u : ℝ³) : 0 ≤ heatPeriod t u := by
  rw [heatPeriod]
  exact tsum_nonneg fun n => heatK3_nonneg ht _

theorem measurable_heatPeriod (t : ℝ) (ht : 0 < t) : Measurable (heatPeriod t) := by
  rw [show heatPeriod t = fun u : ℝ³ => ∑' k : Fin 3 → ℤ,
      Real.exp (-t * ‖Work.BoseB4.vec k‖ ^ 2) * Real.cos (inner ℝ (Work.BoseB4.vec k) u) from
    funext fun u => heatPeriod_eq_tsum t ht u]
  refine Measurable.tsum fun k => ?_
  fun_prop

theorem heatPeriod_le_heatPeriod_zero (t : ℝ) (ht : 0 < t) (u : ℝ³) :
    heatPeriod t u ≤ heatPeriod t 0 := by
  have hsum : Summable (fun k : Fin 3 → ℤ =>
      Real.exp (-t * ‖Work.BoseB4.vec k‖ ^ 2) * Real.cos (inner ℝ (Work.BoseB4.vec k) u)) := by
    refine Summable.of_norm_bounded (summable_exp_neg_norm_vec_sq (t := t) ht) fun k => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (Real.exp_nonneg _) (Real.abs_cos_le_one _)
  have h0 : heatPeriod t 0 = ∑' k : Fin 3 → ℤ, Real.exp (-t * ‖Work.BoseB4.vec k‖ ^ 2) := by
    rw [heatPeriod_eq_tsum t ht 0]
    refine tsum_congr fun k => ?_
    have hz : inner ℝ (Work.BoseB4.vec k) (0 : ℝ³) = 0 := by simp
    rw [hz, Real.cos_zero, mul_one]
  rw [heatPeriod_eq_tsum t ht u, h0]
  exact Summable.tsum_le_tsum (fun k => mul_le_of_le_one_right (Real.exp_nonneg _) (Real.cos_le_one _))
    hsum (summable_exp_neg_norm_vec_sq (t := t) ht)

theorem summable_cos_mul_exp (t : ℝ) (ht : 0 < t) (u : ℝ³) :
    Summable (fun k : Fin 3 → ℤ =>
      Real.exp (-t * ‖Work.BoseB4.vec k‖ ^ 2) * Real.cos (inner ℝ (Work.BoseB4.vec k) u)) := by
  refine Summable.of_norm_bounded (summable_exp_neg_norm_vec_sq (t := t) ht) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (Real.exp_nonneg _) (Real.abs_cos_le_one _)

theorem heatPeriod_sub_one_eq_tsum (t : ℝ) (ht : 0 < t) (u : ℝ³) :
    heatPeriod t u - 1 = ∑' k : {k : Fin 3 → ℤ // k ≠ 0},
      Real.exp (-t * ‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2) *
        Real.cos (inner ℝ (Work.BoseB4.vec (k : Fin 3 → ℤ)) u) := by
  rw [heatPeriod_eq_tsum t ht u, (summable_cos_mul_exp t ht u).tsum_eq_add_tsum_ite 0]
  have h0 : Real.exp (-t * ‖Work.BoseB4.vec 0‖ ^ 2) *
      Real.cos (inner ℝ (Work.BoseB4.vec 0) u) = 1 := by
    have hv : Work.BoseB4.vec 0 = (0 : ℝ³) := by ext i; simp [Work.BoseB4.vec]
    rw [hv]
    simp
  rw [h0, add_sub_cancel_left]
  have hind : (fun n : Fin 3 → ℤ =>
      if n = 0 then 0 else Real.exp (-t * ‖Work.BoseB4.vec n‖ ^ 2) *
        Real.cos (inner ℝ (Work.BoseB4.vec n) u))
      = Set.indicator {k : Fin 3 → ℤ | k ≠ 0}
          (fun k => Real.exp (-t * ‖Work.BoseB4.vec k‖ ^ 2) *
            Real.cos (inner ℝ (Work.BoseB4.vec k) u)) := by
    funext n
    by_cases hn : n = 0
    · simp [Set.indicator, hn]
    · simp [Set.indicator, hn]
  rw [hind, ← tsum_subtype]
  rfl

theorem abs_heatPeriod_sub_one_le (t : ℝ) (ht : 0 < t) (u : ℝ³) :
    |heatPeriod t u - 1| ≤ ∑' k : {k : Fin 3 → ℤ // k ≠ 0},
      Real.exp (-t * ‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2) := by
  have hf : Summable (fun k : {k : Fin 3 → ℤ // k ≠ 0} =>
      Real.exp (-t * ‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2) *
        Real.cos (inner ℝ (Work.BoseB4.vec (k : Fin 3 → ℤ)) u)) :=
    (summable_cos_mul_exp t ht u).subtype _
  have hfabs : Summable (fun k : {k : Fin 3 → ℤ // k ≠ 0} =>
      ‖Real.exp (-t * ‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2) *
        Real.cos (inner ℝ (Work.BoseB4.vec (k : Fin 3 → ℤ)) u)‖) := hf.norm
  have hg : Summable (fun k : {k : Fin 3 → ℤ // k ≠ 0} =>
      Real.exp (-t * ‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2)) :=
    (summable_exp_neg_norm_vec_sq (t := t) ht).subtype _
  rw [heatPeriod_sub_one_eq_tsum t ht u]
  refine le_trans (norm_tsum_le_tsum_norm hfabs) ?_
  refine Summable.tsum_le_tsum (fun k => ?_) hfabs hg
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (Real.exp_nonneg _) (Real.abs_cos_le_one _)

theorem integral_unitCell_heatPeriod (t : ℝ) (ht : 0 < t) :
    ∫ u in Work.BoseB4.unitCell, heatPeriod t u = 1 := by
  have hfun : heatPeriod t = fun u : ℝ³ => ∑' k : Fin 3 → ℤ,
      Real.exp (-t * ‖Work.BoseB4.vec k‖ ^ 2) * Real.cos (inner ℝ (Work.BoseB4.vec k) u) :=
    funext fun u => heatPeriod_eq_tsum t ht u
  rw [hfun, integral_tsum]
  · have hterm : ∀ k : Fin 3 → ℤ,
        ∫ u in Work.BoseB4.unitCell,
            Real.exp (-t * ‖Work.BoseB4.vec k‖ ^ 2) * Real.cos (inner ℝ (Work.BoseB4.vec k) u)
          = Real.exp (-t * ‖Work.BoseB4.vec k‖ ^ 2) * (if k = 0 then 1 else 0) := by
      intro k
      rw [integral_const_mul]
      congr 1
      exact Work.BoseB4.integral_unitCell_cos_lattice k
    rw [tsum_congr hterm, tsum_eq_single 0]
    · rw [if_pos rfl, mul_one]
      have hv : Work.BoseB4.vec 0 = (0 : ℝ³) := by ext i; simp [Work.BoseB4.vec]
      rw [hv]
      simp
    · intro k hk
      rw [if_neg hk, mul_zero]
  · intro k
    exact (by fun_prop : Continuous (fun u : ℝ³ =>
      Real.exp (-t * ‖Work.BoseB4.vec k‖ ^ 2) * Real.cos (inner ℝ (Work.BoseB4.vec k) u))).aestronglyMeasurable
  · rw [← lt_top_iff_ne_top]
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun k => ?_)
      (Summable.tsum_ofReal_lt_top (summable_exp_neg_norm_vec_sq (t := t) ht))
    have hvol : (volume.restrict Work.BoseB4.unitCell) Set.univ = 1 := by
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      exact Work.BoseB4.volume_unitCell
    calc ∫⁻ u, ‖Real.exp (-t * ‖Work.BoseB4.vec k‖ ^ 2) * Real.cos (inner ℝ (Work.BoseB4.vec k) u)‖ₑ
            ∂(volume.restrict Work.BoseB4.unitCell)
        ≤ ∫⁻ u, ENNReal.ofReal (Real.exp (-t * ‖Work.BoseB4.vec k‖ ^ 2))
            ∂(volume.restrict Work.BoseB4.unitCell) := by
          refine lintegral_mono fun u => ?_
          rw [← ofReal_norm, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
          exact ENNReal.ofReal_le_ofReal
            (mul_le_of_le_one_right (Real.exp_nonneg _) (Real.abs_cos_le_one _))
      _ = ENNReal.ofReal (Real.exp (-t * ‖Work.BoseB4.vec k‖ ^ 2)) := by
          rw [lintegral_const, hvol, mul_one]

theorem measurableSet_unitCell_add (n : Fin 3 → ℤ) :
    MeasurableSet ((fun y : ℝ³ => y + latVec n) '' Work.BoseB4.unitCell) := by
  rw [Set.image_add_right]
  exact MeasurableSet.preimage
    (Work.BoseB4.isClosed_unitCell.measurableSet : MeasurableSet Work.BoseB4.unitCell)
    (measurable_add_const _)

theorem restrict_image_add_unitCell (n : Fin 3 → ℤ) :
    volume.restrict ((fun y : ℝ³ => y + latVec n) '' Work.BoseB4.unitCell)
      = Measure.map (fun y : ℝ³ => y + latVec n) (volume.restrict Work.BoseB4.unitCell) := by
  have hinj : Function.Injective (fun y : ℝ³ => y + latVec n) := fun a b h => add_right_cancel h
  have hpre : (fun y : ℝ³ => y + latVec n) ⁻¹'
      ((fun y : ℝ³ => y + latVec n) '' Work.BoseB4.unitCell) = Work.BoseB4.unitCell :=
    Set.preimage_image_eq _ hinj
  have hmap : Measure.map (fun y : ℝ³ => y + latVec n) volume = volume :=
    (measurePreserving_add_right volume (latVec n)).map_eq
  calc volume.restrict ((fun y : ℝ³ => y + latVec n) '' Work.BoseB4.unitCell)
      = (Measure.map (fun y : ℝ³ => y + latVec n) volume).restrict
          ((fun y : ℝ³ => y + latVec n) '' Work.BoseB4.unitCell) := by rw [hmap]
    _ = Measure.map (fun y : ℝ³ => y + latVec n)
          (volume.restrict ((fun y : ℝ³ => y + latVec n) ⁻¹'
            ((fun y : ℝ³ => y + latVec n) '' Work.BoseB4.unitCell))) :=
        Measure.restrict_map (measurable_add_const (latVec n)) (measurableSet_unitCell_add n)
    _ = Measure.map (fun y : ℝ³ => y + latVec n) (volume.restrict Work.BoseB4.unitCell) := by
        rw [hpre]

theorem volume_image_add_unitCell (n : Fin 3 → ℤ) :
    volume ((fun y : ℝ³ => y + latVec n) '' Work.BoseB4.unitCell) = 1 := by
  calc volume ((fun y : ℝ³ => y + latVec n) '' Work.BoseB4.unitCell)
      = (volume.restrict ((fun y : ℝ³ => y + latVec n) '' Work.BoseB4.unitCell)) Set.univ :=
        (Measure.restrict_apply_univ _).symm
    _ = (Measure.map (fun y : ℝ³ => y + latVec n) (volume.restrict Work.BoseB4.unitCell))
          Set.univ := by rw [restrict_image_add_unitCell n]
    _ = (volume.restrict Work.BoseB4.unitCell) ((fun y : ℝ³ => y + latVec n) ⁻¹' Set.univ) :=
        Measure.map_apply (measurable_add_const (latVec n)) MeasurableSet.univ
    _ = (volume.restrict Work.BoseB4.unitCell) Set.univ := by rw [Set.preimage_univ]
    _ = 1 := by rw [Measure.restrict_apply_univ, Work.BoseB4.volume_unitCell]

theorem integral_image_add_unitCell_heatPeriod (t : ℝ) (ht : 0 < t) (n : Fin 3 → ℤ) :
    ∫ u in (fun y : ℝ³ => y + latVec n) '' Work.BoseB4.unitCell, heatPeriod t u = 1 := by
  calc ∫ u in (fun y : ℝ³ => y + latVec n) '' Work.BoseB4.unitCell, heatPeriod t u
      = ∫ u, heatPeriod t u ∂(volume.restrict ((fun y : ℝ³ => y + latVec n) '' Work.BoseB4.unitCell)) :=
        rfl
    _ = ∫ u, heatPeriod t u ∂(Measure.map (fun y : ℝ³ => y + latVec n)
          (volume.restrict Work.BoseB4.unitCell)) := by rw [restrict_image_add_unitCell n]
    _ = ∫ y, heatPeriod t (y + latVec n) ∂(volume.restrict Work.BoseB4.unitCell) := by
          rw [integral_map (measurable_add_const (latVec n)).aemeasurable
            (measurable_heatPeriod t ht).aestronglyMeasurable]
    _ = ∫ y, heatPeriod t y ∂(volume.restrict Work.BoseB4.unitCell) :=
          integral_congr_ae (Filter.Eventually.of_forall fun y => heatPeriod_add_latVec t y n)
    _ = 1 := integral_unitCell_heatPeriod t ht

theorem setIntegral_ball_heatPeriod_le (t : ℝ) (ht : 0 < t) :
    ∫ u in Metric.ball (0 : ℝ³) 2, heatPeriod t u ≤ 1000 := by
  set F : Finset (Fin 3 → ℤ) := Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-2 : ℤ) 2) with hF
  set A : (Fin 3 → ℤ) → Set ℝ³ :=
    fun n => (fun y : ℝ³ => y + latVec n) '' Work.BoseB4.unitCell with hA
  have hAms : ∀ n, MeasurableSet (A n) := fun n => measurableSet_unitCell_add n
  have hvolA : ∀ n, volume (A n) = 1 := fun n => volume_image_add_unitCell n
  have hcover : Metric.ball (0 : ℝ³) 2 ⊆ ⋃ n ∈ F, A n := by
    intro u hu
    rw [Set.mem_iUnion₂]
    have hnorm : ‖u‖ < 2 := by rwa [Metric.mem_ball, dist_zero_right] at hu
    refine ⟨fun i => ⌊u i + 1 / 2⌋, ?_, ?_⟩
    · rw [hF, Fintype.mem_piFinset]
      intro i
      have hcoord : |u i| ≤ ‖u‖ := by
        have h := PiLp.norm_apply_le u i
        rwa [Real.norm_eq_abs] at h
      have h1 : (⌊u i + 1 / 2⌋ : ℝ) ≤ u i + 1 / 2 := Int.floor_le _
      have h2 : u i + 1 / 2 < (⌊u i + 1 / 2⌋ : ℝ) + 1 := Int.lt_floor_add_one _
      have hlo := (abs_le.mp hcoord).1
      have hhi := (abs_le.mp hcoord).2
      rw [Finset.mem_Icc]
      constructor
      · have h3 : (-3 : ℤ) < ⌊u i + 1 / 2⌋ := by
          exact_mod_cast (by linarith : (-3 : ℝ) < (⌊u i + 1 / 2⌋ : ℝ))
        omega
      · have h3 : ⌊u i + 1 / 2⌋ < 3 := by
          exact_mod_cast (by linarith : (⌊u i + 1 / 2⌋ : ℝ) < 3)
        omega
    · rw [hA, Set.mem_image]
      refine ⟨u - latVec (fun i => ⌊u i + 1 / 2⌋), ?_, by abel⟩
      intro i
      have h1 : (⌊u i + 1 / 2⌋ : ℝ) ≤ u i + 1 / 2 := Int.floor_le _
      have h2 : u i + 1 / 2 < (⌊u i + 1 / 2⌋ : ℝ) + 1 := Int.lt_floor_add_one _
      rw [WithLp.ofLp_sub, Pi.sub_apply, latVec_apply', abs_le]
      constructor <;> linarith
  have hAint : ∀ n ∈ F, Integrable ((A n).indicator (fun u => heatPeriod t u)) volume := by
    intro n hn
    rw [integrable_indicator_iff (hAms n)]
    haveI : IsFiniteMeasure (volume.restrict (A n)) := by
      rw [isFiniteMeasure_restrict, hvolA n]; exact ENNReal.one_ne_top
    refine Integrable.of_bound (measurable_heatPeriod t ht).aestronglyMeasurable (heatPeriod t 0) ?_
    filter_upwards with u
    rw [Real.norm_of_nonneg (heatPeriod_nonneg t ht u)]
    exact heatPeriod_le_heatPeriod_zero t ht u
  have hbdd : Integrable ((Metric.ball (0 : ℝ³) 2).indicator (fun u => heatPeriod t u)) volume := by
    rw [integrable_indicator_iff measurableSet_ball]
    haveI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : ℝ³) 2)) := by
      rw [isFiniteMeasure_restrict]
      exact measure_ball_lt_top.ne
    refine Integrable.of_bound (measurable_heatPeriod t ht).aestronglyMeasurable (heatPeriod t 0) ?_
    filter_upwards with u
    rw [Real.norm_of_nonneg (heatPeriod_nonneg t ht u)]
    exact heatPeriod_le_heatPeriod_zero t ht u
  have hpt : ∀ u, (Metric.ball (0 : ℝ³) 2).indicator (fun u => heatPeriod t u) u
      ≤ ∑ n ∈ F, (A n).indicator (fun u => heatPeriod t u) u := by
    intro u
    by_cases hu : u ∈ Metric.ball (0 : ℝ³) 2
    · rw [Set.indicator_of_mem hu]
      obtain ⟨n, hnF, hnu⟩ := Set.mem_iUnion₂.mp (hcover hu)
      have hle := Finset.single_le_sum
        (f := fun m => (A m).indicator (fun u => heatPeriod t u) u)
        (fun m _ => Set.indicator_nonneg (fun _ _ => heatPeriod_nonneg t ht _) u) hnF
      rwa [Set.indicator_of_mem hnu] at hle
    · rw [Set.indicator_of_notMem hu]
      exact Finset.sum_nonneg (fun m _ => Set.indicator_nonneg (fun _ _ => heatPeriod_nonneg t ht _) u)
  have hcard : F.card ≤ 1000 := by
    rw [hF, Fintype.card_piFinset]
    have h5 : ∀ i : Fin 3, (Finset.Icc (-2 : ℤ) 2).card = 5 := fun i => by decide
    calc ∏ i : Fin 3, (Finset.Icc (-2 : ℤ) 2).card
        = ∏ _i : Fin 3, 5 := Finset.prod_congr rfl fun i _ => h5 i
      _ = 125 := by simp
      _ ≤ 1000 := by norm_num
  calc ∫ u in Metric.ball (0 : ℝ³) 2, heatPeriod t u
      = ∫ u, (Metric.ball (0 : ℝ³) 2).indicator (fun u => heatPeriod t u) u :=
        (integral_indicator measurableSet_ball).symm
    _ ≤ ∫ u, ∑ n ∈ F, (A n).indicator (fun u => heatPeriod t u) u :=
        integral_mono hbdd (integrable_finsetSum F hAint) hpt
    _ = ∑ n ∈ F, ∫ u, (A n).indicator (fun u => heatPeriod t u) u :=
        integral_finsetSum F hAint
    _ = ∑ n ∈ F, ∫ u in A n, heatPeriod t u := by
        refine Finset.sum_congr rfl fun n _ => ?_
        exact integral_indicator (hAms n)
    _ = ∑ n ∈ F, 1 := Finset.sum_congr rfl fun n _ => integral_image_add_unitCell_heatPeriod t ht n
    _ = (F.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ 1000 := by exact_mod_cast hcard

theorem setIntegral_ball3_heatPeriod_le (t : ℝ) (ht : 0 < t) :
    ∫ u in Metric.ball (0 : ℝ³) 3, heatPeriod t u ≤ 1000 := by
  set F : Finset (Fin 3 → ℤ) := Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-3 : ℤ) 3) with hF
  set A : (Fin 3 → ℤ) → Set ℝ³ :=
    fun n => (fun y : ℝ³ => y + latVec n) '' Work.BoseB4.unitCell with hA
  have hAms : ∀ n, MeasurableSet (A n) := fun n => measurableSet_unitCell_add n
  have hvolA : ∀ n, volume (A n) = 1 := fun n => volume_image_add_unitCell n
  have hcover : Metric.ball (0 : ℝ³) 3 ⊆ ⋃ n ∈ F, A n := by
    intro u hu
    rw [Set.mem_iUnion₂]
    have hnorm : ‖u‖ < 3 := by rwa [Metric.mem_ball, dist_zero_right] at hu
    refine ⟨fun i => ⌊u i + 1 / 2⌋, ?_, ?_⟩
    · rw [hF, Fintype.mem_piFinset]
      intro i
      have hcoord : |u i| ≤ ‖u‖ := by
        have h := PiLp.norm_apply_le u i
        rwa [Real.norm_eq_abs] at h
      have h1 : (⌊u i + 1 / 2⌋ : ℝ) ≤ u i + 1 / 2 := Int.floor_le _
      have h2 : u i + 1 / 2 < (⌊u i + 1 / 2⌋ : ℝ) + 1 := Int.lt_floor_add_one _
      have hlo := (abs_le.mp hcoord).1
      have hhi := (abs_le.mp hcoord).2
      rw [Finset.mem_Icc]
      constructor
      · have h3 : (-4 : ℤ) < ⌊u i + 1 / 2⌋ := by
          exact_mod_cast (by linarith : (-4 : ℝ) < (⌊u i + 1 / 2⌋ : ℝ))
        omega
      · have h3 : ⌊u i + 1 / 2⌋ < 4 := by
          exact_mod_cast (by linarith : (⌊u i + 1 / 2⌋ : ℝ) < 4)
        omega
    · rw [hA, Set.mem_image]
      refine ⟨u - latVec (fun i => ⌊u i + 1 / 2⌋), ?_, by abel⟩
      intro i
      have h1 : (⌊u i + 1 / 2⌋ : ℝ) ≤ u i + 1 / 2 := Int.floor_le _
      have h2 : u i + 1 / 2 < (⌊u i + 1 / 2⌋ : ℝ) + 1 := Int.lt_floor_add_one _
      rw [WithLp.ofLp_sub, Pi.sub_apply, latVec_apply', abs_le]
      constructor <;> linarith
  have hAint : ∀ n ∈ F, Integrable ((A n).indicator (fun u => heatPeriod t u)) volume := by
    intro n hn
    rw [integrable_indicator_iff (hAms n)]
    haveI : IsFiniteMeasure (volume.restrict (A n)) := by
      rw [isFiniteMeasure_restrict, hvolA n]; exact ENNReal.one_ne_top
    refine Integrable.of_bound (measurable_heatPeriod t ht).aestronglyMeasurable (heatPeriod t 0) ?_
    filter_upwards with u
    rw [Real.norm_of_nonneg (heatPeriod_nonneg t ht u)]
    exact heatPeriod_le_heatPeriod_zero t ht u
  have hbdd : Integrable ((Metric.ball (0 : ℝ³) 3).indicator (fun u => heatPeriod t u)) volume := by
    rw [integrable_indicator_iff measurableSet_ball]
    haveI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : ℝ³) 3)) := by
      rw [isFiniteMeasure_restrict]
      exact measure_ball_lt_top.ne
    refine Integrable.of_bound (measurable_heatPeriod t ht).aestronglyMeasurable (heatPeriod t 0) ?_
    filter_upwards with u
    rw [Real.norm_of_nonneg (heatPeriod_nonneg t ht u)]
    exact heatPeriod_le_heatPeriod_zero t ht u
  have hpt : ∀ u, (Metric.ball (0 : ℝ³) 3).indicator (fun u => heatPeriod t u) u
      ≤ ∑ n ∈ F, (A n).indicator (fun u => heatPeriod t u) u := by
    intro u
    by_cases hu : u ∈ Metric.ball (0 : ℝ³) 3
    · rw [Set.indicator_of_mem hu]
      obtain ⟨n, hnF, hnu⟩ := Set.mem_iUnion₂.mp (hcover hu)
      have hle := Finset.single_le_sum
        (f := fun m => (A m).indicator (fun u => heatPeriod t u) u)
        (fun m _ => Set.indicator_nonneg (fun _ _ => heatPeriod_nonneg t ht _) u) hnF
      rwa [Set.indicator_of_mem hnu] at hle
    · rw [Set.indicator_of_notMem hu]
      exact Finset.sum_nonneg (fun m _ => Set.indicator_nonneg (fun _ _ => heatPeriod_nonneg t ht _) u)
  have hcard : F.card ≤ 1000 := by
    rw [hF, Fintype.card_piFinset]
    have h5 : ∀ i : Fin 3, (Finset.Icc (-3 : ℤ) 3).card = 7 := fun i => by decide
    calc ∏ i : Fin 3, (Finset.Icc (-3 : ℤ) 3).card
        = ∏ _i : Fin 3, 7 := Finset.prod_congr rfl fun i _ => h5 i
      _ = 343 := by simp
      _ ≤ 1000 := by norm_num
  calc ∫ u in Metric.ball (0 : ℝ³) 3, heatPeriod t u
      = ∫ u, (Metric.ball (0 : ℝ³) 3).indicator (fun u => heatPeriod t u) u :=
        (integral_indicator measurableSet_ball).symm
    _ ≤ ∫ u, ∑ n ∈ F, (A n).indicator (fun u => heatPeriod t u) u :=
        integral_mono hbdd (integrable_finsetSum F hAint) hpt
    _ = ∑ n ∈ F, ∫ u, (A n).indicator (fun u => heatPeriod t u) u :=
        integral_finsetSum F hAint
    _ = ∑ n ∈ F, ∫ u in A n, heatPeriod t u := by
        refine Finset.sum_congr rfl fun n _ => ?_
        exact integral_indicator (hAms n)
    _ = ∑ n ∈ F, 1 := Finset.sum_congr rfl fun n _ => integral_image_add_unitCell_heatPeriod t ht n
    _ = (F.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ 1000 := by exact_mod_cast hcard

theorem integral_abs_autoCorr_mul_heatPeriod_le {V : ℝ³ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hInt : MeasureTheory.Integrable (autoCorr V))
    (hsup : ∀ u : ℝ³, |autoCorr V u| ≤ M)
    (hsupp : ∀ u : ℝ³, 2 < ‖u‖ → autoCorr V u = 0)
    {t : ℝ} (ht : 0 < t) :
    ∫ u, ‖autoCorr V u * (heatPeriod t u - 1)‖ ≤ M * 1000 + ∫ u, ‖autoCorr V u‖ := by
  have hnormeq : ∀ u : ℝ³, ‖autoCorr V u * (heatPeriod t u - 1)‖
      = |autoCorr V u| * |heatPeriod t u - 1| := by
    intro u; simp only [Real.norm_eq_abs, abs_mul]
  have hInt_p1 : MeasureTheory.Integrable (fun u : ℝ³ => (heatPeriod t u + 1) * |autoCorr V u|) volume := by
    refine (hInt.abs).bdd_mul (c := heatPeriod t 0 + 1) (f := fun u : ℝ³ => heatPeriod t u + 1) ?_ ?_
    · exact ((measurable_heatPeriod t ht).add measurable_const).aestronglyMeasurable
    · filter_upwards with u
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [heatPeriod_nonneg t ht u])]
      linarith [heatPeriod_le_heatPeriod_zero t ht u]
  have hInt_rhs : MeasureTheory.Integrable (fun u : ℝ³ => |autoCorr V u| * (heatPeriod t u + 1)) volume :=
    hInt_p1.congr (Filter.Eventually.of_forall fun u => by ring)
  have hInt_sep' : MeasureTheory.Integrable (fun u : ℝ³ => heatPeriod t u * |autoCorr V u|) volume := by
    refine (hInt.abs).bdd_mul (c := heatPeriod t 0) (f := fun u : ℝ³ => heatPeriod t u) ?_ ?_
    · exact (measurable_heatPeriod t ht).aestronglyMeasurable
    · filter_upwards with u
      rw [Real.norm_eq_abs, abs_of_nonneg (heatPeriod_nonneg t ht u)]
      exact heatPeriod_le_heatPeriod_zero t ht u
  have hInt_sep : MeasureTheory.Integrable (fun u : ℝ³ => |autoCorr V u| * heatPeriod t u) volume :=
    hInt_sep'.congr (Filter.Eventually.of_forall fun u => by ring)
  have hInt_ind : MeasureTheory.Integrable
      (fun u : ℝ³ => M * (Metric.ball (0 : ℝ³) 3).indicator (fun u => heatPeriod t u) u) volume := by
    refine MeasureTheory.Integrable.const_mul ?_ M
    rw [MeasureTheory.integrable_indicator_iff measurableSet_ball]
    haveI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : ℝ³) 3)) := by
      rw [isFiniteMeasure_restrict]
      exact measure_ball_lt_top.ne
    refine MeasureTheory.Integrable.of_bound (measurable_heatPeriod t ht).aestronglyMeasurable
      (heatPeriod t 0) ?_
    filter_upwards with u
    rw [Real.norm_of_nonneg (heatPeriod_nonneg t ht u)]
    exact heatPeriod_le_heatPeriod_zero t ht u
  have hpt1 : ∀ u : ℝ³, ‖autoCorr V u * (heatPeriod t u - 1)‖
      ≤ |autoCorr V u| * (heatPeriod t u + 1) := by
    intro u
    rw [hnormeq]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_sub_le_iff]
    exact ⟨by linarith [heatPeriod_nonneg t ht u], by linarith [heatPeriod_nonneg t ht u]⟩
  have hpt2 : ∀ u : ℝ³, |autoCorr V u| * heatPeriod t u
      ≤ M * (Metric.ball (0 : ℝ³) 3).indicator (fun u => heatPeriod t u) u := by
    intro u
    by_cases hu : u ∈ Metric.ball (0 : ℝ³) 3
    · rw [Set.indicator_of_mem hu]
      exact mul_le_mul_of_nonneg_right (hsup u) (heatPeriod_nonneg t ht u)
    · rw [Set.indicator_of_notMem hu]
      have hnot : ¬ ‖u‖ < 3 := by
        intro hc
        exact hu (by simpa [Metric.mem_ball, dist_zero_right] using hc)
      have hz : autoCorr V u = 0 := hsupp u (by linarith [not_lt.mp hnot])
      rw [hz, abs_zero, zero_mul, mul_zero]
  have hInt_lhs : MeasureTheory.Integrable
      (fun u : ℝ³ => ‖autoCorr V u * (heatPeriod t u - 1)‖) volume :=
    (hInt_rhs.mono' (hInt.aestronglyMeasurable.mul
      ((measurable_heatPeriod t ht).sub measurable_const).aestronglyMeasurable)
        (Filter.Eventually.of_forall hpt1)).norm
  calc ∫ u, ‖autoCorr V u * (heatPeriod t u - 1)‖
      ≤ ∫ u, |autoCorr V u| * (heatPeriod t u + 1) :=
        integral_mono hInt_lhs hInt_rhs hpt1
    _ = ∫ u, (|autoCorr V u| * heatPeriod t u + |autoCorr V u|) :=
        integral_congr_ae (Filter.Eventually.of_forall fun u => by ring)
    _ = (∫ u, |autoCorr V u| * heatPeriod t u) + (∫ u, |autoCorr V u|) := by
        simpa using integral_add hInt_sep hInt.abs
    _ ≤ M * (∫ u in Metric.ball (0 : ℝ³) 3, heatPeriod t u) + ∫ u, ‖autoCorr V u‖ := by
        refine add_le_add ?_ le_rfl
        calc ∫ u, |autoCorr V u| * heatPeriod t u
            ≤ ∫ u, M * (Metric.ball (0 : ℝ³) 3).indicator (fun u => heatPeriod t u) u :=
              integral_mono hInt_sep hInt_ind hpt2
          _ = M * ∫ u in Metric.ball (0 : ℝ³) 3, heatPeriod t u := by
              rw [integral_const_mul, integral_indicator measurableSet_ball]
    _ ≤ M * 1000 + ∫ u, ‖autoCorr V u‖ := by
        refine add_le_add ?_ le_rfl
        exact mul_le_mul_of_nonneg_left (setIntegral_ball3_heatPeriod_le t ht) hM

theorem measurable_heatPeriod_pair :
    Measurable (fun p : ℝ × ℝ³ => heatPeriod p.1 p.2) := by
  rw [show (fun p : ℝ × ℝ³ => heatPeriod p.1 p.2)
      = fun p : ℝ × ℝ³ => ∑' n : Fin 3 → ℤ, heatK3 p.1 (p.2 - latVec n) from by
    funext p
    rw [heatPeriod]]
  refine Measurable.tsum fun n => ?_
  unfold heatK3
  fun_prop

theorem abs_heatPeriod_sub_one_le_exp {t : ℝ} (ht : 1 ≤ t) (u : ℝ³) :
    |heatPeriod t u - 1| ≤ (∑' k : {k : Fin 3 → ℤ // k ≠ 0},
        Real.exp (-(‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2))) * Real.exp 1 * Real.exp (-t) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hS : Summable (fun k : {k : Fin 3 → ℤ // k ≠ 0} =>
      Real.exp (-(‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2))) := by
    refine ((summable_exp_neg_norm_vec_sq (t := (1 : ℝ)) one_pos).subtype _).congr fun k => ?_
    simp only [Function.comp_apply, neg_mul, one_mul]
  have hS2 : Summable (fun k : {k : Fin 3 → ℤ // k ≠ 0} =>
      Real.exp (-(‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2)) * Real.exp (-(t - 1))) :=
    hS.mul_right _
  have hlam : ∀ k : {k : Fin 3 → ℤ // k ≠ 0}, (1 : ℝ) ≤ ‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2 := by
    intro k
    have h1 : (1 : ℝ) ≤ ‖latVec (k : Fin 3 → ℤ)‖ ^ 2 := by
      rw [norm_sq_latVec]
      obtain ⟨i, hi⟩ : ∃ i : Fin 3, (k : Fin 3 → ℤ) i ≠ 0 := by
        by_contra h
        exact k.2 (funext fun i => by simpa using not_exists.mp h i)
      have h2 : (1 : ℝ) ≤ |(((k : Fin 3 → ℤ) i : ℤ) : ℝ)| := by
        exact_mod_cast (Int.one_le_abs hi)
      have h3 : (1 : ℝ) ≤ ((((k : Fin 3 → ℤ) i : ℤ) : ℝ)) ^ 2 := by
        have hm := one_le_mul_of_one_le_of_one_le h2 h2
        rwa [← sq, sq_abs] at hm
      exact le_trans h3 (Finset.single_le_sum
        (f := fun j : Fin 3 => (((k : Fin 3 → ℤ) j : ℤ) : ℝ) ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i))
    rw [norm_sq_vec]
    nlinarith [h1, Real.pi_gt_three]
  have hterm : ∀ k : {k : Fin 3 → ℤ // k ≠ 0},
      Real.exp (-t * ‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2)
        ≤ Real.exp (-(‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2)) * Real.exp (-(t - 1)) := by
    intro k
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hlam k, ht]
  calc |heatPeriod t u - 1|
      ≤ ∑' k : {k : Fin 3 → ℤ // k ≠ 0},
          Real.exp (-t * ‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2) :=
        abs_heatPeriod_sub_one_le t ht0 u
    _ ≤ ∑' k : {k : Fin 3 → ℤ // k ≠ 0},
          Real.exp (-(‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2)) * Real.exp (-(t - 1)) := by
        refine Summable.tsum_le_tsum hterm ?_ hS2
        exact (summable_exp_neg_norm_vec_sq (t := t) ht0).subtype _
    _ = (∑' k : {k : Fin 3 → ℤ // k ≠ 0},
          Real.exp (-(‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2))) * Real.exp (-(t - 1)) :=
        tsum_mul_right
    _ = (∑' k : {k : Fin 3 → ℤ // k ≠ 0},
          Real.exp (-(‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2))) * Real.exp 1 * Real.exp (-t) := by
        rw [show -(t - 1) = 1 + -t by ring, Real.exp_add]
        ring

end Work.BoseFixR.LatGreen
