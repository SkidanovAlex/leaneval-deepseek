import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.EllipticEst.remov.coerc

/-- Cauchy–Schwarz for interval integrals of a real function: if `g` is a.e. strongly
measurable and `g ^ 2` is integrable on `Ioc a b` (with `a ≤ b`) then
`∫ x in a..b, |g x| ≤ sqrt (b - a) * sqrt (∫ x in a..b, g x ^ 2)`. -/
theorem intervalIntegral_abs_le_sqrt_mul_sqrt {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hmeas : AEStronglyMeasurable g (volume.restrict (Set.Ioc a b)))
    (hint : IntegrableOn (fun x => g x ^ 2) (Set.Ioc a b)) :
    (∫ x in a..b, |g x|) ≤ Real.sqrt (b - a) * Real.sqrt (∫ x in a..b, g x ^ 2) := by
  have hfin : IsFiniteMeasure (volume.restrict (Set.Ioc a b)) := by
    rw [isFiniteMeasure_restrict, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top.ne
  have habs_meas : AEStronglyMeasurable (fun x => |g x|) (volume.restrict (Set.Ioc a b)) := by
    simpa [Real.norm_eq_abs] using hmeas.norm
  have hm1 : MemLp (fun x => |g x|) (ENNReal.ofReal 2) (volume.restrict (Set.Ioc a b)) := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num,
      memLp_two_iff_integrable_sq habs_meas]
    exact hint.congr (Eventually.of_forall fun x => (sq_abs (g x)).symm)
  have hm2 : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2) (volume.restrict (Set.Ioc a b)) := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num,
      memLp_two_iff_integrable_sq aestronglyMeasurable_const]
    rw [integrable_const_iff]
    exact Or.inr hfin
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict (Set.Ioc a b)) hpq
    (f := fun x => |g x|) (g := fun _ : ℝ => (1 : ℝ))
    (Eventually.of_forall fun x => abs_nonneg (g x))
    (Eventually.of_forall fun _ => zero_le_one) hm1 hm2
  have hL1 : (∫ x in a..b, |g x|) = ∫ x in Set.Ioc a b, |g x| * (1 : ℝ) := by
    rw [intervalIntegral.integral_of_le hab]
    simp only [mul_one]
  have hR1 : (∫ x in a..b, g x ^ 2) = ∫ x in Set.Ioc a b, |g x| ^ (2 : ℝ) := by
    rw [intervalIntegral.integral_of_le hab]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show g x ^ 2 = |g x| ^ (2 : ℝ)
    rw [Real.rpow_two, sq_abs]
  have hR2 : b - a = ∫ x in Set.Ioc a b, (1 : ℝ) ^ (2 : ℝ) := by
    rw [← intervalIntegral.integral_of_le hab]
    have : (∫ x in a..b, (1 : ℝ) ^ (2 : ℝ)) = ∫ x in a..b, (1 : ℝ) :=
      intervalIntegral.integral_congr fun x _ => by simp
    rw [this, intervalIntegral.integral_const]
    simp
  have hRHS : Real.sqrt (b - a) * Real.sqrt (∫ x in a..b, g x ^ 2) =
      (∫ x in Set.Ioc a b, |g x| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        (∫ x in Set.Ioc a b, (1 : ℝ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, hR2, hR1]
    exact mul_comm _ _
  calc (∫ x in a..b, |g x|) ≤ ∫ x in Set.Ioc a b, |g x| * (1 : ℝ) := le_of_eq hL1
    _ ≤ (∫ x in Set.Ioc a b, |g x| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∫ x in Set.Ioc a b, (1 : ℝ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hH
    _ = Real.sqrt (b - a) * Real.sqrt (∫ x in a..b, g x ^ 2) := hRHS.symm

/-- If a real function has a Hölder-`1/2` modulus on `(a, b)` then it is Cauchy along any
filter that sits in `(a, b)` and is eventually confined to sets of arbitrarily small diameter;
in particular along `nhdsWithin a (Ioi a)` and along `nhdsWithin b (Iio b)`. -/
theorem cauchy_map_of_modulus {u : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K) {l : Filter ℝ} [NeBot l]
    {a b : ℝ} (hab : a < b)
    (hV : ∀ δ : ℝ, 0 < δ → δ ≤ b - a → ∃ V ∈ l, V ⊆ Set.Ioo a b ∧
      ∀ x ∈ V, ∀ y ∈ V, |x - y| < δ)
    (hmod : ∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Ioo a b,
      dist (u x) (u y) ≤ K * Real.sqrt |x - y|) :
    Cauchy (map u l) := by
  rw [cauchy_map_iff', tendsto_def]
  intro U hU
  rw [Metric.mem_uniformity_dist] at hU
  obtain ⟨ε, hε, hεU⟩ := hU
  have hK1 : 0 < K + 1 := by linarith
  have hδpos : 0 < min (b - a) (((K + 1)⁻¹ * ε) ^ 2) :=
    lt_min (by linarith) (by positivity)
  obtain ⟨V, hVl, hVsub, hVδ⟩ := hV _ hδpos (min_le_left _ _)
  refine mem_of_superset (prod_mem_prod hVl hVl) fun p hp => ?_
  obtain ⟨hx, hy⟩ := hp
  show (u p.1, u p.2) ∈ U
  have hkey : K * Real.sqrt |p.1 - p.2| < ε := by
    have hsle : Real.sqrt |p.1 - p.2| ≤ (K + 1)⁻¹ * ε := by
      have h1 : Real.sqrt |p.1 - p.2| ≤ Real.sqrt (((K + 1)⁻¹ * ε) ^ 2) :=
        Real.sqrt_le_sqrt (le_of_lt (lt_of_lt_of_le (hVδ _ hx _ hy) (min_le_right _ _)))
      rwa [Real.sqrt_sq (by positivity)] at h1
    rcases eq_or_lt_of_le (Real.sqrt_nonneg |p.1 - p.2|) with h | h
    · rw [← h, mul_zero]; exact hε
    · have h2 : K * Real.sqrt |p.1 - p.2| < (K + 1) * Real.sqrt |p.1 - p.2| := by nlinarith
      have h3 : (K + 1) * Real.sqrt |p.1 - p.2| ≤ (K + 1) * ((K + 1)⁻¹ * ε) :=
        mul_le_mul_of_nonneg_left hsle (by linarith)
      have h4 : (K + 1) * ((K + 1)⁻¹ * ε) = ε := by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hK1), one_mul]
      linarith
  exact hεU (lt_of_le_of_lt (hmod p.1 (hVsub hx) p.2 (hVsub hy)) hkey)

theorem tendsTo_atEnds_of_integrableOn_sq_deriv {u : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 L))
    (h1 : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) (Set.Icc 0 L)) :
    (∃ α : ℝ, Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds α)) ∧
      (∃ ν : ℝ, Filter.Tendsto u (nhdsWithin L (Set.Iio L)) (nhds ν)) := by
  set C : ℝ := ∫ x in (0 : ℝ)..L, (deriv u x) ^ 2 with hC
  have hcont : ContinuousOn (deriv u) (Set.Ioo 0 L) :=
    hu.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hdiff : DifferentiableOn ℝ u (Set.Ioo 0 L) := hu.differentiableOn (by norm_num)
  have hfull : IntervalIntegrable (fun x => (deriv u x) ^ 2) volume 0 L := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (le_of_lt hL)]
    exact h1.mono_set fun t ht => ⟨ht.1.le, ht.2⟩
  -- the analytic bound: `u` is Hölder-`1/2` with constant `sqrt C` on `(0, L)`
  have key : ∀ x ∈ Set.Ioo 0 L, ∀ y ∈ Set.Ioo 0 L, x ≤ y →
      dist (u x) (u y) ≤ Real.sqrt C * Real.sqrt |x - y| := by
    intro x hx y hy hxy
    have hsub_xy : Set.Icc x y ⊆ Set.Ioo 0 L :=
      fun t ht => ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hy.2⟩
    have hcont_xy : ContinuousOn (deriv u) (Set.uIcc x y) := by
      rw [Set.uIcc_of_le hxy]
      exact hcont.mono hsub_xy
    have hint_deriv : IntervalIntegrable (deriv u) volume x y := hcont_xy.intervalIntegrable
    have hdiff_xy : ∀ t ∈ Set.uIcc x y, DifferentiableAt ℝ u t := by
      intro t ht
      rw [Set.uIcc_of_le hxy] at ht
      exact hdiff.differentiableAt (isOpen_Ioo.mem_nhds (hsub_xy ht))
    have hftc : (∫ t in x..y, deriv u t) = u y - u x :=
      intervalIntegral.integral_deriv_eq_sub hdiff_xy hint_deriv
    have hstep1 : |u x - u y| ≤ ∫ t in x..y, |deriv u t| := by
      have h := intervalIntegral.norm_integral_le_integral_norm (f := deriv u) (μ := volume) hxy
      rw [hftc] at h
      simpa [Real.norm_eq_abs, abs_sub_comm] using h
    have hmeas : AEStronglyMeasurable (deriv u) (volume.restrict (Set.Ioc x y)) := by
      refine (hcont.mono ?_).aestronglyMeasurable measurableSet_Ioc
      intro t ht
      exact ⟨lt_of_lt_of_le hx.1 ht.1.le, lt_of_le_of_lt ht.2 hy.2⟩
    have hint_sq : IntegrableOn (fun t => (deriv u t) ^ 2) (Set.Ioc x y) :=
      h1.mono_set fun t ht => ⟨le_of_lt (lt_of_lt_of_le hx.1 ht.1.le), le_trans ht.2 hy.2.le⟩
    have hCS := intervalIntegral_abs_le_sqrt_mul_sqrt hxy hmeas hint_sq
    have hcmp : (∫ t in x..y, (deriv u t) ^ 2) ≤ C := by
      rw [hC]
      exact intervalIntegral.integral_mono_interval (f := fun t => (deriv u t) ^ 2)
        (c := 0) (d := L) (le_of_lt hx.1) hxy (le_of_lt hy.2)
        (Eventually.of_forall fun t => sq_nonneg _) hfull
    calc dist (u x) (u y) = |u x - u y| := Real.dist_eq _ _
      _ ≤ ∫ t in x..y, |deriv u t| := hstep1
      _ ≤ Real.sqrt (y - x) * Real.sqrt (∫ t in x..y, (deriv u t) ^ 2) := hCS
      _ ≤ Real.sqrt (y - x) * Real.sqrt C :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcmp) (Real.sqrt_nonneg _)
      _ = Real.sqrt C * Real.sqrt |x - y| := by
            rw [abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub]
            ring
  have hmod : ∀ x ∈ Set.Ioo 0 L, ∀ y ∈ Set.Ioo 0 L,
      dist (u x) (u y) ≤ Real.sqrt C * Real.sqrt |x - y| := by
    intro x hx y hy
    rcases le_total x y with hxy | hxy
    · exact key x hx y hy hxy
    · rw [dist_comm, abs_sub_comm]
      exact key y hy x hx hxy
  -- the two endpoint filters
  have hV0 : ∀ δ : ℝ, 0 < δ → δ ≤ L - 0 → ∃ V ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0),
      V ⊆ Set.Ioo 0 L ∧ ∀ x ∈ V, ∀ y ∈ V, |x - y| < δ := by
    intro δ hδ hδL
    refine ⟨Set.Ioo 0 δ, ?_, ?_, ?_⟩
    · have hmem : Set.Iio δ ∩ Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
        Filter.inter_mem (nhdsWithin_le_nhds (Iio_mem_nhds hδ)) self_mem_nhdsWithin
      exact mem_of_superset hmem fun x hx => ⟨hx.2, hx.1⟩
    · intro x hx
      exact ⟨hx.1, lt_of_lt_of_le hx.2 (by linarith)⟩
    · intro x hx y hy
      rw [abs_sub_lt_iff]
      exact ⟨by linarith [hx.2, hy.1], by linarith [hy.2, hx.1]⟩
  have hV1 : ∀ δ : ℝ, 0 < δ → δ ≤ L - 0 → ∃ V ∈ nhdsWithin L (Set.Iio L),
      V ⊆ Set.Ioo 0 L ∧ ∀ x ∈ V, ∀ y ∈ V, |x - y| < δ := by
    intro δ hδ hδL
    refine ⟨Set.Ioo (L - δ) L, ?_, ?_, ?_⟩
    · have hmem : Set.Ioi (L - δ) ∩ Set.Iio L ∈ nhdsWithin L (Set.Iio L) :=
        Filter.inter_mem (nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith))) self_mem_nhdsWithin
      exact mem_of_superset hmem fun x hx => ⟨hx.1, hx.2⟩
    · intro x hx
      exact ⟨by linarith [hx.1, hδL], hx.2⟩
    · intro x hx y hy
      rw [abs_sub_lt_iff]
      exact ⟨by linarith [hx.2, hy.1], by linarith [hx.1, hy.2]⟩
  constructor
  · have hcauchy : Cauchy (map u (nhdsWithin (0 : ℝ) (Set.Ioi 0))) :=
      cauchy_map_of_modulus (Real.sqrt_nonneg C) (l := nhdsWithin (0 : ℝ) (Set.Ioi 0))
        hL hV0 hmod
    obtain ⟨α, hα⟩ := CompleteSpace.complete hcauchy
    exact ⟨α, hα⟩
  · have hcauchy : Cauchy (map u (nhdsWithin L (Set.Iio L))) :=
      cauchy_map_of_modulus (Real.sqrt_nonneg C) (l := nhdsWithin L (Set.Iio L))
        hL hV1 hmod
    obtain ⟨ν, hν⟩ := CompleteSpace.complete hcauchy
    exact ⟨ν, hν⟩

end Work.FTS.EllipticEst.remov.coerc
