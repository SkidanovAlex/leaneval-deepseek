import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

namespace Commons.Analysis.Calculus

open Filter MeasureTheory
open scoped Topology Interval

lemma intervalIntegral_hasDerivAt_fixed_upper_of_continuous
    {F F' : ℝ → ℝ → ℝ} {a b x₀ : ℝ}
    (hF_cont : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (hF'_cont : Continuous (fun p : ℝ × ℝ => F' p.1 p.2))
    (hF'_isDeriv : ∀ u t : ℝ, HasDerivAt (fun v : ℝ => F v t) (F' u t) u) :
    HasDerivAt (fun x : ℝ => ∫ t in a..b, F x t) (∫ t in a..b, F' x₀ t) x₀ := by
  let s : Set ℝ := Metric.ball x₀ 1
  have hs : s ∈ 𝓝 x₀ := by
    exact Metric.ball_mem_nhds x₀ zero_lt_one
  have hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) (volume.restrict (Ι a b)) := by
    filter_upwards with x
    have hcont : Continuous (fun t : ℝ => F x t) := by
      exact hF_cont.comp ((continuous_const.prodMk continuous_id) : Continuous (fun t : ℝ => (x, t)))
    exact hcont.aestronglyMeasurable
  have hF_int : IntervalIntegrable (F x₀) volume a b := by
    have hcont : Continuous (fun t : ℝ => F x₀ t) := by
      exact hF_cont.comp ((continuous_const.prodMk continuous_id) : Continuous (fun t : ℝ => (x₀, t)))
    exact hcont.intervalIntegrable _ _
  have hF'_meas : AEStronglyMeasurable (F' x₀) (volume.restrict (Ι a b)) := by
    have hcont : Continuous (fun t : ℝ => F' x₀ t) := by
      exact hF'_cont.comp ((continuous_const.prodMk continuous_id) : Continuous (fun t : ℝ => (x₀, t)))
    exact hcont.aestronglyMeasurable
  have hK : IsCompact ((Metric.closedBall x₀ 1) ×ˢ ([[a, b]] : Set ℝ)) :=
    (ProperSpace.isCompact_closedBall x₀ 1).prod isCompact_uIcc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (show ContinuousOn (fun p : ℝ × ℝ => ‖F' p.1 p.2‖) ((Metric.closedBall x₀ 1) ×ˢ ([[a, b]] : Set ℝ)) by
      exact (continuous_norm.comp hF'_cont).continuousOn)
  let bound : ℝ → ℝ := fun _ => M
  have h_bound : ∀ᵐ t ∂volume, t ∈ Ι a b → ∀ x ∈ s, ‖F' x t‖ ≤ bound t := by
    filter_upwards with t ht x hx
    have hx_closed : x ∈ Metric.closedBall x₀ 1 := Metric.ball_subset_closedBall hx
    have ht_closed : t ∈ ([[a, b]] : Set ℝ) := Set.uIoc_subset_uIcc ht
    have hpt : (x, t) ∈ (Metric.closedBall x₀ 1) ×ˢ ([[a, b]] : Set ℝ) := by
      exact ⟨hx_closed, ht_closed⟩
    simpa [bound] using hM (x, t) hpt
  have bound_int : IntervalIntegrable bound volume a b := by
    simpa [bound] using (intervalIntegrable_const (μ := volume) (c := M) : IntervalIntegrable (fun _ : ℝ => M) volume a b)
  have h_diff : ∀ᵐ t ∂volume, t ∈ Ι a b → ∀ x ∈ s, HasDerivAt (fun v : ℝ => F v t) (F' x t) x := by
    filter_upwards with t ht x hx
    exact hF'_isDeriv x t
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (μ := volume) (E := ℝ) (F := F) (F' := F') (x₀ := x₀) (s := s)
    (a := a) (b := b) (bound := bound) hs hF_meas hF_int hF'_meas h_bound bound_int h_diff
  exact h.2

lemma intervalIntegral_hasFDerivAt_upper_continuous
    {F : ℝ → ℝ → ℝ} {x₀ b₀ : ℝ}
    (hF_cont : Continuous (fun p : ℝ × ℝ => F p.1 p.2)) :
    HasFDerivAt (fun p : ℝ × ℝ => ∫ t in b₀..p.2, F p.1 t)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (F x₀ b₀)) (x₀, b₀) := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simp only [Prod.fst_add, Prod.snd_add]
  have hnum : (fun h : ℝ × ℝ =>
      (∫ t in b₀..(b₀ + h.2), F (x₀ + h.1) t) - (∫ t in b₀..b₀, F x₀ t) -
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (F x₀ b₀)) h)
      = fun h : ℝ × ℝ => ∫ t in b₀..(b₀ + h.2), (F (x₀ + h.1) t - F x₀ b₀) := by
    ext h
    simp only [ContinuousLinearMap.coe_snd', ContinuousLinearMap.smulRight_apply]
    simp only [smul_eq_mul]
    rw [intervalIntegral.integral_same]
    have hconst : h.2 * F x₀ b₀ = (b₀ + h.2 - b₀) • F x₀ b₀ := by simp
    rw [hconst, ← intervalIntegral.integral_const]
    ring_nf
    rw [← intervalIntegral.integral_sub]
    · have hprod : Continuous (fun t : ℝ => (x₀ + h.1, t)) :=
        continuous_const.prodMk continuous_id
      exact (hF_cont.comp hprod).intervalIntegrable _ _
    · exact intervalIntegrable_const (μ := volume) (c := F x₀ b₀)
  rw [hnum]
  refine Asymptotics.IsLittleO.of_bound ?_
  intro ε hε
  have hcont : ContinuousAt (fun p : ℝ × ℝ => F p.1 p.2) (x₀, b₀) := hF_cont.continuousAt
  rcases Metric.continuousAt_iff.mp hcont ε hε with ⟨δ, hδpos, hδ⟩
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ × ℝ) hδpos] with h hh
  have hnorm : ‖h‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hh
  have hmax : max |h.1| |h.2| < δ := by
    simpa [Prod.norm_def, Real.norm_eq_abs] using hnorm
  have h1 : |h.1| < δ := (max_lt_iff.mp hmax).1
  have h2 : |h.2| < δ := (max_lt_iff.mp hmax).2
  have hnorm_le : |h.2| ≤ ‖h‖ := by
    rw [Prod.norm_def, Real.norm_eq_abs]
    exact le_max_right _ _
  have h_bound : ∀ t ∈ Ι b₀ (b₀ + h.2), ‖F (x₀ + h.1) t - F x₀ b₀‖ ≤ ε := by
    intro t ht
    have ht_uIcc : t ∈ [[b₀, b₀ + h.2]] := (Set.uIoc_subset_uIcc) ht
    have ht_bound : |t - b₀| ≤ |h.2| := by
      rcases Set.mem_uIcc.mp ht_uIcc with hcase | hcase
      · have hle : b₀ ≤ t ∧ t ≤ b₀ + h.2 := hcase
        have hpos : 0 ≤ t - b₀ := sub_nonneg.mpr hle.1
        have hle2 : t - b₀ ≤ h.2 := by linarith
        rw [abs_of_nonneg hpos]
        exact hle2.trans (le_abs_self h.2)
      · have hle : b₀ + h.2 ≤ t ∧ t ≤ b₀ := hcase
        have hneg : t - b₀ ≤ 0 := by linarith
        rw [abs_of_nonpos hneg]
        have hneg2 : h.2 ≤ 0 := by linarith
        rw [abs_of_nonpos hneg2]
        linarith
    have hq : dist (x₀ + h.1, t) (x₀, b₀) < δ := by
      simp only [Prod.dist_eq, Real.dist_eq]
      ring_nf
      have : max |h.1| |t - b₀| ≤ max |h.1| |h.2| :=
        max_le (le_max_left _ _) (ht_bound.trans (le_max_right _ _))
      exact lt_of_le_of_lt this hmax
    have hFdist := hδ hq
    have hFle : dist (F (x₀ + h.1) t) (F x₀ b₀) ≤ ε := le_of_lt hFdist
    simpa [Real.dist_eq] using hFle
  calc
    ‖∫ t in b₀..(b₀ + h.2), (F (x₀ + h.1) t - F x₀ b₀)‖
        ≤ ε * |(b₀ + h.2) - b₀| := intervalIntegral.norm_integral_le_of_norm_le_const h_bound
    _ = ε * |h.2| := by ring_nf
    _ ≤ ε * ‖h‖ := by gcongr

lemma intervalIntegral_hasFDerivAt_upper_of_continuous'
    {F F' : ℝ → ℝ → ℝ} {a b x₀ : ℝ}
    (hF_cont : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (hF'_cont : Continuous (fun p : ℝ × ℝ => F' p.1 p.2))
    (hF'_isDeriv : ∀ u t : ℝ, HasDerivAt (fun v : ℝ => F v t) (F' u t) u) :
    HasFDerivAt (fun p : ℝ × ℝ => ∫ t in a..p.2, F p.1 t)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (∫ t in a..b, F' x₀ t)
        + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (F x₀ b)) (x₀, b) := by
  have hA : HasDerivAt (fun x : ℝ => ∫ t in a..b, F x t) (∫ t in a..b, F' x₀ t) x₀ :=
    intervalIntegral_hasDerivAt_fixed_upper_of_continuous hF_cont hF'_cont hF'_isDeriv
  have hG1 : HasFDerivAt (fun p : ℝ × ℝ => ∫ t in a..b, F p.1 t)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (∫ t in a..b, F' x₀ t)) (x₀, b) := by
    let I : ℝ := ∫ t in a..b, F' x₀ t
    have hcomp := HasFDerivAt.comp (x := (x₀, b)) (f := Prod.fst)
      (g := fun x : ℝ => ∫ t in a..b, F x t)
      (f' := ContinuousLinearMap.fst ℝ ℝ ℝ)
      (g' := ContinuousLinearMap.toSpanSingleton ℝ I)
      hA.hasFDerivAt (hasFDerivAt_fst (p := (x₀, b)))
    have hder : (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight I =
        (ContinuousLinearMap.toSpanSingleton ℝ I).comp (ContinuousLinearMap.fst ℝ ℝ ℝ) := by
      refine ContinuousLinearMap.ext fun h => ?_
      simp [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    rw [hder]
    change HasFDerivAt ((fun x : ℝ => ∫ t in a..b, F x t) ∘ Prod.fst)
      ((ContinuousLinearMap.toSpanSingleton ℝ I).comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) (x₀, b)
    exact hcomp
  have hG2 : HasFDerivAt (fun p : ℝ × ℝ => ∫ t in b..p.2, F p.1 t)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (F x₀ b)) (x₀, b) :=
    intervalIntegral_hasFDerivAt_upper_continuous (x₀ := x₀) (b₀ := b) hF_cont
  have hsum := hG1.add hG2
  have hint : ∀ x a b : ℝ, IntervalIntegrable (fun t : ℝ => F x t) volume a b := by
    intro x a b
    have hprod : Continuous (fun t : ℝ => (x, t)) := continuous_const.prodMk continuous_id
    exact (hF_cont.comp hprod).intervalIntegrable _ _
  have hfun : (fun p : ℝ × ℝ => (∫ t in a..b, F p.1 t) + ∫ t in b..p.2, F p.1 t)
      = fun p : ℝ × ℝ => ∫ t in a..p.2, F p.1 t := by
    ext p
    exact intervalIntegral.integral_add_adjacent_intervals (hint p.1 a b) (hint p.1 b p.2)
  refine hsum.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall (fun p => by exact (congrFun hfun p).symm)

lemma intervalIntegral_hasDerivAt_upper_piece_of_continuous
    {F F' : ℝ → ℝ → ℝ} {c : ℝ} {y : ℝ → ℝ} {y' : ℝ} {s : ℝ}
    (hF_cont : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (hF'_cont : Continuous (fun p : ℝ × ℝ => F' p.1 p.2))
    (hF'_isDeriv : ∀ u t : ℝ, HasDerivAt (fun v : ℝ => F v t) (F' u t) u)
    (hy : HasDerivAt y y' s) (hy_cont : ContinuousAt y s) :
    HasDerivAt (fun u : ℝ => ∫ t in c..(y u), F u t)
      ((∫ t in c..(y s), F' s t) + F s (y s) * y') s := by
  let b : ℝ := y s
  let I : ℝ := ∫ t in c..b, F' s t
  have hG : HasFDerivAt (fun p : ℝ × ℝ => ∫ t in c..p.2, F p.1 t)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight I
        + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (F s b)) (s, b) := by
    simpa [b, I] using intervalIntegral_hasFDerivAt_upper_of_continuous' (a := c) (b := b) (x₀ := s) hF_cont hF'_cont hF'_isDeriv
  have hγ : HasDerivAt (fun u : ℝ => (u, y u)) (1, y') s := by
    simpa using (hasDerivAt_id s).prodMk hy
  have hcomp := HasFDerivAt.comp_hasDerivAt (x := s) hG hγ
  have hval : ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight I
        + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (F s b)) (1, y') = I + F s b * y' := by
    simp [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', smul_eq_mul]
    ring
  have hcompI := hcomp.congr_deriv hval
  have hfun : (fun u : ℝ => ∫ t in c..(y u), F u t) =
      (fun p : ℝ × ℝ => ∫ t in c..p.2, F p.1 t) ∘ (fun u : ℝ => (u, y u)) := by
    funext u
    rfl
  have hcomp_fun := hcompI.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun u => by exact congrFun hfun u))
  simpa [b, I] using hcomp_fun

end Commons.Analysis.Calculus