import Submission.CertSmooth
import Submission.Rescale

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

open scoped BigOperators Topology
open Filter Finset MeasureTheory

/-!
# The `J`-functionals of the smoothed certificate

For a.e. `u` in the marginal orthant, the inner integral `∫ x, certSmooth γ (extendAt i x u)`
converges to `∫ x, certFun (extendAt i x u)` as `γ → 0⁺`, by dominated convergence with the
integrable bound `certBound (extendAt i x u)`.  The bad `u`-set is the union of the coordinate
hyperplanes (null), and for good `u` the bad `x`-set is finite (the facets `x = 0` and the
boundary hyperplane `x + Σ u = 26/25`).  This yields the convergence of the marginal
functionals `JFunc 50 i cc` for the smoothed certificate.
-/

namespace Commons.NumberTheory.MaynardSieve

noncomputable section

/-- The marginal orthant of the Maynard functionals. -/
abbrev Marg (k : ℕ) (i : Fin k) : Type := {j : Fin k // j ≠ i} → ℝ

theorem volume_marg_coord_eq_zero {k : ℕ} (i : Fin k) (j : {l : Fin k // l ≠ i}) (c : ℝ) :
    (volume : Measure (Marg k i)) {u | u j = c} = 0 := by
  rw [volume_pi]
  exact Measure.pi_eval_preimage_null (fun _ => (volume : Measure ℝ)) Real.volume_singleton

theorem certBound_eq_zero_of_notMem {t : Fin 50 → ℝ} (h : t ∉ simplexC 50 ((26 : ℝ) / 25)) :
    certBound t = 0 := by
  rw [certBound, Set.indicator_of_notMem h, mul_zero]

theorem exists_certPoly_bound :
    ∃ B : ℝ, ∀ t ∈ simplexC 50 ((26 : ℝ) / 25), |certPoly t| ≤ B := by
  obtain ⟨C, hC⟩ := (isCompact_simplexC 50 ((26 : ℝ) / 25)).exists_bound_of_continuousOn
    continuous_certPoly.continuousOn
  exact ⟨C, fun t ht => by simpa [Real.norm_eq_abs] using hC t ht⟩

/-- Pointwise convergence of the smoothed certificate along the marginal lines. -/
theorem tendsto_certSmooth_extendAt {i : Fin 50} {u : Marg 50 i} {x : ℝ}
    (hx : x ≠ 0) (hu : ∀ j, u j ≠ 0)
    (hs : x + ∑ j : {j : Fin 50 // j ≠ i}, u j ≠ (26 : ℝ) / 25) :
    Tendsto (fun n : ℕ => certSmooth ((1 : ℝ) / (n + 1)) (extendAt i x u)) atTop
      (𝓝 (certFun (extendAt i x u))) := by
  by_cases hmem : extendAt i x u ∈ simplexC 50 ((26 : ℝ) / 25)
  · refine tendsto_certSmooth_of_mem hmem ?_ ?_
    · intro j
      by_cases hj : j = i
      · subst hj; rwa [extendAt, dif_pos rfl]
      · rw [extendAt, dif_neg hj]; exact hu ⟨j, hj⟩
    · rwa [sum_extendAt]
  · exact tendsto_certSmooth_of_notMem hmem

theorem certBound_eq_indicator (t : Fin 50 → ℝ) :
    certBound t = (simplexC 50 ((26 : ℝ) / 25)).indicator (fun t => |certPoly t|) t := by
  classical
  rw [certBound, Set.indicator_apply, Set.indicator_apply]
  by_cases ht : t ∈ simplexC 50 ((26 : ℝ) / 25) <;> simp [ht]

theorem measurable_certBound : Measurable certBound := by
  rw [funext certBound_eq_indicator]
  exact (continuous_abs.comp continuous_certPoly).measurable.indicator
    (measurableSet_simplexC 50 _)

theorem continuous_extendAt (i : Fin 50) (u : Marg 50 i) :
    Continuous (fun x : ℝ => extendAt i x u) := by
  refine continuous_pi (fun j => ?_)
  by_cases hj : j = i
  · rw [show (fun y : ℝ => extendAt i y u j) = fun y => y from
      funext (fun y => by rw [extendAt, dif_pos hj])]
    exact continuous_id
  · rw [show (fun y : ℝ => extendAt i y u j) = fun _ => u ⟨j, hj⟩ from
      funext (fun y => by rw [extendAt, dif_neg hj])]
    exact continuous_const

theorem extendAt_notMem_of_neg {i : Fin 50} {u : Marg 50 i} {x : ℝ} (hx : x < 0) :
    extendAt i x u ∉ simplexC 50 ((26 : ℝ) / 25) := by
  intro h
  have h1 := h.1 i
  rw [extendAt, dif_pos rfl] at h1
  linarith

theorem extendAt_notMem_of_neg_coord {i : Fin 50} {u : Marg 50 i} (j : {l : Fin 50 // l ≠ i})
    (hj : u j < 0) (x : ℝ) :
    extendAt i x u ∉ simplexC 50 ((26 : ℝ) / 25) := by
  intro h
  have h1 := h.1 j
  rw [extendAt, dif_neg j.2] at h1
  linarith

/-- The bound function along a marginal line is integrable in `x`. -/
theorem integrable_certBound_extendAt (i : Fin 50) (u : Marg 50 i) :
    Integrable (fun x : ℝ => certBound (extendAt i x u)) volume := by
  obtain ⟨B, hB⟩ := exists_certPoly_bound
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB (fun _ => 0) (by
    refine ⟨fun _ => le_refl 0, ?_⟩
    simp only [Finset.sum_const_zero]
    norm_num))
  have hsupp : ∀ x : ℝ, x ∉ Set.Icc (0 : ℝ) ((26 : ℝ) / 25) →
      certBound (extendAt i x u) = 0 := by
    intro x hx
    refine certBound_eq_zero_of_notMem ?_
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with h | h
    · exact extendAt_notMem_of_neg h
    · by_cases hu : ∃ j : {l : Fin 50 // l ≠ i}, u j < 0
      · obtain ⟨j, hj⟩ := hu
        exact extendAt_notMem_of_neg_coord j hj x
      · push Not at hu
        intro hmem
        have h1 := hmem.2
        rw [sum_extendAt] at h1
        have h2 : (0 : ℝ) ≤ ∑ j : {l : Fin 50 // l ≠ i}, u j :=
          Finset.sum_nonneg (fun j _ => hu j)
        linarith
  have hg : Integrable
      (fun x : ℝ => B * (Set.Icc (0 : ℝ) ((26 : ℝ) / 25)).indicator (fun _ => (1 : ℝ)) x)
      volume := by
    rw [show (fun x : ℝ => B * (Set.Icc (0 : ℝ) ((26 : ℝ) / 25)).indicator (fun _ => (1 : ℝ)) x)
        = (Set.Icc (0 : ℝ) ((26 : ℝ) / 25)).indicator (fun _ => B) from by
      funext x
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hx : x ∈ Set.Icc (0 : ℝ) ((26 : ℝ) / 25) <;> simp [hx]]
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  classical
  refine Integrable.mono' hg (measurable_certBound.comp (continuous_extendAt i u).measurable).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs]
  by_cases hx : x ∈ Set.Icc (0 : ℝ) ((26 : ℝ) / 25)
  · rw [Set.indicator_of_mem hx]
    have hle : certBound (extendAt i x u) ≤ B := by
      rw [certBound]
      by_cases hmem : extendAt i x u ∈ simplexC 50 ((26 : ℝ) / 25)
      · rw [Set.indicator_of_mem hmem]
        simp only [mul_one]
        exact hB _ hmem
      · rw [Set.indicator_of_notMem hmem, mul_zero]
        exact hB0
    calc |certBound (extendAt i x u)| = certBound (extendAt i x u) :=
          abs_of_nonneg (by
            rw [certBound]
            exact mul_nonneg (abs_nonneg _) (by
              rw [Set.indicator_apply]; split <;> norm_num))
      _ ≤ B := hle
      _ = B * 1 := by ring
  · rw [Set.indicator_of_notMem hx, hsupp x hx, abs_zero, mul_zero]


/-- **For a.e. `u`, the inner integral of the smoothed certificate converges.** -/
theorem ae_tendsto_inner_certSmooth (i : Fin 50) :
    ∀ᵐ u ∂(volume : Measure (Marg 50 i)),
      Tendsto (fun n : ℕ => ∫ x, certSmooth ((1 : ℝ) / (n + 1)) (extendAt i x u)) atTop
        (𝓝 (∫ x, certFun (extendAt i x u))) := by
  rw [MeasureTheory.ae_iff]
  have hbad : (volume : Measure (Marg 50 i)) {u | ∃ j : {l : Fin 50 // l ≠ i}, u j = 0} = 0 := by
    have hset : {u : Marg 50 i | ∃ j : {l : Fin 50 // l ≠ i}, u j = 0}
        = ⋃ j, {u | u j = 0} := by
      ext u; simp
    rw [hset]
    exact measure_iUnion_null fun j => volume_marg_coord_eq_zero i j 0
  refine measure_mono_null ?_ hbad
  intro u hu
  simp only [Set.mem_setOf_eq] at hu ⊢
  by_contra hcon
  push Not at hcon
  have haex : ∀ᵐ x : ℝ ∂(volume : Measure ℝ),
      Tendsto (fun n : ℕ => certSmooth ((1 : ℝ) / (n + 1)) (extendAt i x u)) atTop
        (𝓝 (certFun (extendAt i x u))) := by
    rw [MeasureTheory.ae_iff]
    have hS : (volume : Measure ℝ) ({(0 : ℝ)} ∪
        {((26 : ℝ) / 25 - ∑ j : {l : Fin 50 // l ≠ i}, u j)}) = 0 :=
      measure_union_null (s := {(0 : ℝ)}) (t := {((26 : ℝ) / 25 - ∑ j : {l : Fin 50 // l ≠ i}, u j)})
        Real.volume_singleton Real.volume_singleton
    refine measure_mono_null ?_ hS
    intro x hx
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff] at hx ⊢
    by_contra hcon2
    push Not at hcon2
    obtain ⟨hx0, hxs⟩ := hcon2
    refine hx (tendsto_certSmooth_extendAt hx0 hcon ?_)
    intro hsum
    exact hxs (by linarith)
  have hP : Tendsto (fun n : ℕ => ∫ x, certSmooth ((1 : ℝ) / (n + 1)) (extendAt i x u)) atTop
      (𝓝 (∫ x, certFun (extendAt i x u))) :=
    tendsto_integral_of_dominated_convergence (fun x => certBound (extendAt i x u))
      (fun n => ((continuous_certSmooth (by positivity)).comp
        (continuous_extendAt i u)).aestronglyMeasurable)
      (integrable_certBound_extendAt i u)
      (fun n => by
        filter_upwards with x
        rw [Real.norm_eq_abs]
        exact certSmooth_abs_le_certBound (by positivity) (extendAt i x u))
      haex
  exact absurd hP hu

/-- The marginal set is bounded, hence of finite volume. -/
theorem volume_marginalSet_lt_top (cc : ℝ) (i : Fin 50) :
    (volume : Measure (Marg 50 i)) (marginalSet 50 i cc) < ⊤ := by
  refine Bornology.IsBounded.measure_lt_top ?_
  refine (Metric.isBounded_iff_subset_closedBall (0 : Marg 50 i)).mpr ⟨max cc 0, fun u hu => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).mpr (fun j => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hu.1 j)]
  calc u j ≤ ∑ j' : {l : Fin 50 // l ≠ i}, u j' :=
        Finset.single_le_sum (fun j' _ => hu.1 j') (Finset.mem_univ j)
    _ ≤ cc := hu.2
    _ ≤ max cc 0 := le_max_left _ _

/-- Along a marginal line outside the box `[0, 26/25]` the bound function vanishes. -/
theorem certBound_extendAt_eq_zero (i : Fin 50) (u : Marg 50 i) {x : ℝ}
    (hx : x ∉ Set.Icc (0 : ℝ) ((26 : ℝ) / 25)) : certBound (extendAt i x u) = 0 := by
  refine certBound_eq_zero_of_notMem ?_
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with h | h
  · exact extendAt_notMem_of_neg h
  · by_cases hu : ∃ j : {l : Fin 50 // l ≠ i}, u j < 0
    · obtain ⟨j, hj⟩ := hu
      exact extendAt_notMem_of_neg_coord j hj x
    · push Not at hu
      intro hmem
      have h1 := hmem.2
      rw [sum_extendAt] at h1
      have h2 : (0 : ℝ) ≤ ∑ j : {l : Fin 50 // l ≠ i}, u j :=
        Finset.sum_nonneg (fun j _ => hu j)
      linarith

/-- The integral of the bound function along a marginal line is at most `B·(26/25)`. -/
theorem integral_certBound_extendAt_le (i : Fin 50) (u : Marg 50 i) {B : ℝ}
    (hB : ∀ t ∈ simplexC 50 ((26 : ℝ) / 25), |certPoly t| ≤ B) (hB0 : 0 ≤ B) :
    ∫ x, certBound (extendAt i x u) ≤ B * ((26 : ℝ) / 25) := by
  have h1 : ∀ x : ℝ, certBound (extendAt i x u)
      ≤ B * (Set.Icc (0 : ℝ) ((26 : ℝ) / 25)).indicator (fun _ => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) ((26 : ℝ) / 25)
    · rw [Set.indicator_of_mem hx, mul_one]
      by_cases hmem : extendAt i x u ∈ simplexC 50 ((26 : ℝ) / 25)
      · rw [certBound, Set.indicator_of_mem hmem]
        simp only [mul_one]
        exact hB _ hmem
      · rw [certBound, Set.indicator_of_notMem hmem, mul_zero]
        exact hB0
    · rw [Set.indicator_of_notMem hx, mul_zero, certBound_extendAt_eq_zero i u hx]
  have h2 : Integrable (fun x : ℝ => B * (Set.Icc (0 : ℝ) ((26 : ℝ) / 25)).indicator (fun _ => (1 : ℝ)) x)
      volume := by
    rw [show (fun x : ℝ => B * (Set.Icc (0 : ℝ) ((26 : ℝ) / 25)).indicator (fun _ => (1 : ℝ)) x)
        = (Set.Icc (0 : ℝ) ((26 : ℝ) / 25)).indicator (fun _ => B) from by
      funext x
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hx : x ∈ Set.Icc (0 : ℝ) ((26 : ℝ) / 25) <;> simp [hx]]
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  calc ∫ x, certBound (extendAt i x u)
      ≤ ∫ x, B * (Set.Icc (0 : ℝ) ((26 : ℝ) / 25)).indicator (fun _ => (1 : ℝ)) x :=
        integral_mono (integrable_certBound_extendAt i u) h2 h1
    _ = B * ∫ x, (Set.Icc (0 : ℝ) ((26 : ℝ) / 25)).indicator (fun _ => (1 : ℝ)) x :=
        integral_const_mul _ _
    _ = B * ((26 : ℝ) / 25) := by
        rw [integral_indicator measurableSet_Icc, MeasureTheory.setIntegral_const,
          smul_eq_mul, mul_one]
        rw [Measure.real, Real.volume_Icc]
        norm_num

/-- The `J`-functional as an integral over the marginal orthant. -/
theorem JFunc_eq_integral (k : ℕ) (i : Fin k) (c : ℝ) (F : (Fin k → ℝ) → ℝ) :
    JFunc k i c F = ∫ u : Marg k i,
      (marginalSet k i c).indicator (fun _ => (1 : ℝ)) u * (∫ x, F (extendAt i x u)) ^ 2 := by
  unfold JFunc
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  simp only []
  by_cases h : u ∈ marginalSet k i c
  · rw [Set.indicator_of_mem h, if_pos h]; ring
  · rw [Set.indicator_of_notMem h, if_neg h]; ring

theorem certSmooth_extendAt_eq_zero (i : Fin 50) (u : Marg 50 i) {γ : ℝ} (hγ : 0 < γ)
    {x : ℝ} (hx : x ∉ Set.Icc (0 : ℝ) ((26 : ℝ) / 25)) : certSmooth γ (extendAt i x u) = 0 := by
  refine certSmooth_support hγ ?_
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with h | h
  · exact extendAt_notMem_of_neg h
  · by_cases hu : ∃ j : {l : Fin 50 // l ≠ i}, u j < 0
    · obtain ⟨j, hj⟩ := hu
      exact extendAt_notMem_of_neg_coord j hj x
    · push Not at hu
      intro hmem
      have h1 := hmem.2
      rw [sum_extendAt] at h1
      have h2 : (0 : ℝ) ≤ ∑ j : {l : Fin 50 // l ≠ i}, u j :=
        Finset.sum_nonneg (fun j _ => hu j)
      linarith

theorem certSmooth_integrable_extendAt (i : Fin 50) (u : Marg 50 i) {γ : ℝ} (hγ : 0 < γ) :
    Integrable (fun x : ℝ => certSmooth γ (extendAt i x u)) volume := by
  refine (continuous_certSmooth hγ).comp (continuous_extendAt i u) |>.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (0 : ℝ))
    (b := (26 : ℝ) / 25)) (fun x hx => ?_)
  by_contra h
  exact (Function.mem_support.mp hx) (certSmooth_extendAt_eq_zero i u hγ h)

/-- The inner integral of the smoothed certificate is bounded by `B·(26/25)`. -/
theorem abs_integral_certSmooth_le (i : Fin 50) (u : Marg 50 i) {γ : ℝ} (hγ : 0 < γ) {B : ℝ}
    (hB : ∀ t ∈ simplexC 50 ((26 : ℝ) / 25), |certPoly t| ≤ B) (hB0 : 0 ≤ B) :
    |∫ x, certSmooth γ (extendAt i x u)| ≤ B * ((26 : ℝ) / 25) := by
  refine le_trans abs_integral_le_integral_abs ?_
  refine le_trans (integral_mono (certSmooth_integrable_extendAt i u hγ).abs
    (integrable_certBound_extendAt i u) (fun x => certSmooth_abs_le_certBound hγ _)) ?_
  exact integral_certBound_extendAt_le i u hB hB0

/-- **The marginal functionals of the smoothed certificate converge to the certificate's.** -/
theorem tendsto_JFunc_certSmooth (i : Fin 50) (cc : ℝ) :
    Tendsto (fun n : ℕ => JFunc 50 i cc (certSmooth ((1 : ℝ) / (n + 1)))) atTop
      (𝓝 (JFunc 50 i cc certFun)) := by
  classical
  obtain ⟨B, hB⟩ := exists_certPoly_bound
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB (fun _ => 0) (by
    refine ⟨fun _ => le_refl 0, ?_⟩
    simp only [Finset.sum_const_zero]
    norm_num))
  have hbd : Integrable (fun u : Marg 50 i =>
      (marginalSet 50 i cc).indicator (fun _ => (1 : ℝ)) u * (B * ((26 : ℝ) / 25)) ^ 2)
      volume := by
    rw [show (fun u : Marg 50 i =>
          (marginalSet 50 i cc).indicator (fun _ => (1 : ℝ)) u * (B * ((26 : ℝ) / 25)) ^ 2)
        = (marginalSet 50 i cc).indicator (fun _ => (B * ((26 : ℝ) / 25)) ^ 2) from by
      funext u
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases h : u ∈ marginalSet 50 i cc <;> simp [h]]
    rw [integrable_indicator_iff (measurableSet_marginalSet 50 i cc)]
    exact integrableOn_const (ne_of_lt (volume_marginalSet_lt_top cc i))
  have h_eq : ∀ F : (Fin 50 → ℝ) → ℝ, JFunc 50 i cc F =
      ∫ u : Marg 50 i,
        (marginalSet 50 i cc).indicator (fun _ => (1 : ℝ)) u * (∫ x, F (extendAt i x u)) ^ 2 :=
    fun F => JFunc_eq_integral 50 i cc F
  simp only [h_eq]
  refine tendsto_integral_of_dominated_convergence
    (fun u : Marg 50 i =>
      (marginalSet 50 i cc).indicator (fun _ => (1 : ℝ)) u * (B * ((26 : ℝ) / 25)) ^ 2)
    (fun n => ?_) hbd (fun n => ?_) ?_
  · -- measurability
    have hcont : Continuous (fun p : Marg 50 i × ℝ =>
        certSmooth ((1 : ℝ) / (n + 1)) (extendAt i p.2 p.1)) := by
      refine (continuous_certSmooth (by positivity)).comp ?_
      refine continuous_pi (fun j => ?_)
      by_cases hj : j = i
      · simp only [extendAt, dif_pos hj]
        exact continuous_snd
      · simp only [extendAt, dif_neg hj]
        exact (continuous_apply (⟨j, hj⟩ : {l : Fin 50 // l ≠ i})).comp continuous_fst
    have hsm : StronglyMeasurable (fun u : Marg 50 i =>
        ∫ x, certSmooth ((1 : ℝ) / (n + 1)) (extendAt i x u)) :=
      StronglyMeasurable.integral_prod_right (by
        show StronglyMeasurable (Function.uncurry fun u x =>
          certSmooth ((1 : ℝ) / (n + 1)) (extendAt i x u))
        exact hcont.stronglyMeasurable)
    exact ((Measurable.indicator (measurable_const : Measurable fun _ : Marg 50 i => (1 : ℝ))
      (measurableSet_marginalSet 50 i cc)).aestronglyMeasurable.mul
        (hsm.pow 2).aestronglyMeasurable)
  · -- the pointwise bound
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) u)]
    refine mul_le_mul_of_nonneg_left ?_ (Set.indicator_nonneg (fun _ _ => zero_le_one) u)
    rw [abs_of_nonneg (sq_nonneg _), sq_le_sq,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ B * ((26 : ℝ) / 25))]
    exact abs_integral_certSmooth_le i u (by positivity) hB hB0
  · -- a.e. convergence
    filter_upwards [ae_tendsto_inner_certSmooth i] with u hu
    exact (hu.pow 2).const_mul ((marginalSet 50 i cc).indicator (fun _ => (1 : ℝ)) u)

end

end Commons.NumberTheory.MaynardSieve




