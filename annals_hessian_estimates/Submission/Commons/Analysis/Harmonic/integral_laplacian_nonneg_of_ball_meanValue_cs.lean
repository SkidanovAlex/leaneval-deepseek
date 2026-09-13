import Mathlib
import Submission.Commons.Analysis.Harmonic.laplacian_nonneg_of_le_setAverage_ball
import Submission.Commons.Analysis.Harmonic.setAverage_ball_bilinear
import Submission.Commons.Analysis.Calculus.Taylor.abs_taylor_remainder_two_half_le
import Submission.Commons.Analysis.Measure.setAverage_ball_add
import Submission.Commons.Analysis.Measure.setAverage_mul_const
import Submission.Commons.Analysis.Harmonic.integral_mul_setAverage_ball_comm
import Submission.Commons.Analysis.Calculus.Laplacian.continuousOn_laplacian

open MeasureTheory Metric Set Filter Function
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace

namespace Commons.Analysis.Harmonic

noncomputable section

/-! ## Elementary helpers -/

/-- The Lebesgue measure (as a real number) of a ball is independent of its centre. -/
lemma measureReal_ball_centre_eq {n : ℕ} (c : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball c r)
      = (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 r) := by
  have hpre : (fun y : EuclideanSpace ℝ (Fin n) => c + y) ⁻¹' Metric.ball c r
      = Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r := by
    ext y
    simp only [mem_preimage, mem_ball, dist_eq_norm]
    rw [add_sub_cancel_left, sub_zero]
  have hmap : (volume : Measure (EuclideanSpace ℝ (Fin n))).map (fun y => c + y) = volume :=
    Measure.IsAddLeftInvariant.map_add_left_eq_self c
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball c r)
      = (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball 0 r) := by
    have h1 : (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball c r)
        = ((volume : Measure (EuclideanSpace ℝ (Fin n))).map (fun y => c + y))
            (Metric.ball c r) := by
      rw [hmap]
    rw [h1, Measure.map_apply (measurable_const_add c) measurableSet_ball, hpre]
  rw [Measure.real_def, Measure.real_def, hvol]

/-- The set average of a difference of two integrable functions. -/
lemma setAverage_sub_real {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    {f g : α → ℝ} (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ) :
    (⨍ x in s, (f x - g x) ∂μ) = (⨍ x in s, f x ∂μ) - (⨍ x in s, g x ∂μ) := by
  rw [setAverage_eq, setAverage_eq, setAverage_eq, integral_sub hf hg, smul_sub]

/-- The set average of a difference of four integrable functions. -/
lemma setAverage_sub4_real {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    {f₁ f₂ f₃ f₄ : α → ℝ} (h₁ : IntegrableOn f₁ s μ) (h₂ : IntegrableOn f₂ s μ)
    (h₃ : IntegrableOn f₃ s μ) (h₄ : IntegrableOn f₄ s μ) :
    (⨍ x in s, (f₁ x - f₂ x - f₃ x - f₄ x) ∂μ)
      = (⨍ x in s, f₁ x ∂μ) - (⨍ x in s, f₂ x ∂μ)
        - (⨍ x in s, f₃ x ∂μ) - (⨍ x in s, f₄ x ∂μ) := by
  have h12 : IntegrableOn (fun x => f₁ x - f₂ x) s μ := h₁.sub h₂
  have h123 : IntegrableOn (fun x => f₁ x - f₂ x - f₃ x) s μ := h12.sub h₃
  rw [setAverage_sub_real h123 h₄, setAverage_sub_real h12 h₃, setAverage_sub_real h₁ h₂]

/-- Set averages commute with the application of a continuous linear functional. -/
lemma setAverage_clm_apply {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (L : E →L[ℝ] ℝ) (f : α → E) (hf : IntegrableOn f s μ) :
    (⨍ x in s, L (f x) ∂μ) = L (⨍ x in s, f x ∂μ) := by
  rw [setAverage_eq, setAverage_eq, ContinuousLinearMap.integral_comp_comm L hf, map_smul]

/-- The set average of `u y - u c` over a ball equals `⨍ u − u c`. -/
lemma setAverage_ball_sub_const {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hu : ContinuousOn u (Metric.closedBall c r)) :
    (⨍ y in Metric.ball c r, (u y - u c)) = (⨍ y in Metric.ball c r, u y) - u c := by
  have hballfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball c r) < ∞ :=
    lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
      (isCompact_closedBall c r).measure_lt_top
  have huint : IntegrableOn u (Metric.ball c r) volume :=
    (hu.integrableOn_compact (isCompact_closedBall c r)).mono_set Metric.ball_subset_closedBall
  have hcint : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin n) => u c) (Metric.ball c r) volume :=
    integrableOn_const hballfin.ne (by simp)
  rw [setAverage_sub_real huint hcint,
    setAverage_const (measure_ball_pos volume c hr).ne' hballfin.ne (u c)]

/-- **Second-order Taylor expansion of the ball average.**
If `φ` is `C²` and `ε` bounds the oscillation of `D²φ` on the ball of radius `r` around `x₀`,
then the average of `φ` over that ball equals `φ x₀ + (r²/(2(n+2))) Δφ x₀` up to `ε r²`. -/
theorem abs_setAverage_ball_sub_self_sub_laplacian_le {n : ℕ} (hn : 0 < n)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 2 φ)
    {x₀ : EuclideanSpace ℝ (Fin n)} {r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε)
    (hD2 : ∀ z : EuclideanSpace ℝ (Fin n), ‖z - x₀‖ ≤ r →
      ‖fderiv ℝ (fderiv ℝ φ) z - fderiv ℝ (fderiv ℝ φ) x₀‖ ≤ ε) :
    |(⨍ y in Metric.ball x₀ r, φ y) - φ x₀
        - r ^ 2 / (2 * ((n : ℝ) + 2)) * Laplacian.laplacian φ x₀| ≤ ε * r ^ 2 := by
  set M₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    fderiv ℝ (fderiv ℝ φ) x₀ with hM₀
  set R : EuclideanSpace ℝ (Fin n) → ℝ := fun w =>
    φ (x₀ + w) - φ x₀ - (fderiv ℝ φ x₀) w - (1 / 2 : ℝ) * M₀ w w with hR
  -- pointwise Taylor bound
  have hpt : ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ ≤ r → |R w| ≤ ε * ‖w‖ ^ 2 := by
    intro w hw
    have h := Commons.Analysis.Calculus.Taylor.abs_taylor_remainder_two_half_le
      (f := φ) (x := x₀) (y := w) (B := M₀) hε
      (fun t _ => hφ.contDiffAt)
      (fun t ht => by
        have ht0 : 0 ≤ t := ht.1
        have h1 : ‖t • w‖ = t * ‖w‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
        have h2 : ‖(x₀ + t • w) - x₀‖ ≤ r := by
          rw [add_sub_cancel_left, h1]
          nlinarith [ht.2, hw, norm_nonneg w]
        exact hD2 _ h2)
    simpa [hR] using h
  -- integrability on the ball
  have hint : ∀ g : EuclideanSpace ℝ (Fin n) → ℝ, Continuous g →
      IntegrableOn g (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) volume := fun g hg =>
    (hg.continuousOn.integrableOn_compact (isCompact_closedBall 0 r)).mono_set
      Metric.ball_subset_closedBall
  have hcont1 : Continuous (fun w : EuclideanSpace ℝ (Fin n) => φ (x₀ + w)) :=
    hφ.continuous.comp (continuous_const.add continuous_id)
  have hcont3 : Continuous (fun w : EuclideanSpace ℝ (Fin n) => (fderiv ℝ φ x₀) w) :=
    (fderiv ℝ φ x₀).continuous
  have hcont4 : Continuous (fun w : EuclideanSpace ℝ (Fin n) => M₀ w w) := by
    have h2 : Continuous (fun w : EuclideanSpace ℝ (Fin n) => M₀ w) := M₀.continuous
    exact h2.clm_apply continuous_id
  -- the average of `R`
  have hkey : (⨍ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r, R w)
      = (⨍ y in Metric.ball x₀ r, φ y) - φ x₀
        - r ^ 2 / (2 * ((n : ℝ) + 2)) * Laplacian.laplacian φ x₀ := by
    have e1 : (⨍ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r,
          (φ (x₀ + w) - φ x₀ - (fderiv ℝ φ x₀) w - (1 / 2 : ℝ) * M₀ w w))
        = (⨍ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r, φ (x₀ + w))
          - (⨍ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r, φ x₀)
          - (⨍ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r, (fderiv ℝ φ x₀) w)
          - (⨍ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r, (1 / 2 : ℝ) * M₀ w w) :=
      setAverage_sub4_real (hint _ hcont1) (hint _ continuous_const) (hint _ hcont3)
        (hint (fun w : EuclideanSpace ℝ (Fin n) => (1 / 2 : ℝ) * M₀ w w)
          (hcont4.const_mul (1 / 2)))
    have e2 : (⨍ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r, φ (x₀ + w))
        = ⨍ y in Metric.ball x₀ r, φ y :=
      (Commons.Analysis.Measure.setAverage_ball_add x₀ r φ).symm
    have e3 : (⨍ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r, φ x₀) = φ x₀ :=
      setAverage_const (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) hr).ne'
        (lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
          (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) r).measure_lt_top).ne (φ x₀)
    have e4 : (⨍ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r, (fderiv ℝ φ x₀) w) = 0 := by
      rw [setAverage_clm_apply (fderiv ℝ φ x₀) (fun w : EuclideanSpace ℝ (Fin n) => w)
        (IntegrableOn.mono_set
          ((continuous_id.continuousOn).integrableOn_compact
            (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) r))
          Metric.ball_subset_closedBall)]
      rw [setAverage_ball_self_eq_zero r, map_zero]
    have e5 : (⨍ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r,
          (1 / 2 : ℝ) * M₀ w w)
        = r ^ 2 / (2 * ((n : ℝ) + 2)) * Laplacian.laplacian φ x₀ := by
      rw [setAverage_mul_const_real, setAverage_ball_bilinear hn M₀ hr,
        laplacian_eq_sum_fderiv_fderiv, hM₀]
      have hcoef : (1 / 2 : ℝ) * (r ^ 2 / ((n : ℝ) + 2)) = r ^ 2 / (2 * ((n : ℝ) + 2)) := by
        field_simp
      rw [← mul_assoc, hcoef]
    rw [hR, e1, e2, e3, e4, e5]
    ring
  -- the norm bound on the average of `R`
  have hbound : ‖(⨍ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r, R w)‖ ≤ ε * r ^ 2 := by
    refine norm_setAverage_le
      (lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
        (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) r).measure_lt_top)
      ?_ ?_
    · rw [Measure.real_def]
      exact ENNReal.toReal_pos (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) hr).ne'
        (lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
          (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) r).measure_lt_top).ne
    · intro w hw
      have hwr : ‖w‖ ≤ r := le_of_lt (by simpa [mem_ball, dist_eq_norm] using hw)
      calc ‖R w‖ = |R w| := by rw [Real.norm_eq_abs]
        _ ≤ ε * ‖w‖ ^ 2 := hpt w hwr
        _ ≤ ε * r ^ 2 := by
            have h2 : ‖w‖ ^ 2 ≤ r ^ 2 := by nlinarith [norm_nonneg w]
            exact mul_le_mul_of_nonneg_left h2 hε
  rw [hkey] at hbound
  simpa [Real.norm_eq_abs] using hbound

/-- The ball average of a compactly supported continuous function is continuous. -/
theorem continuous_setAverage_ball (n : ℕ) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hfc : HasCompactSupport f) (hf : Continuous f) {r : ℝ} (hr : 0 < r) :
    Continuous (fun y => ⨍ x in Metric.ball y r, f x) := by
  rw [continuous_iff_continuousAt]
  intro y₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuous_iff.mp
    (hfc.uniformContinuous_of_continuous hf) (ε / 2) (by linarith)
  refine ⟨δ, hδpos, fun y hy => ?_⟩
  have h1 : (⨍ x in Metric.ball y r, f x)
      = ⨍ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r, f (y + z) :=
    Commons.Analysis.Measure.setAverage_ball_add y r f
  have h2 : (⨍ x in Metric.ball y₀ r, f x)
      = ⨍ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r, f (y₀ + z) :=
    Commons.Analysis.Measure.setAverage_ball_add y₀ r f
  rw [h1, h2]
  have hint : ∀ w : EuclideanSpace ℝ (Fin n),
      IntegrableOn (fun z : EuclideanSpace ℝ (Fin n) => f (w + z))
        (Metric.ball 0 r) volume := fun w =>
    ((hf.comp (continuous_const.add continuous_id)).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) r)).mono_set
        Metric.ball_subset_closedBall
  have hsub : (⨍ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r, f (y + z))
        - (⨍ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r, f (y₀ + z))
      = ⨍ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r, (f (y + z) - f (y₀ + z)) :=
    (setAverage_sub_real (hint y) (hint y₀)).symm
  rw [dist_eq_norm, hsub]
  have hfin : (volume : Measure (EuclideanSpace ℝ (Fin n)))
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) < ∞ :=
    lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
      ((isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) r).measure_lt_top (μ := volume))
  have hpos : 0 < (volume : Measure (EuclideanSpace ℝ (Fin n))).real
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) := by
    rw [Measure.real_def]
    exact ENNReal.toReal_pos (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) hr).ne'
      hfin.ne
  refine lt_of_le_of_lt (norm_setAverage_le (C := ε / 2) hfin hpos ?_) (by linarith)
  intro z _
  rw [Real.norm_eq_abs]
  have hy' : dist (y + z) (y₀ + z) < δ := by
    simpa [dist_eq_norm] using hy
  have hlt : |f (y + z) - f (y₀ + z)| < ε / 2 := by
    have := hδ hy'
    rwa [dist_eq_norm, Real.norm_eq_abs] at this
  exact le_of_lt hlt

open MeasureTheory Metric Set Filter Function in
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace in
theorem integral_laplacian_nonneg_of_ball_meanValue_cs {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {s : Set (EuclideanSpace ℝ (Fin n))} (hs : IsOpen s)
    (hu : ContinuousOn u s)
    (hMVP : ∀ c ∈ s, ∀ r : ℝ, 0 < r → closedBall c r ⊆ s → u c ≤ ⨍ y in ball c r, u y) :
    ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ s → 0 ≤ φ →
      0 ≤ ∫ x, u x * Laplacian.laplacian φ x := by
  intro φ hφcd hφcs hφs hφnn
  rcases isEmpty_or_nonempty (Fin n) with h0 | hn
  · haveI : IsEmpty (Fin n) := h0
    have hzero : (fun x : EuclideanSpace ℝ (Fin n) => u x * Laplacian.laplacian φ x)
        = fun _ => (0 : ℝ) := by
      funext x
      rw [laplacian_eq_sum_fderiv_fderiv]
      exact mul_eq_zero_of_right _ (Finset.sum_eq_zero (fun i _ => (IsEmpty.false i).elim))
    rw [hzero]
    simp
  · haveI : Nonempty (Fin n) := hn
    have hnpos : 0 < n := Fin.pos_iff_nonempty.mpr hn
    have hφcont : Continuous φ := hφcd.continuous
    have hφ2 : ContDiff ℝ 2 φ := hφcd.of_le (WithTop.coe_le_coe.mpr le_top)
    set K : Set (EuclideanSpace ℝ (Fin n)) := tsupport φ with hKdef
    have hKc : IsCompact K := hφcs
    have hKs : K ⊆ s := hφs
    have hKmeas : MeasurableSet K := hKc.measurableSet
    have hφzero : ∀ x, x ∉ K → φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
    obtain ⟨δ, hδpos, hδsub⟩ := hKc.exists_cthickening_subset_open hs hKs
    set r₀ : ℝ := δ / 2 with hr₀def
    have hr₀pos : 0 < r₀ := by rw [hr₀def]; linarith
    have hr₀δ : r₀ < δ := by rw [hr₀def]; linarith
    have hcth_s : Metric.cthickening r₀ K ⊆ s :=
      (Metric.cthickening_mono hr₀δ.le K).trans hδsub
    obtain ⟨M, hM⟩ := (hKc.cthickening (r := r₀)).exists_bound_of_continuousOn (hu.mono hcth_s)
    set Mb : ℝ := max M 0 with hMbdef
    have hMbnn : 0 ≤ Mb := le_max_right _ _
    have hMle : ∀ y ∈ Metric.cthickening r₀ K, ‖u y‖ ≤ Mb :=
      fun y hy => (hM y hy).trans (le_max_left _ _)
    set C : ℝ := Mb * (volume : Measure (EuclideanSpace ℝ (Fin n))).real
      (Metric.cthickening r₀ K) with hCdef
    have hCnn : 0 ≤ C := by rw [hCdef]; exact mul_nonneg hMbnn measureReal_nonneg
    have hcth_meas : MeasurableSet (Metric.cthickening r₀ K) :=
      (hKc.cthickening (r := r₀)).isClosed.measurableSet
    have hcth_fin : (volume : Measure (EuclideanSpace ℝ (Fin n)))
        (Metric.cthickening r₀ K) < ∞ :=
      (hKc.cthickening (r := r₀)).measure_lt_top (μ := volume)
    have key : ∀ ε > 0, 0 ≤ (∫ x, u x * Laplacian.laplacian φ x) + ε := by
      intro ε hε
      set D : ℝ := 2 * ((n : ℝ) + 2) * C with hDdef
      have hDnn : 0 ≤ D := by rw [hDdef]; positivity
      have hD1pos : 0 < D + 1 := by linarith
      set η : ℝ := ε / (D + 1) with hηdef
      have hηpos : 0 < η := by rw [hηdef]; positivity
      have hD2cont : Continuous
          (fun z : EuclideanSpace ℝ (Fin n) => fderiv ℝ (fderiv ℝ φ) z) := by fun_prop
      have hunif : @UniformContinuousOn (EuclideanSpace ℝ (Fin n))
          (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
          (PseudoMetricSpace.toUniformSpace : UniformSpace (EuclideanSpace ℝ (Fin n)))
          (PseudoMetricSpace.toUniformSpace : UniformSpace
            (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
          (fun z => fderiv ℝ (fderiv ℝ φ) z)
          (Metric.cthickening (2 * r₀) K) :=
        (hKc.cthickening (r := 2 * r₀)).uniformContinuousOn_of_continuous hD2cont.continuousOn
      obtain ⟨ρ, hρpos, hρ⟩ := Metric.uniformContinuousOn_iff_le.mp hunif η hηpos
      set r : ℝ := min ρ r₀ / 2 with hrdef
      have hrpos : 0 < r := by rw [hrdef]; positivity
      have hrltρ : r < ρ := by
        rw [hrdef]; have := min_le_left ρ r₀; linarith
      have hrler₀ : r ≤ r₀ := by
        rw [hrdef]; have := min_le_right ρ r₀; linarith
      have hcth_r_s : Metric.cthickening r K ⊆ s :=
        (Metric.cthickening_mono (hrler₀.trans hr₀δ.le) K).trans hδsub
      have huc : ContinuousOn u (Metric.cthickening r K) := hu.mono hcth_r_s
      set Φ : EuclideanSpace ℝ (Fin n) → ℝ := fun y => ⨍ x in Metric.ball y r, φ x with hΦdef
      set Ψ : EuclideanSpace ℝ (Fin n) → ℝ :=
        fun y => ⨍ x in Metric.ball y r, (φ x - φ y) with hΨdef
      set A : EuclideanSpace ℝ (Fin n) → ℝ :=
        fun y => r ^ 2 / (2 * ((n : ℝ) + 2)) * Laplacian.laplacian φ y with hAdef
      set E : EuclideanSpace ℝ (Fin n) → ℝ := fun y => Φ y - φ y - A y with hEdef
      have hΦcont : Continuous Φ := continuous_setAverage_ball n hφcs hφcont hrpos
      have hAcont : Continuous A := by
        rw [hAdef]
        exact continuous_const.mul (continuousOn_univ.mp
          (Commons.Analysis.Calculus.Laplacian.continuousOn_laplacian isOpen_univ hφ2.contDiffOn))
      have hEcont : Continuous E := by rw [hEdef]; exact (hΦcont.sub hφcont).sub hAcont
      have hΨeq : ∀ y, Ψ y = Φ y - φ y := by
        intro y
        rw [hΨdef, hΦdef]
        exact setAverage_ball_sub_const hrpos hφcont.continuousOn
      have hΨAE : ∀ y, Ψ y = A y + E y := by
        intro y; rw [hΨeq y, hEdef]; ring
      have hEbound : ∀ y ∈ Metric.cthickening r₀ K, |E y| ≤ η * r ^ 2 := by
        intro y hy
        have hT := abs_setAverage_ball_sub_self_sub_laplacian_le hnpos hφ2
          (x₀ := y) (r := r) (ε := η) hrpos hηpos.le (fun z hz => by
            have hymem : y ∈ Metric.cthickening (2 * r₀) K :=
              Metric.cthickening_mono (by linarith) K hy
            have hzmem : z ∈ Metric.cthickening (2 * r₀) K := by
              rw [Metric.mem_cthickening_iff]
              have hy' : Metric.infEDist y K ≤ ENNReal.ofReal r₀ :=
                Metric.mem_cthickening_iff.mp hy
              refine le_trans (Metric.infEDist_le_infEDist_add_edist (x := z) (y := y)) ?_
              have hedist : edist z y ≤ ENNReal.ofReal r := by
                rw [edist_dist, ENNReal.ofReal_le_ofReal_iff hrpos.le]
                simpa [dist_eq_norm] using hz
              calc infEDist y K + edist z y ≤ ENNReal.ofReal r₀ + ENNReal.ofReal r :=
                    add_le_add hy' hedist
                _ = ENNReal.ofReal (r₀ + r) := (ENNReal.ofReal_add hr₀pos.le hrpos.le).symm
                _ ≤ ENNReal.ofReal (2 * r₀) := ENNReal.ofReal_le_ofReal (by linarith)
            have hd : dist (fderiv ℝ (fderiv ℝ φ) y) (fderiv ℝ (fderiv ℝ φ) z) ≤ η :=
              hρ y hymem z hzmem
                (by rw [dist_eq_norm, norm_sub_rev]; exact le_of_lt (lt_of_le_of_lt hz hrltρ))
            rw [dist_eq_norm' (fderiv ℝ (fderiv ℝ φ) y) (fderiv ℝ (fderiv ℝ φ) z)] at hd
            exact hd)
        simpa [hEdef, hΦdef, hAdef] using hT
      have hΨ0 : ∀ y, y ∉ Metric.cthickening r₀ K → Ψ y = 0 := by
        intro y hy
        have hyK : y ∉ K := fun h => hy (Metric.self_subset_cthickening (δ := r₀) K h)
        have hΦy : Φ y = 0 := by
          change (⨍ x in Metric.ball y r, φ x) = 0
          rw [setAverage_eq]
          have hz0 : (∫ x in Metric.ball y r, φ x) = 0 := by
            apply setIntegral_eq_zero_of_forall_eq_zero
            intro x hx
            apply hφzero
            intro hxK
            have h1 : Metric.infEDist y K ≤ ENNReal.ofReal r := by
              refine le_trans (Metric.infEDist_le_edist_of_mem hxK) ?_
              rw [edist_dist, ENNReal.ofReal_le_ofReal_iff hrpos.le]
              have hx' : ‖y - x‖ < r := by
                rw [mem_ball, dist_eq_norm, norm_sub_rev] at hx
                exact hx
              exact le_of_lt hx'
            exact hy (Metric.mem_cthickening_iff.mpr (h1.trans (ENNReal.ofReal_le_ofReal hrler₀)))
          rw [hz0, smul_zero]
        rw [hΨeq y, hΦy, hφzero y hyK, sub_zero]
      have hcontΨ : Continuous (fun y => Ψ y) := by
        rw [show (fun y => Ψ y) = fun y => Φ y - φ y from funext (fun y => hΨeq y)]
        exact hΦcont.sub hφcont
      have hIntΨ : IntegrableOn (fun y => u y * Ψ y) (Metric.cthickening r₀ K) volume :=
        ((hu.mono hcth_s).mul hcontΨ.continuousOn).integrableOn_compact
          (hKc.cthickening (r := r₀))
      have hIntA : IntegrableOn (fun y => u y * A y) (Metric.cthickening r₀ K) volume :=
        ((hu.mono hcth_s).mul hAcont.continuousOn).integrableOn_compact
          (hKc.cthickening (r := r₀))
      have hIntE : IntegrableOn (fun y => u y * E y) (Metric.cthickening r₀ K) volume :=
        ((hu.mono hcth_s).mul hEcont.continuousOn).integrableOn_compact
          (hKc.cthickening (r := r₀))
      have hInn : 0 ≤ ∫ x in K, φ x * (⨍ y in Metric.ball x r, (u y - u x)) := by
        apply setIntegral_nonneg hKmeas
        intro x hx
        have hb : closedBall x r ⊆ s := (Metric.closedBall_subset_cthickening hx r).trans hcth_r_s
        have hmvp := hMVP x (hKs hx) r hrpos hb
        have hsub : (⨍ y in Metric.ball x r, (u y - u x)) = (⨍ y in Metric.ball x r, u y) - u x :=
          setAverage_ball_sub_const hrpos (hu.mono hb)
        rw [hsub]
        exact mul_nonneg (hφnn x) (by linarith)
      have hIeq : (∫ x in K, φ x * (⨍ y in Metric.ball x r, (u y - u x))) = ∫ y, u y * Ψ y := by
        rw [hΨdef]
        exact integral_mul_setAverage_ball_comm hrpos hKc hφcont subset_rfl huc
      have hJeq : (∫ y, u y * Ψ y) = ∫ y in Metric.cthickening r₀ K, u y * Ψ y :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun y hy => by rw [hΨ0 y hy, mul_zero])).symm
      have hsplit : (∫ y in Metric.cthickening r₀ K, u y * Ψ y)
          = (∫ y in Metric.cthickening r₀ K, u y * A y)
            + ∫ y in Metric.cthickening r₀ K, u y * E y := by
        rw [← integral_add hIntA hIntE]
        apply setIntegral_congr_fun hcth_meas
        intro y _
        change u y * Ψ y = u y * A y + u y * E y
        rw [hΨAE y]; ring
      have hAint : (∫ y in Metric.cthickening r₀ K, u y * A y)
          = r ^ 2 / (2 * ((n : ℝ) + 2)) * (∫ x, u x * Laplacian.laplacian φ x) := by
        have h1 : (∫ y in Metric.cthickening r₀ K, u y * A y)
            = ∫ y in Metric.cthickening r₀ K,
                (r ^ 2 / (2 * ((n : ℝ) + 2))) * (u y * Laplacian.laplacian φ y) := by
          apply setIntegral_congr_fun hcth_meas
          intro y _
          change u y * A y = (r ^ 2 / (2 * ((n : ℝ) + 2))) * (u y * Laplacian.laplacian φ y)
          rw [hAdef]; ring
        have h2 : (∫ y in Metric.cthickening r₀ K,
              (r ^ 2 / (2 * ((n : ℝ) + 2))) * (u y * Laplacian.laplacian φ y))
            = (r ^ 2 / (2 * ((n : ℝ) + 2))) *
                (∫ y in Metric.cthickening r₀ K, u y * Laplacian.laplacian φ y) :=
          integral_const_mul _ _
        have h3 : (∫ y in Metric.cthickening r₀ K, u y * Laplacian.laplacian φ y)
            = ∫ y, u y * Laplacian.laplacian φ y :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero
            (f := fun y => u y * Laplacian.laplacian φ y) (fun y hy => by
            have hyK : y ∉ K := fun h => hy (Metric.self_subset_cthickening (δ := r₀) K h)
            have hev : φ =ᶠ[𝓝 y] 0 := notMem_tsupport_iff_eventuallyEq.mp (by rwa [hKdef] at hyK)
            have h2 := (InnerProductSpace.laplacian_congr_nhds hev).eq_of_nhds
            have h3 : Laplacian.laplacian φ y = 0 := by
              have h2' : Laplacian.laplacian φ y
                  = Laplacian.laplacian (fun _ : EuclideanSpace ℝ (Fin n) => (0:ℝ)) y := h2
              rw [h2']
              exact congrFun (InnerProductSpace.laplacian_const (c := (0:ℝ))) y
            rw [h3, mul_zero]))
        rw [h1, h2, h3]
      have hEbound_int : ‖∫ y in Metric.cthickening r₀ K, u y * E y‖ ≤ η * r ^ 2 * C := by
        have h1 := norm_setIntegral_le_of_norm_le_const (C := Mb * (η * r ^ 2)) hcth_fin
          (fun y hy => by
            rw [Real.norm_eq_abs, abs_mul]
            have hu1 : |u y| ≤ Mb := by rw [← Real.norm_eq_abs]; exact hMle y hy
            have hE1 : |E y| ≤ η * r ^ 2 := hEbound y hy
            calc |u y| * |E y| ≤ Mb * (η * r ^ 2) := mul_le_mul hu1 hE1 (abs_nonneg _) hMbnn
              _ = Mb * (η * r ^ 2) := rfl)
        calc ‖∫ y in Metric.cthickening r₀ K, u y * E y‖
            ≤ Mb * (η * r ^ 2) * (volume : Measure (EuclideanSpace ℝ (Fin n))).real
                (Metric.cthickening r₀ K) := h1
          _ = η * r ^ 2 * C := by rw [hCdef]; ring
      have hnonneg : 0 ≤ ∫ y in Metric.cthickening r₀ K, u y * Ψ y := by
        rw [← hJeq, ← hIeq]; exact hInn
      have hElow : -(η * r ^ 2 * C) ≤ ∫ y in Metric.cthickening r₀ K, u y * E y :=
        neg_le_of_abs_le hEbound_int
      have hcoefpos : 0 < r ^ 2 / (2 * ((n : ℝ) + 2)) := by positivity
      have hKc_eq : (η * r ^ 2 * C) / (r ^ 2 / (2 * ((n : ℝ) + 2))) = η * D := by
        rw [hDdef]; field_simp
      have hEup : ∫ y in Metric.cthickening r₀ K, u y * E y ≤ η * r ^ 2 * C :=
        le_of_abs_le hEbound_int
      have hge : ∫ x, u x * Laplacian.laplacian φ x ≥ -(η * D) := by
        have hchain : r ^ 2 / (2 * ((n : ℝ) + 2)) * (∫ x, u x * Laplacian.laplacian φ x)
            = (∫ y in Metric.cthickening r₀ K, u y * Ψ y)
              - ∫ y in Metric.cthickening r₀ K, u y * E y := by
          rw [hsplit, hAint]; ring
        have h1 : -(η * r ^ 2 * C)
            ≤ (r ^ 2 / (2 * ((n : ℝ) + 2))) * (∫ x, u x * Laplacian.laplacian φ x) := by
          rw [hchain]; linarith [hnonneg, hEup]
        have h2 : -(η * r ^ 2 * C) / (r ^ 2 / (2 * ((n : ℝ) + 2)))
            ≤ (∫ x, u x * Laplacian.laplacian φ x) :=
          (div_le_iff₀ hcoefpos).mpr (by
            rw [mul_comm (∫ x, u x * Laplacian.laplacian φ x) (r ^ 2 / (2 * ((n : ℝ) + 2)))]
            exact h1)
        have h4 : (-(η * r ^ 2 * C)) / (r ^ 2 / (2 * ((n : ℝ) + 2))) = -(η * D) := by
          rw [neg_div, hKc_eq]
        rw [h4] at h2
        exact h2
      have hηD : η * D ≤ ε := by
        rw [hηdef, div_mul_eq_mul_div, div_le_iff₀ hD1pos]
        nlinarith [hDnn, hε]
      linarith [hge, hηD]
    exact le_of_forall_pos_le_add key

end

end Commons.Analysis.Harmonic
