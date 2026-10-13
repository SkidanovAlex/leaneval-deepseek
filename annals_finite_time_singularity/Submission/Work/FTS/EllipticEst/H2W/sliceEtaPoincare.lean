import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.cs_integral
import Submission.Work.FTS.EllipticEst.H2W.SliceEtaFacts
import Submission.Work.FTS.EllipticEst.H2W.HardyPrimEta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

/-!
# The weighted slice Poincaré inequality with the angular weight `sin(2θ)^{-η}`

For a function `u` that is `C^∞` on the open interval `(0, π/2)`, tends to `0` at both endpoints
and has `∫_{Iθ} (u'')² sin(2θ)^{-η} < ∞`, we prove that `u` and `u'` are square integrable against
the weight `sin(2θ)^{-η}` and that both weighted norms are controlled by the weighted norm of the
second derivative.  The proof writes `u' = c₀ + V` with `V = ∫_0^θ u''` the primitive of `u''`;
the constant `c₀` is pinned down by `∫_{Iθ} u' = 0` (a consequence of the vanishing endpoint
limits, via the fundamental theorem of calculus with limits) and is bounded by
`c₀² ≤ (2/π) ∫_{Iθ} V²`; the weighted Hardy inequality `HardyPrimEta` (primitive form) is then
applied to `g = u''` and to `g = u'`.
-/

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The iterated derivatives of a function that is `C^n` on the open interval `(0, π/2)` for every
`n` are again `C^m` there, for every `m`. -/
private theorem contDiffOn_iterate_deriv {u : ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo (0 : ℝ) (Real.pi / 2))) (k : ℕ) :
    ∀ m : ℕ, ContDiffOn ℝ m ((deriv^[k]) u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  induction k with
  | zero => intro m; simpa using hu m
  | succ k ih =>
      intro m
      have h1 : ContDiffOn ℝ (m + 1) ((deriv^[k]) u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        ih (m + 1)
      have h2 : ContDiffOn ℝ m (deriv ((deriv^[k]) u)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        ContDiffOn.deriv_of_isOpen h1 isOpen_Ioo (by exact_mod_cast le_refl (m + 1))
      simpa only [Function.iterate_succ_apply'] using h2

/-- The first derivatives of a function in the class of the slice Poincaré lemma. -/
private theorem contDiffOn_deriv_one {u : ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo (0 : ℝ) (Real.pi / 2))) (m : ℕ) :
    ContDiffOn ℝ m (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  simpa using contDiffOn_iterate_deriv hu 1 m

/-- The second derivatives of a function in the class of the slice Poincaré lemma. -/
private theorem contDiffOn_deriv_deriv {u : ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo (0 : ℝ) (Real.pi / 2))) (m : ℕ) :
    ContDiffOn ℝ m (deriv (deriv u)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  simpa using contDiffOn_iterate_deriv hu 2 m

/-- A closed unordered interval contained in `[0, π/2]` is contained in `Iθ`. -/
private theorem uIcc_subset_Iθ {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : a ≤ Real.pi / 2)
    (hb' : b ≤ Real.pi / 2) : Set.uIcc a b ⊆ Work.Spaces.Iθ := by
  intro x hx
  exact ⟨le_trans (le_min ha hb) hx.1, le_trans hx.2 (max_le ha' hb')⟩

/-- An integrable function on `Iθ` is interval integrable on `[0, π/2]`. -/
private theorem intervalIntegrable_of_integrableOn_Iθ {f : ℝ → ℝ}
    (h : MeasureTheory.IntegrableOn f Work.Spaces.Iθ) :
    IntervalIntegrable f volume 0 (Real.pi / 2) := by
  have h' : MeasureTheory.IntegrableOn f (Set.uIcc (0 : ℝ) (Real.pi / 2)) volume := by
    rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2), ← Work.Spaces.Iθ]
    exact h
  exact h'.intervalIntegrable

theorem sliceEtaPoincare :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ → ℝ,
      (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) →
      Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn
        (fun θ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ C * ∫ θ in Work.Spaces.Iθ,
            (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ ∧
      (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ C * ∫ θ in Work.Spaces.Iθ,
            (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  obtain ⟨K, hKpos, hKmain⟩ := HardyPrimEta
  obtain ⟨hwint, hwle, hone, hwnn, hwcont⟩ := SliceEtaFacts
  refine ⟨(2 * 10 ^ 4 + 2) * (K + K ^ 2), ?_, ?_⟩
  · have h1 : (0 : ℝ) < 2 * 10 ^ 4 + 2 := by norm_num
    have h2 : (0 : ℝ) < K + K ^ 2 := by nlinarith
    exact mul_pos h1 h2
  · intro u hu hlim0 hlim1 hint
    have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
    have hpi4 : (0 : ℝ) < Real.pi / 4 := by positivity
    -- the open interval and `Iθ` carry the same restricted measure
    have hIoo_ae : volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
        = volume.restrict Work.Spaces.Iθ :=
      Measure.restrict_congr_set (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)
    have hcontW : ContinuousOn (fun θ => Work.FTS.EllipticEst.sEta θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      fun θ hθ => (hwcont θ hθ).continuousWithinAt
    have hone_ae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        1 ≤ Work.FTS.EllipticEst.sEta θ := by
      rw [← hIoo_ae]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact hone θ hθ
    -- smoothness of `u'` and `u''` on the open interval
    have hderiv1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt u (deriv u θ) θ :=
      fun θ hθ =>
        (((hu 1).differentiableOn_one).differentiableAt (isOpen_Ioo.mem_nhds hθ)).hasDerivAt
    have hderiv2 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        HasDerivAt (deriv u) (deriv (deriv u) θ) θ := fun θ hθ =>
      (((contDiffOn_deriv_one hu 1).differentiableOn_one).differentiableAt
        (isOpen_Ioo.mem_nhds hθ)).hasDerivAt
    have hcontD1 : ContinuousOn (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (contDiffOn_deriv_one hu 1).continuousOn
    have hcontD2 : ContinuousOn (deriv (deriv u)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (contDiffOn_deriv_deriv hu 1).continuousOn
    -- the weighted norm of `u''`
    set R : ℝ := ∫ θ in Work.Spaces.Iθ,
      (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ with hR
    have hRnn : 0 ≤ R := by
      rw [hR]
      exact setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (hwnn θ hθ))
    -- `(u'')²` and `u''` are integrable on `Iθ`
    have hu2sq_int : IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2) Work.Spaces.Iθ := by
      refine Integrable.mono'
        (g := fun θ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) hint ?_ ?_
      · rw [← hIoo_ae]
        exact (hcontD2.pow 2).aestronglyMeasurable measurableSet_Ioo
      · filter_upwards [hone_ae] with θ hθ
        have h2 : (0 : ℝ) ≤ (deriv (deriv u) θ) ^ 2 := sq_nonneg _
        rw [Real.norm_eq_abs, abs_of_nonneg h2]
        nlinarith [h2, hθ]
    have hu2_int : IntegrableOn (fun θ => deriv (deriv u) θ) Work.Spaces.Iθ := by
      refine Integrable.mono'
        (g := fun θ => (1 / 2) * ((deriv (deriv u) θ) ^ 2 + 1)) ?_ ?_ ?_
      · exact (hu2sq_int.add (integrableOn_const (s := Work.Spaces.Iθ) (C := (1 : ℝ))
          (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top))).const_mul
          (1 / 2)
      · rw [← hIoo_ae]
        exact hcontD2.aestronglyMeasurable measurableSet_Ioo
      · filter_upwards with θ
        rw [Real.norm_eq_abs]
        refine abs_le.2 ⟨?_, ?_⟩
        · nlinarith [sq_nonneg (deriv (deriv u) θ + 1)]
        · nlinarith [sq_nonneg (deriv (deriv u) θ - 1)]
    -- the primitive `V` of `u''`
    set V : ℝ → ℝ := fun θ => ∫ t in (0 : ℝ)..θ, deriv (deriv u) t with hV
    have hVval : ∀ θ : ℝ, V θ = ∫ t in (0 : ℝ)..θ, deriv (deriv u) t := fun θ => by simp [hV]
    have hVcont : ContinuousOn V Work.Spaces.Iθ := by
      have h : ContinuousOn (fun θ : ℝ => ∫ t in (0 : ℝ)..θ, deriv (deriv u) t)
          (Set.uIcc (0 : ℝ) (Real.pi / 2)) :=
        intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := Real.pi / 2)
          (f := fun t => deriv (deriv u) t) (by
            rw [Set.uIcc_of_le hpi.le, ← Work.Spaces.Iθ]; exact hu2_int)
      rwa [Set.uIcc_of_le hpi.le, ← Work.Spaces.Iθ] at h
    have hIθ_compact : IsCompact Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ]; exact isCompact_Icc
    obtain ⟨CV, hCV⟩ := hIθ_compact.exists_bound_of_continuousOn hVcont
    have hV2_int : IntegrableOn (fun θ => (V θ) ^ 2) Work.Spaces.Iθ := by
      refine Integrable.mono' (g := fun _ : ℝ => (max CV 0) ^ 2) ?_ ?_ ?_
      · exact integrableOn_const (s := Work.Spaces.Iθ) (C := (max CV 0) ^ 2)
          (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      · exact (hVcont.pow 2).aestronglyMeasurable measurableSet_Icc
      · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with θ hθ
        have hb : ‖V θ‖ ≤ max CV 0 := (hCV θ hθ).trans (le_max_left _ _)
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        calc (V θ) ^ 2 = ‖V θ‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
          _ ≤ (max CV 0) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    have hV_memLp : MemLp V 2 (volume.restrict Work.Spaces.Iθ) := by
      rw [memLp_two_iff_integrable_sq (hVcont.aestronglyMeasurable measurableSet_Icc)]
      exact hV2_int
    have h1_memLp : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict Work.Spaces.Iθ) := by
      rw [memLp_two_iff_integrable_sq aestronglyMeasurable_const]
      simpa using (integrableOn_const (s := Work.Spaces.Iθ) (C := (1 : ℝ))
        (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    have hvol : (∫ θ in Work.Spaces.Iθ, (1 : ℝ)) = Real.pi / 2 := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, Measure.real_def,
        Work.Spaces.Iθ, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
      ring
    have hVsq_le : (∫ θ in Work.Spaces.Iθ, V θ) ^ 2 ≤ (Real.pi / 2)
        * ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 := by
      have hcs := Work.Spaces.cs_integral (u := V) (v := fun _ : ℝ => (1 : ℝ))
        (s := Work.Spaces.Iθ) hV_memLp h1_memLp
      simpa [mul_one, one_pow, hvol, mul_comm] using hcs
    -- the constant `c₀` and the identity `u' = c₀ + V`
    set c₀ : ℝ := deriv u (Real.pi / 4) - V (Real.pi / 4) with hc0
    have hFTCmid : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        ∫ t in (Real.pi / 4)..θ, deriv (deriv u) t = deriv u θ - deriv u (Real.pi / 4) := by
      intro θ hθ
      have hsub1 : Set.Icc (Real.pi / 4) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
        ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, hθ.2]⟩
      have hsub2 : Set.Icc θ (Real.pi / 4) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
        ⟨by linarith [hx.1, hθ.1], by linarith [hx.2, Real.pi_pos]⟩
      have hI1 : Set.uIcc (Real.pi / 4) θ ⊆ Work.Spaces.Iθ :=
        uIcc_subset_Iθ (by positivity) hθ.1.le (by linarith [Real.pi_pos]) hθ.2.le
      have hI2 : Set.uIcc θ (Real.pi / 4) ⊆ Work.Spaces.Iθ :=
        uIcc_subset_Iθ hθ.1.le (by positivity) hθ.2.le (by linarith [Real.pi_pos])
      rcases le_total (Real.pi / 4) θ with hle | hle
      · exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle (hcontD1.mono hsub1)
          (fun x hx => hderiv2 x (hsub1 ⟨hx.1.le, hx.2.le⟩))
          (hu2_int.mono_set hI1).intervalIntegrable
      · have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle (hcontD1.mono hsub2)
          (fun x hx => hderiv2 x (hsub2 ⟨hx.1.le, hx.2.le⟩))
          (hu2_int.mono_set hI2).intervalIntegrable
        have hsym := intervalIntegral.integral_symm (μ := volume) (a := θ) (b := Real.pi / 4)
          (f := fun t => deriv (deriv u) t)
        linarith [h, hsym]
    have hdecomp : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), deriv u θ = c₀ + V θ := by
      intro θ hθ
      have hI1 : Set.uIcc (0 : ℝ) (Real.pi / 4) ⊆ Work.Spaces.Iθ :=
        uIcc_subset_Iθ le_rfl (by positivity) (by linarith [Real.pi_pos])
          (by linarith [Real.pi_pos])
      have hI2 : Set.uIcc (Real.pi / 4) θ ⊆ Work.Spaces.Iθ :=
        uIcc_subset_Iθ (by positivity) hθ.1.le (by linarith [Real.pi_pos]) hθ.2.le
      have hint1 : IntervalIntegrable (fun t => deriv (deriv u) t) volume (0 : ℝ)
          (Real.pi / 4) := (hu2_int.mono_set hI1).intervalIntegrable
      have hint2 : IntervalIntegrable (fun t => deriv (deriv u) t) volume (Real.pi / 4) θ :=
        (hu2_int.mono_set hI2).intervalIntegrable
      have hadd := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
      rw [hVval θ, hc0, hVval (Real.pi / 4), ← hadd, hFTCmid θ hθ]
      ring
    -- `u'` is bounded, hence integrable
    have hderiv_bound : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        ‖deriv u θ‖ ≤ |c₀| + CV := by
      intro θ hθ
      have hVb : |V θ| ≤ CV := by
        have h := hCV θ (⟨hθ.1.le, hθ.2.le⟩ : θ ∈ Work.Spaces.Iθ)
        rwa [Real.norm_eq_abs] at h
      rw [hdecomp θ hθ, Real.norm_eq_abs]
      calc |c₀ + V θ| ≤ |c₀| + |V θ| := abs_add_le _ _
        _ ≤ |c₀| + CV := by linarith
    have hderiv_int : IntegrableOn (fun θ => deriv u θ) Work.Spaces.Iθ := by
      refine Integrable.mono' (g := fun _ : ℝ => |c₀| + CV) ?_ ?_ ?_
      · exact integrableOn_const (s := Work.Spaces.Iθ) (C := |c₀| + CV)
          (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      · rw [← hIoo_ae]
        exact hcontD1.aestronglyMeasurable measurableSet_Ioo
      · rw [← hIoo_ae]
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
        exact hderiv_bound θ hθ
    -- `∫_{Iθ} u' = 0`, from the two vanishing endpoint limits
    have hzero : ∫ θ in (0 : ℝ)..(Real.pi / 2), deriv u θ = 0 := by
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a := (0 : ℝ))
        (b := Real.pi / 2) (f := u) (f' := fun θ => deriv u θ) hpi hderiv1
        (intervalIntegrable_of_integrableOn_Iθ hderiv_int) hlim0 hlim1
      simpa using h
    have hkey : ∀ f : ℝ → ℝ,
        (∫ θ in Work.Spaces.Iθ, f θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), f θ := by
      intro f
      rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hpi.le]
    -- the identity `c₀ = -(2/π) ∫_{Iθ} V`
    have hc0_eq : c₀ = -(2 / Real.pi) * ∫ θ in Work.Spaces.Iθ, V θ := by
      have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ Real.pi / 2 := by
        rw [MeasureTheory.ae_iff]
        have hset : {x : ℝ | ¬(x ≠ Real.pi / 2)} = {Real.pi / 2} := by
          ext x; simp
        rw [hset]
        exact MeasureTheory.measure_singleton (Real.pi / 2)
      have hcongr_int : ∫ θ in (0 : ℝ)..(Real.pi / 2), deriv u θ
          = ∫ θ in (0 : ℝ)..(Real.pi / 2), (c₀ + V θ) := by
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards [hne] with x hx hmem
        rw [Set.uIoc_of_le hpi.le] at hmem
        exact hdecomp x ⟨hmem.1, lt_of_le_of_ne hmem.2 hx⟩
      have hsplit : ∫ θ in (0 : ℝ)..(Real.pi / 2), (c₀ + V θ)
          = c₀ * (Real.pi / 2) + ∫ θ in (0 : ℝ)..(Real.pi / 2), V θ := by
        rw [intervalIntegral.integral_add intervalIntegrable_const
          (hVcont.intervalIntegrable_of_Icc hpi.le), intervalIntegral.integral_const]
        ring
      have hval : c₀ * (Real.pi / 2) + ∫ θ in (0 : ℝ)..(Real.pi / 2), V θ = 0 := by
        rw [← hsplit, ← hcongr_int, hzero]
      rw [hkey V] at ⊢
      rw [← hkey V] at hval
      field_simp at hval ⊢
      linarith
    -- `c₀²` is controlled by the weighted norm of `V`
    have hc0sq : c₀ ^ 2 ≤ (2 / Real.pi) * ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 := by
      have hsq : c₀ ^ 2 = (2 / Real.pi) ^ 2 * (∫ θ in Work.Spaces.Iθ, V θ) ^ 2 := by
        rw [hc0_eq]; ring
      rw [hsq]
      calc (2 / Real.pi) ^ 2 * (∫ θ in Work.Spaces.Iθ, V θ) ^ 2
          ≤ (2 / Real.pi) ^ 2 * ((Real.pi / 2) * ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2) :=
            mul_le_mul_of_nonneg_left hVsq_le (by positivity)
        _ = (2 / Real.pi) * ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 := by
            have hc : (2 / Real.pi) ^ 2 * (Real.pi / 2) = 2 / Real.pi := by field_simp
            rw [← mul_assoc, hc]
    -- the weighted Hardy inequality for the datum `u''`
    have hHard2 := hKmain (fun θ => deriv (deriv u) θ) hu2_int hint
      (fun θ hθ => hcontD2.continuousAt (isOpen_Ioo.mem_nhds hθ))
    have hfun_prim : (fun θ => (∫ t in (0 : ℝ)..θ, deriv (deriv u) t) ^ 2
          * Work.FTS.EllipticEst.sEta θ)
        = fun θ => (V θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
      funext θ; rw [hVval θ]
    have hV2w_int : IntegrableOn
        (fun θ => (V θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
      hHard2.1.congr (Filter.Eventually.of_forall (congrFun hfun_prim))
    have hV2w_le : ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 * Work.FTS.EllipticEst.sEta θ ≤ K * R := by
      have h1 : ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
          = ∫ θ in Work.Spaces.Iθ,
              (∫ t in (0 : ℝ)..θ, deriv (deriv u) t) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
        rw [hfun_prim]
      rw [h1, hR]
      exact hHard2.2
    have hV2_le_w : ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
      refine integral_mono_ae hV2_int hV2w_int ?_
      filter_upwards [hone_ae] with θ hθ
      nlinarith [sq_nonneg (V θ)]
    have hc0sq_le : c₀ ^ 2 ≤ K * R := by
      have h2π : (2 / Real.pi : ℝ) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [Real.pi_gt_three]
      have hKR : 0 ≤ K * R := mul_nonneg (le_of_lt hKpos) hRnn
      calc c₀ ^ 2 ≤ (2 / Real.pi) * ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 := hc0sq
        _ ≤ (2 / Real.pi) * (K * R) := by
            refine mul_le_mul_of_nonneg_left (le_trans hV2_le_w hV2w_le) (by positivity)
        _ ≤ K * R := by
            calc (2 / Real.pi) * (K * R) ≤ 1 * (K * R) :=
                  mul_le_mul_of_nonneg_right h2π hKR
              _ = K * R := one_mul _
    -- `u` is the primitive of `u'`
    have hu_eq : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), u θ = ∫ t in (0 : ℝ)..θ, deriv u t := by
      intro θ hθ
      have hcont : ContinuousAt u θ :=
        (hu 1).continuousOn.continuousAt (isOpen_Ioo.mem_nhds hθ)
      have hsub : Set.uIcc (0 : ℝ) θ ⊆ Work.Spaces.Iθ :=
        uIcc_subset_Iθ le_rfl hθ.1.le (by linarith [Real.pi_pos]) hθ.2.le
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a := (0 : ℝ))
        (b := θ) hθ.1 (fun x hx => hderiv1 x ⟨hx.1, lt_of_lt_of_le hx.2 hθ.2.le⟩)
        (hderiv_int.mono_set hsub).intervalIntegrable hlim0
        (hcont.tendsto.mono_left nhdsWithin_le_nhds)
      simpa using h.symm
    -- the weighted Hardy inequality for the datum `u'`
    have hdom_int : IntegrableOn
        (fun θ => (2 * c₀ ^ 2 + 2 * (V θ) ^ 2) * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ := by
      refine ((hwint.const_mul (2 * c₀ ^ 2)).add (hV2w_int.const_mul 2)).congr
        (Filter.Eventually.of_forall fun θ => ?_)
      simp only [Pi.add_apply]
      ring
    have hae_dom : (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ᵐ[volume.restrict Work.Spaces.Iθ]
          (fun θ => (2 * c₀ ^ 2 + 2 * (V θ) ^ 2) * Work.FTS.EllipticEst.sEta θ) := by
      rw [← hIoo_ae]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hs : 0 ≤ Work.FTS.EllipticEst.sEta θ := hwnn θ ⟨hθ.1.le, hθ.2.le⟩
      have hpt : (deriv u θ) ^ 2 ≤ 2 * c₀ ^ 2 + 2 * (V θ) ^ 2 := by
        rw [hdecomp θ hθ]
        nlinarith [sq_nonneg (c₀ - V θ)]
      exact mul_le_mul_of_nonneg_right hpt hs
    have hderivsq_int : IntegrableOn
        (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
      refine Integrable.mono' (g := fun θ => (2 * c₀ ^ 2 + 2 * (V θ) ^ 2)
        * Work.FTS.EllipticEst.sEta θ) hdom_int ?_ ?_
      · rw [← hIoo_ae]
        exact ((hcontD1.pow 2).mul hcontW).aestronglyMeasurable measurableSet_Ioo
      · rw [← hIoo_ae]
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
        have hs : 0 ≤ Work.FTS.EllipticEst.sEta θ := hwnn θ ⟨hθ.1.le, hθ.2.le⟩
        have hpt : (deriv u θ) ^ 2 ≤ 2 * c₀ ^ 2 + 2 * (V θ) ^ 2 := by
          rw [hdecomp θ hθ]
          nlinarith [sq_nonneg (c₀ - V θ)]
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hs)]
        exact mul_le_mul_of_nonneg_right hpt hs
    have hHard1 := hKmain (fun θ => deriv u θ) hderiv_int hderivsq_int
      (fun θ hθ => hcontD1.continuousAt (isOpen_Ioo.mem_nhds hθ))
    have hae_eq : (fun θ => (∫ t in (0 : ℝ)..θ, deriv u t) ^ 2
          * Work.FTS.EllipticEst.sEta θ)
        =ᵐ[volume.restrict Work.Spaces.Iθ]
          (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
      rw [← hIoo_ae]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      show (∫ t in (0 : ℝ)..θ, deriv u t) ^ 2 * Work.FTS.EllipticEst.sEta θ
        = (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      rw [hu_eq θ hθ]
    have hu2w_int : IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ := hHard1.1.congr hae_eq
    have hu2w_le : ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        ≤ K * ∫ θ in Work.Spaces.Iθ,
            (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
      rw [← integral_congr_ae hae_eq]
      exact hHard1.2
    -- `∫ (u')² w ≤ (2·10⁴ + 2) K R`
    have hderivsq_le : ∫ θ in Work.Spaces.Iθ,
        (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ ≤ (2 * 10 ^ 4 + 2) * K * R := by
      have hmono : ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
          ≤ ∫ θ in Work.Spaces.Iθ,
              (2 * c₀ ^ 2 + 2 * (V θ) ^ 2) * Work.FTS.EllipticEst.sEta θ :=
        integral_mono_ae hderivsq_int hdom_int hae_dom
      have hsplit2 : ∫ θ in Work.Spaces.Iθ,
          (2 * c₀ ^ 2 + 2 * (V θ) ^ 2) * Work.FTS.EllipticEst.sEta θ
          = (2 * c₀ ^ 2) * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ)
            + 2 * ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
        have hcongr : ∫ θ in Work.Spaces.Iθ,
            (2 * c₀ ^ 2 + 2 * (V θ) ^ 2) * Work.FTS.EllipticEst.sEta θ
            = ∫ θ in Work.Spaces.Iθ,
                ((2 * c₀ ^ 2) * Work.FTS.EllipticEst.sEta θ
                  + 2 * ((V θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
          show (2 * c₀ ^ 2 + 2 * (V θ) ^ 2) * Work.FTS.EllipticEst.sEta θ
            = (2 * c₀ ^ 2) * Work.FTS.EllipticEst.sEta θ
              + 2 * ((V θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          ring
        rw [hcongr, integral_add (hwint.const_mul (2 * c₀ ^ 2)) (hV2w_int.const_mul 2),
          integral_const_mul, integral_const_mul]
      rw [hsplit2] at hmono
      have hterm1 : (2 * c₀ ^ 2) * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ)
          ≤ (2 * c₀ ^ 2) * 10 ^ 4 :=
        mul_le_mul_of_nonneg_left hwle (by positivity)
      have hterm2 : 2 * ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
          ≤ 2 * (K * R) := mul_le_mul_of_nonneg_left hV2w_le (by norm_num)
      have hcombine : (2 * c₀ ^ 2) * 10 ^ 4 + 2 * (K * R) ≤ (2 * 10 ^ 4 + 2) * K * R := by
        nlinarith [hc0sq_le, hRnn, hKpos]
      linarith [hmono, hterm1, hterm2, hcombine]
    refine ⟨hu2w_int, hderivsq_int, ?_, ?_⟩
    · have h1 : ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
          ≤ K * ((2 * 10 ^ 4 + 2) * K * R) :=
        le_trans hu2w_le (mul_le_mul_of_nonneg_left hderivsq_le (le_of_lt hKpos))
      have h2 : K * ((2 * 10 ^ 4 + 2) * K * R) = (2 * 10 ^ 4 + 2) * K ^ 2 * R := by ring
      have h3 : (2 * 10 ^ 4 + 2) * K ^ 2 * R
          ≤ ((2 * 10 ^ 4 + 2) * (K + K ^ 2)) * R := by
        refine mul_le_mul_of_nonneg_right ?_ hRnn
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (le_of_lt hKpos)) (by norm_num)
      linarith [h1, h3, le_of_eq h2]
    · have hC : (2 * 10 ^ 4 + 2) * K ≤ (2 * 10 ^ 4 + 2) * (K + K ^ 2) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg K)) (by norm_num)
      exact le_trans hderivsq_le (mul_le_mul_of_nonneg_right hC hRnn)

end

end Work.FTS.EllipticEst.H2W
