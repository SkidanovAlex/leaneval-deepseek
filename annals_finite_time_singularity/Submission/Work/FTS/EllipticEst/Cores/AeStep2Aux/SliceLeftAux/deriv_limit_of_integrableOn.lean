import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux.SliceLeftAux

open Set Filter MeasureTheory

/-- If `φ` is differentiable on `(0,θ)` with `|φ'| ≤ M` there, and `φ` tends to `0` at `0⁺`,
then `|φ θ| ≤ M * θ`.  (Mean-value-theorem argument: for every `w ∈ (0,θ)` the MVT gives a
point `ξ ∈ (w,θ)` with `φ θ - φ w = φ' ξ · (θ - w)`, then let `w → 0⁺`.) -/
private theorem abs_le_mul_of_deriv_bound {φ : ℝ → ℝ} {M θ : ℝ} (hθ : 0 < θ)
    (hdiff : DifferentiableOn ℝ φ (Ioo 0 θ))
    (hcont : ∀ w ∈ Ioo (0:ℝ) θ, ContinuousOn φ (Icc w θ))
    (hbound : ∀ y ∈ Ioo (0:ℝ) θ, |deriv φ y| ≤ M)
    (htend : Tendsto φ (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0)) :
    |φ θ| ≤ M * θ := by
  have hineq : ∀ w ∈ Ioo (0:ℝ) θ, |φ θ - φ w| ≤ M * (θ - w) := by
    intro w hw
    obtain ⟨ξ, hξ, hξeq⟩ := exists_deriv_eq_slope φ hw.2 (hcont w hw)
      (hdiff.mono (fun z hz => ⟨lt_trans hw.1 hz.1, hz.2⟩))
    have hθw : 0 < θ - w := sub_pos.mpr hw.2
    have h1 : |φ θ - φ w| = |deriv φ ξ| * (θ - w) := by
      rw [hξeq, abs_div, abs_of_pos hθw, div_mul_cancel₀ _ (ne_of_gt hθw)]
    rw [h1]
    exact mul_le_mul_of_nonneg_right (hbound ξ ⟨lt_trans hw.1 hξ.1, hξ.2⟩) (le_of_lt hθw)
  have h1 : Tendsto (fun w : ℝ => |φ θ - φ w|) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds |φ θ|) := by
    have hconst : Tendsto (fun _ : ℝ => φ θ) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (φ θ)) :=
      tendsto_const_nhds
    have := (hconst.sub htend).abs
    simpa using this
  have h2 : Tendsto (fun w : ℝ => M * (θ - w)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (M * θ)) := by
    have hid : Tendsto (fun w : ℝ => w) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (0:ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hconst : Tendsto (fun _ : ℝ => θ) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds θ) :=
      tendsto_const_nhds
    have := (hconst.sub hid).const_mul M
    simpa using this
  exact le_of_tendsto_of_tendsto h1 h2 (Filter.mem_of_superset
    (Filter.mem_of_superset (Filter.inter_mem self_mem_nhdsWithin
      (nhdsWithin_le_nhds (Iio_mem_nhds hθ))) (fun y hy => hy))
    (fun y hy => hineq y hy))

theorem deriv_limit_of_integrableOn {f : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 c))
    (hint : MeasureTheory.IntegrableOn (fun x : ℝ => deriv (deriv f) x) (Set.Ioo 0 c))
    (h0 : Filter.Tendsto f (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0)) :
    ∃ L : ℝ, Filter.Tendsto (deriv f) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds L) ∧
      Filter.Tendsto (fun θ : ℝ => (f θ - L * θ) / θ) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
  -- `f` is `C²` on the open interval; record the two derivative facts we need.
  have hs_open : IsOpen (Ioo (0:ℝ) c) := isOpen_Ioo
  have hderiv1 : ∀ x ∈ Ioo (0:ℝ) c, HasDerivAt f (deriv f x) x := fun x hx =>
    ((hf.contDiffAt (hs_open.mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt
  have hderiv2 : ∀ x ∈ Ioo (0:ℝ) c, HasDerivAt (deriv f) (deriv (deriv f) x) x := fun x hx =>
    (((hf.deriv_of_isOpen hs_open (by norm_num : (1:WithTop ℕ∞) + 1 ≤ 2)).contDiffAt
      (hs_open.mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt
  have hcontf : ContinuousOn f (Ioo (0:ℝ) c) := hf.continuousOn
  -- Fundamental theorem of calculus for `deriv f` on `(0,c)`.
  have hFTC : ∀ x y : ℝ, 0 < x → x ≤ y → y < c →
      ∫ t in x..y, deriv (deriv f) t = deriv f y - deriv f x := by
    intro x y hx hxy hyc
    have hsub : uIcc x y ⊆ Ioo (0:ℝ) c := by
      rw [uIcc_of_le hxy]
      intro z hz
      exact ⟨lt_of_lt_of_le hx hz.1, lt_of_le_of_lt hz.2 hyc⟩
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z hz => hderiv2 z (hsub hz)) ?_
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hxy]
    exact hint.mono_set (fun z hz => ⟨lt_trans hx hz.1, lt_of_le_of_lt hz.2 hyc⟩)
  set a : ℝ := c / 2 with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; linarith
  have ha_lt : a < c := by rw [ha_def]; linarith
  have hInt : ∀ y : ℝ, 0 ≤ y → y ≤ a →
      IntervalIntegrable (fun t : ℝ => deriv (deriv f) t) volume 0 y := by
    intro y hy0 hya
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hy0]
    exact hint.mono_set (fun z hz => ⟨hz.1, lt_of_le_of_lt (le_trans hz.2 hya) ha_lt⟩)
  -- The primitive of the (integrable) second derivative vanishes at `0⁺`.
  have hG : Tendsto (fun x : ℝ => ∫ t in (0:ℝ)..x, deriv (deriv f) t)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
    have hint_s : IntegrableOn (fun t : ℝ => deriv (deriv f) t) (Ioc 0 a) :=
      hint.mono_set (fun z hz => ⟨hz.1, lt_of_le_of_lt hz.2 ha_lt⟩)
    have hμ : Integrable (fun t : ℝ => deriv (deriv f) t) (volume.restrict (Ioc 0 a)) := hint_s
    have hmeas : Tendsto (fun x : ℝ => (volume.restrict (Ioc 0 a)) (Ioc 0 x))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
      have hof : Tendsto (fun x : ℝ => ENNReal.ofReal x) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
        have h1 : Tendsto (fun x : ℝ => x) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (0:ℝ)) :=
          tendsto_id.mono_left nhdsWithin_le_nhds
        have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp h1
        simpa [Function.comp_def] using h2
      refine Tendsto.congr' ?_ hof
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds ha_pos)] with x hx hxa
      have hxle : x ≤ a := le_of_lt hxa
      have hsub : Ioc 0 x ⊆ Ioc 0 a := fun z hz => ⟨hz.1, le_trans hz.2 hxle⟩
      rw [Measure.restrict_apply measurableSet_Ioc, inter_eq_self_of_subset_left hsub,
        Real.volume_Ioc, sub_zero]
    have hlim := hμ.tendsto_setIntegral_nhds_zero hmeas
    have hcongr : (fun x : ℝ => ∫ t in Ioc 0 x, deriv (deriv f) t ∂(volume.restrict (Ioc 0 a)))
        =ᶠ[nhdsWithin (0:ℝ) (Ioi 0)] (fun x : ℝ => ∫ t in (0:ℝ)..x, deriv (deriv f) t) := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds ha_pos)] with x hx hxa
      have hxle : x ≤ a := le_of_lt hxa
      have hsub : Ioc 0 x ⊆ Ioc 0 a := fun z hz => ⟨hz.1, le_trans hz.2 hxle⟩
      rw [Measure.restrict_restrict_of_subset hsub, intervalIntegral.integral_of_le (le_of_lt hx)]
    exact hlim.congr' hcongr
  -- The candidate limit.
  set L : ℝ := deriv f a - ∫ t in (0:ℝ)..a, deriv (deriv f) t with hL_def
  have heq : (fun x : ℝ => L + ∫ t in (0:ℝ)..x, deriv (deriv f) t)
      =ᶠ[nhdsWithin (0:ℝ) (Ioi 0)] deriv f := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds ha_pos)] with x hx hxa
    have hxa' : x ≤ a := le_of_lt hxa
    have h1 := intervalIntegral.integral_interval_sub_left (hInt a (le_of_lt ha_pos) le_rfl)
      (hInt x (le_of_lt hx) hxa')
    have h2 := hFTC x a hx hxa' ha_lt
    rw [hL_def]
    linarith
  have hL : Tendsto (deriv f) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds L) := by
    have h1 : Tendsto (fun x : ℝ => L + ∫ t in (0:ℝ)..x, deriv (deriv f) t)
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds L) := by
      simpa using (hG.const_add L)
    exact h1.congr' heq
  refine ⟨L, hL, ?_⟩
  -- Second part: `(f θ - L θ)/θ → 0`, by the mean-value-theorem slope bound.
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hEv := Metric.tendsto_nhds.mp hL (ε / 2) hε2
  obtain ⟨δ, hδpos, hδball⟩ := Metric.mem_nhdsWithin_iff.mp hEv
  have hminpos : 0 < min δ a := lt_min hδpos ha_pos
  have hIoo : Ioo (0:ℝ) (min δ a) ∈ nhdsWithin (0:ℝ) (Ioi 0) :=
    Filter.mem_of_superset (Filter.inter_mem self_mem_nhdsWithin
      (nhdsWithin_le_nhds (Iio_mem_nhds hminpos))) (fun y hy => hy)
  refine Filter.mem_of_superset hIoo ?_
  intro θ hθ
  have hθδ : θ < δ := lt_of_lt_of_le hθ.2 (min_le_left δ a)
  have hθa : θ < a := lt_of_lt_of_le hθ.2 (min_le_right δ a)
  have hθ0 : 0 < θ := hθ.1
  have hb : ∀ y ∈ Ioo (0:ℝ) θ, |deriv f y - L| ≤ ε / 2 := by
    intro y hy
    have hyδ : y < δ := lt_trans hy.2 hθδ
    have hymem : y ∈ Metric.ball (0:ℝ) δ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hy.1]
      exact hyδ
    have hthis : dist (deriv f y) L < ε / 2 := hδball ⟨hymem, hy.1⟩
    rw [Real.dist_eq] at hthis
    exact le_of_lt hthis
  have hderivφ : ∀ y ∈ Ioo (0:ℝ) θ, deriv (fun y : ℝ => f y - L * y) y = deriv f y - L := by
    intro y hy
    have hyc : y ∈ Ioo (0:ℝ) c := ⟨hy.1, lt_trans hy.2 (lt_trans hθa ha_lt)⟩
    have h1 := hderiv1 y hyc
    have h2 : HasDerivAt (fun y : ℝ => L * y) L y := by
      simpa using (hasDerivAt_id y).const_mul L
    exact (h1.sub h2).deriv
  have hφdiff : DifferentiableOn ℝ (fun y : ℝ => f y - L * y) (Ioo (0:ℝ) θ) := by
    refine DifferentiableOn.sub ?_ ?_
    · exact (hf.differentiableOn (by norm_num)).mono
        (fun z hz => ⟨hz.1, lt_trans hz.2 (lt_trans hθa ha_lt)⟩)
    · exact (differentiableOn_id.const_mul L)
  have hφcont : ∀ w ∈ Ioo (0:ℝ) θ, ContinuousOn (fun y : ℝ => f y - L * y) (Icc w θ) := by
    intro w hw
    refine (hcontf.mono ?_).sub ?_
    · intro z hz
      exact ⟨lt_of_lt_of_le hw.1 hz.1, lt_of_le_of_lt hz.2 (lt_trans hθa ha_lt)⟩
    · exact (continuous_const.mul continuous_id).continuousOn
  have hbound : ∀ y ∈ Ioo (0:ℝ) θ, |deriv (fun y : ℝ => f y - L * y) y| ≤ ε / 2 := by
    intro y hy
    rw [hderivφ y hy]
    exact hb y hy
  have hφ0 : Tendsto (fun y : ℝ => f y - L * y) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
    have hid : Tendsto (fun y : ℝ => y) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (0:ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hc' : Tendsto (fun _ : ℝ => L) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds L) := tendsto_const_nhds
    have := h0.sub (hc'.mul hid)
    simpa using this
  have hkey := abs_le_mul_of_deriv_bound hθ0 hφdiff hφcont hbound hφ0
  show dist ((f θ - L * θ) / θ) 0 < ε
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hθ0, div_lt_iff₀ hθ0]
  calc |f θ - L * θ| ≤ ε / 2 * θ := hkey
    _ < ε * θ := by nlinarith [hθ0, hε]

end Work.FTS.EllipticEst.Cores.AeStep2Aux.SliceLeftAux
