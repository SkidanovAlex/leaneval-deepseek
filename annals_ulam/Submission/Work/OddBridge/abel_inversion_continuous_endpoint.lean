import Mathlib
import Submission.Work.OddBridge.Defs
import Submission.Work.OddVolterra.Abel.abel_inversion_b1

/-!
# Abel inversion on `(a,1)` with `Q` only smooth on compact subintervals

This file proves `Work.OddBridge.abel_inversion_continuous_endpoint`: the inverse direction of
the Abel/Volterra equivalence with `b = 1`, where the right-hand side `Q` is assumed only
continuous on `[a,1]` and `C²` on each compact subinterval `[a,c]`, `c < 1`.

The structure is the one of `Work.OddVolterra.Abel.abel_inversion_b1`: the only input that
lemma needs beyond the standing hypotheses is the differentiability of the Abel transform
`u ↦ ∫_v∈(u,1) (√(v-u))⁻¹ • Q v` on `(a,1)`.  That is supplied here
(`differentiableAt_abel_transform_of_smoothOn_compacts`): at an interior point `s` one splits
the integral at a point `c` with `s < c < 1`.  The piece on `(u,c]` is handled by the elliptic
substitution `v = u + (c-u)t²` (`Commons.Analysis.Abel.differentiableAt_intervalIntegral_invSqrt_Q`,
which needs `C²` on `[a,c]` only), and the piece on `[c,1]` by differentiating under the integral
sign — there the weight `(√(v-u))⁻¹` is smooth, since `v ≥ c > u`.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddBridge

noncomputable section

/-- The derivative of `u ↦ (√(v - u))⁻¹` at `s`, for `v > s`. -/
lemma hasDerivAt_inv_sqrt_sub {v s : ℝ} (hs : 0 < v - s) :
    HasDerivAt (fun u : ℝ => (Real.sqrt (v - u))⁻¹)
      (1 / 2 * ((Real.sqrt (v - s))⁻¹) ^ 3) s := by
  have hs' : v - s ≠ 0 := ne_of_gt hs
  have hpos : 0 < Real.sqrt (v - s) := Real.sqrt_pos.mpr hs
  have hlin : HasDerivAt (fun u : ℝ => v - u) (-1) s := (hasDerivAt_id s).const_sub v
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (v - s))) (v - s) :=
    Real.hasDerivAt_sqrt hs'
  have hcomp : HasDerivAt (fun u : ℝ => Real.sqrt (v - u))
      ((1 / (2 * Real.sqrt (v - s))) * (-1)) s :=
    HasDerivAt.comp (x := s) hsqrt hlin
  have hinv : HasDerivAt (fun u : ℝ => (Real.sqrt (v - u))⁻¹)
      (-((1 / (2 * Real.sqrt (v - s))) * (-1)) / (Real.sqrt (v - s)) ^ 2) s :=
    hcomp.inv (ne_of_gt hpos)
  refine hinv.congr_deriv ?_
  rw [div_eq_mul_inv]
  field_simp

/-- **Differentiability of the Abel transform of `Q` at an interior point.**  If `Q` is continuous
on `[a,1]` and `C²` on each `[a,c]` with `c < 1`, then `u ↦ ∫_v∈(u,1) (√(v-u))⁻¹ • Q v` is
differentiable at every `s ∈ (a,1)`. -/
lemma differentiableAt_abel_transform_of_smoothOn_compacts {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {a : ℝ} {Q : ℝ → E}
    (hQcont : ContinuousOn Q (Set.Icc a 1))
    (hQsmooth : ∀ c : ℝ, a < c → c < 1 → ContDiffOn ℝ 2 Q (Set.Icc a c))
    {s : ℝ} (hs : s ∈ Set.Ioo a 1) :
    DifferentiableAt ℝ (fun u : ℝ => ∫ v in u..1, (Real.sqrt (v - u))⁻¹ • Q v) s := by
  -- a splitting point `c` strictly between `s` and `1`
  set c : ℝ := (s + 1) / 2 with hcdef
  have hsc : s < c := by rw [hcdef]; linarith [hs.2]
  have hc1 : c < 1 := by rw [hcdef]; linarith [hs.2]
  have hac : a < c := lt_trans hs.1 hsc
  have hQc : ContDiffOn ℝ 2 Q (Set.Icc a c) := hQsmooth c hac hc1
  have hc1le : c ≤ 1 := le_of_lt hc1
  -- ## the piece `∫_u^c`
  have hnear : DifferentiableAt ℝ (fun u : ℝ => ∫ v in u..c, (Real.sqrt (v - u))⁻¹ • Q v) s := by
    have hsub : ContDiffOn ℝ 2 (fun v : ℝ => Q v - Q c) (Set.Icc a c) :=
      hQc.sub contDiffOn_const
    have hzero : (fun v : ℝ => Q v - Q c) c = 0 := by simp
    have h1 : DifferentiableAt ℝ
        (fun u : ℝ => ∫ v in u..c, (Real.sqrt (v - u))⁻¹ • (Q v - Q c)) s :=
      Commons.Analysis.Abel.differentiableAt_intervalIntegral_invSqrt_Q (E := E) hac hsub hzero
        ⟨hs.1, hsc⟩
    have h2 : DifferentiableAt ℝ (fun u : ℝ => (2 * Real.sqrt (c - u)) • Q c) s := by
      have hc' : (0 : ℝ) < c - s := sub_pos.mpr hsc
      have hlin : HasDerivAt (fun u : ℝ => c - u) (-1) s := (hasDerivAt_id s).const_sub c
      have hsqrt0 : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (c - s))) (c - s) := by
        simpa using Real.hasDerivAt_sqrt (sub_ne_zero.mpr (ne_of_gt hc'))
      have hcomp : HasDerivAt (fun u : ℝ => Real.sqrt (c - u))
          (1 / (2 * Real.sqrt (c - s)) * -1) s := by
        simpa [Function.comp_def] using HasDerivAt.comp (x := s)
          (h := fun u : ℝ => c - u) (h₂ := Real.sqrt)
          (h' := -1) (h₂' := 1 / (2 * Real.sqrt (c - s))) hsqrt0 hlin
      exact ((hcomp.const_mul 2).smul_const (Q c)).differentiableAt
    refine (h1.add h2).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds (show s ∈ Set.Ioo a c from ⟨hs.1, hsc⟩)] with u hu
    show (∫ v in u..c, (Real.sqrt (v - u))⁻¹ • Q v) =
      (∫ v in u..c, (Real.sqrt (v - u))⁻¹ • (Q v - Q c)) + (2 * Real.sqrt (c - u)) • Q c
    have hu1 : u < c := hu.2
    have huIcc : u ∈ Set.Icc a c := ⟨le_of_lt hu.1, le_of_lt hu.2⟩
    have hw : IntervalIntegrable (fun v : ℝ => (Real.sqrt (v - u))⁻¹) volume u c := by
      simpa using Commons.Analysis.Abel.intervalIntegrable_invSqrt_sub (a := u) (b := c) hu1
    have hQuI : ContinuousOn Q (Set.uIcc u c) := by
      refine hQcont.mono ?_
      rw [Set.uIcc_of_le (le_of_lt hu1)]
      intro v hv
      exact ⟨le_trans huIcc.1 hv.1, le_trans hv.2 hc1le⟩
    have hQuI' : ContinuousOn (fun v : ℝ => Q v - Q c) (Set.uIcc u c) :=
      hQuI.sub continuousOn_const
    have h1int : IntervalIntegrable (fun v : ℝ => (Real.sqrt (v - u))⁻¹ • (Q v - Q c))
        volume u c := hw.smul_continuousOn hQuI'
    have h2int : IntervalIntegrable (fun v : ℝ => (Real.sqrt (v - u))⁻¹ • Q c) volume u c :=
      hw.smul_continuousOn continuousOn_const
    have hcongr : (∫ v in u..c, (Real.sqrt (v - u))⁻¹ • Q v) =
        ∫ v in u..c, ((Real.sqrt (v - u))⁻¹ • (Q v - Q c) + (Real.sqrt (v - u))⁻¹ • Q c) := by
      refine intervalIntegral.integral_congr_Ioo_of_le (le_of_lt hu1) (fun v _ => ?_)
      show (Real.sqrt (v - u))⁻¹ • Q v =
        (Real.sqrt (v - u))⁻¹ • (Q v - Q c) + (Real.sqrt (v - u))⁻¹ • Q c
      rw [← smul_add, sub_add_cancel]
    calc (∫ v in u..c, (Real.sqrt (v - u))⁻¹ • Q v)
        = ∫ v in u..c,
            ((Real.sqrt (v - u))⁻¹ • (Q v - Q c) + (Real.sqrt (v - u))⁻¹ • Q c) := hcongr
      _ = (∫ v in u..c, (Real.sqrt (v - u))⁻¹ • (Q v - Q c)) +
            ∫ v in u..c, (Real.sqrt (v - u))⁻¹ • Q c :=
          intervalIntegral.integral_add h1int h2int
      _ = (∫ v in u..c, (Real.sqrt (v - u))⁻¹ • (Q v - Q c)) +
            (∫ v in u..c, (Real.sqrt (v - u))⁻¹) • Q c := by
          rw [intervalIntegral.integral_smul_const]
      _ = (∫ v in u..c, (Real.sqrt (v - u))⁻¹ • (Q v - Q c)) +
            (2 * Real.sqrt (c - u)) • Q c := by
          rw [Commons.Analysis.Abel.integral_invSqrt_sub (a := u) (b := c) hu1]
  -- ## the piece `∫_c^1`, by differentiating under the integral sign
  have hfar : DifferentiableAt ℝ (fun u : ℝ => ∫ v in c..1, (Real.sqrt (v - u))⁻¹ • Q v) s := by
    have hsa : 0 < s - a := sub_pos.mpr hs.1
    have hcs : 0 < c - s := sub_pos.mpr hsc
    set δ : ℝ := min (s - a) (c - s) / 2 with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef]; exact half_pos (lt_min hsa hcs)
    have hδ_le : δ ≤ (c - s) / 2 := by
      rw [hδdef]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    have hmpos : 0 < (c - s) / 2 := half_pos hcs
    let U : Set ℝ := Metric.ball s δ
    have hU_nhds : U ∈ 𝓝 s := Metric.ball_mem_nhds s hδpos
    have hU_lt : ∀ x ∈ U, x < s + (c - s) / 2 := by
      intro x hx
      have hx' : |x - s| < δ := by
        simpa [U, Metric.mem_ball, dist_eq_norm, Real.dist_eq] using hx
      have h1 : x - s < δ := (abs_lt.mp hx').2
      have h2 : x - s < (c - s) / 2 := lt_of_lt_of_le h1 hδ_le
      linarith
    have hU_gt : ∀ x ∈ U, a < x := by
      intro x hx
      have hx' : |x - s| < δ := by
        simpa [U, Metric.mem_ball, dist_eq_norm, Real.dist_eq] using hx
      have h1 : -δ < x - s := (abs_lt.mp hx').1
      have h2 : δ ≤ s - a := by
        rw [hδdef]
        have hmin : min (s - a) (c - s) ≤ s - a := min_le_left _ _
        linarith
      linarith
    -- the uniform gap `(c - s) / 2 ≤ t - x`
    have hgap : ∀ x ∈ U, ∀ t ∈ Set.uIoc c 1, (c - s) / 2 ≤ t - x := by
      intro x hx t ht
      rw [Set.uIoc_of_le hc1le] at ht
      have ht1 : c < t := ht.1
      have hxlt : x < s + (c - s) / 2 := hU_lt x hx
      linarith
    -- a uniform bound for `‖Q‖` on `[c,1]`
    obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hQcont.norm.mono (fun t ht => ⟨le_trans (le_of_lt hac) ht.1, ht.2⟩))
    let C : ℝ := max C₀ 0
    have hC_bound : ∀ t ∈ Set.Icc c 1, ‖Q t‖ ≤ C := by
      intro t ht
      exact le_trans (by simpa using hC₀ t ht) (le_max_left _ _)
    let F : ℝ → ℝ → E := fun u v => (Real.sqrt (v - u))⁻¹ • Q v
    let F' : ℝ → ℝ → E := fun u v => (1 / 2 * ((Real.sqrt (v - u))⁻¹) ^ 3) • Q v
    let bound : ℝ → ℝ := fun _ => (1 / 2 * ((Real.sqrt ((c - s) / 2))⁻¹) ^ 3) * C
    have hsub : Set.uIoc c 1 ⊆ Set.Icc c 1 := by
      rw [Set.uIoc_of_le hc1le]
      exact fun t ht => ⟨le_of_lt ht.1, ht.2⟩
    have hF_meas : ∀ᶠ u in 𝓝 s, AEStronglyMeasurable (F u) (volume.restrict (Ι c 1)) := by
      filter_upwards [hU_nhds] with u hu
      have hcont : ContinuousOn (fun v : ℝ => F u v) (Set.Icc c 1) := by
        refine ContinuousOn.smul ?_ ?_
        · refine ContinuousOn.inv₀ ?_ ?_
          · exact Real.continuous_sqrt.comp_continuousOn
              (continuousOn_id.sub continuousOn_const)
          · intro v hv
            exact ne_of_gt (Real.sqrt_pos.mpr (by
              have hv1 : c ≤ v := hv.1
              have hu_lt : u < s + (c - s) / 2 := hU_lt u hu
              linarith))
        · exact hQcont.mono (fun v hv => ⟨le_trans (le_of_lt hac) hv.1, hv.2⟩)
      exact hcont.aestronglyMeasurable_of_subset_isCompact isCompact_Icc measurableSet_uIoc hsub
    have hF_int : IntervalIntegrable (F s) volume c 1 := by
      have hcont : ContinuousOn (fun v : ℝ => F s v) (Set.Icc c 1) := by
        refine ContinuousOn.smul ?_ ?_
        · refine ContinuousOn.inv₀ ?_ ?_
          · exact Real.continuous_sqrt.comp_continuousOn
              (continuousOn_id.sub continuousOn_const)
          · intro v hv
            exact ne_of_gt (Real.sqrt_pos.mpr (by have := hv.1; linarith))
        · exact hQcont.mono (fun v hv => ⟨le_trans (le_of_lt hac) hv.1, hv.2⟩)
      have hcont' : ContinuousOn (fun v : ℝ => F s v) (Set.uIcc c 1) := by
        rw [Set.uIcc_of_le hc1le]
        exact hcont
      exact hcont'.intervalIntegrable
    have hF'_meas : AEStronglyMeasurable (F' s) (volume.restrict (Ι c 1)) := by
      have hcont : ContinuousOn (fun v : ℝ => F' s v) (Set.Icc c 1) := by
        refine ContinuousOn.smul ?_ ?_
        · refine ContinuousOn.const_mul ?_ _
          refine ContinuousOn.pow ?_ 3
          refine ContinuousOn.inv₀ ?_ ?_
          · exact Real.continuous_sqrt.comp_continuousOn
              (continuousOn_id.sub continuousOn_const)
          · intro v hv
            exact ne_of_gt (Real.sqrt_pos.mpr (by have := hv.1; linarith))
        · exact hQcont.mono (fun v hv => ⟨le_trans (le_of_lt hac) hv.1, hv.2⟩)
      exact hcont.aestronglyMeasurable_of_subset_isCompact isCompact_Icc measurableSet_uIoc hsub
    have h_bound : ∀ᵐ t ∂volume, t ∈ Ι c 1 → ∀ x ∈ U, ‖F' x t‖ ≤ bound t := by
      filter_upwards with t ht
      intro x hx
      have hmt : (c - s) / 2 ≤ t - x := hgap x hx t ht
      have hpos : 0 < t - x := lt_of_lt_of_le hmpos hmt
      have hsqrt_ge : Real.sqrt ((c - s) / 2) ≤ Real.sqrt (t - x) := Real.sqrt_le_sqrt hmt
      have hsqrtm_pos : 0 < Real.sqrt ((c - s) / 2) := Real.sqrt_pos.mpr hmpos
      have hinv_le : (Real.sqrt (t - x))⁻¹ ≤ (Real.sqrt ((c - s) / 2))⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le hsqrtm_pos hsqrt_ge
      have h3 : ((Real.sqrt (t - x))⁻¹) ^ 3 ≤ ((Real.sqrt ((c - s) / 2))⁻¹) ^ 3 :=
        pow_le_pow_left₀ (inv_nonneg.mpr (Real.sqrt_nonneg _)) hinv_le 3
      have htIcc : t ∈ Set.Icc c 1 := hsub ht
      have hC : ‖Q t‖ ≤ C := hC_bound t htIcc
      calc ‖F' x t‖ = ‖(1 / 2 * ((Real.sqrt (t - x))⁻¹) ^ 3) • Q t‖ := rfl
        _ = |1 / 2 * ((Real.sqrt (t - x))⁻¹) ^ 3| * ‖Q t‖ := norm_smul _ _
        _ = (1 / 2 * ((Real.sqrt (t - x))⁻¹) ^ 3) * ‖Q t‖ := by
              rw [abs_of_nonneg (by positivity)]
        _ ≤ (1 / 2 * ((Real.sqrt ((c - s) / 2))⁻¹) ^ 3) * C := by
              refine mul_le_mul ?_ hC (norm_nonneg _) (by positivity)
              exact mul_le_mul_of_nonneg_left h3 (by norm_num)
        _ = bound t := rfl
    have hbound_int : IntervalIntegrable bound volume c 1 := intervalIntegrable_const
    have h_diff : ∀ᵐ t ∂volume, t ∈ Ι c 1 → ∀ x ∈ U,
        HasDerivAt (fun u : ℝ => F u t) (F' x t) x := by
      filter_upwards with t ht
      intro x hx
      have hxt : 0 < t - x := lt_of_lt_of_le hmpos (hgap x hx t ht)
      have hd : HasDerivAt (fun u : ℝ => (Real.sqrt (t - u))⁻¹)
          (1 / 2 * ((Real.sqrt (t - x))⁻¹) ^ 3) x :=
        hasDerivAt_inv_sqrt_sub (v := t) (s := x) hxt
      simpa [F, F'] using hd.smul_const (Q t)
    have hdom := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (𝕜 := ℝ) (μ := volume) (E := E) (a := c) (b := 1)
      (F := F) (F' := F') (x₀ := s) (s := U) (bound := bound)
      hU_nhds hF_meas hF_int hF'_meas h_bound hbound_int h_diff
    exact hdom.2.differentiableAt
  -- ## assemble
  have hsplit : (fun u : ℝ => ∫ v in u..1, (Real.sqrt (v - u))⁻¹ • Q v)
      =ᶠ[𝓝 s] ((fun u : ℝ => ∫ v in u..c, (Real.sqrt (v - u))⁻¹ • Q v)
        + (fun u : ℝ => ∫ v in c..1, (Real.sqrt (v - u))⁻¹ • Q v)) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show s ∈ Set.Ioo a c from ⟨hs.1, hsc⟩)] with u hu
    have hu1 : u < c := hu.2
    have huc_gen : u ≤ c := le_of_lt hu1
    have huIcc : u ∈ Set.Icc a 1 := ⟨le_of_lt hu.1, le_trans huc_gen hc1le⟩
    have hcont1 : ContinuousOn (fun v : ℝ => (Real.sqrt (v - u))⁻¹ • Q v) (Set.Icc c 1) := by
      refine ContinuousOn.smul ?_ ?_
      · refine ContinuousOn.inv₀ ?_ ?_
        · exact Real.continuous_sqrt.comp_continuousOn (continuousOn_id.sub continuousOn_const)
        · intro v hv
          exact ne_of_gt (Real.sqrt_pos.mpr (by have := hv.1; linarith))
      · exact hQcont.mono (fun v hv => ⟨le_trans (le_of_lt hac) hv.1, hv.2⟩)
    have h2int : IntervalIntegrable (fun v : ℝ => (Real.sqrt (v - u))⁻¹ • Q v) volume c 1 := by
      have hc' : ContinuousOn (fun v : ℝ => (Real.sqrt (v - u))⁻¹ • Q v) (Set.uIcc c 1) := by
        rw [Set.uIcc_of_le hc1le]; exact hcont1
      exact hc'.intervalIntegrable
    have hw : IntervalIntegrable (fun v : ℝ => (Real.sqrt (v - u))⁻¹) volume u c := by
      simpa using Commons.Analysis.Abel.intervalIntegrable_invSqrt_sub (a := u) (b := c) hu1
    have hQuI : ContinuousOn Q (Set.uIcc u c) := by
      refine hQcont.mono ?_
      rw [Set.uIcc_of_le huc_gen]
      intro v hv
      exact ⟨le_trans huIcc.1 hv.1, le_trans hv.2 hc1le⟩
    have h1int : IntervalIntegrable (fun v : ℝ => (Real.sqrt (v - u))⁻¹ • Q v) volume u c :=
      hw.smul_continuousOn hQuI
    exact (intervalIntegral.integral_add_adjacent_intervals h1int h2int).symm
  exact (hnear.add hfar).congr_of_eventuallyEq hsplit

/-- **Abel inversion on `(a,1)` with `Q` merely continuous on `[a,1]`.**  -/
theorem abel_inversion_continuous_endpoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {a : ℝ} (ha : 0 < a) {K : ℝ → ℝ → E} {Q : ℝ → E}
    (hK : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a 1 ×ˢ Set.Icc a 1))
    (hQcont : ContinuousOn Q (Set.Icc a 1))
    (hQsmooth : ∀ c : ℝ, a < c → c < 1 → ContDiffOn ℝ 2 Q (Set.Icc a c))
    (hdvi : ∀ s ∈ Set.Ioo a 1,
      - (∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K s s)
        + (∫ σ in s..1, deriv (fun u : ℝ => ∫ τ in (0 : ℝ)..1,
            (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K (u + τ * (σ - u)) σ) s)
      = deriv (fun u : ℝ => ∫ v in u..1, (Real.sqrt (v - u))⁻¹ • Q v) s) :
    ∀ s ∈ Set.Ioo a 1, (∫ σ in s..1, (Real.sqrt (σ - s))⁻¹ • K s σ) = Q s := by
  intro s hs
  have ha1 : a < 1 := lt_trans hs.1 hs.2
  exact Work.OddVolterra.Abel.abel_inversion_b1 (E := E) ha1 hK hQcont
    (fun x hx => differentiableAt_abel_transform_of_smoothOn_compacts hQcont hQsmooth hx) hdvi s hs

end

end Work.OddBridge
