import Submission.Commons.Analysis.Calculus.integral_two_mul_s_div_sq_add_sq
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Commons.Analysis.Calculus

open MeasureTheory Set Filter intervalIntegral
open scoped Topology

/-- The first absolute moment of the Poisson kernel on `[-δ, δ]`. -/
theorem integral_two_mul_s_mul_abs_div_sq_add_sq {s δ : ℝ} (hs : 0 < s) (hδ : 0 ≤ δ) :
    ∫ u in (-δ)..δ, (2 * s) / (u ^ 2 + s ^ 2) * |u| = 2 * s * Real.log (1 + δ ^ 2 / s ^ 2) := by
  set g : ℝ → ℝ := fun u => (2 * s) / (u ^ 2 + s ^ 2) * |u| with hg
  have hden : ∀ u : ℝ, u ^ 2 + s ^ 2 ≠ 0 := fun u => by positivity
  have hcontg : Continuous g := by
    rw [hg]; apply Continuous.mul _ continuous_abs
    exact continuous_const.div (by fun_prop) hden
  have hsym : ∫ u in (-δ)..0, g u = ∫ u in (0:ℝ)..δ, g u := by
    have h1 := intervalIntegral.integral_comp_neg (f := g) (a := -δ) (b := 0)
    simp only [neg_zero, neg_neg] at h1
    have h2 : ∫ x in (-δ)..0, g (-x) = ∫ x in (-δ)..0, g x := by
      apply intervalIntegral.integral_congr
      intro u hu
      simp only
      rw [hg]; simp only
      rw [abs_neg]
      congr 1
      ring
    rw [← h2]
    exact h1
  have hint1 : IntervalIntegrable g volume (-δ) 0 := hcontg.intervalIntegrable _ _
  have hint2 : IntervalIntegrable g volume (0:ℝ) δ := hcontg.intervalIntegrable _ _
  have hsplit : ∫ u in (-δ)..δ, g u = 2 * ∫ u in (0:ℝ)..δ, g u := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2, hsym]
    ring
  have hhalf : ∫ u in (0:ℝ)..δ, g u = s * Real.log (δ ^ 2 + s ^ 2) - s * Real.log (s ^ 2) := by
    have hc : ∫ u in (0:ℝ)..δ, g u = ∫ u in (0:ℝ)..δ, (2*s*u/(u^2+s^2)) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le hδ] at hu
      rw [hg]; simp only
      rw [abs_of_nonneg hu.1]
      ring
    rw [hc]
    have hderiv : ∀ u : ℝ, HasDerivAt (fun u : ℝ => s * Real.log (u^2 + s^2)) (2*s*u/(u^2+s^2)) u := by
      intro u
      have hbase : HasDerivAt (fun u : ℝ => u ^ 2 + s ^ 2) (2 * u) u := by
        have h := (hasDerivAt_pow 2 u).add_const (s ^ 2)
        refine h.congr_deriv ?_
        norm_num
      have hl := hbase.log (hden u)
      have := hl.const_mul s
      refine this.congr_deriv ?_
      field_simp
    have hint : IntervalIntegrable (fun u : ℝ => 2*s*u/(u^2+s^2)) volume (0:ℝ) δ := by
      apply Continuous.intervalIntegrable
      apply Continuous.div (by fun_prop) (by fun_prop) hden
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) hint]
    norm_num
  rw [hsplit, hhalf]
  have h1 : δ ^ 2 + s ^ 2 ≠ 0 := by positivity
  have h2 : s ^ 2 ≠ 0 := by positivity
  have hlog : Real.log (δ ^ 2 + s ^ 2) - Real.log (s ^ 2) = Real.log (1 + δ ^ 2 / s ^ 2) := by
    rw [← Real.log_div h1 h2]
    congr 1
    field_simp
    ring
  rw [← mul_sub, hlog]
  ring

/-- `arctan (δ/s) → π/2` as `s → 0⁺` for `δ > 0`. -/
theorem tendsto_arctan_div_self_nhdsGT {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto (fun s : ℝ => Real.arctan (δ / s)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.pi / 2)) := by
  have h1 : Filter.Tendsto (fun s : ℝ => s⁻¹) (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    tendsto_inv_nhdsGT_zero
  have h2 : Filter.Tendsto (fun s : ℝ => δ * s⁻¹) (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    h1.const_mul_atTop hδ
  have h3 : Filter.Tendsto (fun s : ℝ => Real.arctan (δ * s⁻¹)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h2
  simpa [div_eq_mul_inv] using h3

/-- `s * log (1 + c/s²) → 0` as `s → 0⁺` for `c > 0`. -/
theorem tendsto_mul_log_one_add_div_sq {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun s : ℝ => s * Real.log (1 + c / s ^ 2)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  have hs0 : Filter.Tendsto (fun s : ℝ => s) (nhdsWithin 0 (Set.Ioi 0)) (nhds (0:ℝ)) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  have hslog : Filter.Tendsto (fun s : ℝ => Real.log s * s) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (0:ℝ)) := by
    simpa using tendsto_log_mul_rpow_nhdsGT_zero (r := 1) (by norm_num)
  have hsq : Filter.Tendsto (fun s : ℝ => s ^ 2 + c) (nhdsWithin 0 (Set.Ioi 0)) (nhds c) := by
    have h1 : Filter.Tendsto (fun s : ℝ => s ^ 2) (nhdsWithin 0 (Set.Ioi 0)) (nhds (0:ℝ)) := by
      simpa using hs0.pow 2
    simpa using h1.add_const c
  have hlogc : Filter.Tendsto (fun s : ℝ => Real.log (s ^ 2 + c)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.log c)) :=
    (Real.continuousAt_log hc.ne').tendsto.comp hsq
  have hterm1 : Filter.Tendsto (fun s : ℝ => s * Real.log (s ^ 2 + c)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (0:ℝ)) := by
    have := hs0.mul hlogc
    simpa using this
  have hterm2 : Filter.Tendsto (fun s : ℝ => 2 * (s * Real.log s)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (0:ℝ)) := by
    have h : Filter.Tendsto (fun s : ℝ => 2 * (Real.log s * s)) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (2 * (0:ℝ))) := hslog.const_mul 2
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hmain : Filter.Tendsto (fun s : ℝ => s * Real.log (s ^ 2 + c) - 2 * (s * Real.log s))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (0:ℝ)) := by
    have := hterm1.sub hterm2
    simpa using this
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hsne : s ≠ 0 := ne_of_gt hs
  have h1 : s ^ 2 + c ≠ 0 := by positivity
  have h2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hsne
  have hkey : 1 + c / s ^ 2 = (s ^ 2 + c) / s ^ 2 := by field_simp
  rw [hkey, Real.log_div h1 h2, Real.log_pow]
  ring

/-- The Poisson kernel on the real line is an approximate identity at the origin:
for `h` continuous on `[-δ, δ]`, the integrals `∫ u in (-δ)..δ, (2s/(u²+s²)) • h u`
converge to `(2π) • h 0` as `s → 0⁺`. -/
theorem tendsto_integral_poisson_kernel {h : ℝ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hc : ContinuousOn h (Set.Icc (-δ) δ)) :
    Filter.Tendsto (fun s : ℝ => ∫ u in (-δ)..δ, ((2 * s) / (u ^ 2 + s ^ 2) : ℝ) • h u)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((2 * Real.pi : ℝ) • h 0)) := by
  have hle : (-δ : ℝ) ≤ δ := by linarith
  have hmem : Set.Icc (-δ) δ ∈ 𝓝 (0:ℝ) := by
    refine Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioo ?_) Set.Ioo_subset_Icc_self
    exact ⟨by linarith, by linarith⟩
  have hcont : ContinuousAt h 0 := hc.continuousAt hmem
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := (-δ)) (b := δ)).exists_bound_of_continuousOn
    (hc.sub continuousOn_const)
  set M : ℝ := max M₀ 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hMb : ∀ u ∈ Set.Icc (-δ) δ, ‖h u - h 0‖ ≤ M :=
    fun u hu => (hM₀ u hu).trans (le_max_left _ _)
  -- Main estimate: the "error" term tends to 0.
  have hA : Filter.Tendsto
      (fun s : ℝ => ∫ u in (-δ)..δ, ((2 * s) / (u ^ 2 + s ^ 2) : ℝ) • (h u - h 0))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε1 : (0:ℝ) < ε / (4 * Real.pi) := by positivity
    obtain ⟨η, hηpos, hη⟩ := Metric.continuousAt_iff.mp hcont (ε / (4 * Real.pi)) hε1
    have hL : Filter.Tendsto
        (fun s : ℝ => (M / η) * (2 * s * Real.log (1 + δ ^ 2 / s ^ 2)))
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
      have h1 : Filter.Tendsto (fun s : ℝ => 2 * s * Real.log (1 + δ ^ 2 / s ^ 2))
          (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
        have := (tendsto_mul_log_one_add_div_sq (c := δ^2) (by positivity)).const_mul 2
        simpa [mul_assoc] using this
      simpa using h1.const_mul (M / η)
    have hLMe : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0),
        (M / η) * (2 * s * Real.log (1 + δ ^ 2 / s ^ 2)) < ε / 2 :=
      hL.eventually (eventually_lt_nhds (by linarith))
    filter_upwards [self_mem_nhdsWithin, hLMe] with s hs hLsmall
    rw [dist_zero_right]
    set Ps : ℝ → ℝ := fun u => (2 * s) / (u ^ 2 + s ^ 2) with hPs
    have hs' : (0:ℝ) < s := hs
    have hPs_nonneg : ∀ u, 0 ≤ Ps u := by
      intro u
      change 0 ≤ (2 * s) / (u ^ 2 + s ^ 2)
      positivity
    have hPs_cont : ContinuousOn (fun u => Ps u) (Set.Icc (-δ) δ) := by
      change ContinuousOn (fun u => (2 * s) / (u ^ 2 + s ^ 2)) (Set.Icc (-δ) δ)
      exact (continuous_const.div (by fun_prop) (fun u => ne_of_gt (by positivity))).continuousOn
    -- pointwise linear bound
    have hbound : ∀ u ∈ Set.Icc (-δ) δ,
        ‖h u - h 0‖ ≤ ε / (4 * Real.pi) + (M / η) * |u| := by
      intro u hu
      rcases lt_or_ge (|u|) η with hlt | hge
      · have hdist : dist u 0 < η := by rw [Real.dist_eq]; simpa using hlt
        have h1 : dist (h u) (h 0) < ε / (4 * Real.pi) := hη hdist
        have h2 : ‖h u - h 0‖ < ε / (4 * Real.pi) := by simpa [dist_eq_norm] using h1
        have h3 : 0 ≤ (M / η) * |u| := mul_nonneg (div_nonneg hM0 hηpos.le) (abs_nonneg u)
        linarith
      · have h1 : ‖h u - h 0‖ ≤ M := hMb u hu
        have h2 : M ≤ (M / η) * |u| := by
          have hge1 : 1 ≤ |u| / η := (le_div_iff₀ hηpos).mpr (by linarith)
          calc M = M * 1 := by ring
            _ ≤ M * (|u| / η) := mul_le_mul_of_nonneg_left hge1 hM0
            _ = (M / η) * |u| := by ring
        have h3 : 0 ≤ ε / (4 * Real.pi) := le_of_lt hε1
        linarith
    -- interval integrability of the pieces
    have hint_left : IntervalIntegrable (fun u => Ps u * ‖h u - h 0‖) volume (-δ) δ :=
      ((hPs_cont.mul (hc.sub continuousOn_const).norm)).intervalIntegrable_of_Icc hle
    have hint_right : IntervalIntegrable
        (fun u => Ps u * (ε / (4 * Real.pi) + (M / η) * |u|)) volume (-δ) δ := by
      apply ContinuousOn.intervalIntegrable_of_Icc hle
      exact hPs_cont.mul ((continuousOn_const.add
        ((continuous_const.mul continuous_abs).continuousOn)))
    have hintA : IntervalIntegrable
        (fun u => ε / (4 * Real.pi) * Ps u) volume (-δ) δ :=
      (continuousOn_const.mul hPs_cont).intervalIntegrable_of_Icc hle
    have hintB : IntervalIntegrable
        (fun u => (M / η) * (Ps u * |u|)) volume (-δ) δ :=
      (continuousOn_const.mul (hPs_cont.mul continuous_abs.continuousOn)).intervalIntegrable_of_Icc hle
    -- step 1
    have hstep1 : ‖∫ u in (-δ)..δ, Ps u • (h u - h 0)‖
        ≤ ∫ u in (-δ)..δ, Ps u * ‖h u - h 0‖ := by
      have h1 := intervalIntegral.norm_integral_le_integral_norm
        (μ := volume) (f := fun u => Ps u • (h u - h 0)) hle
      refine h1.trans_eq ?_
      apply intervalIntegral.integral_congr
      intro u hu
      show ‖Ps u • (h u - h 0)‖ = Ps u * ‖h u - h 0‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hPs_nonneg u)]
    -- step 2
    have hstep2 : ∫ u in (-δ)..δ, Ps u * ‖h u - h 0‖
        ≤ ∫ u in (-δ)..δ, Ps u * (ε / (4 * Real.pi) + (M / η) * |u|) := by
      apply intervalIntegral.integral_mono_on hle hint_left hint_right
      intro u hu
      exact mul_le_mul_of_nonneg_left (hbound u hu) (hPs_nonneg u)
    -- step 3
    have hMs : ∫ u in (-δ)..δ, Ps u = 4 * Real.arctan (δ / s) := by
      rw [hPs]; exact integral_two_mul_s_div_sq_add_sq hs δ
    have hLs : ∫ u in (-δ)..δ, Ps u * |u| = 2 * s * Real.log (1 + δ ^ 2 / s ^ 2) := by
      rw [hPs]; exact integral_two_mul_s_mul_abs_div_sq_add_sq hs hδ.le
    have hstep3 : ∫ u in (-δ)..δ, Ps u * (ε / (4 * Real.pi) + (M / η) * |u|)
        = ε / (4 * Real.pi) * (∫ u in (-δ)..δ, Ps u)
          + (M / η) * (∫ u in (-δ)..δ, Ps u * |u|) := by
      have hpoint : (fun u => Ps u * (ε / (4 * Real.pi) + (M / η) * |u|))
          = fun u => ε / (4 * Real.pi) * Ps u + (M / η) * (Ps u * |u|) := by
        funext u; ring
      rw [hpoint, intervalIntegral.integral_add hintA hintB,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    -- final numeric estimate
    have hMs_le : (∫ u in (-δ)..δ, Ps u) ≤ 2 * Real.pi := by
      rw [hMs]; linarith [Real.arctan_lt_pi_div_two (δ / s)]
    have hfinal : ε / (4 * Real.pi) * (∫ u in (-δ)..δ, Ps u)
        + (M / η) * (∫ u in (-δ)..δ, Ps u * |u|) < ε := by
      have h1 : ε / (4 * Real.pi) * (∫ u in (-δ)..δ, Ps u) ≤ ε / 2 := by
        calc ε / (4 * Real.pi) * (∫ u in (-δ)..δ, Ps u)
            ≤ ε / (4 * Real.pi) * (2 * Real.pi) := mul_le_mul_of_nonneg_left hMs_le (le_of_lt hε1)
          _ = ε / 2 := by field_simp; ring
      have h2 : (M / η) * (∫ u in (-δ)..δ, Ps u * |u|) < ε / 2 := by
        rw [hLs]; exact hLsmall
      linarith
    calc ‖∫ u in (-δ)..δ, Ps u • (h u - h 0)‖
        ≤ ∫ u in (-δ)..δ, Ps u * ‖h u - h 0‖ := hstep1
      _ ≤ ∫ u in (-δ)..δ, Ps u * (ε / (4 * Real.pi) + (M / η) * |u|) := hstep2
      _ = ε / (4 * Real.pi) * (∫ u in (-δ)..δ, Ps u)
            + (M / η) * (∫ u in (-δ)..δ, Ps u * |u|) := hstep3
      _ < ε := hfinal
  -- Mass limit
  have hms : Filter.Tendsto (fun s : ℝ => ∫ u in (-δ)..δ, ((2 * s) / (u ^ 2 + s ^ 2) : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (2 * Real.pi)) := by
    have h1 := (tendsto_arctan_div_self_nhdsGT hδ).const_mul 4
    rw [show (4:ℝ) * (Real.pi / 2) = 2 * Real.pi by ring] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (integral_two_mul_s_div_sq_add_sq hs δ).symm
  have hmass : Filter.Tendsto
      (fun s : ℝ => ((∫ u in (-δ)..δ, ((2 * s) / (u ^ 2 + s ^ 2) : ℝ)) - 2 * Real.pi) • h 0)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    have h2 := hms.sub_const (2 * Real.pi)
    have h3 := h2.smul_const (h 0)
    simpa using h3
  -- decomposition
  have hdecomp : ∀ s : ℝ, 0 < s →
      (∫ u in (-δ)..δ, ((2 * s) / (u ^ 2 + s ^ 2) : ℝ) • h u)
        = (∫ u in (-δ)..δ, ((2 * s) / (u ^ 2 + s ^ 2) : ℝ) • (h u - h 0))
          + (∫ u in (-δ)..δ, ((2 * s) / (u ^ 2 + s ^ 2) : ℝ)) • h 0 := by
    intro s hs
    have hPs_cont : ContinuousOn (fun u : ℝ => ((2 * s) / (u ^ 2 + s ^ 2) : ℝ))
        (Set.Icc (-δ) δ) :=
      (continuous_const.div (by fun_prop) (fun u => by positivity)).continuousOn
    have hi1 : IntervalIntegrable
        (fun u : ℝ => ((2 * s) / (u ^ 2 + s ^ 2) : ℝ) • (h u - h 0)) volume (-δ) δ :=
      (hPs_cont.smul (hc.sub continuousOn_const)).intervalIntegrable_of_Icc hle
    have hi2 : IntervalIntegrable
        (fun u : ℝ => ((2 * s) / (u ^ 2 + s ^ 2) : ℝ) • h 0) volume (-δ) δ :=
      (hPs_cont.smul continuousOn_const).intervalIntegrable_of_Icc hle
    have h1 : (∫ u in (-δ)..δ, ((2 * s) / (u ^ 2 + s ^ 2) : ℝ) • h u)
        = ∫ u in (-δ)..δ,
            (((2 * s) / (u ^ 2 + s ^ 2) : ℝ) • (h u - h 0)
              + ((2 * s) / (u ^ 2 + s ^ 2) : ℝ) • h 0) := by
      apply intervalIntegral.integral_congr
      intro u hu
      show ((2 * s) / (u ^ 2 + s ^ 2) : ℝ) • h u
          = ((2 * s) / (u ^ 2 + s ^ 2) : ℝ) • (h u - h 0)
            + ((2 * s) / (u ^ 2 + s ^ 2) : ℝ) • h 0
      rw [smul_sub, sub_add_cancel]
    rw [h1, intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_smul_const]
  -- sum limit
  have hsum : Filter.Tendsto
      (fun s : ℝ => (∫ u in (-δ)..δ, ((2 * s) / (u ^ 2 + s ^ 2) : ℝ) • (h u - h 0))
        + (((∫ u in (-δ)..δ, ((2 * s) / (u ^ 2 + s ^ 2) : ℝ)) - 2 * Real.pi) • h 0))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    have := hA.add hmass
    simpa using this
  have hfinal : Filter.Tendsto
      (fun s : ℝ => (∫ u in (-δ)..δ, ((2 * s) / (u ^ 2 + s ^ 2) : ℝ) • h u)
        - (2 * Real.pi : ℝ) • h 0)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    refine hsum.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hdecomp s hs, sub_smul]
    abel
  simpa using hfinal.add_const ((2 * Real.pi : ℝ) • h 0)

end Commons.Analysis.Calculus
