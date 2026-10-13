import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllSol.VthAux.traceAux.hardyPowPrimIbp
import Submission.Work.FTS.EllSol.VthAux.traceAux.integrableOn_Ioo_of_intervalIntegral_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.VthAux.traceAux

open MeasureTheory Set Filter
open scoped Real Topology ENNReal Interval


private theorem abs_deriv_sub_le {ε : ℝ} {h : ℝ → ℝ} (hC2 : ContDiffOn ℝ 2 h (Set.Ioo 0 ε))
    {x y : ℝ} (hx : x ∈ Set.Ioo 0 ε) (hy : y ∈ Set.Ioo 0 ε) (hxy : x ≤ y) :
    |deriv h y - deriv h x| ≤ ∫ s in x..y, |deriv (deriv h) s| := by
  have hC1 : ContDiffOn ℝ 1 h (Set.Ioo 0 ε) := (contDiffOn_iff_forall_nat_le.mp hC2) 1 (by norm_num)
  have hφc : ContDiffOn ℝ 1 (deriv h) (Set.Ioo 0 ε) := hC2.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have h2 : ContDiffOn ℝ 0 (deriv (deriv h)) (Set.Ioo 0 ε) :=
    hφc.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hψc : ContinuousOn (deriv (deriv h)) (Set.Ioo 0 ε) := h2.continuousOn
  have hsub : Set.uIcc x y ⊆ Set.Ioo 0 ε := by
    rw [Set.uIcc_of_le hxy]
    intro z hz
    exact ⟨lt_of_lt_of_le hx.1 hz.1, lt_of_le_of_lt hz.2 hy.2⟩
  have hderiv : ∀ z ∈ Set.uIcc x y, HasDerivAt (deriv h) (deriv (deriv h) z) z := fun z hz =>
    (hφc.differentiableOn (by norm_num)).hasDerivAt (isOpen_Ioo.mem_nhds (hsub hz))
  have hint : IntervalIntegrable (deriv (deriv h)) volume x y :=
    (hψc.mono hsub).intervalIntegrable
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  exact intervalIntegral.abs_integral_le_integral_abs hxy

theorem hardyPow_intervalIntegrable_rpow_mul {p δ ε M : ℝ} (hp : p ≤ 0) (hδ0 : 0 < δ)
    (hδε : δ ≤ ε) {g : ℝ → ℝ} (hgc : ContinuousOn g (Set.Ioo δ ε))
    (hbd : ∀ x ∈ Set.Ioo δ ε, |g x| ≤ M) (hM : 0 ≤ M) :
    IntervalIntegrable (fun θ : ℝ => θ ^ p * g θ) volume δ ε := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioo δ ε)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo]; exact ENNReal.ofReal_lt_top⟩
  have hb : IntegrableOn (fun _ : ℝ => δ ^ p * M) (Set.Ioo δ ε) := integrable_const _
  have hInt : IntegrableOn (fun θ : ℝ => θ ^ p * g θ) (Set.Ioo δ ε) := by
    refine MeasureTheory.Integrable.mono' hb ?_ ?_
    · have hc1 : ContinuousOn (fun θ : ℝ => θ ^ p) (Set.Ioo δ ε) :=
        continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_trans hδ0 ht.1)))
      exact (hc1.mul hgc).aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg (le_of_lt (lt_trans hδ0 hθ.1)) _)]
      have h1 : θ ^ p ≤ δ ^ p :=
        Real.rpow_le_rpow_of_nonpos hδ0 hθ.1.le hp
      exact mul_le_mul h1 (hbd θ hθ) (abs_nonneg _) (Real.rpow_nonneg (le_of_lt hδ0) _)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hδε, integrableOn_Ioc_iff_integrableOn_Ioo]
  exact hInt

theorem hardySecondPowStep1 {a ε : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hε : 0 < ε) {h : ℝ → ℝ}
    (hC2 : ContDiffOn ℝ 2 h (Set.Ioo 0 ε))
    (h0 : Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => θ ^ a * |deriv (deriv h) θ|) (Set.Ioo 0 ε)) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => θ ^ (a - 1) * |deriv h θ|) (Set.Ioc 0 ε) ∧
    MeasureTheory.IntegrableOn (fun x : ℝ => |deriv h x|) (Set.Ioo 0 ε) ∧
    (∀ δ ∈ Set.Ioo 0 ε, |h δ|
        ≤ δ ^ (1 - a) * (∫ x in Set.Ioc 0 ε, x ^ (a - 1) * |deriv h x|)) ∧
    (∀ δ ∈ Set.Ioo 0 ε, (∫ x in δ..ε, x ^ (a - 1) * |deriv h x|)
        ≤ ∫ x in Set.Ioc 0 ε, x ^ (a - 1) * |deriv h x|) := by

  have ha1a : (0 : ℝ) < 1 - a := by linarith
  have hC1 : ContDiffOn ℝ 1 h (Set.Ioo 0 ε) := (contDiffOn_iff_forall_nat_le.mp hC2) 1 (by norm_num)
  have hφc : ContDiffOn ℝ 1 (deriv h) (Set.Ioo 0 ε) := hC2.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hψC : ContDiffOn ℝ 0 (deriv (deriv h)) (Set.Ioo 0 ε) :=
    hφc.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hψc : ContinuousOn (deriv (deriv h)) (Set.Ioo 0 ε) := hψC.continuousOn
  have hhc : ContinuousOn h (Set.Ioo 0 ε) := hC1.continuousOn
  have hφ_cont : ContinuousOn (deriv h) (Set.Ioo 0 ε) := hφc.continuousOn
  have hφd : ∀ x ∈ Set.Ioo 0 ε, HasDerivAt h (deriv h x) x := fun x hx =>
    (hC1.differentiableOn (by norm_num)).hasDerivAt (isOpen_Ioo.mem_nhds hx)
  have hIntψ : MeasureTheory.IntegrableOn
      (fun θ : ℝ => θ ^ a * |deriv (deriv h) θ|) (Set.Ioc 0 ε) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo).2 hint
  set θ₀ : ℝ := ε / 2 with hθ₀def
  have hθ₀pos : 0 < θ₀ := by rw [hθ₀def]; linarith
  have hθ₀lt : θ₀ < ε := by rw [hθ₀def]; linarith
  have hθ₀mem : θ₀ ∈ Set.Ioo 0 ε := ⟨hθ₀pos, hθ₀lt⟩
  set Kψ : ℝ := ∫ x in Set.Ioc 0 ε, x ^ a * |deriv (deriv h) x| with hKψ
  have hKψnn : 0 ≤ Kψ := by
    rw [hKψ]
    exact setIntegral_nonneg measurableSet_Ioc
      (fun x hx => mul_nonneg (Real.rpow_nonneg hx.1.le a) (abs_nonneg _))
  have hψ_le : ∀ {u v : ℝ}, 0 < u → u ≤ v → v < ε →
      ∫ s in u..v, |deriv (deriv h) s| ≤ u ^ (-a) * Kψ := by
    intro u v hu huv hv
    have hpt : ∀ s ∈ Set.Ioo u v,
        |deriv (deriv h) s| ≤ u ^ (-a) * (s ^ a * |deriv (deriv h) s|) := by
      intro s hs
      have h1 : u ^ a ≤ s ^ a := Real.rpow_le_rpow (le_of_lt hu) (le_of_lt hs.1) (le_of_lt ha0)
      have h2 : 1 ≤ u ^ (-a) * s ^ a := by
        have h3 : u ^ (-a) * u ^ a = 1 := by
          rw [← Real.rpow_add hu, neg_add_cancel, Real.rpow_zero]
        have h4 : u ^ (-a) * u ^ a ≤ u ^ (-a) * s ^ a :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (le_of_lt hu) _)
        linarith
      have h5 : |deriv (deriv h) s| ≤ (u ^ (-a) * s ^ a) * |deriv (deriv h) s| :=
        by simpa using mul_le_mul_of_nonneg_right h2 (abs_nonneg (deriv (deriv h) s))
      calc |deriv (deriv h) s| ≤ (u ^ (-a) * s ^ a) * |deriv (deriv h) s| := h5
        _ = u ^ (-a) * (s ^ a * |deriv (deriv h) s|) := by ring
    have hsub : Set.uIcc u v ⊆ Set.Ioo 0 ε := fun x hx => by
      rw [Set.uIcc_of_le huv] at hx
      exact ⟨lt_of_lt_of_le hu hx.1, lt_of_le_of_lt hx.2 hv⟩
    have hI1 : IntervalIntegrable (fun s : ℝ => |deriv (deriv h) s|) volume u v :=
      ((hψc.mono hsub).abs).intervalIntegrable
    have hI2 : IntervalIntegrable
        (fun s : ℝ => u ^ (-a) * (s ^ a * |deriv (deriv h) s|)) volume u v := by
      have h3 : MeasureTheory.IntegrableOn
          (fun s : ℝ => u ^ (-a) * (s ^ a * |deriv (deriv h) s|)) (Set.Ioo u v) :=
        ((hint.mono_set (fun x hx => ⟨lt_trans hu hx.1, lt_trans hx.2 hv⟩)).integrable.const_mul _)
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le huv,
        integrableOn_Ioc_iff_integrableOn_Ioo]
      exact h3
    have hstep := intervalIntegral.integral_mono_on_of_le_Ioo huv hI1 hI2 hpt
    have hstep2 : ∫ s in u..v, u ^ (-a) * (s ^ a * |deriv (deriv h) s|) ≤ u ^ (-a) * Kψ := by
      rw [intervalIntegral.integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (le_of_lt hu) _)
      rw [hKψ, intervalIntegral.integral_of_le huv]
      refine setIntegral_mono_set hIntψ
        (ae_restrict_of_forall_mem measurableSet_Ioc
          (fun x hx => mul_nonneg (Real.rpow_nonneg hx.1.le a) (abs_nonneg _)))
        (Filter.Eventually.of_forall fun x hx => ⟨lt_trans hu hx.1, le_trans hx.2 hv.le⟩)
    linarith
  set Kφ : ℝ := |deriv h θ₀| + θ₀ ^ (-a) * Kψ with hKφ
  have hKφnn : 0 ≤ Kφ := by
    rw [hKφ]
    exact add_nonneg (abs_nonneg _)
      (mul_nonneg (Real.rpow_nonneg (le_of_lt hθ₀pos) _) hKψnn)
  have hφ_le_Kφ : ∀ θ ∈ Set.Ioo θ₀ ε, |deriv h θ| ≤ Kφ := by
    intro θ hθ
    have hθmem : θ ∈ Set.Ioo 0 ε := ⟨lt_trans hθ₀pos hθ.1, hθ.2⟩
    have h1 : |deriv h θ - deriv h θ₀| ≤ ∫ s in θ₀..θ, |deriv (deriv h) s| :=
      abs_deriv_sub_le hC2 hθ₀mem hθmem hθ.1.le
    have h2 : ∫ s in θ₀..θ, |deriv (deriv h) s| ≤ θ₀ ^ (-a) * Kψ :=
      hψ_le hθ₀pos hθ.1.le hθ.2
    have h3 : |deriv h θ| ≤ |deriv h θ₀| + |deriv h θ - deriv h θ₀| := by
      have h4 := abs_add_le (deriv h θ - deriv h θ₀) (deriv h θ₀)
      rw [sub_add_cancel] at h4
      linarith
    rw [hKφ]
    linarith
  set K : ℝ := |deriv h θ₀| * θ₀ ^ a / a + (1 / a) * Kψ
      + θ₀ ^ (a - 1) * Kφ * (ε - θ₀) with hK
  have hw_le_K : ∀ δ ∈ Set.Ioo 0 ε, (∫ θ in δ..ε, θ ^ (a - 1) * |deriv h θ|) ≤ K := by
    intro δ hδ
    have hδ0 : 0 < δ := hδ.1
    have hδε : δ ≤ ε := hδ.2.le
    have hIend : IntervalIntegrable (fun θ : ℝ => θ ^ (a - 1) * |deriv h θ|) volume θ₀ ε :=
      hardyPow_intervalIntegrable_rpow_mul (p := a - 1) (by linarith) hθ₀pos hθ₀lt.le
        (hφ_cont.mono (fun x hx => ⟨lt_trans hθ₀pos hx.1, hx.2⟩)).abs
        (fun x hx => by simpa using hφ_le_Kφ x hx) hKφnn
    have hup : ∫ θ in θ₀..ε, θ ^ (a - 1) * |deriv h θ| ≤ θ₀ ^ (a - 1) * Kφ * (ε - θ₀) := by
      have hIconst : IntervalIntegrable
          (fun θ : ℝ => θ₀ ^ (a - 1) * Kφ) volume θ₀ ε := intervalIntegrable_const
      have hpt2 : ∀ θ ∈ Set.Ioo θ₀ ε,
          θ ^ (a - 1) * |deriv h θ| ≤ θ₀ ^ (a - 1) * Kφ := by
        intro θ hθ
        have h1 : θ ^ (a - 1) ≤ θ₀ ^ (a - 1) :=
          Real.rpow_le_rpow_of_nonpos hθ₀pos hθ.1.le (by linarith)
        exact mul_le_mul h1 (hφ_le_Kφ θ hθ) (abs_nonneg _)
          (Real.rpow_nonneg (le_of_lt hθ₀pos) _)
      have h13 := intervalIntegral.integral_mono_on_of_le_Ioo hθ₀lt.le hIend hIconst hpt2
      rw [intervalIntegral.integral_const, smul_eq_mul] at h13
      calc ∫ θ in θ₀..ε, θ ^ (a - 1) * |deriv h θ| ≤ (ε - θ₀) * (θ₀ ^ (a - 1) * Kφ) := h13
        _ = θ₀ ^ (a - 1) * Kφ * (ε - θ₀) := by ring
    rcases le_total δ θ₀ with hcase | hcase
    · -- ### `δ ≤ θ₀`
      have hpt : ∀ θ ∈ Set.Ioo δ θ₀,
          θ ^ (a - 1) * |deriv h θ|
            ≤ θ ^ (a - 1) * (|deriv h θ₀| + ∫ s in θ..θ₀, |deriv (deriv h) s|) := by
        intro θ hθ
        have hθmem : θ ∈ Set.Ioo 0 ε := ⟨lt_trans hδ0 hθ.1, lt_trans hθ.2 hθ₀lt⟩
        have h1 : |deriv h θ| ≤ |deriv h θ₀| + ∫ s in θ..θ₀, |deriv (deriv h) s| := by
          have h2 : |deriv h θ₀ - deriv h θ| ≤ ∫ s in θ..θ₀, |deriv (deriv h) s| :=
            abs_deriv_sub_le hC2 hθmem hθ₀mem hθ.2.le
          have h3 : |deriv h θ| ≤ |deriv h θ₀| + |deriv h θ₀ - deriv h θ| := by
            have h4 := abs_add_le (deriv h θ - deriv h θ₀) (deriv h θ₀)
            rw [sub_add_cancel] at h4
            rw [abs_sub_comm] at h4
            linarith
          linarith
        exact mul_le_mul_of_nonneg_left h1
          (Real.rpow_nonneg (le_of_lt (lt_trans hδ0 hθ.1)) _)
      have hM' : 0 ≤ |deriv h θ₀| + δ ^ (-a) * Kψ :=
        add_nonneg (abs_nonneg _) (mul_nonneg (Real.rpow_nonneg hδ0.le _) hKψnn)
      have hφ_aux : ∀ θ ∈ Set.Ioo δ θ₀, |deriv h θ| ≤ |deriv h θ₀| + δ ^ (-a) * Kψ := by
        intro θ hθ
        have hθmem : θ ∈ Set.Ioo 0 ε := ⟨lt_trans hδ0 hθ.1, lt_trans hθ.2 hθ₀lt⟩
        have h1 : |deriv h θ| ≤ |deriv h θ₀| + ∫ s in θ..θ₀, |deriv (deriv h) s| := by
          have h2 : |deriv h θ₀ - deriv h θ| ≤ ∫ s in θ..θ₀, |deriv (deriv h) s| :=
            abs_deriv_sub_le hC2 hθmem hθ₀mem hθ.2.le
          have h3 : |deriv h θ| ≤ |deriv h θ₀| + |deriv h θ₀ - deriv h θ| := by
            have h4 := abs_add_le (deriv h θ - deriv h θ₀) (deriv h θ₀)
            rw [sub_add_cancel] at h4
            rw [abs_sub_comm] at h4
            linarith
          linarith
        have h5 : ∫ s in θ..θ₀, |deriv (deriv h) s| ≤ δ ^ (-a) * Kψ := by
          have h6 : ∫ s in θ..θ₀, |deriv (deriv h) s| ≤ θ ^ (-a) * Kψ :=
            hψ_le (u := θ) (v := θ₀) (lt_trans hδ0 hθ.1) hθ.2.le hθ₀lt
          have h7 : θ ^ (-a) * Kψ ≤ δ ^ (-a) * Kψ :=
            mul_le_mul_of_nonneg_right
              (Real.rpow_le_rpow_of_nonpos hδ0 hθ.1.le (by linarith : -a ≤ 0)) hKψnn
          linarith
        linarith
      have hI1 : IntervalIntegrable (fun θ : ℝ => θ ^ (a - 1) * |deriv h θ|) volume δ θ₀ :=
        hardyPow_intervalIntegrable_rpow_mul (p := a - 1) (by linarith) hδ0 hcase
          (hφ_cont.mono (fun x hx => ⟨lt_trans hδ0 hx.1, lt_trans hx.2 hθ₀lt⟩)).abs
          (fun x hx => by rw [abs_abs]; exact hφ_aux x hx) hM'
      have hcont2 : ContinuousOn (fun θ : ℝ => ∫ s in θ..θ₀, |deriv (deriv h) s|)
          (Set.Ioo δ θ₀) := by
        have hsub : Set.uIcc δ θ₀ ⊆ Set.Ioo 0 ε := fun x hx => by
          rw [Set.uIcc_of_le hcase] at hx
          exact ⟨lt_of_lt_of_le hδ0 hx.1, lt_of_le_of_lt hx.2 hθ₀lt⟩
        have hII : IntervalIntegrable (fun s : ℝ => |deriv (deriv h) s|) volume δ θ₀ :=
          ((hψc.mono hsub).abs).intervalIntegrable
        have hpc := intervalIntegral.continuousOn_primitive_interval' (a := θ₀) hII (by
          rw [Set.uIcc_of_le hcase]; exact ⟨hcase, le_rfl⟩)
        have hfun : (fun θ : ℝ => ∫ s in θ..θ₀, |deriv (deriv h) s|)
            = fun b : ℝ => -∫ x in θ₀..b, |deriv (deriv h) x| := by
          funext θ
          exact intervalIntegral.integral_symm θ₀ θ
        rw [hfun]
        exact hpc.neg.mono (fun x hx => Set.mem_uIcc.mpr (Or.inl ⟨le_of_lt hx.1, le_of_lt hx.2⟩))
      have hI2 : IntervalIntegrable
          (fun θ : ℝ => θ ^ (a - 1) * (|deriv h θ₀| + ∫ s in θ..θ₀, |deriv (deriv h) s|))
          volume δ θ₀ :=
        hardyPow_intervalIntegrable_rpow_mul (p := a - 1) (by linarith) hδ0 hcase
          (continuousOn_const.add hcont2)
          (fun x hx => by
            rw [abs_of_nonneg (add_nonneg (abs_nonneg _)
              (intervalIntegral.integral_nonneg hx.2.le (fun u _ => abs_nonneg _)))]
            have h6 : ∫ s in x..θ₀, |deriv (deriv h) s| ≤ δ ^ (-a) * Kψ := by
              have h7 : ∫ s in x..θ₀, |deriv (deriv h) s| ≤ x ^ (-a) * Kψ :=
                hψ_le (u := x) (v := θ₀) (lt_trans hδ0 hx.1) hx.2.le hθ₀lt
              have h8 : x ^ (-a) * Kψ ≤ δ ^ (-a) * Kψ :=
                mul_le_mul_of_nonneg_right
                  (Real.rpow_le_rpow_of_nonpos hδ0 hx.1.le (by linarith : -a ≤ 0)) hKψnn
              linarith
            linarith)
          hM'
      have hcomp := intervalIntegral.integral_mono_on_of_le_Ioo hcase hI1 hI2 hpt
      -- split the comparison integral
      have hI2a : IntervalIntegrable
          (fun θ : ℝ => θ ^ (a - 1) * |deriv h θ₀|) volume δ θ₀ :=
        hardyPow_intervalIntegrable_rpow_mul (p := a - 1) (by linarith) hδ0 hcase continuousOn_const
          (fun x hx => by rw [abs_of_nonneg (abs_nonneg (deriv h θ₀))])
          (abs_nonneg _)
      have hI2b : IntervalIntegrable
          (fun θ : ℝ => θ ^ (a - 1) * (∫ s in θ..θ₀, |deriv (deriv h) s|)) volume δ θ₀ :=
        hardyPow_intervalIntegrable_rpow_mul (p := a - 1) (by linarith) hδ0 hcase hcont2
          (fun x hx => by
            rw [abs_of_nonneg (intervalIntegral.integral_nonneg hx.2.le (fun u _ => abs_nonneg _))]
            have h6 : ∫ s in x..θ₀, |deriv (deriv h) s| ≤ δ ^ (-a) * Kψ := by
              have h7 : ∫ s in x..θ₀, |deriv (deriv h) s| ≤ x ^ (-a) * Kψ :=
                hψ_le (u := x) (v := θ₀) (lt_trans hδ0 hx.1) hx.2.le hθ₀lt
              have h8 : x ^ (-a) * Kψ ≤ δ ^ (-a) * Kψ :=
                mul_le_mul_of_nonneg_right
                  (Real.rpow_le_rpow_of_nonpos hδ0 hx.1.le (by linarith : -a ≤ 0)) hKψnn
              linarith
            exact h6)
          (mul_nonneg (Real.rpow_nonneg hδ0.le _) hKψnn)
      have hexp : ∫ θ in δ..θ₀,
            θ ^ (a - 1) * (|deriv h θ₀| + ∫ s in θ..θ₀, |deriv (deriv h) s|)
          = |deriv h θ₀| * (θ₀ ^ a - δ ^ a) / a
            + ∫ θ in δ..θ₀, θ ^ (a - 1) * (∫ s in θ..θ₀, |deriv (deriv h) s|) := by
        rw [show (fun θ : ℝ => θ ^ (a - 1) * (|deriv h θ₀| + ∫ s in θ..θ₀, |deriv (deriv h) s|))
              = fun θ : ℝ => θ ^ (a - 1) * |deriv h θ₀|
                  + θ ^ (a - 1) * (∫ s in θ..θ₀, |deriv (deriv h) s|) from by
              funext θ; ring]
        rw [intervalIntegral.integral_add hI2a hI2b, intervalIntegral.integral_mul_const,
          integral_rpow (Or.inl (by linarith : (-1 : ℝ) < a - 1)),
          show a - 1 + 1 = a by ring]
        ring
      have hstep2 : ∫ θ in δ..θ₀, θ ^ (a - 1) * (∫ s in θ..θ₀, |deriv (deriv h) s|)
          ≤ (1 / a) * ∫ θ in δ..θ₀, θ ^ a * |deriv (deriv h) θ| :=
        hardyPowPrimIbp ha0 ha1 hδ0 hcase
          ((hψc.mono (fun x hx => ⟨lt_of_lt_of_le hδ0 hx.1, lt_of_le_of_lt hx.2 hθ₀lt⟩)).abs)
          (fun s _ => abs_nonneg _)
      have hstep3 : ∫ θ in δ..θ₀, θ ^ a * |deriv (deriv h) θ| ≤ Kψ := by
        rw [hKψ, intervalIntegral.integral_of_le hcase]
        refine setIntegral_mono_set hIntψ
          (ae_restrict_of_forall_mem measurableSet_Ioc
            (fun x hx => mul_nonneg (Real.rpow_nonneg hx.1.le a) (abs_nonneg _)))
          (Filter.Eventually.of_forall fun x hx => ⟨lt_trans hδ0 hx.1, le_trans hx.2 hθ₀lt.le⟩)
      have hfin1 : ∫ θ in δ..θ₀, θ ^ (a - 1) * |deriv h θ| ≤ |deriv h θ₀| * θ₀ ^ a / a
          + (1 / a) * Kψ := by
        have h7 : |deriv h θ₀| * (θ₀ ^ a - δ ^ a) / a ≤ |deriv h θ₀| * θ₀ ^ a / a := by
          have h10 : 0 ≤ |deriv h θ₀| := abs_nonneg _
          have h11 : 0 ≤ |deriv h θ₀| * δ ^ a := mul_nonneg h10 (Real.rpow_nonneg hδ0.le _)
          rw [div_le_div_iff_of_pos_right ha0, mul_sub]
          linarith [h11]
        have h11 : (1 / a) * (∫ θ in δ..θ₀, θ ^ a * |deriv (deriv h) θ|) ≤ (1 / a) * Kψ :=
          mul_le_mul_of_nonneg_left hstep3 (by positivity)
        calc ∫ θ in δ..θ₀, θ ^ (a - 1) * |deriv h θ|
            ≤ ∫ θ in δ..θ₀,
                θ ^ (a - 1) * (|deriv h θ₀| + ∫ s in θ..θ₀, |deriv (deriv h) s|) := hcomp
          _ = |deriv h θ₀| * (θ₀ ^ a - δ ^ a) / a
              + ∫ θ in δ..θ₀, θ ^ (a - 1) * (∫ s in θ..θ₀, |deriv (deriv h) s|) := hexp
          _ ≤ |deriv h θ₀| * (θ₀ ^ a - δ ^ a) / a
              + (1 / a) * ∫ θ in δ..θ₀, θ ^ a * |deriv (deriv h) θ| := add_le_add le_rfl hstep2
          _ ≤ |deriv h θ₀| * θ₀ ^ a / a + (1 / a) * Kψ := add_le_add h7 h11
      have hsplit := intervalIntegral.integral_add_adjacent_intervals hI1 hIend
      have hfin : ∫ θ in δ..ε, θ ^ (a - 1) * |deriv h θ|
          ≤ |deriv h θ₀| * θ₀ ^ a / a + (1 / a) * Kψ + θ₀ ^ (a - 1) * Kφ * (ε - θ₀) := by
        linarith [hfin1, hup, hsplit]
      rw [hK]
      exact hfin
    · -- ### `θ₀ ≤ δ`
      have hdd : ∀ θ ∈ Set.Ioo θ₀ δ, |deriv h θ| ≤ Kφ :=
        fun x hx => hφ_le_Kφ x ⟨hx.1, lt_of_lt_of_le hx.2 hδε⟩
      have hImid : IntervalIntegrable (fun θ : ℝ => θ ^ (a - 1) * |deriv h θ|) volume θ₀ δ :=
        hardyPow_intervalIntegrable_rpow_mul (p := a - 1) (by linarith) hθ₀pos hcase
          (hφ_cont.mono (fun x hx => ⟨lt_trans hθ₀pos hx.1, lt_of_lt_of_le hx.2 hδε⟩)).abs
          (fun x hx => by simpa using hdd x hx) hKφnn
      have hnonneg : 0 ≤ ∫ θ in θ₀..δ, θ ^ (a - 1) * |deriv h θ| :=
        intervalIntegral.integral_nonneg hcase (fun u hu => mul_nonneg
          (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hθ₀pos hu.1)) _) (abs_nonneg _))
      have hIdd : IntervalIntegrable (fun θ : ℝ => θ ^ (a - 1) * |deriv h θ|) volume δ ε :=
        hardyPow_intervalIntegrable_rpow_mul (p := a - 1) (by linarith) hδ0 hδε
          (hφ_cont.mono (fun x hx => ⟨lt_trans hδ0 hx.1, hx.2⟩)).abs
          (fun x hx => by rw [abs_abs]; exact hφ_le_Kφ x ⟨lt_of_le_of_lt hcase hx.1, hx.2⟩) hKφnn
      have hsplit := intervalIntegral.integral_add_adjacent_intervals hImid hIdd
      have hle : ∫ θ in δ..ε, θ ^ (a - 1) * |deriv h θ|
          ≤ ∫ θ in θ₀..ε, θ ^ (a - 1) * |deriv h θ| := by linarith
      have hfin : ∫ θ in δ..ε, θ ^ (a - 1) * |deriv h θ| ≤ K := by
        rw [hK]
        have h1 : 0 ≤ |deriv h θ₀| * θ₀ ^ a / a := by positivity
        have h2 : 0 ≤ (1 / a) * Kψ := by positivity
        linarith [hle, hup, h1, h2]
      exact hfin
  have hIntW : MeasureTheory.IntegrableOn (fun θ : ℝ => θ ^ (a - 1) * |deriv h θ|)
      (Set.Ioo 0 ε) := by
    refine integrableOn_Ioo_of_intervalIntegral_le hε (fun x hx => ?_) (fun δ hδ => ?_) (fun δ hδ => hw_le_K δ hδ)
    · exact mul_nonneg (Real.rpow_nonneg hx.1.le _) (abs_nonneg _)
    · have hMnn : 0 ≤ max (|deriv h θ₀| + δ ^ (-a) * Kψ) Kφ :=
        le_trans (abs_nonneg (deriv h θ₀)) (le_trans (le_add_of_nonneg_right
          (mul_nonneg (Real.rpow_nonneg (le_of_lt hδ.1) _) hKψnn)) (le_max_left _ _))
      have hφ_le_M : ∀ θ ∈ Set.Ioo δ ε,
          |deriv h θ| ≤ max (|deriv h θ₀| + δ ^ (-a) * Kψ) Kφ := by
        intro θ hθ
        rcases lt_or_ge θ θ₀ with hlt | hge
        · have hθmem : θ ∈ Set.Ioo 0 ε := ⟨lt_trans hδ.1 hθ.1, hθ.2⟩
          have h1 : |deriv h θ - deriv h θ₀| ≤ ∫ s in θ..θ₀, |deriv (deriv h) s| := by
            rw [abs_sub_comm]
            exact abs_deriv_sub_le hC2 hθmem hθ₀mem hlt.le
          have h2 : ∫ s in θ..θ₀, |deriv (deriv h) s| ≤ θ ^ (-a) * Kψ :=
            hψ_le (lt_trans hδ.1 hθ.1) hlt.le hθ₀lt
          have h3 : θ ^ (-a) * Kψ ≤ δ ^ (-a) * Kψ :=
            mul_le_mul_of_nonneg_right
              (Real.rpow_le_rpow_of_nonpos hδ.1 hθ.1.le (by linarith : -a ≤ 0)) hKψnn
          have h4 : |deriv h θ| ≤ |deriv h θ₀| + |deriv h θ - deriv h θ₀| := by
            have h5 := abs_add_le (deriv h θ - deriv h θ₀) (deriv h θ₀)
            rw [sub_add_cancel] at h5
            linarith
          exact le_trans (by linarith) (le_max_left _ _)
        · rcases eq_or_lt_of_le hge with heq | hlt
          · rw [← heq]
            exact le_trans (le_add_of_nonneg_right
              (mul_nonneg (Real.rpow_nonneg hδ.1.le _) hKψnn)) (le_max_left _ _)
          · exact le_trans (hφ_le_Kφ θ ⟨hlt, hθ.2⟩) (le_max_right _ _)
      exact hardyPow_intervalIntegrable_rpow_mul (p := a - 1) (by linarith) hδ.1 hδ.2.le
        (hφ_cont.mono (fun x hx => ⟨lt_trans hδ.1 hx.1, hx.2⟩)).abs
        (fun x hx => by simpa using hφ_le_M x hx) hMnn
  have hIntW_Ioc : MeasureTheory.IntegrableOn (fun θ : ℝ => θ ^ (a - 1) * |deriv h θ|)
      (Set.Ioc 0 ε) := (integrableOn_Ioc_iff_integrableOn_Ioo).2 hIntW
  set Δ : ℝ := ∫ x in Set.Ioc 0 ε, x ^ (a - 1) * |deriv h x| with hΔ
  have hΔnn : 0 ≤ Δ := by
    rw [hΔ]
    exact setIntegral_nonneg measurableSet_Ioc
      (fun x hx => mul_nonneg (Real.rpow_nonneg hx.1.le _) (abs_nonneg _))
  have habsIntIoo : MeasureTheory.IntegrableOn (fun x : ℝ => |deriv h x|) (Set.Ioo 0 ε) := by
    have h1 : MeasureTheory.IntegrableOn
        (fun x : ℝ => ε ^ (1 - a) * (x ^ (a - 1) * |deriv h x|)) (Set.Ioo 0 ε) :=
      hIntW.integrable.const_mul _
    refine MeasureTheory.Integrable.mono' h1 ?_ ?_
    · exact hφ_cont.abs.aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      rw [Real.norm_eq_abs, abs_abs]
      have h2 : x ^ (1 - a) ≤ ε ^ (1 - a) :=
        Real.rpow_le_rpow hx.1.le hx.2.le (by linarith)
      have h3 : |deriv h x| = x ^ (1 - a) * (x ^ (a - 1) * |deriv h x|) := by
        rw [← mul_assoc, ← Real.rpow_add hx.1, show 1 - a + (a - 1) = 0 by ring,
          Real.rpow_zero, one_mul]
      calc |deriv h x| = x ^ (1 - a) * (x ^ (a - 1) * |deriv h x|) := h3
        _ ≤ ε ^ (1 - a) * (x ^ (a - 1) * |deriv h x|) :=
            mul_le_mul_of_nonneg_right h2 (mul_nonneg (Real.rpow_nonneg hx.1.le _) (abs_nonneg _))
  have habsInt : ∀ {δ : ℝ}, 0 < δ → δ < ε →
      MeasureTheory.IntegrableOn (fun x : ℝ => |deriv h x|) (Set.Ioc 0 δ) := by
    intro δ hδ0 hδε
    exact (integrableOn_Ioc_iff_integrableOn_Ioo).2
      (habsIntIoo.mono_set (fun x hx => ⟨hx.1, lt_trans hx.2 hδε⟩))
  have hhδ_le : ∀ {δ : ℝ}, 0 < δ → δ < ε → |h δ| ≤ δ ^ (1 - a) * Δ := by
    intro δ hδ0 hδε
    have hInt : MeasureTheory.IntegrableOn (fun x : ℝ => |deriv h x|) (Set.Ioc 0 δ) :=
      habsInt hδ0 hδε
    have hwInt : ∫ x in Set.Ioc 0 δ, |deriv h x| ≤ δ ^ (1 - a) * Δ := by
      rw [← intervalIntegral.integral_of_le hδ0.le]
      have hI1 : IntervalIntegrable (fun x : ℝ => |deriv h x|) volume 0 δ := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hδ0.le]
        exact hInt
      have hI2 : IntervalIntegrable
          (fun x : ℝ => δ ^ (1 - a) * (x ^ (a - 1) * |deriv h x|)) volume 0 δ := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hδ0.le,
          integrableOn_Ioc_iff_integrableOn_Ioo]
        exact (hIntW.mono_set (fun x hx => ⟨hx.1, lt_trans hx.2 hδε⟩)).integrable.const_mul _
      have hstep := intervalIntegral.integral_mono_on_of_le_Ioo hδ0.le hI1 hI2
        (fun x hx => by
          have h1 : x ^ (1 - a) ≤ δ ^ (1 - a) :=
            Real.rpow_le_rpow hx.1.le hx.2.le (by linarith)
          calc |deriv h x| = x ^ (1 - a) * (x ^ (a - 1) * |deriv h x|) := by
                rw [← mul_assoc, ← Real.rpow_add hx.1, show 1 - a + (a - 1) = 0 by ring,
                  Real.rpow_zero, one_mul]
            _ ≤ δ ^ (1 - a) * (x ^ (a - 1) * |deriv h x|) :=
                mul_le_mul_of_nonneg_right h1
                  (mul_nonneg (Real.rpow_nonneg hx.1.le _) (abs_nonneg _)))
      rw [intervalIntegral.integral_const_mul] at hstep
      refine le_trans hstep (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hδ0.le _))
      rw [hΔ, intervalIntegral.integral_of_le hδ0.le]
      exact setIntegral_mono_set hIntW_Ioc
        (ae_restrict_of_forall_mem measurableSet_Ioc
          (fun x hx => mul_nonneg (Real.rpow_nonneg hx.1.le _) (abs_nonneg _)))
        (Filter.Eventually.of_forall fun x hx => ⟨hx.1, le_trans hx.2 hδε.le⟩)
    refine le_of_forall_pos_le_add (fun e he => ?_)
    have hball : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), h t ∈ Metric.ball (0 : ℝ) e :=
      h0.eventually (Metric.ball_mem_nhds (0 : ℝ) he)
    have hev : {t : ℝ | |h t| < e} ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
      refine hball.mono (fun t ht => ?_)
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
      exact ht
    rw [Metric.mem_nhdsWithin_iff] at hev
    obtain ⟨δ', hδ', hsub'⟩ := hev
    set η : ℝ := min (δ / 2) (δ' / 2) with hηdef
    have hη0 : 0 < η := by
      rw [hηdef]; exact lt_min (by linarith) (by linarith)
    have hηδ : η < δ := by
      rw [hηdef]; linarith [min_le_left (δ / 2) (δ' / 2)]
    have hηδ' : η < δ' := by
      rw [hηdef]; linarith [min_le_right (δ / 2) (δ' / 2)]
    have hhη : |h η| < e := by
      refine hsub' ⟨?_, hη0⟩
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hη0]
      exact hηδ'
    have hsub2 : Set.uIcc η δ ⊆ Set.Ioo 0 ε := fun x hx => by
      rw [Set.uIcc_of_le hηδ.le] at hx
      exact ⟨lt_of_lt_of_le hη0 hx.1, lt_of_le_of_lt hx.2 hδε⟩
    have hd : ∀ x ∈ Set.uIcc η δ, HasDerivAt h (deriv h x) x := fun x hx => hφd x (hsub2 hx)
    have hi : IntervalIntegrable (deriv h) volume η δ := (hφ_cont.mono hsub2).intervalIntegrable
    have hFTC : ∫ s in η..δ, deriv h s = h δ - h η :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
    have h1 : |h δ - h η| ≤ ∫ s in η..δ, |deriv h s| := by
      rw [← hFTC]; exact intervalIntegral.abs_integral_le_integral_abs hηδ.le
    have h2 : |h δ| ≤ |h η| + |h δ - h η| := by
      have h3 := abs_add_le (h δ - h η) (h η)
      rw [sub_add_cancel] at h3
      linarith
    have h3 : ∫ s in η..δ, |deriv h s| ≤ ∫ x in Set.Ioc 0 δ, |deriv h x| := by
      rw [intervalIntegral.integral_of_le hηδ.le]
      exact setIntegral_mono_set hInt
        (ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => abs_nonneg _))
        (Filter.Eventually.of_forall fun x hx => ⟨lt_trans hη0 hx.1, hx.2⟩)
    linarith [hhη, h1, h2, h3, hwInt]
  refine ⟨hIntW_Ioc, habsIntIoo, fun δ hδ => ?_, fun δ hδ => ?_⟩
  · rw [hΔ]; exact hhδ_le hδ.1 hδ.2
  · rw [hΔ, intervalIntegral.integral_of_le hδ.2.le]
    exact setIntegral_mono_set hIntW_Ioc
      (ae_restrict_of_forall_mem measurableSet_Ioc
        (fun x hx => mul_nonneg (Real.rpow_nonneg hx.1.le _) (abs_nonneg _)))
      (Filter.Eventually.of_forall fun x hx => ⟨lt_of_le_of_lt hδ.1.le hx.1, hx.2⟩)

end Work.FTS.EllSol.VthAux.traceAux
