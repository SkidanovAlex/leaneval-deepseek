import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.IteratedDeriv.ConvergenceOnBall
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Coercivity.uniform_geometric_bound_of_local
import Submission.Work.Coercivity.slice_deriv_bound
import Submission.Work.Coercivity.hasSum_setIntegral_tsum

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal NNReal ContDiff
open MeasureTheory Set Filter

namespace Work.Coercivity

/-! ### Auxiliary facts used in the proof below -/

-- (private helper)
-- (private helper)
-- (private helper)
-- (private helper)
-- (private helper)
/-- The `k`-th Taylor coefficient (in the vector `(1,0)`) of the slice `z ↦ G (z,θ)`
at the point `z₀`, for a function `G : ℝ × ℝ → ℝ`. -/
private def sliceCoeff (G : ℝ × ℝ → ℝ) (z₀ : ℝ) (k : ℕ) (θ : ℝ) : ℝ :=
  iteratedFDeriv ℝ k G (z₀, θ) (fun _ => ((1 : ℝ), (0 : ℝ))) / (k.factorial : ℝ)

private lemma hfps_comp_add_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {p : FormalMultilinearSeries ℝ E F} {x c : E} {r : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall f p x r) :
    HasFPowerSeriesOnBall (fun y => f (y + c)) p (x - c) r := by
  refine ⟨h.r_le, h.r_pos, ?_⟩
  intro y h1
  have h2 := h.hasSum h1
  convert h2 using 2
  abel

private lemma hfpsAt_comp_add_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {p : FormalMultilinearSeries ℝ E F} {x c : E}
    (h : HasFPowerSeriesAt f p x) :
    HasFPowerSeriesAt (fun y => f (y + c)) p (x - c) := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r, hfps_comp_add_const hr⟩

/-- The slice power series of a function given by a power series at `(z₀,θ)`. -/
private lemma hasFPowerSeriesAt_slice {G : ℝ × ℝ → ℝ} {q : FormalMultilinearSeries ℝ (ℝ × ℝ) ℝ}
    {z₀ θ : ℝ} (h : HasFPowerSeriesAt G q (z₀, θ)) :
    HasFPowerSeriesAt (fun z : ℝ => G (z, θ))
      (q.compContinuousLinearMap (ContinuousLinearMap.inl ℝ ℝ ℝ)) z₀ := by
  have h1 : HasFPowerSeriesAt (fun y : ℝ × ℝ => G (y + (z₀, θ))) q 0 := by
    have hc := hfpsAt_comp_add_const h (c := (z₀, θ))
    rwa [show (z₀, θ) - (z₀, θ) = (0 : ℝ × ℝ) from sub_self _] at hc
  have h2 : HasFPowerSeriesAt
      ((fun y : ℝ × ℝ => G (y + (z₀, θ))) ∘ (ContinuousLinearMap.inl ℝ ℝ ℝ))
      (q.compContinuousLinearMap (ContinuousLinearMap.inl ℝ ℝ ℝ)) ((0 : ℝ)) := by
    have := h1.compContinuousLinearMap (u := ContinuousLinearMap.inl ℝ ℝ ℝ) (x := (0 : ℝ))
    simpa using this
  have h3 := h2.comp_sub z₀
  simpa [Function.comp] using h3

/-- The key identity: the iterated derivative of the slice `z ↦ G (z,θ)` is the iterated
Fréchet derivative of `G` at `(z₀,θ)` evaluated at the constant tuple `(1,0)`. -/
private lemma sliceCoeff_eq_iteratedDeriv {G : ℝ × ℝ → ℝ} {z₀ θ : ℝ}
    (h : AnalyticAt ℝ G (z₀, θ)) (k : ℕ) :
    sliceCoeff G z₀ k θ
      = iteratedDeriv k (fun z => G (z, θ)) z₀ / (k.factorial : ℝ) := by
  obtain ⟨q, hq⟩ := h
  have hslice : HasFPowerSeriesAt (fun z : ℝ => G (z, θ))
      (q.compContinuousLinearMap (ContinuousLinearMap.inl ℝ ℝ ℝ)) z₀ := hasFPowerSeriesAt_slice hq
  have hAnal : AnalyticAt ℝ (fun z : ℝ => G (z, θ)) z₀ := hslice.analyticAt
  have hP : HasFPowerSeriesAt (fun z : ℝ => G (z, θ))
      (FormalMultilinearSeries.ofScalars ℝ
        (fun n => iteratedDeriv n (fun z => G (z, θ)) z₀ / (n.factorial : ℝ))) z₀ :=
    hAnal.hasFPowerSeriesAt
  have heq : (FormalMultilinearSeries.ofScalars ℝ
        (fun n => iteratedDeriv n (fun z => G (z, θ)) z₀ / (n.factorial : ℝ)))
      = q.compContinuousLinearMap (ContinuousLinearMap.inl ℝ ℝ ℝ) :=
    HasFPowerSeriesAt.eq_formalMultilinearSeries hP hslice
  have hk : iteratedDeriv k (fun z => G (z, θ)) z₀ / (k.factorial : ℝ)
      = (q k) (fun _ => ((1 : ℝ), (0 : ℝ))) := by
    have hcongr : (FormalMultilinearSeries.ofScalars ℝ
          (fun n => iteratedDeriv n (fun z => G (z, θ)) z₀ / (n.factorial : ℝ)))
          k (fun _ : Fin k => (1 : ℝ))
        = (q.compContinuousLinearMap (ContinuousLinearMap.inl ℝ ℝ ℝ)) k
          (fun _ : Fin k => (1 : ℝ)) := by
      rw [heq]
    rw [FormalMultilinearSeries.ofScalars_apply_eq,
      FormalMultilinearSeries.compContinuousLinearMap_apply] at hcongr
    simpa [Function.comp_def] using hcongr
  obtain ⟨r, hr⟩ := hq
  have hfs := hr.factorial_smul ((1 : ℝ), (0 : ℝ)) k
  rw [nsmul_eq_mul] at hfs
  rw [sliceCoeff, ← hfs]
  rw [mul_div_cancel_left₀ _ (by exact_mod_cast Nat.factorial_ne_zero k)]
  exact hk.symm

/-- Analyticity of the parametric integral. -/
theorem analyticAt_setIntegral (F : ℝ → ℝ → ℝ)
    (hF : ContDiffOn ℝ ⊤ (Function.uncurry F) (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-1) (π/2 + 1)))
    (z₀ : ℝ) (hz₀ : z₀ ∈ Set.Ioi (0:ℝ)) :
    AnalyticAt ℝ (fun z => ∫ θ in Work.Spaces.Iθ, F z θ) z₀ := by
  have hz₀' : (0 : ℝ) < z₀ := hz₀
  set U : Set (ℝ × ℝ) := Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-1) (π/2 + 1) with hU
  have hUopen : IsOpen U := isOpen_Ioi.prod isOpen_Ioo
  have hAnal : AnalyticOn ℝ (Function.uncurry F) U := hF.analyticOn
  have hAnalAt : ∀ x ∈ U, AnalyticAt ℝ (Function.uncurry F) x :=
    fun x hx => (hUopen.analyticOn_iff_analyticOnNhd.mp hAnal) x hx
  have hIθ_sub : Work.Spaces.Iθ ⊆ Set.Ioo (-1) (π/2 + 1) := by
    intro θ hθ
    simp only [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := isClosed_Icc.measurableSet
  have hIθ_ne_top : volume Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hIθ_compact : IsCompact Work.Spaces.Iθ := isCompact_Icc
  -- local geometric bounds near each angle
  have hloc : ∀ θ ∈ Work.Spaces.Iθ, ∃ ε > 0, ∃ C > 0, ∃ s > 0,
      ∀ k, ∀ θ' ∈ Set.Ioo (θ - ε) (θ + ε),
        |sliceCoeff (Function.uncurry F) z₀ k θ'| ≤ C / s ^ k := by
    intro θ hθ
    have hmem : (z₀, θ) ∈ U := ⟨hz₀, hIθ_sub hθ⟩
    obtain ⟨q, hq⟩ := hAnalAt _ hmem
    obtain ⟨r, hr⟩ := hq
    obtain ⟨r', hr'pos, hr'le⟩ : ∃ r' : ℝ≥0, 0 < r' ∧ (r' : ℝ≥0∞) ≤ r := by
      rcases eq_or_ne r ⊤ with h | h
      · exact ⟨1, one_pos, by simp [h]⟩
      · obtain ⟨r', h0, hlt⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr.r_pos
        exact ⟨r', ENNReal.coe_pos.mp h0, le_of_lt hlt⟩
    have hr'' : HasFPowerSeriesOnBall (Function.uncurry F) q (z₀, θ) (r' : ℝ≥0∞) :=
      HasFPowerSeriesOnBall.mono hr (ENNReal.coe_pos.mpr hr'pos) hr'le
    have hq' : HasFPowerSeriesOnBall
        (fun y : ℝ × ℝ => (Function.uncurry F) (y + (z₀, θ))) q 0 (r' : ℝ≥0∞) := by
      have hthis := hfps_comp_add_const (c := (z₀, θ)) hr''
      simpa using hthis
    have h8pos : (0 : ℝ≥0) < r' / 8 := by positivity
    have h48 : 4 * (r' / 8) < r' := by
      have h4 : (4 : ℝ≥0) * (r' / 8) = r' / 2 := by ring
      rw [h4]
      exact half_lt_self hr'pos
    obtain ⟨C, hCpos, hCbd⟩ := slice_deriv_bound hq' h8pos h48
    refine ⟨((r' / 8 : ℝ≥0) : ℝ), by positivity, C, hCpos, ((r' / 8 : ℝ≥0) : ℝ),
      by positivity, ?_⟩
    intro k θ' hθ'
    rw [Set.mem_Ioo] at hθ'
    have hδ : |θ' - θ| ≤ ((r' / 8 : ℝ≥0) : ℝ) := by
      rw [abs_sub_le_iff]
      exact ⟨by linarith [hθ'.1], by linarith [hθ'.2]⟩
    have hb := hCbd k (θ' - θ) hδ
    have hstep : iteratedFDeriv ℝ k (fun y : ℝ × ℝ => (Function.uncurry F) (y + (z₀, θ)))
          ((0 : ℝ), θ' - θ) (fun _ => ((1 : ℝ), (0 : ℝ)))
        = iteratedFDeriv ℝ k (Function.uncurry F) (z₀, θ') (fun _ => ((1 : ℝ), (0 : ℝ))) := by
      rw [iteratedFDeriv_comp_add_right]
      congr 2
      simp [Prod.mk_add_mk, sub_add_cancel]
    rw [hstep, Real.norm_eq_abs] at hb
    have hkpos : (0 : ℝ) < (k.factorial : ℝ) := by positivity
    rw [sliceCoeff]
    calc |iteratedFDeriv ℝ k (Function.uncurry F) (z₀, θ') (fun _ => ((1 : ℝ), (0 : ℝ)))
            / (k.factorial : ℝ)|
        = |iteratedFDeriv ℝ k (Function.uncurry F) (z₀, θ') (fun _ => ((1 : ℝ), (0 : ℝ)))|
            / (k.factorial : ℝ) := by rw [abs_div, abs_of_pos hkpos]
      _ ≤ (C * (k.factorial : ℝ) / ((r' / 8 : ℝ≥0) : ℝ) ^ k) / (k.factorial : ℝ) := by
          gcongr
      _ = C / ((r' / 8 : ℝ≥0) : ℝ) ^ k := by
          have hA : ((r' / 8 : ℝ≥0) : ℝ) ≠ 0 := by positivity
          field_simp
  obtain ⟨C, hCpos, s, hspos, hbnd⟩ := uniform_geometric_bound_of_local hIθ_compact hloc
  -- a small radius around `z₀`, inside `Ioi 0` and below `s`
  obtain ⟨ρ₀, hρ₀pos, hρ₀z, hρ₀s⟩ :
      ∃ ρ₀ : ℝ≥0, (0 : ℝ) < (ρ₀ : ℝ) ∧ (ρ₀ : ℝ) ≤ z₀ / 2 ∧ (ρ₀ : ℝ) ≤ s := by
    refine ⟨⟨min (z₀ / 2) (s / 2), le_of_lt (lt_min (by linarith) (by linarith))⟩, ?_, ?_, ?_⟩
    · exact lt_min (by linarith) (by linarith)
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (by linarith)
  have hρ₀posE : (0 : ℝ≥0∞) < (ρ₀ : ℝ≥0∞) := ENNReal.coe_pos.mpr (by exact_mod_cast hρ₀pos)
  -- slice analyticity on the whole small ball
  have hslice_anal : ∀ θ ∈ Work.Spaces.Iθ,
      AnalyticOn ℝ (fun z => F z θ) (Metric.eball z₀ (ρ₀ : ℝ≥0∞)) := by
    intro θ hθ z hz
    have hzU : (z, θ) ∈ U := by
      refine ⟨?_, hIθ_sub hθ⟩
      have hb : dist z z₀ < (ρ₀ : ℝ) := by
        rwa [Metric.eball_coe, Metric.mem_ball] at hz
      have h1 : |z - z₀| < z₀ / 2 := lt_of_lt_of_le (by rwa [Real.dist_eq] at hb) hρ₀z
      have h2 : -(z₀ / 2) < z - z₀ := (abs_lt.mp h1).1
      show (0 : ℝ) < z
      linarith
    have h3 : AnalyticAt ℝ (fun z' : ℝ => F z' θ) z := by
      obtain ⟨q, hq⟩ := hAnalAt _ hzU
      exact (hasFPowerSeriesAt_slice hq).analyticAt
    exact h3.analyticWithinAt
  -- power series of the slice with a uniform radius
  have hcoeff : ∀ θ ∈ Work.Spaces.Iθ,
      (fun k => iteratedDeriv k (fun z => F z θ) z₀ / (k.factorial : ℝ))
        = fun k => sliceCoeff (Function.uncurry F) z₀ k θ := by
    intro θ hθ
    funext k
    exact (sliceCoeff_eq_iteratedDeriv (hAnalAt _ ⟨hz₀, hIθ_sub hθ⟩) k).symm
  have hslice_ps : ∀ θ ∈ Work.Spaces.Iθ, HasFPowerSeriesOnBall (fun z => F z θ)
      (FormalMultilinearSeries.ofScalars ℝ (sliceCoeff (Function.uncurry F) z₀ · θ))
      z₀ (ρ₀ : ℝ≥0∞) := by
    intro θ hθ
    have hrad : (ρ₀ : ℝ≥0∞) ≤ (FormalMultilinearSeries.ofScalars ℝ
        (fun k => iteratedDeriv k (fun z => F z θ) z₀ / (k.factorial : ℝ))).radius := by
      rw [hcoeff θ hθ]
      apply FormalMultilinearSeries.le_radius_of_bound _ C
      intro k
      rw [FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs]
      have h1 : |sliceCoeff (Function.uncurry F) z₀ k θ| ≤ C / s ^ k := hbnd k θ hθ
      have h2 : (ρ₀ : ℝ) ^ k ≤ s ^ k := pow_le_pow_left₀ (le_of_lt hρ₀pos) hρ₀s k
      calc |sliceCoeff (Function.uncurry F) z₀ k θ| * (ρ₀ : ℝ) ^ k
          ≤ (C / s ^ k) * s ^ k := by gcongr
        _ = C := by rw [div_mul_cancel₀ _ (pow_ne_zero k (ne_of_gt hspos))]
    have h := (hslice_anal θ hθ).hasFPowerSeriesOnSubball hρ₀posE hrad
    rwa [hcoeff θ hθ] at h
  -- the slice expansions
  have hslicesum : ∀ θ ∈ Work.Spaces.Iθ, ∀ u : ℝ, |u| < (ρ₀ : ℝ) →
      HasSum (fun k => sliceCoeff (Function.uncurry F) z₀ k θ * u ^ k) (F (z₀ + u) θ) := by
    intro θ hθ u hu
    have hmem : u ∈ Metric.eball (0 : ℝ) (ρ₀ : ℝ≥0∞) := by
      rw [Metric.eball_coe, Metric.mem_ball, Real.dist_eq, sub_zero]
      exact hu
    have h := (hslice_ps θ hθ).hasSum (x := z₀) (y := u) hmem
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using h
  -- continuity in the angle of the coefficients
  have hcont_a : ∀ k, ContinuousOn (sliceCoeff (Function.uncurry F) z₀ k) Work.Spaces.Iθ := by
    intro k
    have hdiff : ContDiffOn ℝ (k : ℕ∞ω) (Function.uncurry F) U :=
      hAnal.contDiffOn hUopen.uniqueDiffOn
    have hcont1 : ContinuousOn (iteratedFDerivWithin ℝ k (Function.uncurry F) U) U :=
      hdiff.continuousOn_iteratedFDerivWithin le_rfl hUopen.uniqueDiffOn
    have hcont2 : ContinuousOn (iteratedFDeriv ℝ k (Function.uncurry F)) U :=
      hcont1.congr fun x hx => (iteratedFDerivWithin_of_isOpen k hUopen hx).symm
    have hcont3 : ContinuousOn
        (fun θ => iteratedFDeriv ℝ k (Function.uncurry F) (z₀, θ)) Work.Spaces.Iθ :=
      hcont2.comp ((continuous_const.prodMk continuous_id).continuousOn)
        (fun θ hθ => ⟨hz₀, hIθ_sub hθ⟩)
    have hcont4 : ContinuousOn (fun θ =>
        (iteratedFDeriv ℝ k (Function.uncurry F) (z₀, θ)) (fun _ => ((1 : ℝ), (0 : ℝ))))
        Work.Spaces.Iθ := by
      have hev : Continuous (fun ψ : ContinuousMultilinearMap ℝ (fun _ : Fin k => ℝ × ℝ) ℝ =>
          ψ (fun _ => ((1 : ℝ), (0 : ℝ)))) := continuous_eval_const _
      have hcomp := ContinuousOn.comp
        (f := fun θ => iteratedFDeriv ℝ k (Function.uncurry F) (z₀, θ))
        (g := fun ψ : ContinuousMultilinearMap ℝ (fun _ : Fin k => ℝ × ℝ) ℝ =>
          ψ (fun _ => ((1 : ℝ), (0 : ℝ))))
        (t := Set.univ) hev.continuousOn hcont3 (fun x _ => trivial)
      exact hcomp
    exact hcont4.div_const (k.factorial : ℝ)
  -- swap sum and integral
  have hswap : ∀ u : ℝ, |u| < (ρ₀ : ℝ) → HasSum
      (fun k => (∫ θ in Work.Spaces.Iθ, sliceCoeff (Function.uncurry F) z₀ k θ) * u ^ k)
      (∫ θ in Work.Spaces.Iθ, F (z₀ + u) θ) := by
    intro u hu
    have h1 := hasSum_setIntegral_tsum hCpos hspos hIθ_meas hIθ_ne_top hcont_a hbnd
      (u := u) (by linarith [hu, hρ₀s])
    have hcongr : (∫ θ in Work.Spaces.Iθ,
          ∑' k, sliceCoeff (Function.uncurry F) z₀ k θ * u ^ k)
        = ∫ θ in Work.Spaces.Iθ, F (z₀ + u) θ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hIθ_meas] with θ hθ
      exact (hslicesum θ hθ u hu).tsum_eq
    rwa [hcongr] at h1
  -- the resulting power series for the integral
  refine (show HasFPowerSeriesOnBall (fun z => ∫ θ in Work.Spaces.Iθ, F z θ)
      (FormalMultilinearSeries.ofScalars ℝ
        (fun k => ∫ θ in Work.Spaces.Iθ, sliceCoeff (Function.uncurry F) z₀ k θ)) z₀
      (ρ₀ : ℝ≥0∞) from ?_).analyticAt
  refine ⟨?_, hρ₀posE, ?_⟩
  · apply FormalMultilinearSeries.le_radius_of_bound _ (C * (π / 2))
    intro k
    rw [FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs]
    have hvol : (volume.real Work.Spaces.Iθ) = π / 2 := by
      rw [Measure.real_def, Work.Spaces.Iθ, Real.volume_Icc, sub_zero]
      exact ENNReal.toReal_ofReal (by positivity)
    have h1 : |∫ θ in Work.Spaces.Iθ, sliceCoeff (Function.uncurry F) z₀ k θ|
        ≤ ∫ θ in Work.Spaces.Iθ, |sliceCoeff (Function.uncurry F) z₀ k θ| :=
      abs_integral_le_integral_abs
    have h2 : ∫ θ in Work.Spaces.Iθ, |sliceCoeff (Function.uncurry F) z₀ k θ|
        ≤ (C / s ^ k) * (π / 2) := by
      have hg : Integrable (fun _ : ℝ => C / s ^ k) (volume.restrict Work.Spaces.Iθ) := by
        rw [integrable_const_iff]
        right
        exact ⟨by
          rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
          exact lt_top_iff_ne_top.mpr hIθ_ne_top⟩
      have hle : (fun θ => |sliceCoeff (Function.uncurry F) z₀ k θ|)
          ≤ᵐ[volume.restrict Work.Spaces.Iθ] (fun _ => C / s ^ k) := by
        filter_upwards [ae_restrict_mem hIθ_meas] with θ hθ
        exact hbnd k θ hθ
      have h3 := integral_mono_of_nonneg (Eventually.of_forall fun θ => abs_nonneg _)
        hg hle
      rw [setIntegral_const, hvol, smul_eq_mul, mul_comm] at h3
      exact h3
    have h4 : (ρ₀ : ℝ) ^ k ≤ s ^ k := pow_le_pow_left₀ (le_of_lt hρ₀pos) hρ₀s k
    calc |∫ θ in Work.Spaces.Iθ, sliceCoeff (Function.uncurry F) z₀ k θ| * (ρ₀ : ℝ) ^ k
        ≤ (∫ θ in Work.Spaces.Iθ, |sliceCoeff (Function.uncurry F) z₀ k θ|) * (ρ₀ : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ ((C / s ^ k) * (π / 2)) * s ^ k :=
          mul_le_mul h2 h4 (by positivity) (by positivity)
      _ = C * (π / 2) := by
          rw [mul_assoc, mul_comm (π / 2) (s ^ k), ← mul_assoc,
            div_mul_cancel₀ _ (pow_ne_zero k (ne_of_gt hspos))]
  · intro u hu
    have hu' : |u| < (ρ₀ : ℝ) := by
      rwa [Metric.eball_coe, Metric.mem_ball, Real.dist_eq, sub_zero] at hu
    have h := hswap u hu'
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using h

theorem contDiffOn_setIntegral_Itheta (F : ℝ → ℝ → ℝ)
    (hF : ContDiffOn ℝ ⊤ (Function.uncurry F) (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-1) (π/2 + 1))) :
    ContDiffOn ℝ ⊤ (fun z => ∫ θ in Work.Spaces.Iθ, F z θ) (Set.Ioi 0) := by
  rw [contDiffOn_omega_iff_analyticOn (uniqueDiffOn_Ioi 0)]
  intro z hz
  exact (analyticAt_setIntegral F hF z hz).analyticWithinAt

end Work.Coercivity
