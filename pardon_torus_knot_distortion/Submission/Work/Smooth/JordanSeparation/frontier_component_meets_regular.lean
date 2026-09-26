import Mathlib
import Submission.Work.Smooth.JordanSeparation.Defs
import Submission.Work.Smooth.JordanSeparation.isPreconnected_compl_of_totallyDisconnected

/-!
# The frontier of a component of the complement of a `C¹` curve meets the regular part

For a `C¹` `2π`-periodic plane curve `c : ℝ → ℂ` with at least one regular point
(`deriv c.γ t ≠ 0` somewhere) and any point `z` off the trace, the frontier of the connected
component of `z` in `c.traceᶜ` contains a point `c.γ t` at which `c` is regular.

The proof: if the frontier contained only critical values, then (since the frontier of a component
of an open set is contained in the trace) it would be contained in `K = c.γ '' {deriv c.γ = 0}`.
The set `K` is totally disconnected: its images under the two coordinate projections are the
critical values of the `C¹` functions `t ↦ (c.γ t).re`, `t ↦ (c.γ t).im`, and these are Lebesgue
null (Sard in dimension one). Hence `ℂ ∖ K` is preconnected, while the component `U` is clopen
in `ℂ ∖ K`; so `U = ∅` or `U = ℂ ∖ K`, both of which are impossible.
-/

open Set MeasureTheory

namespace Work.Smooth.JordanSeparation

noncomputable section

open Work.Smooth.Jordan

/-! ## Sard's theorem in dimension one -/

/-- **Sard in dimension one.**  For a `C¹` function `f : ℝ → ℝ` the image of the critical set
`{x | f' x = 0}` is Lebesgue-null. -/
theorem volume_image_deriv_eq_zero (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    volume (f '' {x : ℝ | deriv f x = 0}) = 0 := by
  have hgd : ∀ t, HasDerivAt f (deriv f t) t := fun t =>
    (hf.differentiable (by norm_num)).differentiableAt.hasDerivAt
  refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := volume)
    (f' := fun t => ContinuousLinearMap.toSpanSingleton ℝ (deriv f t)) ?_ ?_
  · intro t _
    exact (hgd t).hasFDerivAt.hasFDerivWithinAt
  · intro t ht
    rw [ht, ContinuousLinearMap.det_toSpanSingleton]

/-- The derivative of the real part of a differentiable curve. -/
theorem deriv_re (c : SmoothPlaneCurve) (t : ℝ) :
    deriv (fun x : ℝ => (c.γ x).re) t = (deriv c.γ t).re := by
  have hf : HasFDerivAt c.γ (ContinuousLinearMap.toSpanSingleton ℝ (deriv c.γ t)) t :=
    (c.differentiable.differentiableAt.hasDerivAt).hasFDerivAt
  have hcomp := Complex.reCLM.hasFDerivAt.comp t hf
  have h1 : (Complex.reCLM.comp (ContinuousLinearMap.toSpanSingleton ℝ (deriv c.γ t))) =
      ContinuousLinearMap.toSpanSingleton ℝ (deriv c.γ t).re := by
    ext y
    simp [ContinuousLinearMap.toSpanSingleton_apply]
  rw [h1] at hcomp
  have h2 := hcomp.hasDerivAt.deriv
  simpa [ContinuousLinearMap.toSpanSingleton_apply, Complex.reCLM_apply,
    Function.comp_def] using h2

/-- The derivative of the imaginary part of a differentiable curve. -/
theorem deriv_im (c : SmoothPlaneCurve) (t : ℝ) :
    deriv (fun x : ℝ => (c.γ x).im) t = (deriv c.γ t).im := by
  have hf : HasFDerivAt c.γ (ContinuousLinearMap.toSpanSingleton ℝ (deriv c.γ t)) t :=
    (c.differentiable.differentiableAt.hasDerivAt).hasFDerivAt
  have hcomp := Complex.imCLM.hasFDerivAt.comp t hf
  have h1 : (Complex.imCLM.comp (ContinuousLinearMap.toSpanSingleton ℝ (deriv c.γ t))) =
      ContinuousLinearMap.toSpanSingleton ℝ (deriv c.γ t).im := by
    ext y
    simp [ContinuousLinearMap.toSpanSingleton_apply]
  rw [h1] at hcomp
  have h2 := hcomp.hasDerivAt.deriv
  simpa [ContinuousLinearMap.toSpanSingleton_apply, Complex.imCLM_apply,
    Function.comp_def] using h2

/-- The real parts of the critical values of a smooth plane curve form a null set. -/
theorem volume_image_re_deriv_eq_zero (c : SmoothPlaneCurve) :
    volume ((fun t : ℝ => (c.γ t).re) '' {t : ℝ | deriv c.γ t = 0}) = 0 := by
  have hsub : {t : ℝ | deriv c.γ t = 0} ⊆ {t : ℝ | deriv (fun x : ℝ => (c.γ x).re) t = 0} := by
    intro t ht
    have ht' : deriv c.γ t = 0 := ht
    change deriv (fun x : ℝ => (c.γ x).re) t = 0
    rw [deriv_re c t, ht', Complex.zero_re]
  have h2 : volume ((fun t : ℝ => (c.γ t).re) ''
      {t : ℝ | deriv (fun x : ℝ => (c.γ x).re) t = 0}) = 0 :=
    volume_image_deriv_eq_zero _ (Complex.reCLM.contDiff.comp c.contDiff)
  exact le_antisymm (le_trans (measure_mono (image_mono hsub)) (le_of_eq h2)) bot_le

/-- The imaginary parts of the critical values of a smooth plane curve form a null set. -/
theorem volume_image_im_deriv_eq_zero (c : SmoothPlaneCurve) :
    volume ((fun t : ℝ => (c.γ t).im) '' {t : ℝ | deriv c.γ t = 0}) = 0 := by
  have hsub : {t : ℝ | deriv c.γ t = 0} ⊆ {t : ℝ | deriv (fun x : ℝ => (c.γ x).im) t = 0} := by
    intro t ht
    have ht' : deriv c.γ t = 0 := ht
    change deriv (fun x : ℝ => (c.γ x).im) t = 0
    rw [deriv_im c t, ht', Complex.zero_im]
  have h2 : volume ((fun t : ℝ => (c.γ t).im) ''
      {t : ℝ | deriv (fun x : ℝ => (c.γ x).im) t = 0}) = 0 :=
    volume_image_deriv_eq_zero _ (Complex.imCLM.contDiff.comp c.contDiff)
  exact le_antisymm (le_trans (measure_mono (image_mono hsub)) (le_of_eq h2)) bot_le

/-- A preconnected subset of `ℝ` of measure zero is a subsingleton. -/
theorem subsingleton_of_isPreconnected_of_volume_eq_zero {E : Set ℝ} (hE : IsPreconnected E)
    (hE0 : volume E = 0) : E.Subsingleton := by
  intro x hx y hy
  by_contra hxy
  have hord : E.OrdConnected := hE.ordConnected
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · have hsub : Set.Icc x y ⊆ E := hord.out hx hy
    have hle : volume (Set.Icc x y) ≤ volume E := measure_mono hsub
    have hzero : volume (Set.Icc x y) = 0 := le_antisymm (hle.trans (le_of_eq hE0)) bot_le
    rw [Real.volume_Icc] at hzero
    have : y - x ≤ 0 := ENNReal.ofReal_eq_zero.mp hzero
    linarith
  · have hsub : Set.Icc y x ⊆ E := hord.out hy hx
    have hle : volume (Set.Icc y x) ≤ volume E := measure_mono hsub
    have hzero : volume (Set.Icc y x) = 0 := le_antisymm (hle.trans (le_of_eq hE0)) bot_le
    rw [Real.volume_Icc] at hzero
    have : x - y ≤ 0 := ENNReal.ofReal_eq_zero.mp hzero
    linarith

/-- **The critical values of a smooth plane curve are totally disconnected.**  Every preconnected
subset of `c.γ '' {t | deriv c.γ t = 0}` is a subsingleton. -/
theorem subsingleton_of_subset_criticalImage (c : SmoothPlaneCurve) {E : Set ℂ}
    (hE : E ⊆ c.γ '' {t : ℝ | deriv c.γ t = 0}) (hp : IsPreconnected E) : E.Subsingleton := by
  have hre_sub : (fun z : ℂ => z.re) '' E ⊆
      (fun t : ℝ => (c.γ t).re) '' {t : ℝ | deriv c.γ t = 0} := by
    rintro _ ⟨w, hw, rfl⟩
    rcases hE hw with ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩
  have him_sub : (fun z : ℂ => z.im) '' E ⊆
      (fun t : ℝ => (c.γ t).im) '' {t : ℝ | deriv c.γ t = 0} := by
    rintro _ ⟨w, hw, rfl⟩
    rcases hE hw with ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩
  have hre : ((fun z : ℂ => z.re) '' E).Subsingleton :=
    subsingleton_of_isPreconnected_of_volume_eq_zero
      (hp.image _ Complex.continuous_re.continuousOn)
      (le_antisymm (le_trans (measure_mono hre_sub)
        (le_of_eq (volume_image_re_deriv_eq_zero c))) bot_le)
  have him : ((fun z : ℂ => z.im) '' E).Subsingleton :=
    subsingleton_of_isPreconnected_of_volume_eq_zero
      (hp.image _ Complex.continuous_im.continuousOn)
      (le_antisymm (le_trans (measure_mono him_sub)
        (le_of_eq (volume_image_im_deriv_eq_zero c))) bot_le)
  intro x hx y hy
  exact Complex.ext (hre ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩) (him ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)

/-! ## The main theorem -/

theorem frontier_component_meets_regular (c : Work.Smooth.Jordan.SmoothPlaneCurve)
    {v : ℝ → ℂ} {δ : ℝ}
    (hv : Continuous v) (hδ : 0 < δ) (hper : Function.Periodic v (2 * Real.pi))
    (hinj : ∀ t t' u u' : ℝ, |u| < δ → |u'| < δ →
      Work.Smooth.JordanSeparation.offset c v (t, u)
        = Work.Smooth.JordanSeparation.offset c v (t', u') → u = u')
    (hnc : ∃ t : ℝ, deriv c.γ t ≠ 0)
    {z : ℂ} (hz : z ∉ c.trace) :
    ∃ t : ℝ, c.γ t ∈ frontier (connectedComponentIn c.traceᶜ z) ∧ deriv c.γ t ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  set U : Set ℂ := connectedComponentIn c.traceᶜ z with hUdef
  set S : Set ℝ := {t : ℝ | deriv c.γ t = 0} with hSdef
  set K : Set ℂ := c.γ '' S with hKdef
  have hzU : z ∈ U := mem_connectedComponentIn hz
  have hUopen : IsOpen U := c.isOpen_compl_trace.connectedComponentIn
  -- The trace is connected.
  have htrace_pre : IsPreconnected c.trace := isPreconnected_range c.cont
  -- Periodicity of the derivative and of the curve.
  have hper_deriv : Function.Periodic (fun t : ℝ => deriv c.γ t) (2 * Real.pi) := by
    intro t
    change deriv c.γ (t + 2 * Real.pi) = deriv c.γ t
    have hfun : (fun s : ℝ => c.γ (s + 2 * Real.pi)) = c.γ :=
      funext fun s => c.periodic_apply s
    rw [← deriv_comp_add_const c.γ (2 * Real.pi) t, hfun]
  have hderiv_periodic_add : ∀ (x : ℝ) (m : ℤ),
      deriv c.γ (x + m * (2 * Real.pi)) = deriv c.γ x := by
    intro x m
    have h2 := hper_deriv.int_mul m x
    simpa using h2
  have hcurve_periodic_add : ∀ (x : ℝ) (m : ℤ),
      c.γ (x + m * (2 * Real.pi)) = c.γ x := by
    intro x m
    have h2 := c.periodic.int_mul m x
    simpa using h2
  -- `K` is compact: it is the image of the closed set `S`, modulo the period.
  have hKcompact : IsCompact K := by
    have hSclosed : IsClosed S := by
      rw [hSdef]
      exact isClosed_eq c.continuous_deriv continuous_const
    have h1 : K = c.γ '' (S ∩ Set.Icc 0 (2 * Real.pi)) := by
      apply Set.Subset.antisymm
      · rintro _ ⟨t, ht, rfl⟩
        set n : ℤ := ⌊t / (2 * Real.pi)⌋ with hn
        have hpos : (0 : ℝ) < 2 * Real.pi := two_pi_pos
        have hper' : deriv c.γ (t - (n : ℝ) * (2 * Real.pi)) = deriv c.γ t := by
          rw [show t - (n : ℝ) * (2 * Real.pi)
              = t + ((-n : ℤ) : ℝ) * (2 * Real.pi) from by push_cast; ring]
          exact hderiv_periodic_add t (-n)
        have hperc : c.γ (t - (n : ℝ) * (2 * Real.pi)) = c.γ t := by
          rw [show t - (n : ℝ) * (2 * Real.pi)
              = t + ((-n : ℤ) : ℝ) * (2 * Real.pi) from by push_cast; ring]
          exact hcurve_periodic_add t (-n)
        refine ⟨t - (n : ℝ) * (2 * Real.pi), ⟨?_, ?_⟩, hperc⟩
        · rw [hSdef]
          exact hper'.trans ht
        · constructor
          · have := (le_div_iff₀ hpos).mp (Int.floor_le (t / (2 * Real.pi)))
            linarith
          · have := (div_lt_iff₀ hpos).mp (Int.lt_floor_add_one (t / (2 * Real.pi)))
            linarith
      · rintro _ ⟨t, ht, rfl⟩
        exact ⟨t, ht.1, rfl⟩
    rw [h1]
    exact (IsCompact.inter_left isCompact_Icc hSclosed).image c.cont
  -- `U` is contained in `Kᶜ`.
  have hUK : U ⊆ Kᶜ := by
    intro x hx
    have hxt : x ∈ c.traceᶜ := connectedComponentIn_subset c.traceᶜ z hx
    rintro ⟨t, -, htx⟩
    exact hxt ⟨t, htx⟩
  -- The frontier of `U` is contained in the trace, hence in `K`.
  have hfront_trace : frontier U ⊆ c.trace := by
    intro q hq
    by_contra hqt
    have hqF : q ∈ c.traceᶜ := hqt
    have hqcl : q ∈ closure U := (frontier_eq_closure_inter_closure (s := U) ▸ hq).1
    have hqU : q ∉ U := (hUopen.frontier_eq ▸ hq).2
    obtain ⟨r, hr, hrF⟩ := Metric.mem_nhds_iff.mp (c.isOpen_compl_trace.mem_nhds hqF)
    have hconv : Convex ℝ (Metric.ball q r) := convex_ball q r
    have hball_pre : IsPreconnected (Metric.ball q r) := hconv.isPreconnected
    obtain ⟨y, hyb, hyU⟩ := mem_closure_iff.mp hqcl (Metric.ball q r) Metric.isOpen_ball
      (Metric.mem_ball_self hr)
    have hsubF : Metric.ball q r ∪ U ⊆ c.traceᶜ := by
      rintro x (hx | hx)
      · exact hrF hx
      · exact connectedComponentIn_subset c.traceᶜ z hx
    have hunion : IsPreconnected (Metric.ball q r ∪ U) :=
      hball_pre.union y hyb hyU isPreconnected_connectedComponentIn
    have hsub_y : Metric.ball q r ∪ U ⊆ connectedComponentIn c.traceᶜ y :=
      IsPreconnected.subset_connectedComponentIn (F := c.traceᶜ) hunion (Or.inl hyb) hsubF
    have hzy : connectedComponentIn c.traceᶜ y = connectedComponentIn c.traceᶜ z := by
      refine subset_antisymm ?_ ?_
      · exact IsPreconnected.subset_connectedComponentIn (F := c.traceᶜ)
          isPreconnected_connectedComponentIn (hsub_y (Or.inr hzU))
          (connectedComponentIn_subset c.traceᶜ y)
      · exact IsPreconnected.subset_connectedComponentIn (F := c.traceᶜ)
          isPreconnected_connectedComponentIn hyU (connectedComponentIn_subset c.traceᶜ z)
    have hsub : Metric.ball q r ∪ U ⊆ U := hsub_y.trans (le_of_eq hzy)
    exact hqU (hsub (Or.inl (Metric.mem_ball_self hr)))
  have hfront : frontier U ⊆ K := by
    intro q hq
    rcases hfront_trace hq with ⟨t, rfl⟩
    exact ⟨t, hcon t hq, rfl⟩
  -- `closure U ∩ Kᶜ = U`
  have hclK : closure U ∩ Kᶜ ⊆ U := by
    intro x ⟨hxcl, hxK⟩
    by_contra hxU
    have hxfront : x ∈ frontier U := by
      rw [frontier_eq_closure_inter_closure]
      exact ⟨hxcl, subset_closure (by simpa using hxU : x ∈ Uᶜ)⟩
    exact hxK (hfront hxfront)
  -- The trace is not contained in `K`: otherwise it would be a point.
  have htrace_not_subset : ¬ (c.trace ⊆ K) := by
    intro hsub
    have hsub' : c.trace.Subsingleton := subsingleton_of_subset_criticalImage c hsub htrace_pre
    obtain ⟨t, ht⟩ := hnc
    have hconst : ∀ s : ℝ, c.γ s = c.γ t := fun s =>
      hsub' (Set.mem_range_self s) (Set.mem_range_self t)
    have hderiv : deriv c.γ t = 0 := by
      have hfun : c.γ = fun _ : ℝ => c.γ t := funext hconst
      rw [hfun, deriv_const]
    exact ht hderiv
  obtain ⟨w, hwt, hwK⟩ := Set.not_subset.mp htrace_not_subset
  have hwKU : w ∈ Kᶜ := hwK
  have hwU : w ∉ U := fun h => (connectedComponentIn_subset c.traceᶜ z h) hwt
  -- `ℂ ∖ K` is preconnected, so the clopen subset `U` of it is empty or everything.
  have hpre : IsPreconnected (Kᶜ) :=
    isPreconnected_compl_of_totallyDisconnected hKcompact
      (fun E hE hp => subsingleton_of_subset_criticalImage c hE hp)
  haveI : PreconnectedSpace ↥(Kᶜ) := isPreconnected_iff_preconnectedSpace.mp hpre
  have hclopen : IsClopen ((Subtype.val ⁻¹' U : Set ↥(Kᶜ))) := by
    refine ⟨?_, hUopen.preimage continuous_subtype_val⟩
    have heq : (Subtype.val ⁻¹' U : Set ↥(Kᶜ)) = Subtype.val ⁻¹' closure U := by
      ext x
      constructor
      · intro hx; exact subset_closure hx
      · intro hx; exact hclK ⟨hx, x.2⟩
    rw [heq]
    exact isClosed_closure.preimage continuous_subtype_val
  rcases isClopen_iff.mp hclopen with h0 | h1
  · have hmem : (⟨z, hUK hzU⟩ : ↥(Kᶜ)) ∈ (Subtype.val ⁻¹' U : Set ↥(Kᶜ)) := hzU
    rw [h0] at hmem
    exact hmem
  · have hmem : (⟨w, hwKU⟩ : ↥(Kᶜ)) ∈ (Subtype.val ⁻¹' U : Set ↥(Kᶜ)) := by
      rw [h1]; exact trivial
    exact hwU hmem

end

end Work.Smooth.JordanSeparation
