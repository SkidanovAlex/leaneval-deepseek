import Mathlib
import Submission.Work.Smooth.SphereJordan.radialDefs
import Submission.Work.Smooth.SphereJordan.half_spans_setup

/-!
# The winding number of a continuous closed plane curve

For a continuous closed plane curve `c` (a `PlaneCurve`) and a point `p` off its trace, the
**winding number** `wd c p` is the index (`Work.Smooth.SphereJordan.loopIndex`) of the loop
`t ↦ c (2π t) - p`.  Recorded here:

* `wd_mul`, `wd_eq_of_segment` — multiplicativity and constancy along a segment off the trace;
* `wd_eq_zero_of_unbounded_side` — the winding number vanishes on the unbounded side.
-/

open Set

noncomputable section

namespace Work.Smooth.SphereJordan

open Work.Smooth.Jordan

variable {c : PlaneCurve}

/-- The closed loop `t ↦ c (2π t) - p`. -/
def loo (c : PlaneCurve) (p : ℂ) : C(unitInterval, ℂ) :=
  ⟨fun t => c.γ (tp * (t : ℝ)) - p, (c.cont.comp (continuous_const.mul continuous_subtype_val)).sub
    continuous_const⟩

@[simp] theorem loo_apply (c : PlaneCurve) (p : ℂ) (t : unitInterval) :
    loo c p t = c.γ (tp * (t : ℝ)) - p := rfl

theorem loo_closed (c : PlaneCurve) (p : ℂ) : loo c p 0 = loo c p 1 := by
  have h0 : tp * (((0 : unitInterval) : ℝ)) = 0 := by
    rw [show (((0 : unitInterval) : ℝ)) = 0 from rfl, mul_zero]
  have h1 : tp * (((1 : unitInterval) : ℝ)) = tp := by
    rw [show (((1 : unitInterval) : ℝ)) = 1 from rfl, mul_one]
  simp only [loo_apply, h0, h1]
  have hper : c.γ tp = c.γ 0 := by
    have h := c.periodic 0
    rwa [zero_add] at h
  rw [hper]

/-- The winding number of the plane curve `c` around the point `p`. -/
def wd (c : PlaneCurve) (p : ℂ) : ℤ := loopIndex (loo c p)

/-- **Multiplicativity.**  With the ratio loop `t ↦ loo c p t / loo c q t` (a continuous closed
loop when both loops avoid `0`), the winding number around `p` is the winding number around `q`
plus the index of the ratio. -/
theorem wd_mul (c : PlaneCurve) (p q : ℂ)
    (hp : ∀ t : unitInterval, loo c p t ≠ 0) (hq : ∀ t : unitInterval, loo c q t ≠ 0)
    (R : C(unitInterval, ℂ)) (hR : ∀ t, R t = loo c p t / loo c q t) :
    wd c p = wd c q + loopIndex R := by
  have hpq : loo c q * R = loo c p := by
    ext t
    simp only [ContinuousMap.mul_apply, hR t]
    exact mul_div_cancel₀ (loo c p t) (hq t)
  have hRne : ∀ t : unitInterval, R t ≠ 0 := by
    intro t
    rw [hR t]
    exact div_ne_zero (hp t) (hq t)
  have hRcl : R 0 = R 1 := by rw [hR 0, hR 1, loo_closed c p, loo_closed c q]
  have hmul := loopIndex_mul (loo c q) R hq hRne (loo_closed c q) hRcl
  rw [hpq] at hmul
  simp only [wd]
  rw [hmul]

/-- **The Möbius value of a point off a segment.**  For `p ≠ q` and `z ∉ [p,q]`, the number
`(z-p)/(z-q)` lies in the slit plane `ℂ ∖ (-∞,0]`. -/
theorem mobius_mem_slitPlane {p q z : ℂ} (hpq : p ≠ q) (hz : z ∉ segment ℝ p q) :
    (z - p) / (z - q) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_contra hcon
  push Not at hcon
  obtain ⟨hre, him⟩ := hcon
  have hzq : z ≠ q := fun h => hz (h ▸ right_mem_segment ℝ p q)
  obtain ⟨t, ht⟩ : ∃ t : ℝ, (z - p) / (z - q) = t :=
    ⟨((z - p) / (z - q)).re, Complex.ext (Complex.ofReal_re _) (by
      rw [Complex.ofReal_im, him])⟩
  have ht0 : t ≤ 0 := by have := hre; rw [ht] at this; simpa using this
  have ht1 : t ≠ 1 := fun h => by rw [h] at ht0; norm_num at ht0
  have h2 : z - p = (t : ℂ) * (z - q) := by
    have h3 := congrArg (fun w => w * (z - q)) ht
    rw [div_mul_cancel₀ (z - p) (sub_ne_zero.mpr hzq)] at h3
    exact h3
  have hz1 : z * ((1 : ℂ) - (t : ℂ)) = p - (t : ℂ) * q := by
    linear_combination h2
  set lam : ℝ := -t / (1 - t) with hlamdef
  have hden : (1 - t) ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
  have hlam0 : 0 ≤ lam := by
    rw [hlamdef]; exact div_nonneg (by linarith) (by linarith)
  have hlam1 : lam ≤ 1 := by
    rw [hlamdef, div_le_one (by linarith)]; linarith
  -- the value `(1-lam) p + lam q` equals `z`
  have hlamc : (lam : ℂ) = -(t : ℂ) / ((1 : ℂ) - (t : ℂ)) := by
    rw [hlamdef]
    push_cast
    rw [show ((1 : ℂ) - (t : ℂ)) = ((1 - t : ℝ) : ℂ) by push_cast; ring]
  have hval : ((1 : ℂ) - (lam : ℂ)) * p + (lam : ℂ) * q = z := by
    have hdenC : ((1 : ℂ) - (t : ℂ)) ≠ 0 := by
      rw [show ((1 : ℂ) - (t : ℂ)) = ((1 - t : ℝ) : ℂ) by push_cast; ring]
      exact_mod_cast hden
    apply mul_right_cancel₀ hdenC
    rw [hz1, hlamc]
    field_simp
    ring
  refine hz ?_
  rw [segment_eq_image]
  refine ⟨lam, ⟨hlam0, hlam1⟩, ?_⟩
  change (1 - lam : ℝ) • p + lam • q = z
  rw [show (1 - lam : ℝ) • p + lam • q = ((1 : ℂ) - (lam : ℂ)) * p + (lam : ℂ) * q by
    rw [Complex.real_smul, Complex.real_smul]; push_cast; ring]
  exact hval

/-- **The winding number is constant along a segment avoiding the trace.** -/
theorem wd_eq_of_segment {p q : ℂ} (hpq : ∀ z ∈ segment ℝ p q, z ∉ c.trace) :
    wd c p = wd c q := by
  by_cases hpq' : p = q
  · rw [hpq']
  have hp : ∀ t : unitInterval, loo c p t ≠ 0 := by
    intro t h
    refine hpq p (left_mem_segment ℝ p q) ?_
    have : c.γ (tp * (t : ℝ)) = p := sub_eq_zero.mp (by simpa [loo_apply] using h)
    exact this ▸ c.mem_trace _
  have hq : ∀ t : unitInterval, loo c q t ≠ 0 := by
    intro t h
    refine hpq q (right_mem_segment ℝ p q) ?_
    have : c.γ (tp * (t : ℝ)) = q := sub_eq_zero.mp (by simpa [loo_apply] using h)
    exact this ▸ c.mem_trace _
  have hRne : ∀ t : unitInterval, loo c p t / loo c q t ≠ 0 :=
    fun t => div_ne_zero (hp t) (hq t)
  have hRcl : (fun t : unitInterval => loo c p t / loo c q t) 0
      = (fun t : unitInterval => loo c p t / loo c q t) 1 := by
    simp only [loo_closed c p, loo_closed c q]
  have hcont : Continuous fun t : unitInterval => loo c p t / loo c q t :=
    (loo c p).continuous.div (loo c q).continuous (fun t => hq t)
  obtain ⟨R, hR⟩ : ∃ R : C(unitInterval, ℂ), ∀ t, R t = loo c p t / loo c q t :=
    ⟨⟨_, hcont⟩, fun t => rfl⟩
  have hR2ne : ∀ t, R t ≠ 0 := fun t => by rw [hR t]; exact hRne t
  have hR2cl : R 0 = R 1 := by rw [hR 0, hR 1]; exact hRcl
  have hslit : ∀ t, R t ∈ Complex.slitPlane := fun t => by
    rw [hR t]
    exact mobius_mem_slitPlane hpq' (fun h => hpq _ h (c.mem_trace _))
  have hzero : loopIndex R = 0 := loopIndex_eq_zero_of_slitPlane R hR2ne hR2cl hslit
  have := wd_mul c p q hp hq R hR
  rw [hzero, add_zero] at this
  exact this

/-- **The winding number is constant on a preconnected set avoiding the trace.** -/
theorem wd_eq_of_preconnected {W : Set ℂ} (hW : IsPreconnected W)
    (hsub : W ⊆ c.traceᶜ) {p q : ℂ} (hp : p ∈ W) (hq : q ∈ W) : wd c p = wd c q := by
  haveI : ConnectedSpace W := isConnected_iff_connectedSpace.mp ⟨⟨p, hp⟩, hW⟩
  have hloc : IsLocallyConstant (fun z : W => wd c z.1) := by
    intro s
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp c.isOpen_compl_trace z.1 (hsub z.2)
    have hmem : Subtype.val ⁻¹' Metric.ball z.1 ε ∈ nhds z :=
      (continuous_subtype_val.continuousAt).preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
    refine Filter.mem_of_superset hmem ?_
    intro y hy
    have hconst : wd c y.1 = wd c z.1 := by
      refine wd_eq_of_segment (p := y.1) (q := z.1) (fun w hw => ?_)
      exact hball ((convex_ball z.1 ε).segment_subset hy (Metric.mem_ball_self hε) hw)
    change wd c y.1 ∈ s
    rw [hconst]
    exact hz
  have hcont : Continuous (fun z : W => wd c z.1) := hloc.continuous
  have hpre : IsPreconnected (Set.range (fun z : W => wd c z.1)) := by
    rw [← Set.image_univ]
    exact isPreconnected_univ.image _ hcont.continuousOn
  have hmem : wd c p ∈ Set.range (fun z : W => wd c z.1) := ⟨⟨p, hp⟩, rfl⟩
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hpre) ({wd c p} : Set ℤ)
    ({wd c p}ᶜ) (isClosed_discrete _) (isClosed_discrete _)
    (fun x _ => by by_cases h : x = wd c p <;> simp [h]) (by simp) with h | h
  · exact (Set.mem_singleton_iff.mp (h ⟨⟨q, hq⟩, rfl⟩)).symm
  · exact absurd (h hmem) (by simp)

/-- **The winding number vanishes on the unbounded side.** -/
theorem wd_eq_zero_of_unbounded_side {h : PlaneSeparation c}
    (htrace : c.trace ⊆ Metric.closedBall (0 : ℂ) 1) :
    ∀ p ∈ h.U, wd c p = 0 := by
  obtain ⟨C, hC⟩ := c.isCompact_trace.isBounded.exists_norm_le
  set R : ℝ := max C 1 + 1 with hR
  have hCR : C < R := by
    rw [hR]; exact lt_of_le_of_lt (le_max_left C 1) (lt_add_one _)
  have hR1 : (1:ℝ) < R := by
    rw [hR]; exact lt_of_le_of_lt (le_max_right C 1) (lt_add_one _)
  set p₀ : ℂ := -(R : ℂ) with hp₀
  have hp₀zero : wd c p₀ = 0 := by
    have hne : ∀ t : unitInterval, loo c p₀ t ≠ 0 := by
      intro t hzero
      have h1 : c.γ (tp * (t:ℝ)) = p₀ := sub_eq_zero.mp (by simpa [loo_apply] using hzero)
      have h2 : ‖c.γ (tp * (t:ℝ))‖ ≤ C := hC _ (c.mem_trace _)
      have h3 : ‖c.γ (tp * (t:ℝ))‖ = R := by
        rw [h1, hp₀, norm_neg, Complex.norm_real, Real.norm_eq_abs]
        exact abs_of_pos (by linarith)
      rw [h3] at h2; linarith
    have hslit : ∀ t : unitInterval, loo c p₀ t ∈ Complex.slitPlane := by
      intro t
      rw [Complex.mem_slitPlane_iff]
      left
      have h2 : ‖c.γ (tp * (t:ℝ))‖ ≤ C := hC _ (c.mem_trace _)
      have hre : -C ≤ (c.γ (tp * (t:ℝ))).re := by
        have h1 := (abs_le.mp (Complex.abs_re_le_norm (c.γ (tp * (t:ℝ))))).1
        linarith
      have : (loo c p₀ t).re = (c.γ (tp * (t:ℝ))).re + R := by
        rw [loo_apply, hp₀]
        simp [Complex.sub_re, Complex.neg_re, Complex.ofReal_re]
      rw [this]; linarith
    exact loopIndex_eq_zero_of_slitPlane _ hne (loo_closed c p₀) hslit
  have hfar : p₀ ∈ h.U := by
    refine exterior_subset_sideU h htrace ?_
    show 1 < ‖p₀‖
    rw [hp₀, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    exact hR1
  intro p hp
  rw [wd_eq_of_preconnected h.preconn_U (fun z hz => by rw [← h.union_eq]; exact Or.inl hz)
    hp hfar, hp₀zero]

end Work.Smooth.SphereJordan

end
