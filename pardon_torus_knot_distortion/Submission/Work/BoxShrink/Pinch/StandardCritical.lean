import Submission.Work.BoxShrink.Pinch.PerpForm
import Submission.Work.BoxShrink.Pinch.winding_zero_of_lift_sin
import Submission.Work.BoxShrink.Bubble.cex_windingSpan_boxRegion_eq_top

/-!
# The residual at the critical configuration: it is verified, and its first branch fails

The residual of the pinch, in the concrete form of `PerpForm.lean`, is the disjunction

  `W(box) ≤ W(halves)`  or  `∃ v ≠ 0` (a class of the trace of the plane) with
  `W(box) ⊓ ℚ ∙ v ≤ W(halves)`.

At the *critical* box of the challenge (`s = 5/2` for the standard torus with `σ = swap 1 2`,
`c = u = 0`, the largest box that still meets the standard torus in a curve with `|x| = s`,
cf. `Work.BoxShrink.Bubble.not_containsEssentialLoop_sphereSet_swap`) both the sphere trace and
the slice are inessential, and this module determines the residual there completely:

* **the first branch of the residual fails**: `W(box) = ⊤` (the box contains the meridian and the
  longitude, `Work.BoxShrink.Bubble.cex_windingSpan_boxRegion_eq_top`) while the region of the box
  above (or below) the cutting plane realises no longitude class at all, so its span is *exactly*
  the line `ℚ ∙ (0,1)` spanned by the meridian;
* **the second branch holds**, with `v = (0,1)` — the class of the trace, which is the meridian at
  `θ = π/2`: the trace of the plane `{y = 0}` on the standard torus is the two meridians
  `θ ∈ {0, π}`, so every trace period is a multiple of `(0,1)`, and the meridian `θ = π/2` lies
  entirely in the upper half-region, so `ℚ ∙ (0,1) ≤ W(halves)` and the containment holds.

This is the chapter's check that the residual is *not refuted* at the configuration where the
naive forms of the push-off fail (`Work.BoxShrink.Pinch.BubbleHalfRefuted`,
`Work.BoxShrink.Bubble.cex_not_slicePushOffSpan`), and that its two branches are both necessary:
the `≤ + 1` of the pinch is exactly the drop from `⊤` to the meridian line.

## The tool

`windingSpan_le_span_snd_of_preimage_sin_pos` (and its sign-reversed form) shows the way the
general statement will have to go: if the preimage of a region of the surface lies in the
half-strip `{sin θ > 0}` of the parameter plane, then no loop of the region advances the longitude
parameter, so the winding span of the region is contained in the line of the meridian:

  `W(X) ≤ ℚ ∙ (0,1)`  whenever  `Φ⁻¹ X ⊆ {0 < sin θ}`.

The proof is `winding_zero_of_lift_sin`'s `eq_zero_of_cont_sin_pos`: a lift of a loop whose `Θ`
stays where `sin` is positive advances by strictly less than `π` over a period, and that advance is
an integer multiple of `2π`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.BoxShrink.Pinch

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## The longitude winding vanishes when the preimage lies in `{sin θ > 0}` -/

/-- **The winding span of a region whose preimage lies in the half-strip `{sin θ > 0}` is contained
in the line of the meridian.**  No loop of such a region can advance the longitude parameter by a
nonzero multiple of `2π`: along a lift, `sin (L.Θ ·)` is positive, and the advance over one period
is an integer multiple of `2π` and strictly less than `π`. -/
theorem windingSpan_le_span_snd_of_preimage_sin_pos {X : Set R3}
    (h : ∀ q : ℝ × ℝ, q ∈ planePreimage P X → 0 < Real.sin q.1) :
    Work.SurgeryInvariance.WindingSpan P X ≤
      Submodule.span ℚ {((0 : ℚ), (1 : ℚ))} := by
  rw [Work.SurgeryInvariance.WindingSpan, Submodule.span_le]
  rintro v ⟨γ, hγ, rfl⟩
  set L : Work.CoreTopology.LiftOf P γ :=
    Classical.choice (Work.TorusCover.ParamTorus_exists_liftOf P γ) with hL
  have hsin : ∀ t : ℝ, 0 < Real.sin (L.Θ t) := by
    intro t
    refine h (L.Θ t, L.Φ t) ?_
    rw [mem_planePreimage]
    rw [L.lifts t]
    exact hγ t
  have hdiff : L.Θ (2 * Real.pi) - L.Θ 0 = ((L.winding).1 : ℝ) * (2 * Real.pi) := by
    rw [L.winding_spec.1]; ring
  have hk : (L.winding).1 = 0 := eq_zero_of_cont_sin_pos L.contΘ hsin hdiff
  rw [Work.SurgeryInvariance.windingOf_eq P γ L, hk]
  have hgoal : ((((0 : ℤ) : ℚ), (((L.winding).2 : ℤ) : ℚ)) : ℚ × ℚ) =
      (((L.winding).2 : ℤ) : ℚ) • ((0 : ℚ), (1 : ℚ)) := by
    ext <;> simp
  rw [hgoal]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

/-- **The same for the sign-reversed half-strip `{sin θ < 0}`**: no loop advances the longitude
parameter there either.  (Apply the positive form to the shifted continuous function
`t ↦ L.Θ t + π`, whose `sin` is `- sin (L.Θ t)`.) -/
theorem windingSpan_le_span_snd_of_preimage_sin_neg {X : Set R3}
    (h : ∀ q : ℝ × ℝ, q ∈ planePreimage P X → Real.sin q.1 < 0) :
    Work.SurgeryInvariance.WindingSpan P X ≤
      Submodule.span ℚ {((0 : ℚ), (1 : ℚ))} := by
  rw [Work.SurgeryInvariance.WindingSpan, Submodule.span_le]
  rintro v ⟨γ, hγ, rfl⟩
  set L : Work.CoreTopology.LiftOf P γ :=
    Classical.choice (Work.TorusCover.ParamTorus_exists_liftOf P γ) with hL
  have hsin : ∀ t : ℝ, 0 < Real.sin (L.Θ t + Real.pi) := by
    intro t
    have ht : (L.Θ t, L.Φ t) ∈ planePreimage P X := by
      rw [mem_planePreimage]; rw [L.lifts t]; exact hγ t
    have := h (L.Θ t, L.Φ t) ht
    rw [Real.sin_add_pi]
    linarith
  have hdiff : (L.Θ (2 * Real.pi) + Real.pi) - (L.Θ 0 + Real.pi) =
      ((L.winding).1 : ℝ) * (2 * Real.pi) := by
    rw [L.winding_spec.1]; ring
  have hk : (L.winding).1 = 0 :=
    eq_zero_of_cont_sin_pos (L.contΘ.add continuous_const) hsin hdiff
  rw [Work.SurgeryInvariance.windingOf_eq P γ L, hk]
  have hgoal : ((((0 : ℤ) : ℚ), (((L.winding).2 : ℤ) : ℚ)) : ℚ × ℚ) =
      (((L.winding).2 : ℤ) : ℚ) • ((0 : ℚ), (1 : ℚ)) := by
    ext <;> simp
  rw [hgoal]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

/-! ## The standard torus at the critical box: the halves realise only the meridian class -/

/-- The preimage of the upper half-region of the standard torus, at the box `s = 5/2` with
`σ = swap 1 2`, lies in `{sin θ > 0}`: the upper region is defined by `y > 0`, and the
`y`-coordinate of the standard torus is `(2 + cos φ) sin θ` with `2 + cos φ ≥ 1 > 0`. -/
theorem preimage_upperRegion_standard_sin_pos :
    ∀ q : ℝ × ℝ, q ∈ planePreimage Work.CoreTopology.standard
      (Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard (5 / 2) 0
        (Equiv.swap (1 : Fin 3) 2) 0) → 0 < Real.sin q.1 := by
  intro q hq
  rw [mem_planePreimage] at hq
  have hpos := ((Work.BoxShrink.Core.mem_upperRegion).mp hq).2.2
  rw [show (Equiv.swap (1 : Fin 3) 2) 2 = 1 from rfl, WithLp.ofLp_zero, Pi.zero_apply,
    zero_add, standard_psi, torusMap_apply_one] at hpos
  have hc : 0 < 2 + Real.cos q.2 := by linarith [Real.neg_one_le_cos q.2]
  nlinarith [hpos, hc]

/-- The preimage of the lower half-region of the same configuration lies in `{sin θ < 0}`. -/
theorem preimage_lowerRegion_standard_sin_neg :
    ∀ q : ℝ × ℝ, q ∈ planePreimage Work.CoreTopology.standard
      (Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard (5 / 2) 0
        (Equiv.swap (1 : Fin 3) 2) 0) → Real.sin q.1 < 0 := by
  intro q hq
  rw [mem_planePreimage] at hq
  have hneg := ((Work.BoxShrink.Core.mem_lowerRegion).mp hq).2.2
  rw [show (Equiv.swap (1 : Fin 3) 2) 2 = 1 from rfl, WithLp.ofLp_zero, Pi.zero_apply,
    zero_add, standard_psi, torusMap_apply_one] at hneg
  have hc : 0 < 2 + Real.cos q.2 := by linarith [Real.neg_one_le_cos q.2]
  nlinarith [hneg, hc]

/-- **The two half-regions of the critical box realise no longitude class**: their winding spans
are contained in the line of the meridian. -/
theorem windingSpan_halves_standard_critical_le :
    Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
        (Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard (5 / 2) 0
            (Equiv.swap (1 : Fin 3) 2) 0 ∪
          Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard (5 / 2) 0
            (Equiv.swap (1 : Fin 3) 2) 0) ≤
      Submodule.span ℚ {((0 : ℚ), (1 : ℚ))} := by
  rw [Work.SurgeryInvariance.Span.union_eq_sup
    (Work.BoxShrink.Core.isOpenInCarrier_upperRegion _ _ _ _ _)
    (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion _ _ _ _ _)
    (Work.BoxShrink.Core.disjoint_upperRegion_lowerRegion _ _ _ _ _)]
  exact sup_le
    (windingSpan_le_span_snd_of_preimage_sin_pos preimage_upperRegion_standard_sin_pos)
    (windingSpan_le_span_snd_of_preimage_sin_neg preimage_lowerRegion_standard_sin_neg)

/-- **The meridian `θ = π/2` lies in the upper half-region of the critical box, and realises the
class `(0,1)`** — so the half-regions' span is *exactly* the meridian line. -/
theorem meridian_mem_upperRegion_standard_critical :
    ∀ t : ℝ, Work.CoreTopology.meridianCurve Work.CoreTopology.standard (Real.pi / 2) t ∈
      Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard (5 / 2) 0
        (Equiv.swap (1 : Fin 3) 2) 0 := by
  intro t
  rw [Work.BoxShrink.Core.mem_upperRegion]
  refine ⟨(Work.CoreTopology.meridianCurve Work.CoreTopology.standard (Real.pi / 2)).mem t,
    ?_, ?_⟩
  · rw [Work.BoxShrink.Bubble.cex_mem_PBox]
    have hx : (Work.CoreTopology.meridianCurve Work.CoreTopology.standard (Real.pi / 2)).γ t 0
        = 0 := by
      rw [Work.CoreTopology.meridianCurve_apply, standard_psi, torusMap_apply_zero,
        Real.cos_pi_div_two, mul_zero]
    have hy : (Work.CoreTopology.meridianCurve Work.CoreTopology.standard (Real.pi / 2)).γ t 1
        = 2 + Real.cos t := by
      rw [Work.CoreTopology.meridianCurve_apply, standard_psi, torusMap_apply_one,
        Real.sin_pi_div_two, mul_one]
    have hz : (Work.CoreTopology.meridianCurve Work.CoreTopology.standard (Real.pi / 2)).γ t 2
        = Real.sin t := by
      rw [Work.CoreTopology.meridianCurve_apply, standard_psi, torusMap_apply_two]
    rw [hx, hy, hz]
    refine ⟨by norm_num, ?_, ?_⟩
    · rw [abs_lt]
      exact ⟨by nlinarith [Real.neg_one_le_sin t, Submission.one_le_rpow_third],
        by nlinarith [Real.sin_le_one t, Submission.one_le_rpow_third]⟩
    · rw [abs_lt]
      exact ⟨by nlinarith [Real.neg_one_le_cos t, Work.BoxShrink.Bubble.cex_rpow_two_thirds_gt],
        by nlinarith [Real.cos_le_one t, Work.BoxShrink.Bubble.cex_rpow_two_thirds_gt]⟩
  · rw [show (Equiv.swap (1 : Fin 3) 2) 2 = 1 from rfl, WithLp.ofLp_zero, Pi.zero_apply,
      zero_add, Work.CoreTopology.meridianCurve_apply, standard_psi, torusMap_apply_one,
      Real.sin_pi_div_two, mul_one]
    linarith [Real.neg_one_le_cos t]

/-- The meridian realises the class `(0,1)` in the two half-regions. -/
theorem snd_mem_windingSpan_halves_standard_critical :
    ((0 : ℚ), (1 : ℚ)) ∈ Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
      (Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard (5 / 2) 0
          (Equiv.swap (1 : Fin 3) 2) 0 ∪
        Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard (5 / 2) 0
          (Equiv.swap (1 : Fin 3) 2) 0) := by
  refine Submodule.subset_span ⟨_, fun t => Or.inl
    (meridian_mem_upperRegion_standard_critical t), ?_⟩
  rw [Work.SurgeryInvariance.windingOf_eq _ _
    (Work.CoreTopology.meridianLift _ _), Work.CoreTopology.meridianLift_winding]
  norm_num

/-! ## The trace of the plane at the critical configuration -/

/-- **Every trace period of the plane `{y = 0}` on the standard torus has vanishing longitude
component.**  The preimage of the plane is the union of the meridians `θ ∈ πℤ`; each of those is a
connected component of the preimage, so a periodic path of the preimage lies in one of them, its
longitude parameter is constant, and the realised period is a multiple of `(0,1)`. -/
theorem tracePeriod_fst_eq_zero_standard {k l : ℤ}
    (h : TracePeriod Work.CoreTopology.standard 0 (Equiv.swap (1 : Fin 3) 2) 0 k l) : k = 0 := by
  obtain ⟨q, hq, hper, hmem⟩ := h
  -- the longitude coordinate of a point of the trace is an integer multiple of `π`
  have hq1 : ∀ t : ℝ, ∃ m : ℤ, (q t).1 = (m : ℝ) * Real.pi := by
    intro t
    have ht := hmem t
    rw [tracePreimage, mem_planePreimage, Work.BoxShrink.Core.mem_cutPlane] at ht
    have hzero : (Work.Core.torusMap (q t).1 (q t).2) 1 = 0 := by
      simpa [standard_psi, show (Equiv.swap (1 : Fin 3) 2) 2 = 1 from rfl, WithLp.ofLp_zero,
        Pi.zero_apply, zero_add] using ht
    rw [torusMap_apply_one] at hzero
    have hc : 0 < 2 + Real.cos (q t).2 := by linarith [Real.neg_one_le_cos (q t).2]
    have hs : Real.sin (q t).1 = 0 := by
      rcases mul_eq_zero.mp hzero with h' | h'
      · exfalso; linarith [h', hc]
      · exact h'
    obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hs
    exact ⟨m, hm.symm⟩
  -- hence `2 * θ` is a constant integer multiple of `2π` along the whole path
  obtain ⟨k₀, hk₀⟩ := Work.CoreTopology.LiftOf.continuous_int_multiple_const
    (fun t : ℝ => 2 * (q t).1) (continuous_const.mul (continuous_fst.comp hq))
    (fun t => by obtain ⟨m, hm⟩ := hq1 t; exact ⟨m, by rw [hm]; ring⟩)
  -- but it must also change by `4π k` over one period
  have hper1 : (q (0 + 1)).1 = (q 0).1 + (k : ℝ) * (2 * Real.pi) := by
    have h' := (Prod.ext_iff.mp (hper 0)).1
    simp only [Prod.fst_add, Work.TorusCover.periodShift] at h'
    exact h'
  have h2 := hk₀ (0 + 1)
  have h0 := hk₀ 0
  have heq : 2 * ((q 0).1 + (k : ℝ) * (2 * Real.pi)) = 2 * (q 0).1 := by
    rw [← hper1, h2, h0]
  have hk0 : (k : ℝ) * (2 * Real.pi) = 0 := by linarith [heq]
  have hkR : (k : ℝ) = 0 := by
    rcases mul_eq_zero.mp hk0 with h' | h'
    · exact h'
    · exfalso; linarith [h', Real.pi_pos]
  exact_mod_cast hkR

/-- **The trace's line at the critical configuration is the meridian line.** -/
theorem traceLine_standard_zero :
    TraceLine Work.CoreTopology.standard 0 (Equiv.swap (1 : Fin 3) 2) 0
      (Submodule.span ℚ {((0 : ℚ), (1 : ℚ))}) := by
  refine ⟨?_, ?_⟩
  · rw [finrank_span_singleton]; norm_num
  · intro k l hkl
    have hk : k = 0 := tracePeriod_fst_eq_zero_standard hkl
    have hgoal : ((((0 : ℤ) : ℚ), ((l : ℤ) : ℚ)) : ℚ × ℚ) =
        ((l : ℤ) : ℚ) • ((0 : ℚ), (1 : ℚ)) := by
      ext <;> simp
    rw [hk, hgoal]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

/-! ## The two conclusions -/

/-- **The first branch of the residual fails at the critical configuration**: the region inside the
box realises the whole of `H₁(T²; ℚ)`, while the two half-regions realise only the meridian
class. -/
theorem windingSpan_box_standard_critical_not_le_halves :
    ¬ (Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
          (Work.BoxShrink.Core.boxRegion Work.CoreTopology.standard (5 / 2) 0
            (Equiv.swap (1 : Fin 3) 2)) ≤
        Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
          (Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard (5 / 2) 0
              (Equiv.swap (1 : Fin 3) 2) 0 ∪
            Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard (5 / 2) 0
              (Equiv.swap (1 : Fin 3) 2) 0)) := by
  intro h
  have htop : Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
      (Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard (5 / 2) 0
          (Equiv.swap (1 : Fin 3) 2) 0 ∪
        Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard (5 / 2) 0
          (Equiv.swap (1 : Fin 3) 2) 0) = ⊤ := by
    rw [eq_top_iff]
    rw [Work.BoxShrink.Bubble.cex_windingSpan_boxRegion_eq_top] at h
    exact h
  have hle : (⊤ : Submodule ℚ (ℚ × ℚ)) ≤
      Submodule.span ℚ {((0 : ℚ), (1 : ℚ))} := by
    rw [← htop]; exact windingSpan_halves_standard_critical_le
  have hsp : Module.finrank ℚ ↥(Submodule.span ℚ {((0 : ℚ), (1 : ℚ))}) = 1 := by
    rw [finrank_span_singleton]; norm_num
  have hd := Submodule.finrank_mono hle
  rw [finrank_top, Module.finrank_prod, Module.finrank_self, hsp] at hd
  norm_num at hd

/-- **The residual holds at the critical configuration**, through its second branch: the trace
class `(0,1)` is the class of the meridian, which lies in the upper half-region. -/
theorem traceMultipleRealisable_standard_critical :
    TraceMultipleRealisable Work.CoreTopology.standard (5 / 2) 0 (Equiv.swap (1 : Fin 3) 2) 0 := by
  refine Or.inr ⟨((0 : ℚ), (1 : ℚ)), by norm_num,
    ⟨Submodule.span ℚ {((0 : ℚ), (1 : ℚ))}, traceLine_standard_zero,
      Submodule.subset_span (Set.mem_singleton _)⟩, ?_⟩
  rw [Work.BoxShrink.Bubble.cex_windingSpan_boxRegion_eq_top, top_inf_eq]
  exact Submodule.span_le.mpr (by
    rintro v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    exact snd_mem_windingSpan_halves_standard_critical)

end

end Work.BoxShrink.Pinch
