import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.planeTwoDiscs
import Submission.Work.Smooth.SphereJordan.Basic
import Submission.Work.Smooth.SphereJordan.planeIndexGeom
import Submission.Work.Smooth.SphereJordan.disc_openImage_subset_boundedSide
import Submission.Work.Smooth.SphereJordan.argChangeLift
import Submission.Work.Smooth.Jordan.noFilling_of_mem_V
import Submission.Work.Smooth.Jordan.plane_separation_unbounded
import Submission.Work.Smooth.Jordan.plane_separation_preconnected_subset
import Submission.Work.Smooth.Jordan.unitCircle_jordanSchoenflies
import Submission.Work.Smooth.Jordan.All

/-!
# Foundation lemmas for the theta-graph two-halves theorem

The elementary facts about the winding number of a simple closed plane curve which the
`Work.Smooth.SphereJordan` chapter and its downstream users need, kept in their own module so that
they can be imported *without* the (later) module
`Submission.Work.Smooth.SphereJordan.thetaTwoHalvesSphereOfPlane` -- this avoids the import cycle
that arises because several winding-number modules import the latter.

* `isPreconnected_far` -- the exterior of a disc is preconnected;
* `windNumber_eq_of_preconnected` -- the winding number is constant on a preconnected set off the
  trace;
* `windNumber_eq_zero_of_mem_U` -- the winding number vanishes on the unbounded side (sharp form,
  with no normalisation hypothesis on the curve).
-/

open Set
open Work.Smooth.Jordan

namespace Work.Smooth.SphereJordan

noncomputable section

theorem isPreconnected_far {R : ℝ} (hR : 0 < R) : IsPreconnected {w : ℂ | R < ‖w‖} := by
  have hpre0 : IsPreconnected {w : ℂ | (1:ℝ) < ‖w‖} :=
    Work.Smooth.Jordan.isPreconnected_exterior_unitBall
  have himg := hpre0.image (fun w : ℂ => R * w) ((continuous_const.mul continuous_id).continuousOn)
  have heq : (fun w : ℂ => R * w) '' {w : ℂ | (1:ℝ) < ‖w‖} = {w : ℂ | R < ‖w‖} := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hnorm : ‖R * v‖ = R * ‖v‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
      rw [Set.mem_ofPred_eq, hnorm]
      simpa using mul_lt_mul_of_pos_left hv hR
    · intro hw
      refine ⟨R⁻¹ * w, ?_, ?_⟩
      · have hnorm : ‖R⁻¹ * w‖ = R⁻¹ * ‖w‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
        rw [Set.mem_ofPred_eq, hnorm, inv_mul_eq_div, one_lt_div hR]
        exact hw
      · have hRne : ((R : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hR)
        show (fun w : ℂ => R * w) (R⁻¹ * w) = w
        push_cast
        field_simp
  rwa [heq] at himg

/-- **The winding number is locally constant off the trace of a plane curve.** -/
theorem windNumber_eq_of_preconnected (c : Work.Smooth.Jordan.PlaneCurve) {W : Set ℂ}
    (hW : IsPreconnected W) (hsub : W ⊆ c.traceᶜ) {p q : ℂ} (hp : p ∈ W) (hq : q ∈ W) :
    windNumber c.γ c.cont p = windNumber c.γ c.cont q := by
  haveI : ConnectedSpace W := isConnected_iff_connectedSpace.mp ⟨⟨p, hp⟩, hW⟩
  have hball' : ∀ {z : ℂ}, z ∈ W → ∃ ε > 0, Metric.ball z ε ⊆ c.traceᶜ := by
    intro z hz
    exact Metric.isOpen_iff.mp c.isOpen_compl_trace z (hsub hz)
  have hloc : IsLocallyConstant (fun z : W => windNumber c.γ c.cont z.1) := by
    intro t
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨ε, hε, hball⟩ := hball' z.2
    have hmem : Subtype.val ⁻¹' Metric.ball z.1 ε ∈ nhds z :=
      (continuous_subtype_val.continuousAt).preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
    refine Filter.mem_of_superset hmem ?_
    intro y hy
    have hyB : y.1 ∈ Metric.ball z.1 ε := hy
    have hzB : z.1 ∈ Metric.ball z.1 ε := Metric.mem_ball_self hε
    have hconst : windNumber c.γ c.cont y.1 = windNumber c.γ c.cont z.1 := by
      refine windNumber_eq_of_segment c.cont c.periodic (fun t ht => ?_) (fun t ht => ?_)
        (fun t s hs => ?_)
      · exact hball hyB ⟨t, ht⟩
      · exact hball hzB ⟨t, ht⟩
      · have hconv : Convex ℝ (Metric.ball (z.1 : ℂ) ε) := convex_ball _ _
        have hmem : (1 - s) • (↑y : ℂ) + s • (↑z : ℂ) ∈ Metric.ball z.1 ε :=
          hconv hyB hzB (by linarith [hs.1, hs.2]) hs.1 (by ring)
        have hgoal : ((1 - s : ℝ) : ℂ) * (↑y) + (s : ℂ) * (↑z) ∈ Metric.ball z.1 ε := by
          simpa [Complex.real_smul] using hmem
        intro h
        exact hball hgoal ⟨t, by rw [h]; push_cast; ring⟩
    change windNumber c.γ c.cont y.1 ∈ t
    rw [hconst]
    exact hz
  have hcont : Continuous (fun z : W => windNumber c.γ c.cont z.1) := hloc.continuous
  have hpre : IsPreconnected (Set.range (fun z : W => windNumber c.γ c.cont z.1)) := by
    rw [← Set.image_univ]
    exact isPreconnected_univ.image _ hcont.continuousOn
  have hmem : windNumber c.γ c.cont p ∈ Set.range (fun z : W => windNumber c.γ c.cont z.1) :=
    ⟨⟨p, hp⟩, rfl⟩
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hpre) ({windNumber c.γ c.cont p} : Set ℤ)
    ({windNumber c.γ c.cont p}ᶜ) (isClosed_discrete _) (isClosed_discrete _)
    (fun x _ => by by_cases h : x = windNumber c.γ c.cont p <;> simp [h]) (by simp) with h | h
  · exact (Set.mem_singleton_iff.mp (h ⟨⟨q, hq⟩, rfl⟩)).symm
  · exact absurd (h hmem) (by simp)

/-- **The winding number vanishes on the unbounded side** of a simple closed plane curve, with no
normalisation hypothesis on the curve. -/
theorem windNumber_eq_zero_of_mem_U {c : Work.Smooth.Jordan.PlaneCurve}
    (h : Work.Smooth.Jordan.PlaneSeparation c) {p : ℂ} (hp : p ∈ h.U) :
    windNumber c.γ c.cont p = 0 := by
  obtain ⟨C, hC⟩ := c.isCompact_trace.isBounded.exists_norm_le
  obtain ⟨D, hD⟩ := h.bounded_V.exists_norm_le
  set R : ℝ := max C D + 1 with hRdef
  have hCR : C < R := by rw [hRdef]; exact lt_of_le_of_lt (le_max_left C D) (lt_add_one _)
  have hDR : D < R := by rw [hRdef]; exact lt_of_le_of_lt (le_max_right C D) (lt_add_one _)
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC _ (c.mem_trace 0))
  have hR0 : 0 < R := by rw [hRdef]; linarith [hC0, le_max_left C D]
  have hfarU : ∀ z : ℂ, R < ‖z‖ → z ∈ h.U := by
    intro z hz
    have hsub : {w : ℂ | R < ‖w‖} ⊆ c.traceᶜ := by
      intro w hw hwt
      obtain ⟨t, rfl⟩ := hwt
      have h1 : ‖c.γ t‖ ≤ C := hC _ (c.mem_trace t)
      exact absurd (lt_of_le_of_lt h1 hCR) (not_lt.mpr (le_of_lt hw))
    have hpre : IsPreconnected {w : ℂ | R < ‖w‖} := isPreconnected_far hR0
    rcases Work.Smooth.Jordan.plane_separation_preconnected_subset h hpre hsub with hU | hV
    · exact hU hz
    · have h1 : ‖z‖ ≤ D := hD z (hV hz)
      linarith [hDR]
  set p₀ : ℂ := -(((R + 1 : ℝ)) : ℂ) with hp₀def
  have hp₀norm : ‖p₀‖ = R + 1 := by
    rw [hp₀def, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hR0])]
  have hp₀U : p₀ ∈ h.U := hfarU p₀ (by rw [hp₀norm]; exact lt_add_one R)
  have hp₀zero : windNumber c.γ c.cont p₀ = 0 := by
    have hbdd : ∀ t : ℝ, ‖c.γ t‖ ≤ R := fun t => le_of_lt (lt_of_le_of_lt (hC _ (c.mem_trace t)) hCR)
    exact windNumber_eq_zero_of_norm_gt c.cont c.periodic hbdd (by rw [hp₀norm]; exact lt_add_one R)
  rw [windNumber_eq_of_preconnected c h.preconn_U
    (fun z hz => by rw [← h.union_eq]; exact Or.inl hz) hp hp₀U, hp₀zero]

end

end Work.Smooth.SphereJordan
