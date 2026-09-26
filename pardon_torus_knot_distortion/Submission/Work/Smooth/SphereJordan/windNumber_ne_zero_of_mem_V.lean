import Mathlib
import Submission.Work.Smooth.SphereJordan.planeIndexGeom
import Submission.Work.Smooth.SphereJordan.chordWitness
import Submission.Work.Smooth.SphereJordan.windNumber_ne_zero_of_antiperiodic
import Submission.Work.Smooth.SphereJordan.disc_openImage_subset_boundedSide
import Submission.Work.Smooth.Jordan.All

/-!
# The winding number of a simple closed plane curve is nonzero on the bounded side

Let `γ` be a simple closed plane curve, presented by a Jordan–Schoenflies datum
`S : PlaneSchoenflies γ` (so `S.V` is the bounded side and `S.e : 𝔻 → ℂ` an embedded spanning disc
with `Set.range S.e = closure S.V`).  Then for every `z ∈ S.V` the topological winding number
`Work.Smooth.SphereJordan.windNumber γ.γ γ.cont z` is nonzero.

This is the continuous-curve, topological form of the "inside direction" of Jordan separation: a
point of the bounded side is wound around by the curve.

## The argument

Pick `z₀ : 𝔻` with `S.e z₀ = z`; since `z` lies on the bounded side it is off the trace, so
`z₀` is an interior point of the model disc.  The parity (Borsuk–Ulam) argument for the injective
disc map `S.e` (`Work.Smooth.SphereJordan.hlp_winding_ne_zero`) provides a continuous lift
`Λ : ℝ → ℝ` of the normalised boundary loop `θ ↦ (S.e (e^{iθ}) - z)/‖·‖` with nonzero increment
`Λ (2π) - Λ 0 ≠ 0`.

The unnormalised loop `c t = γ.γ (2π t) - z` of the theorem is lifted to `ℂ` by
`Λc t = log ‖c t‖ + Λ (2π t) · I`; its exponential is `‖c t‖ · (c t/‖c t‖) = c t`, and its
increment `Λc 1 - Λc 0 = (Λ (2π) - Λ 0) · I` is nonzero.  By the defining property of the index
(`loopIndex_spec`) the increment of *any* lift of a nowhere vanishing closed loop is
`loopIndex c · 2πi`, so `loopIndex c ≠ 0`, i.e. `windNumber γ.γ γ.cont z ≠ 0`.
-/

namespace Work.Smooth.SphereJordan

open Set

theorem windNumber_ne_zero_of_mem_V {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {z : ℂ} (hz : z ∈ S.V) :
    Work.Smooth.SphereJordan.windNumber γ.γ γ.cont z ≠ 0 := by
  -- `z` is off the trace of the curve
  have hz_trace : z ∉ γ.trace := by
    have hVsub : S.V ⊆ γ.traceᶜ := by
      intro y hy
      have h : y ∈ S.U ∪ S.V := Or.inr hy
      rwa [S.union_eq] at h
    exact hVsub hz
  have hz_trace' : ∀ t : ℝ, γ.γ t ≠ z := fun t h => hz_trace ⟨t, h⟩
  -- `z` is the image of an interior point of the model disc
  have hz_range : z ∈ Set.range S.e := by
    rw [S.range_e]; exact subset_closure hz
  obtain ⟨z₀, hz₀⟩ := hz_range
  have hz₀lt : ‖(z₀ : ℂ)‖ < 1 := by
    have hle : ‖(z₀ : ℂ)‖ ≤ 1 := by
      have h := z₀.2; rwa [Metric.mem_closedBall, dist_zero_right] at h
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exfalso
      obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq z₀ heq
      exact hz_trace ⟨θ, by rw [← S.boundary θ, hθ, hz₀]⟩
  -- a real lift of the normalised boundary loop, with nonzero increment
  have hne : ∀ θ : ℝ, S.e (circlePoint θ) - S.e z₀ ≠ 0 := hlp_loop_ne_zero S.e S.inj hz₀lt
  have hφc : Continuous fun θ : ℝ =>
      Work.CoreTopology.normCircle (S.e (circlePoint θ) - S.e z₀) (hne θ) :=
    Work.CoreTopology.continuous_normCircle _
      ((S.e.continuous.comp hlp_continuous_circlePoint).sub continuous_const) hne
  obtain ⟨Λ, hΛ⟩ := hlp_exists_continuous_lift
    ⟨fun θ : ℝ => Work.CoreTopology.normCircle (S.e (circlePoint θ) - S.e z₀) (hne θ), hφc⟩
  have hinc : Λ (2 * Real.pi) - Λ 0 ≠ 0 :=
    hlp_winding_ne_zero S.e S.inj hz₀lt Λ Λ.continuous hΛ
  -- the loop of the theorem, and a complex lift of it
  let c : C(unitInterval, ℂ) := curveLoop (fun t => γ.γ t - z) (γ.cont.sub continuous_const)
  have hc : ∀ t : unitInterval, c t ≠ 0 := by
    intro t
    exact sub_ne_zero.mpr (hz_trace' (2 * Real.pi * (t : ℝ)))
  have hloop : c 0 = c 1 := by
    show γ.γ (2 * Real.pi * ((0 : unitInterval) : ℝ)) - z
      = γ.γ (2 * Real.pi * ((1 : unitInterval) : ℝ)) - z
    rw [show ((0 : unitInterval) : ℝ) = 0 from rfl,
      show ((1 : unitInterval) : ℝ) = 1 from rfl, mul_zero, mul_one]
    have hp : γ.γ (2 * Real.pi) = γ.γ 0 := by simpa using γ.periodic_apply 0
    rw [hp]
  have hlogc : Continuous fun t : unitInterval => Real.log ‖c t‖ :=
    c.continuous.norm.log (fun t => norm_ne_zero_iff.mpr (hc t))
  have hΛcont : Continuous fun t : unitInterval => ((Λ (2 * Real.pi * (t : ℝ)) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Λ.continuous.comp (by fun_prop))
  let Λc : C(unitInterval, ℂ) :=
    ⟨fun t => (Real.log ‖c t‖ : ℂ) + ((Λ (2 * Real.pi * (t : ℝ)) : ℝ) : ℂ) * Complex.I,
      (Complex.continuous_ofReal.comp hlogc).add (hΛcont.mul continuous_const)⟩
  have halg : ∀ w : ℂ, w ≠ 0 → ((‖w‖ : ℝ) : ℂ) * (w / ((‖w‖ : ℝ) : ℂ)) = w := by
    intro w hw
    rw [← mul_div_assoc,
      mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw))]
  have hΛc : ∀ t : unitInterval, Complex.exp (Λc t) = c t := by
    intro t
    have h1 : Complex.exp ((Real.log ‖c t‖ : ℝ) : ℂ) = ((‖c t‖ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_exp, Real.exp_log (norm_pos_iff.mpr (hc t))]
    have h2 : Complex.exp (((Λ (2 * Real.pi * (t : ℝ)) : ℝ) : ℂ) * Complex.I)
        = (Work.CoreTopology.normCircle
            (S.e (circlePoint (2 * Real.pi * (t : ℝ))) - S.e z₀)
            (hne (2 * Real.pi * (t : ℝ))) : ℂ) := by
      rw [← Circle.coe_exp]
      exact congrArg (fun w : Circle => (w : ℂ)) (hΛ (2 * Real.pi * (t : ℝ)))
    show Complex.exp ((Real.log ‖c t‖ : ℂ)
        + ((Λ (2 * Real.pi * (t : ℝ)) : ℝ) : ℂ) * Complex.I) = c t
    rw [Complex.exp_add, h1, h2, Work.CoreTopology.normCircle_coe, S.boundary, hz₀]
    exact halg (γ.γ (2 * Real.pi * (t : ℝ)) - z) (hc t)
  have hsub : Λc 1 - Λc 0 = (((Λ (2 * Real.pi) - Λ 0 : ℝ)) : ℂ) * Complex.I := by
    have hnorm : ‖c 1‖ = ‖c 0‖ := by rw [hloop]
    show ((Real.log ‖c 1‖ : ℂ)
        + ((Λ (2 * Real.pi * ((1 : unitInterval) : ℝ)) : ℝ) : ℂ) * Complex.I)
        - ((Real.log ‖c 0‖ : ℂ)
          + ((Λ (2 * Real.pi * ((0 : unitInterval) : ℝ)) : ℝ) : ℂ) * Complex.I)
        = (((Λ (2 * Real.pi) - Λ 0 : ℝ)) : ℂ) * Complex.I
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl,
      show ((0 : unitInterval) : ℝ) = 0 from rfl, mul_one, mul_zero, hnorm]
    push_cast
    ring
  have hΛc_ne : Λc 1 - Λc 0 ≠ 0 := by
    rw [hsub]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hinc) Complex.I_ne_zero
  have hloopidx : loopIndex c ≠ 0 := by
    intro h0
    have hspec := loopIndex_spec c hc hloop Λc hΛc
    rw [h0] at hspec
    simp only [Int.cast_zero, zero_mul] at hspec
    exact hΛc_ne hspec
  show loopIndex c ≠ 0
  exact hloopidx

end Work.Smooth.SphereJordan
