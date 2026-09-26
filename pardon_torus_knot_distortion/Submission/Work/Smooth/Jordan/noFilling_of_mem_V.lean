import Mathlib
import Submission.Work.Smooth.Jordan.Defs
import Submission.Work.Smooth.Jordan.Separation
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.disc_openImage_subset_boundedSide

/-!
# A Jordan curve cannot be filled by a disc avoiding a point of its bounded side

Let `γ` be a simple closed plane curve, `h : PlaneSchoenflies γ` a Jordan–Schoenflies datum for it
(so `h.V` is the bounded side of `γ` and `h.e : 𝔻 → ℂ` is an embedded disc whose image is
`closure h.V` and whose boundary circle maps to `γ`).  Then for `x ∈ h.V` there is **no** continuous
map `F : 𝔻 → ℂ` which avoids `x` and whose boundary circle is `γ` (in the given parametrisation).

This is the homotopy form of the hard direction of the Jordan curve theorem: the boundary loop
`θ ↦ γ.γ θ` is *essential* in `ℂ ∖ {x}` for every point `x` of the bounded side.

## The argument

Write `z₀` for the (unique) point of the open model disc with `h.e z₀ = x`; it is an interior point
because the boundary circle of `𝔻` maps onto the trace of `γ`, which does not meet `V`.

* **The loop does not contract.**  A hypothetical `F` with `F (e^{iθ}) = γ.γ θ` and no value `x`
  normalises to a continuous map `Ψ : 𝔻 → S¹`, `Ψ z = (F z - x)/‖F z - x‖`, whose boundary values
  are the loop `φ θ = (γ.γ θ - x)/‖γ.γ θ - x‖`.  By the monodromy of the universal cover
  `Circle.exp : ℝ → S¹` (`Work.Smooth.SphereJordan.hlp_lift_diff_eq_zero_of_extends`) *every* lift
  `Λ` of `φ` is a loop: `Λ (2π) = Λ 0`.
* **The loop is essential.**  The same loop is also
  `θ ↦ (h.e (e^{iθ}) - h.e z₀)/‖h.e (e^{iθ}) - h.e z₀‖`, and the parity (Borsuk–Ulam) argument for
  the *injective* disc map `h.e` (`Work.Smooth.SphereJordan.hlp_winding_ne_zero`) — the loop is
  homotopic, along the straight segments from `z₀` to the antipode `e^{i(θ+π)}` inside `𝔻`, to the
  antipodal loop `θ ↦ (h.e (e^{iθ}) - h.e (e^{i(θ+π)}))/‖·‖`, whose oddness forces an odd winding
  number — shows that instead `Λ (2π) - Λ 0 ≠ 0`.

The two computations contradict each other.
-/

open Set

namespace Work.Smooth.Jordan

/-- **No disc filling avoids a point of the bounded side.**  For a simple closed plane curve `γ`
presented as the boundary of an embedded disc by `h : PlaneSchoenflies γ`, no continuous
`F : 𝔻 → ℂ` avoids a point `x ∈ h.V` while mapping the boundary circle to `γ`. -/
theorem noFilling_of_mem_V {γ : Work.Smooth.Jordan.PlaneCurve}
    (h : Work.Smooth.Jordan.PlaneSchoenflies γ) {x : ℂ} (hx : x ∈ h.V) :
    ¬ ∃ F : C(Work.Smooth.SphereJordan.Disc, ℂ),
      (∀ z : Work.Smooth.SphereJordan.Disc, (F z : ℂ) ≠ x) ∧
      (∀ θ : ℝ, (F (Work.Smooth.SphereJordan.circlePoint θ) : ℂ) = γ.γ θ) := by
  rintro ⟨F, hFne, hFbd⟩
  -- The bounded side avoids the trace of the curve.
  have hVsub : h.V ⊆ γ.traceᶜ := by
    intro y hy
    have hmem : y ∈ h.U ∪ h.V := Or.inr hy
    rwa [h.union_eq] at hmem
  -- `x` is the image of a point `z₀` of the spanning disc, and `z₀` is an interior point.
  have hxrange : x ∈ Set.range h.e := by
    rw [h.range_e]; exact subset_closure hx
  obtain ⟨z₀, hz₀eq⟩ := hxrange
  have hz₀lt : ‖((z₀ : Disc) : ℂ)‖ < 1 := by
    have hle : ‖((z₀ : Disc) : ℂ)‖ ≤ 1 := by
      have h := z₀.2
      rwa [Metric.mem_closedBall, dist_zero_right] at h
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exfalso
      obtain ⟨θ, hθ⟩ := exists_circlePoint_eq z₀ heq
      have hmem : x ∈ γ.trace := ⟨θ, by rw [← h.boundary θ, hθ, hz₀eq]⟩
      exact hVsub hx hmem
  -- The boundary loop `θ ↦ γ.γ θ - x` never vanishes.
  have hγne : ∀ θ : ℝ, γ.γ θ - x ≠ 0 := fun θ =>
    sub_ne_zero.mpr fun he => hVsub hx (he ▸ γ.mem_trace θ)
  -- ... and its normalisation, the loop `φ` of the circle.
  let φ : ℝ → Circle := fun θ => Work.CoreTopology.normCircle (γ.γ θ - x) (hγne θ)
  have hφc : Continuous φ :=
    Work.CoreTopology.continuous_normCircle _ (γ.cont.sub continuous_const) hγne
  -- A lift of the loop to the universal cover of the circle.
  obtain ⟨Λ, hΛ⟩ := Work.Smooth.SphereJordan.hlp_exists_continuous_lift ⟨φ, hφc⟩
  have hΛ' : ∀ t : ℝ, Circle.exp (Λ t) = φ t := fun t => hΛ t
  -- The loop is `2π`-periodic.
  have hper : ∀ t : ℝ, φ (t + 2 * Real.pi) = φ t := by
    intro t
    apply Subtype.ext
    simp only [φ, Work.CoreTopology.normCircle_coe, γ.periodic t]
  -- The hypothetical filling extends the loop over the disc ...
  have hFne' : ∀ z : Work.Smooth.SphereJordan.Disc, F z - x ≠ 0 :=
    fun z => sub_ne_zero.mpr (hFne z)
  let Ψ : C(Work.Smooth.SphereJordan.Disc, Circle) :=
    ⟨fun z => Work.CoreTopology.normCircle (F z - x) (hFne' z),
      Work.CoreTopology.continuous_normCircle _ (F.continuous.sub continuous_const) hFne'⟩
  have hΨb : ∀ θ : ℝ, Ψ (Work.Smooth.SphereJordan.circlePoint θ) = φ θ := by
    intro θ
    apply Subtype.ext
    simp only [Ψ, ContinuousMap.coe_mk, φ, Work.CoreTopology.normCircle_coe]
    rw [hFbd θ]
  -- ... so every lift of it is closed.
  have hzero : Λ (2 * Real.pi) - Λ 0 = 0 :=
    Work.Smooth.SphereJordan.hlp_lift_diff_eq_zero_of_extends φ hφc hper Ψ hΨb Λ Λ.continuous hΛ'
  -- On the other hand the same loop winds once around `x = h.e z₀`, by the parity argument.
  have hne : Λ (2 * Real.pi) - Λ 0 ≠ 0 :=
    Work.Smooth.SphereJordan.hlp_winding_ne_zero h.e h.inj hz₀lt Λ Λ.continuous fun t => by
      rw [hΛ' t]
      exact Work.Smooth.SphereJordan.hlp_normCircle_congr
        (by rw [h.boundary t, hz₀eq])
        (hγne t) (Work.Smooth.SphereJordan.hlp_loop_ne_zero h.e h.inj hz₀lt t)
  exact hne hzero

end Work.Smooth.Jordan
