import Mathlib
import Submission.Work.Smooth.Jordan.Separation

/-!
# The bounded side of a Schoenflies curve is the open disc

If `h : PlaneSchoenflies c` presents the simple closed curve `c` as the boundary of an embedded
closed disc `h.e : 𝔻 → ℂ` whose image is the closure of the bounded side `h.V`, then the *interior*
of the disc — the image of the open unit disc — is exactly `h.V`.

The proof is purely topological, and splits into two elementary facts.

* `h.e` maps the boundary circle `{‖z‖ = 1}` onto `c.trace`: this is the injectivity of `e` together
  with the boundary condition `h.boundary`.
* `closure h.V \ c.trace = h.V`: since `h.V` is open and `h.V = c.traceᶜ \ h.U` with `h.U` open,
  `h.V` is clopen in `c.traceᶜ`, so its closure meets `c.traceᶜ` in `h.V` itself.

Combining the two with `Set.range h.e = closure h.V` gives
`h.e '' {‖z‖ < 1} = (range h.e) \ c.trace = closure h.V \ c.trace = h.V`.
-/

open Set

namespace Work.Smooth.Jordan

theorem plane_schoenflies_openDisc_eq {c : PlaneCurve} (h : PlaneSchoenflies c) :
    h.e '' {z : Disc | ‖(z : ℂ)‖ < 1} = h.V := by
  -- The boundary circle of the disc maps onto the trace of the curve.
  have hsphere : h.e '' {z : Disc | ‖(z : ℂ)‖ = 1} = c.trace := by
    apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨θ, rfl⟩ := exists_circlePoint_eq z hz
      exact ⟨θ, (h.boundary θ).symm⟩
    · rintro _ ⟨θ, rfl⟩
      refine ⟨circlePoint θ, ?_, h.boundary θ⟩
      change ‖((circlePoint θ : Disc) : ℂ)‖ = 1
      rw [circlePoint_coe]
      exact Complex.norm_exp_ofReal_mul_I θ
  -- The bounded side lies in the complement of the trace.
  have hVsub : h.V ⊆ c.traceᶜ := by
    intro x hx
    have : x ∈ h.U ∪ h.V := Or.inr hx
    rw [h.union_eq] at this
    exact this
  -- The bounded side is clopen in the complement of the trace, hence `closure V \ trace = V`.
  have hcloV : closure h.V \ c.trace = h.V := by
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨hyc, hyt⟩ := hy
      have hyU : y ∈ h.U ∪ h.V := by rw [h.union_eq]; exact hyt
      rcases hyU with hyU | hyV
      · exfalso
        obtain ⟨w, hwU, hwV⟩ := mem_closure_iff.mp hyc h.U h.isOpen_U hyU
        exact Set.disjoint_left.mp h.disjoint_UV hwU hwV
      · exact hyV
    · intro y hy
      exact ⟨subset_closure hy, hVsub hy⟩
  apply Set.Subset.antisymm
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hmem : (h.e z : ℂ) ∈ closure h.V \ c.trace := by
      refine ⟨?_, ?_⟩
      · rw [← h.range_e]; exact ⟨z, rfl⟩
      · intro hcontra
        rw [← hsphere] at hcontra
        obtain ⟨w, hw, hwe⟩ := hcontra
        have hwz : w = z := h.inj hwe
        rw [hwz] at hw
        exact absurd hw (ne_of_lt hz)
    rwa [hcloV] at hmem
  · intro y hy
    have hyrange : y ∈ Set.range h.e := by rw [h.range_e]; exact subset_closure hy
    obtain ⟨z, rfl⟩ := hyrange
    refine ⟨z, ?_, rfl⟩
    have hzle : ‖(z : ℂ)‖ ≤ 1 := by
      have := z.2; rwa [Metric.mem_closedBall, dist_zero_right] at this
    rcases lt_or_eq_of_le hzle with hlt | heq
    · exact hlt
    · exfalso
      have hztrace : (h.e z : ℂ) ∈ c.trace := by
        rw [← hsphere]
        exact ⟨z, heq, rfl⟩
      exact (hVsub hy) hztrace

end Work.Smooth.Jordan
