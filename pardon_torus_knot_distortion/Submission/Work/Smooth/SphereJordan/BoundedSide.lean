import Submission.Work.Smooth.SphereJordan.Defs

/-!
# The bounded side of a curve inside the open disc is inside the closed disc

A small but reusable ingredient of the "two cuts" route to the planar annulus theorem
(`Submission/Work/Smooth/SphereJordan/README.md`, §7.1): if the trace of a simple closed plane curve
`c` lies in the *open* unit disc, then its bounded side `V` lies in the *closed* unit disc.

The proof is the classical "ray to infinity": if `x` lies in the bounded side with `1 < ‖x‖`, the
outward ray `{s • x : s ≥ 1}` is preconnected, avoids the trace (every point of it has norm at least
`‖x‖ > 1`, while the trace has norm `< 1`) and contains `x`, so it lies on one side
(`Work.Smooth.Jordan.plane_separation_preconnected_subset`); it cannot lie in the unbounded side
(it meets the bounded side, and the two sides are disjoint), so it lies in the bounded side, which
is therefore unbounded — contradicting `PlaneSeparation.bounded_V`.

The same argument, applied to a curve inside any open ball, gives the corresponding bound; and,
applied to the *curve* `θ ↦ h (e^{iθ})` of an embedding `h : 𝔻 ↪ 𝔻` whose boundary circle lies in
the open disc, it is the first half of the statement that the disc bounded by such a curve is
contained in `𝔻`.
-/

open Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.SphereJordan

noncomputable section

/-- **The bounded side of a simple closed curve inside the open unit disc is contained in the closed
unit disc.** -/
theorem planeSeparation_V_subset_closedBall {c : Work.Smooth.Jordan.PlaneCurve}
    (d : Work.Smooth.Jordan.PlaneSeparation c) (hc : ∀ θ : ℝ, ‖c.γ θ‖ < 1) :
    ∀ x ∈ d.V, ‖x‖ ≤ 1 := by
  intro x hxV
  by_contra hcon
  push Not at hcon
  -- the outward ray through `x`
  set R : Set ℂ := (fun s : ℝ => s • x) '' Set.Ici 1 with hR
  have hRpre : IsPreconnected R :=
    isPreconnected_Ici.image _ (continuous_id.smul continuous_const).continuousOn
  have hxR : x ∈ R := ⟨1, Set.mem_Ici.mpr le_rfl, by simp⟩
  -- the ray avoids the trace
  have hRsub : R ⊆ c.traceᶜ := by
    rintro y ⟨s, hs, hys⟩ hy
    rw [← hys] at hy
    obtain ⟨θ, hθ⟩ := hy
    have hs1 : (1 : ℝ) ≤ s := Set.mem_Ici.mp hs
    have hnorm : ‖s • x‖ = s * ‖x‖ := by
      rw [norm_smul, Real.norm_of_nonneg (le_trans zero_le_one hs1)]
    have hge : ‖x‖ ≤ ‖s • x‖ := by
      rw [hnorm]
      nlinarith [norm_nonneg x]
    have hle : ‖x‖ ≤ ‖c.γ θ‖ := by rw [hθ]; exact hge
    linarith [hc θ, hcon, hle]
  -- so the ray lies on one side
  rcases Work.Smooth.Jordan.plane_separation_preconnected_subset d hRpre hRsub with hU | hV
  · exact Set.disjoint_left.mp d.disjoint_UV (hU hxR) hxV
  · -- the ray is unbounded, contradicting the boundedness of `V`
    have hb := d.bounded_V.subset hV
    rw [isBounded_iff_forall_norm_le] at hb
    obtain ⟨C, hC⟩ := hb
    have hxn : 0 < ‖x‖ := lt_trans zero_lt_one hcon
    set s : ℝ := (C + 1) / ‖x‖ with hs
    have hs1 : (1 : ℝ) ≤ s := by
      rw [hs, le_div_iff₀ hxn]
      linarith [hC x hxR]
    have hmem : s • x ∈ R := ⟨s, hs1, rfl⟩
    have hval : C + 1 ≤ C := by
      calc C + 1 = ‖s • x‖ := by
            rw [norm_smul, Real.norm_of_nonneg (le_trans zero_le_one hs1), hs]
            field_simp
        _ ≤ C := hC _ hmem
    linarith

end

end Work.Smooth.SphereJordan
