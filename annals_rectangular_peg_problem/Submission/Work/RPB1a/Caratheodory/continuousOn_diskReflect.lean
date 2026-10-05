import Mathlib
import Submission.Work.RPB1a.Caratheodory.ReflDefs

/-!
# Continuity of the circle reflection of `f - a`

`diskReflect f a` agrees with `f - a` on the closed unit disc and with
`conj (f (1 / conj z)) - conj a` outside it.  The two pieces are each continuous on a closed
set, so the only possible obstruction to continuity is the unit circle.  If `f = a` on the part
of the unit circle lying in the ball `ball z₀ δ`, the two pieces agree there (both equal `0`)
and the piecewise function is continuous on that ball.

This is the local gluing input used in the Painlevé/Schwarz-reflection argument for
`not_eqOn_const_sphere_of_injOn`: away from the exceptional circle the reflection is holomorphic,
and this lemma supplies the continuity across the arc where `f = a`.
-/

namespace Work.RPB1a.Caratheodory

open Complex Set Metric
open scoped ContDiff Real Topology ComplexConjugate

/-- On the unit circle, `1 / conj z = z`. -/
lemma one_div_conj_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : 1 / conj z = z := by
  rw [one_div]
  apply inv_eq_of_mul_eq_one_left
  rw [mul_conj, normSq_eq_norm_sq, hz]
  norm_num

theorem continuousOn_diskReflect {f : ℂ → ℂ} {a z₀ : ℂ} {δ : ℝ}
    (hc : ContinuousOn f (Metric.closedBall 0 1))
    (hsph : ∀ z : ℂ, z ∈ Metric.sphere 0 1 → dist z z₀ < δ → f z = a) :
    ContinuousOn (Work.RPB1a.Caratheodory.diskReflect f a) (Metric.ball z₀ δ) := by
  change ContinuousOn
    (fun z : ℂ => if ‖z‖ ≤ 1 then (fun w => f w - a) z else diskReflectOuter f a z)
    (Metric.ball z₀ δ)
  apply ContinuousOn.if
  · -- On the frontier of the disc, inside the ball, `f = a` and the two pieces agree (at `0`).
    intro x hx
    obtain ⟨hxball, hxfr⟩ := hx
    have hxsphere : x ∈ Metric.sphere 0 1 := by
      have hball : {w : ℂ | ‖w‖ ≤ 1} = Metric.closedBall (0 : ℂ) 1 := by
        ext w; simp [Metric.mem_closedBall, dist_eq_norm]
      rw [hball, frontier_closedBall'] at hxfr
      exact hxfr
    have hd : dist x z₀ < δ := by simpa [Metric.mem_ball] using hxball
    have hfx : f x = a := hsph x hxsphere hd
    have hnorm : ‖x‖ = 1 := by
      rw [Metric.mem_sphere] at hxsphere
      simpa [dist_eq_norm] using hxsphere
    have hinv : 1 / conj x = x := one_div_conj_of_norm_eq_one hnorm
    simp [diskReflectOuter, hinv, hfx]
  · -- The inner piece is continuous on the closed disc, hence on the ball ∩ closure.
    refine (hc.sub continuousOn_const).mono ?_
    intro z hz
    have hcl : IsClosed {w : ℂ | ‖w‖ ≤ 1} := isClosed_Iic.preimage continuous_norm
    have hz1 : ‖z‖ ≤ 1 := by
      have h := hz.2
      rwa [hcl.closure_eq] at h
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz1
  · -- The outer piece is continuous on `{1 ≤ ‖z‖}`, which contains the relevant closure.
    have hOuter : ContinuousOn (diskReflectOuter f a) {w : ℂ | 1 ≤ ‖w‖} := by
      unfold diskReflectOuter
      have hmap : ContinuousOn (fun z : ℂ => 1 / conj z) {w : ℂ | 1 ≤ ‖w‖} := by
        have hconj : ContinuousOn (fun z : ℂ => conj z) {w : ℂ | 1 ≤ ‖w‖} :=
          Complex.continuous_conj.continuousOn
        have hne : ∀ z ∈ {w : ℂ | 1 ≤ ‖w‖}, conj z ≠ 0 := by
          intro z hz hz0
          have hz_eq : z = 0 := by
            have h1 := congrArg conj hz0
            simpa using h1
          have hle : (1 : ℝ) ≤ ‖z‖ := hz
          rw [hz_eq] at hle
          norm_num at hle
        refine (hconj.inv₀ hne).congr ?_
        intro z _
        simp [one_div]
      have hcomp : ContinuousOn (fun z : ℂ => f (1 / conj z)) {w : ℂ | 1 ≤ ‖w‖} :=
        hc.comp hmap (by
          intro z hz
          rw [Metric.mem_closedBall, dist_zero_right]
          show ‖1 / conj z‖ ≤ 1
          rw [one_div, norm_inv, Complex.norm_conj]
          exact inv_le_one_of_one_le₀ hz)
      exact (Complex.continuous_conj.continuousOn.comp hcomp (Set.mapsTo_univ _ _)).sub
        continuousOn_const
    have hcl : IsClosed {w : ℂ | 1 ≤ ‖w‖} := isClosed_Ici.preimage continuous_norm
    have hsub : {w : ℂ | ¬ ‖w‖ ≤ 1} ⊆ {w : ℂ | 1 ≤ ‖w‖} :=
      fun w hw => le_of_lt (not_le.mp hw)
    exact hOuter.mono (fun z hz => closure_minimal hsub hcl hz.2)

end Work.RPB1a.Caratheodory
