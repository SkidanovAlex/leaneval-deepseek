import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.RoucheBridge

/-!
# Covering near the identity

If `g` is complex differentiable on the closed disc `closedBall c R` and is `ε`-close to the
identity on its boundary sphere, then `g` is a bijection from the open disc `ball c R` onto the
open disc `ball c (R - ε)` in the sense that every `a` with `dist a c < R - ε` has a *unique*
preimage under `g` inside `ball c R`.

The proof is Rouché's theorem (`Commons.Analysis.Complex.rouche_simple_zero`): translating by `c`,
the two functions `f u = u - (a - c)` and `w u = g (c + u) - c - u` satisfy `‖w u‖ < ‖f u‖` on the
sphere of radius `R` (since `‖w u‖ ≤ ε` while `‖f u‖ ≥ R - ‖a - c‖ > ε`).  Hence `f + w`, i.e.
`u ↦ g (c + u) - a`, has the same number of zeros in the disc as `f`, which is exactly one.
-/

namespace Work.Repel

open Metric

theorem covering_near_id {c a : ℂ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (hεR : ε < R)
    {g : ℂ → ℂ} (hd : DifferentiableOn ℂ g (Metric.closedBall c R))
    (hclose : ∀ z ∈ Metric.sphere c R, ‖g z - z‖ ≤ ε)
    (ha : a ∈ Metric.ball c (R - ε)) : ∃! z ∈ Metric.ball c R, g z = a := by
  have hac : ‖a - c‖ < R - ε := by
    rw [Metric.mem_ball, dist_eq_norm] at ha
    exact ha
  have hacR : ‖a - c‖ < R := by linarith
  -- the translated map `u ↦ g (c + u) - c - u` is holomorphic on `closedBall 0 R`
  have hmaps : Set.MapsTo (fun u : ℂ => c + u) (Metric.closedBall (0 : ℂ) R)
      (Metric.closedBall c R) := by
    intro u hu
    rw [Metric.mem_closedBall, dist_eq_norm] at hu ⊢
    rw [add_sub_cancel_left]
    simpa using hu
  have hG_diff : DifferentiableOn ℂ (fun u : ℂ => g (c + u) - c - u)
      (Metric.closedBall (0 : ℂ) R) := by
    have h1 : DifferentiableOn ℂ (fun u : ℂ => c + u) (Metric.closedBall (0 : ℂ) R) :=
      differentiableOn_id.const_add c
    have h2 : DifferentiableOn ℂ (fun u : ℂ => g (c + u)) (Metric.closedBall (0 : ℂ) R) :=
      hd.comp h1 hmaps
    exact (h2.sub_const c).sub differentiableOn_id
  have hf_diff : DifferentiableOn ℂ (fun u : ℂ => u - (a - c)) (Metric.closedBall (0 : ℂ) R) :=
    differentiableOn_id.sub_const (a - c)
  -- the sphere inequality
  have hsphere : ∀ u ∈ Metric.sphere (0 : ℂ) R,
      ‖g (c + u) - c - u‖ < ‖(fun u : ℂ => u - (a - c)) u‖ := by
    intro u hu
    have hunorm : ‖u‖ = R := by
      have h := Metric.mem_sphere.mp hu
      rwa [dist_zero_right] at h
    have hcu : c + u ∈ Metric.sphere c R := by
      rw [Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left]
      exact hunorm
    have hcl := hclose (c + u) hcu
    have hcl' : ‖g (c + u) - c - u‖ ≤ ε := by
      have hEq : g (c + u) - (c + u) = g (c + u) - c - u := by ring
      rw [← hEq]
      exact hcl
    have hlb : R - ‖a - c‖ ≤ ‖u - (a - c)‖ := by
      have h1 : ‖u‖ ≤ ‖u - (a - c)‖ + ‖a - c‖ := by
        have h := norm_add_le (u - (a - c)) (a - c)
        rwa [sub_add_cancel] at h
      rw [hunorm] at h1
      linarith
    have : ε < ‖u - (a - c)‖ := by linarith
    linarith
  -- Rouché with `f` the identity shifted by `a - c` and `g` the perturbation
  obtain ⟨z, hzball, hz0, hzuniq⟩ :=
    Commons.Analysis.Complex.rouche_simple_zero (R := R) hR hacR
      (f := fun u : ℂ => u - (a - c)) (g := fun u : ℂ => g (c + u) - c - u)
      hf_diff hf_diff.continuousOn hG_diff hG_diff.continuousOn hsphere
      (by ring) (by simp) (by intro z _ hz; simpa using sub_eq_zero.mp hz)
  have hgz : g (c + z) = a := by
    have h : g (c + z) - a = 0 := by linear_combination hz0
    exact sub_eq_zero.mp h
  refine ⟨c + z, ⟨?_, hgz⟩, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    simpa [Metric.mem_ball, dist_eq_norm] using hzball
  · intro y hy
    obtain ⟨hyball, hgy⟩ := hy
    have hyball' : y - c ∈ Metric.ball (0 : ℂ) R := by
      have h : ‖y - c‖ < R := by
        rw [Metric.mem_ball, dist_eq_norm] at hyball
        exact hyball
      simpa [Metric.mem_ball, dist_eq_norm] using h
    have hzero : (fun u : ℂ => u - (a - c)) (y - c) + (g (c + (y - c)) - c - (y - c)) = 0 := by
      have hcy : c + (y - c) = y := by ring
      rw [hcy]
      linear_combination hgy
    have hzy : y - c = z := hzuniq (y - c) hyball' hzero
    linear_combination hzy

end Work.Repel
