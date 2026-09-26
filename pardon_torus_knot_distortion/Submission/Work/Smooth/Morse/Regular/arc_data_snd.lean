import Mathlib
import Submission.Work.Smooth.Morse.Regular.contDiffAt_one_deriv_nhds

/-!
# The level set of a `C¹` function of two variables is locally a graph over the first variable

This is the implicit function theorem in the plane, in the form needed for the local
description of regular level sets: if `f : ℝ × ℝ → ℝ` is `C¹` at `p`, with `f p = t` and with
invertible partial derivative in the *second* variable, then near `p` the level set `{f = t}` is
the graph `x ↦ (x, ψ x)` of a `C¹` function `ψ`.

Besides the graph property `f (x, ψ x) = t` on a symmetric interval around `p.1`, the statement
records the local regularity of `ψ` (`HasDerivAt` with derivative `deriv ψ`, continuity of `ψ`
and of `deriv ψ`) and the uniqueness of the implicit function: inside a neighbourhood `U` of `p`,
every point of the level set has second coordinate `ψ` applied to its first coordinate.

The implicit function itself is produced by Mathlib's implicit function theorem
(`ContDiffAt.implicitFunction`), and the regularity on an interval around `p.1` is extracted from
`Work.Smooth.Morse.Regular.contDiffAt_one_deriv_nhds`.
-/

open Set

open scoped Topology

namespace Work.Smooth.Morse.Regular

theorem arc_data_snd {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} {t : ℝ}
    (hf : ContDiffAt ℝ 1 f p) (hp : f p = t)
    (hinv : (fderiv ℝ f p ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible) :
    ∃ (ψ : ℝ → ℝ) (ρ : ℝ) (U : Set (ℝ × ℝ)),
      0 < ρ ∧ IsOpen U ∧ p ∈ U ∧ ψ p.1 = p.2 ∧
      ContinuousAt (deriv ψ) p.1 ∧
      (∀ x ∈ Set.Ioo (p.1 - ρ) (p.1 + ρ), HasDerivAt ψ (deriv ψ x) x) ∧
      ContinuousOn (deriv ψ) (Set.Ioo (p.1 - ρ) (p.1 + ρ)) ∧
      ContinuousOn ψ (Set.Ioo (p.1 - ρ) (p.1 + ρ)) ∧
      (∀ x ∈ Set.Ioo (p.1 - ρ) (p.1 + ρ), f (x, ψ x) = t) ∧
      (∀ v ∈ U, f v = t → v.2 = ψ v.1) := by
  -- The implicit function `ψ` solving `f (x, ψ x) = f p` near `p.1`.
  have hn : (1 : WithTop ℕ∞) ≠ 0 := one_ne_zero
  set ψ : ℝ → ℝ := hf.implicitFunction hn hinv with hψdef
  -- `ψ` is `C¹` at `p.1` and takes the value `p.2` there.
  have hψcd : ContDiffAt ℝ 1 ψ p.1 := by
    rw [hψdef]; exact hf.contDiffAt_implicitFunction hn hinv
  have hψself : ψ p.1 = p.2 := by
    rw [hψdef]; exact hf.implicitFunction_apply_self hn hinv
  -- Regularity of `ψ` and of `deriv ψ` on an interval around `p.1`.
  obtain ⟨ρ₁, hρ₁, hdc, hder, hψc⟩ := contDiffAt_one_deriv_nhds hψcd
  -- `f (x, ψ x) = t` for `x` near `p.1`.
  have hlev : ∀ᶠ x in 𝓝 p.1, f (x, ψ x) = t := by
    have h := hf.eventually_apply_implicitFunction hn hinv
    rw [← hψdef] at h
    filter_upwards [h] with x hx
    rw [hx, hp]
  obtain ⟨ρ₂, hρ₂, hρ₂sub⟩ := Metric.mem_nhds_iff.mp hlev
  -- Uniqueness: locally the level set is exactly the graph of `ψ`.
  have huniq : ∀ᶠ v in 𝓝 p, f v = t → v.2 = ψ v.1 := by
    have h := hf.eventually_apply_eq_iff_implicitFunction hn hinv
    rw [← hψdef] at h
    filter_upwards [h] with v hv hfv
    exact (hv.mp (by rw [hfv, hp])).symm
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp huniq
  refine ⟨ψ, min ρ₁ ρ₂, Metric.ball p δ, lt_min hρ₁ hρ₂, Metric.isOpen_ball,
    Metric.mem_ball_self hδ, hψself, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `deriv ψ` is continuous at `p.1`
    exact hdc.continuousAt (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
  · -- `ψ` is differentiable, with derivative `deriv ψ`, on the interval
    intro x hx
    exact hder x
      ⟨by have := min_le_left ρ₁ ρ₂; linarith [hx.1],
       by have := min_le_left ρ₁ ρ₂; linarith [hx.2]⟩
  · -- continuity of `deriv ψ` on the interval
    exact hdc.mono (fun x hx =>
      ⟨by have := min_le_left ρ₁ ρ₂; linarith [hx.1],
       by have := min_le_left ρ₁ ρ₂; linarith [hx.2]⟩)
  · -- continuity of `ψ` on the interval
    exact hψc.mono (fun x hx =>
      ⟨by have := min_le_left ρ₁ ρ₂; linarith [hx.1],
       by have := min_le_left ρ₁ ρ₂; linarith [hx.2]⟩)
  · -- the graph lies in the level set
    intro x hx
    apply hρ₂sub
    rw [Real.ball_eq_Ioo]
    exact ⟨by have := min_le_right ρ₁ ρ₂; linarith [hx.1],
           by have := min_le_right ρ₁ ρ₂; linarith [hx.2]⟩
  · -- the level set in `U` is contained in the graph of `ψ`
    intro v hv hfv
    exact hδsub hv hfv

end Work.Smooth.Morse.Regular
