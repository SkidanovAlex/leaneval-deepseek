import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.basic
import Submission.Work.Repel.pushdown_holo

/-!
# `pushdown Ẽ_{f₀}` is holomorphic on the punctured disc of radius `exp(-2πη₀)`

For a point `ζ` of `0 < |ζ| < exp(-2πη₀)` the principal lift `w = log ζ/(2πi)` satisfies
`Im w > η₀`: indeed `|π w| = exp(-2π Im w)`, so `|ζ| = |π w| < exp(-2πη₀)` gives
`Im w > η₀`.  Hence `|Im w| > η₀`, and the field `ParabData.ends_sub` (the lifted horn map is
defined at both ends) puts `w` in `Dφ` with `φ w` in the parabolic basin, i.e. `w ∈ d.DE`.

The set `S = {w | η₀ < |Im w|}` is `T`-invariant (the translation `w ↦ w+1` preserves `Im`),
`Ẽ = Φ ∘ φ` is holomorphic and `T`-equivariant on it, so the colleague-proved
`Work.Repel.pushdown_holo` gives differentiability of `pushdown Ẽ` on `π '' S`.  Finally
`π '' S` contains the punctured disc, because every such `ζ` is `π` of its principal lift.
-/

open MandelDim Set Metric Filter Topology Complex
open scoped Topology

namespace Work.Horn

noncomputable section

/-- The set `{|Im w| > η}` is invariant under `w ↦ w + 1` (translation preserves `Im`). -/
theorem isTInvariant_abs_im_gt (η : ℝ) : IsTInvariant {w : ℂ | η < |w.im|} := by
  intro w
  simp

/-- `Ẽ = Φ ∘ φ` is holomorphic on `{|Im w| > η₀}`: both ends lie in `Dφ` and map into the
parabolic basin. -/
theorem differentiableOn_E_abs_im_gt {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) :
    DifferentiableOn ℂ d.E {w : ℂ | d.η₀ < |w.im|} := by
  intro w hw
  have hwD : w ∈ d.Dφ := (d.ends_sub w hw).1
  have hwB : d.φ w ∈ ParabolicBasin f₀ D₀ := (d.ends_sub w hw).2
  have hφ : DifferentiableWithinAt ℂ d.φ {w : ℂ | d.η₀ < |w.im|} w :=
    (d.φ_holo w hwD).mono (fun x hx => (d.ends_sub x hx).1)
  have hΦ : DifferentiableWithinAt ℂ d.Φ (ParabolicBasin f₀ D₀) (d.φ w) :=
    d.Φ_holo (d.φ w) hwB
  exact hΦ.comp w hφ (fun x hx => (d.ends_sub x hx).2)

/-- `Ẽ` is `T`-equivariant on `{|Im w| > η₀}`. -/
theorem isTEquivariantOn_E_abs_im_gt {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) :
    IsTEquivariantOn d.E {w : ℂ | d.η₀ < |w.im|} := by
  refine ⟨isTInvariant_abs_im_gt d.η₀, fun w hw => ?_⟩
  have hw1 : w + 1 ∈ {w : ℂ | d.η₀ < |w.im|} := (isTInvariant_abs_im_gt d.η₀ w).mp hw
  have h1 : w ∈ d.Dφ := (d.ends_sub w hw).1
  have h2 : w + 1 ∈ d.Dφ := (d.ends_sub (w + 1) hw1).1
  have h3 : d.φ w ∈ ParabolicBasin f₀ D₀ := (d.ends_sub w hw).2
  simp only [ParabData.E]
  rw [d.φ_abel w h1 h2, d.Φ_abel (d.φ w) h3]

theorem pushdown_differentiableOn_punctured (f₀ : ℂ → ℂ) (D₀ : Set ℂ)
    (d : MandelDim.ParabData f₀ D₀) :
    DifferentiableOn ℂ (MandelDim.pushdown d.E)
      (Metric.ball 0 (Real.exp (-(2 * Real.pi * d.η₀))) \ {0}) := by
  refine (Work.Repel.pushdown_holo (isTEquivariantOn_E_abs_im_gt d)
    (differentiableOn_E_abs_im_gt d)).mono ?_
  intro ζ hζ
  rw [Set.mem_sdiff, Set.mem_singleton_iff, Metric.mem_ball, dist_zero_right] at hζ
  obtain ⟨hball, hne⟩ := hζ
  refine ⟨Complex.log ζ / (2 * Real.pi * Complex.I), ?_,
    Work.Horn.MandelDim.piExp_log_div ζ hne⟩
  show d.η₀ < |(Complex.log ζ / (2 * Real.pi * Complex.I)).im|
  have him : (Complex.log ζ / (2 * Real.pi * Complex.I)).im =
      -(Real.log ‖ζ‖) / (2 * Real.pi) := by
    rw [Complex.div_im, Complex.log_re, Complex.log_im]
    have h1 : (2 * ↑Real.pi * Complex.I : ℂ).re = 0 := by simp
    have h2 : (2 * ↑Real.pi * Complex.I : ℂ).im = 2 * Real.pi := by simp
    have h3 : Complex.normSq ((2 : ℂ) * ↑Real.pi * Complex.I) = (2 * Real.pi) ^ 2 := by
      rw [show ((2 : ℂ) * ↑Real.pi * Complex.I) = ↑(2 * Real.pi) * Complex.I by
        push_cast; ring]
      rw [Complex.normSq_apply]
      simp
      ring
    rw [h1, h2, h3]
    field_simp
    ring
  rw [him]
  have hlog : Real.log ‖ζ‖ < -(2 * Real.pi * d.η₀) := by
    have h1 : Real.log ‖ζ‖ < Real.log (Real.exp (-(2 * Real.pi * d.η₀))) :=
      Real.log_lt_log (norm_pos_iff.mpr hne) hball
    simpa using h1
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hgt : d.η₀ < -(Real.log ‖ζ‖) / (2 * Real.pi) := by
    rw [lt_div_iff₀ h2pi]
    linarith
  exact lt_of_lt_of_le hgt (le_abs_self _)

end

end Work.Horn
