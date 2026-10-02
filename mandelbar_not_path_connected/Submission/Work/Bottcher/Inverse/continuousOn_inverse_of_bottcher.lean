import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.log_half_le_green
import Submission.Work.Escape.green_le_log
import Submission.Work.Escape.continuous_green

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Continuity of the inverse Böttcher coordinate

If `φ` is holomorphic and injective on the escaping set `{z | 0 < green c z}` of the tricorn
family, then every right inverse `Ψ` of `φ`, defined on the exterior disc `{w | 1 < ‖w‖}` and
taking values in the escaping set, is continuous there.  (No modulus hypothesis is needed:
injectivity together with the open mapping theorem already gives this.)

The proof is the standard "a section of an injective open map is continuous".  Let
`z₀ = Ψ w₀`, so that `f z₀ = w₀`.  Since the escaping set is open (by continuity of the Green
function), it contains a ball `ball z₀ ε₁`.  At `z₀` the open mapping theorem
(`AnalyticAt.eventually_constant_or_nhds_le_map_nhds`) says that either `φ` is constant in a
neighbourhood of `z₀` — impossible, because `φ` is injective on the escaping set and `z₀` is an
interior point of it — or that the image `φ '' ball z₀ ρ` is a neighbourhood of `w₀ = φ z₀`.
In the second case, for every `w` with `‖w - w₀‖ < δ` we may write `w = φ z` with
`z ∈ ball z₀ ρ ⊆ EscapeSet c`; then `φ (Ψ w) = w = φ z` and injectivity force `Ψ w = z`, hence
`‖Ψ w - z₀‖ < ρ ≤ ε`.
-/

open Filter Function
open scoped Topology

namespace Work.Bottcher.Inverse

open LeanEval.ComplexAnalysis (Tantibar)

/-- The escaping set `{z | 0 < green c z}` of the tricorn family is open. -/
theorem isOpen_escapeSet_bot (c : ℂ) : IsOpen {z : ℂ | 0 < Work.Bottcher.green c z} := by
  have hcont : Continuous fun z : ℂ => Work.Escape.green (Tantibar c) 2 z :=
    Work.Escape.continuous_green (Tantibar c) 2 ‖c‖
      (Work.Escape.monicGrowth_Tantibar c) (le_refl 2)
  exact isOpen_lt continuous_const hcont

/-- Distance from `z` to `z + r`, for a real `r`. -/
private lemma dist_add_ofReal (x : ℂ) (r : ℝ) : dist (x + (r : ℂ)) x = |r| := by
  rw [dist_eq_norm, add_sub_cancel_left]
  exact RCLike.norm_ofReal r

/-- **A continuous right inverse of an injective holomorphic function on an open set.**
Let `s` be open, `f : ℂ → ℂ` analytic on `s` and injective on `s`, and let `g` be a right inverse
of `f` with values in `s` (i.e. `f (g w) = w` and `g w ∈ s` for `w ∈ t`).  Then `g` is continuous
on `t`. -/
theorem continuousOn_of_rightInverse {f g : ℂ → ℂ} {s t : Set ℂ} (hs : IsOpen s)
    (han : AnalyticOnNhd ℂ f s) (hinj : Set.InjOn f s)
    (hg : ∀ w ∈ t, g w ∈ s ∧ f (g w) = w) : ContinuousOn g t := by
  intro w0 hw0
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨hz0s, hfz0⟩ := hg w0 hw0
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.isOpen_iff.mp hs (g w0) hz0s
  set ρ : ℝ := min ε ε₁ with hρdef
  have hρ : 0 < ρ := lt_min hε hε₁
  have hρ_le_ε : ρ ≤ ε := min_le_left _ _
  have hρ_le_ε₁ : ρ ≤ ε₁ := min_le_right _ _
  have hballρ : Metric.ball (g w0) ρ ⊆ s :=
    (Metric.ball_subset_ball hρ_le_ε₁).trans hball₁
  rcases (han (g w0) hz0s).eventually_constant_or_nhds_le_map_nhds with hconst | hopen
  · -- `f` is constant near `z₀ = g w₀`; this contradicts injectivity on the open set `s`.
    exfalso
    obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hconst
    set r' : ℝ := min r ε₁ with hr'def
    have hr' : 0 < r' := lt_min hr hε₁
    have hr'_le_r : r' ≤ r := min_le_left _ _
    have hr'_le_ε₁ : r' ≤ ε₁ := min_le_right _ _
    set z₁ : ℂ := g w0 + ((r' / 2 : ℝ) : ℂ) with hz₁def
    have hdist : dist z₁ (g w0) = r' / 2 := by
      rw [hz₁def, dist_add_ofReal, abs_of_nonneg (by linarith)]
    have hz₁_ne : z₁ ≠ g w0 := by
      intro h
      rw [h, dist_self] at hdist
      linarith
    have hz₁_ball_r : z₁ ∈ Metric.ball (g w0) r := by
      rw [Metric.mem_ball, hdist]; linarith
    have hz₁_ball_ε₁ : z₁ ∈ Metric.ball (g w0) ε₁ := by
      rw [Metric.mem_ball, hdist]; linarith
    have hz₁_s : z₁ ∈ s := hball₁ hz₁_ball_ε₁
    have hfeq : f z₁ = f (g w0) := hrsub hz₁_ball_r
    exact hz₁_ne (hinj hz₁_s hz0s hfeq)
  · -- `f` maps every neighbourhood of `z₀` onto a neighbourhood of `f z₀ = w₀`.
    have hmem : f '' Metric.ball (g w0) ρ ∈ 𝓝 (f (g w0)) :=
      (Filter.le_def.mp hopen) _ (Filter.image_mem_map (Metric.ball_mem_nhds _ hρ))
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hmem
    refine ⟨δ, hδ, fun x hx hdist => ?_⟩
    have hxball : x ∈ Metric.ball (f (g w0)) δ := by
      rw [Metric.mem_ball, hfz0]; exact hdist
    obtain ⟨z, hzball, hzeq⟩ := hδsub hxball
    have hz_s : z ∈ s := hballρ hzball
    obtain ⟨hx_s, hxf⟩ := hg x hx
    have hzy : z = g x := hinj hz_s hx_s (by rw [hzeq, hxf])
    have hlt : dist z (g w0) < ρ := hzball
    rw [hzy] at hlt
    exact lt_of_lt_of_le hlt hρ_le_ε

set_option linter.unusedVariables false in
theorem continuousOn_inverse_of_bottcher (c : ℂ) (φ Ψ : ℂ → ℂ)
    (han : AnalyticOnNhd ℂ φ {z : ℂ | 0 < Work.Bottcher.green c z})
    (hinj : Set.InjOn φ {z : ℂ | 0 < Work.Bottcher.green c z})
    (hmod : ∀ z : ℂ, 0 < Work.Bottcher.green c z → ‖φ z‖ = Real.exp (Work.Bottcher.green c z))
    (hΨ : ∀ w : ℂ, 1 < ‖w‖ → Ψ w ∈ {z : ℂ | 0 < Work.Bottcher.green c z} ∧ φ (Ψ w) = w) :
    ContinuousOn Ψ {w : ℂ | 1 < ‖w‖} := by
  refine continuousOn_of_rightInverse (isOpen_escapeSet_bot c) han hinj (fun w hw => hΨ w hw)

end Work.Bottcher.Inverse
