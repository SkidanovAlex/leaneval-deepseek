/-
  WilC4aCS.Helpers: small reusable bridges for the curve-selection step.
-/
import Submission.Work.WilC4aCS.Defs

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped BigOperators
open WilkiesConjecture WilkiesDesign WilkiesDesign.CG

namespace Work.WilC4aCS

open WilkiesDesign.CG.C4a
open WilkiesDesign.E

/-- If `0` lies in the closure of `{x | ∀ j, 0 < g j x}` then no `g j` vanishes identically near
`0`. -/
lemma eventually_ne_zero_of_closure {α : Type*} [PseudoMetricSpace α] {l : ℕ} {a : α}
    (g : Fin l → α → ℝ) (hcl : a ∈ closure {x : α | ∀ j, 0 < g j x}) :
    ∀ j, ¬ (g j =ᶠ[𝓝 a] 0) := by
  intro j hj
  obtain ⟨r, hr, hr'⟩ := Metric.eventually_nhds_iff.mp hj
  obtain ⟨x, hx, hxr⟩ := Metric.mem_closure_iff.mp hcl r hr
  have h1 : g j x = 0 := hr' (by rwa [dist_comm] at hxr)
  have h2 : 0 < g j x := hx j
  rw [h1] at h2
  exact lt_irrefl 0 h2

/-- The equation holds at the origin as soon as the origin lies in the closure of the basic
semianalytic set. -/
lemma eq_zero_of_mem_closure {m l : ℕ} {F : (Fin m → ℝ) → ℝ} {g : Fin l → (Fin m → ℝ) → ℝ}
    (hF : AnalyticAt ℝ F 0) (hcl : (0 : Fin m → ℝ) ∈ closure (BasicSA F g)) : F 0 = 0 := by
  by_contra hne
  have hnb : ∀ᶠ x in 𝓝 (0 : Fin m → ℝ), F x ≠ 0 := hF.continuousAt.eventually_ne hne
  obtain ⟨r, hr, hr'⟩ := Metric.eventually_nhds_iff.mp hnb
  obtain ⟨x, hx, hxr⟩ := Metric.mem_closure_iff.mp hcl r hr
  exact hr' (by simpa [dist_eq_norm] using hxr) hx.1

/-- If `F` vanishes identically near the origin, an arc starting at the origin lies in `{F = 0}` for
small positive parameters. -/
lemma arc_mem_zero_of_eventually_eq_zero {m : ℕ} {F : (Fin m → ℝ) → ℝ} {γ : ℝ → (Fin m → ℝ)}
    (hF : F =ᶠ[𝓝 0] 0) (hγ : ContinuousAt γ 0) (hγ0 : γ 0 = 0) :
    ∃ ε > (0 : ℝ), ∀ s ∈ Set.Ioo (0 : ℝ) ε, F (γ s) = 0 := by
  obtain ⟨r, hr, hr'⟩ := Metric.eventually_nhds_iff.mp hF
  have hball : ∀ᶠ s in 𝓝 (0 : ℝ), γ s ∈ Metric.ball (0 : Fin m → ℝ) r :=
    hγ.tendsto.eventually (by rw [hγ0]; exact Metric.ball_mem_nhds (0 : Fin m → ℝ) hr)
  obtain ⟨ε, hε, hε'⟩ := Metric.eventually_nhds_iff.mp hball
  refine ⟨ε, hε, fun s hs => hr' (hε' ?_)⟩
  show dist s 0 < ε
  rw [dist_eq_norm, Real.norm_eq_abs, sub_zero, abs_of_pos hs.1]
  exact hs.2

/-- Curve selection at the origin, from curve selection at an arbitrary centre. -/
theorem curveSelAt0_of_curveSel {m : ℕ} (h : CurveSel m) : CurveSelAt0 m :=
  fun l F g hF hg hc => h l F g 0 hF hg hc

/-- Curve selection at an arbitrary centre, from curve selection at the origin. -/
theorem curveSel_of_curveSelAt0 {m : ℕ} (h : CurveSelAt0 m) : CurveSel m := by
  intro l F g q hF hg hq
  have hTq : AnalyticAt ℝ (fun x : Fin m → ℝ => x + q) 0 :=
    analyticAt_id.add analyticAt_const
  have hF' : AnalyticAt ℝ (fun x : Fin m → ℝ => F (x + q)) 0 :=
    hF.comp_of_eq hTq (by simp)
  have hg' : ∀ j, AnalyticAt ℝ (fun x : Fin m → ℝ => g j (x + q)) 0 := fun j =>
    (hg j).comp_of_eq hTq (by simp)
  have hq' : (0 : Fin m → ℝ) ∈
      closure (BasicSA (fun x : Fin m → ℝ => F (x + q))
        (fun j x => g j (x + q))) := by
    rw [Metric.mem_closure_iff] at hq ⊢
    intro ε hε
    obtain ⟨y, hy, hyε⟩ := hq ε hε
    refine ⟨y - q, ⟨?_, ?_⟩, ?_⟩
    · simpa [sub_add_cancel] using hy.1
    · intro j
      simpa [sub_add_cancel] using hy.2 j
    · rw [dist_eq_norm]
      simpa [dist_eq_norm] using hyε
  obtain ⟨γ₀, hγ₀an, hγ₀0, ε, hε, hγ₀mem⟩ :=
    h l (fun x : Fin m → ℝ => F (x + q)) (fun j x => g j (x + q)) hF' hg' hq'
  refine ⟨fun s => γ₀ s + q, hγ₀an.add analyticAt_const, ?_, ε, hε, ?_⟩
  · show γ₀ 0 + q = q
    rw [hγ₀0, zero_add]
  · intro s hs
    have h' := hγ₀mem s hs
    exact ⟨h'.1, h'.2⟩

end Work.WilC4aCS
