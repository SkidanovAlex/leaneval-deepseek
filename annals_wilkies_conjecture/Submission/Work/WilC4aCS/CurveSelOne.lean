/-
  WilC4aCS.CurveSelOne: the one-dimensional base case `CurveSel 1`.

  If `F` is not identically zero near the origin we use the general machinery of `CaseB` (with
  `CurveSel 0`); if `F` vanishes identically, only inequalities remain and the problem is genuinely
  one-dimensional: each `gⱼ` has constant sign on each side of `0` (or vanishes identically there),
  and `0 ∈ closure {g > 0}` forces one whole side to lie in the set, over which the linear arc
  `s ↦ s • e₀` (or `s ↦ (-s) • e₀`) runs.
-/
import Submission.Work.WilC4aCS.Helpers
import Submission.Work.WilC4aCS.CaseB
import Submission.Work.WilC4aCS.exists_side_pos
import Submission.Work.WilC4aCS.curveSelAt0_of_red

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped BigOperators
open WilkiesConjecture WilkiesDesign WilkiesDesign.CG

namespace Work.WilC4aCS

open WilkiesDesign.CG.C4a
open WilkiesDesign.E

/-- In dimension one, `0 ∈ closure {g > 0}` forces a whole side to satisfy all the inequalities. -/
theorem one_dim_side {l : ℕ} (g : Fin l → (Fin 1 → ℝ) → ℝ)
    (hg : ∀ j, AnalyticAt ℝ (g j) 0) (hg0 : ∀ j, g j 0 = 0)
    (hcl : (0 : Fin 1 → ℝ) ∈ closure {x : Fin 1 → ℝ | ∀ j, 0 < g j x}) :
    ∃ δ > (0 : ℝ),
      (∀ s : ℝ, 0 < s → s < δ → ∀ j, 0 < g j (s • (fun _ : Fin 1 => (1 : ℝ)))) ∨
      (∀ s : ℝ, 0 < s → s < δ → ∀ j, 0 < g j (s • (fun _ : Fin 1 => (-1 : ℝ)))) := by
  let e₀ : Fin 1 → ℝ := fun _ => 1
  let g₁ : Fin l → ℝ → ℝ := fun j s => g j (s • e₀)
  have hsmul : AnalyticAt ℝ (fun s : ℝ => s • e₀) 0 :=
    (ContinuousLinearMap.toSpanSingleton ℝ e₀).analyticAt 0
  have hg₁an : ∀ j, AnalyticAt ℝ (g₁ j) 0 := fun j =>
    (hg j).comp_of_eq hsmul (by simp [e₀])
  have himg : (fun x : Fin 1 → ℝ => x 0) '' {y : Fin 1 → ℝ | ∀ j, 0 < g j y}
      = {s : ℝ | ∀ j, 0 < g₁ j s} := by
    ext s
    constructor
    · rintro ⟨y, hy, rfl⟩
      intro j
      have hyy : y = (y 0) • e₀ := by
        funext i
        rw [Fin.eq_zero i]
        simp [e₀]
      show 0 < g j ((y 0) • e₀)
      rw [← hyy]
      exact hy j
    · intro hs
      refine ⟨s • e₀, fun j => ?_, by simp [e₀]⟩
      show 0 < g j (s • e₀)
      exact hs j
  have hcl₁ : (0 : ℝ) ∈ closure {s : ℝ | ∀ j, 0 < g₁ j s} := by
    have hcont : Continuous (fun x : Fin 1 → ℝ => x 0) := continuous_apply 0
    have hsub := image_closure_subset_closure_image hcont
      (s := {y : Fin 1 → ℝ | ∀ j, 0 < g j y})
    rw [himg] at hsub
    exact hsub ⟨0, hcl, rfl⟩
  have hnz₁ : ∀ j, ¬ (∀ᶠ s in 𝓝 (0 : ℝ), g₁ j s = 0) :=
    eventually_ne_zero_of_closure g₁ hcl₁
  have hg₁0 : ∀ j, g₁ j 0 = 0 := fun j => by simp [g₁, e₀, hg0 j]
  obtain ⟨δ, hδ, hside⟩ := exists_side_pos g₁ hg₁an hg₁0 hnz₁ hcl₁
  refine ⟨δ, hδ, ?_⟩
  rcases hside with hside | hside
  · left
    intro s hs hlt j
    have h := hside s hs hlt j
    show 0 < g j (s • e₀)
    exact h
  · right
    intro s hs hlt j
    have h := hside (-s) (by linarith) (by linarith) j
    show 0 < g j (s • (fun _ : Fin 1 => (-1 : ℝ)))
    have h' : g j (s • (fun _ : Fin 1 => (-1 : ℝ))) = g j ((-s) • e₀) := by
      congr 1
      ext i
      simp [Pi.smul_apply, e₀]
    rw [h']
    exact h

/-- Curve selection at the origin in dimension one. -/
theorem curveSelAt0_one (hW : RealWeierstrass) (hA : ArcLift) (hT : TS1) : CurveSelAt0 1 :=
  curveSelAt0_of_red (m := 1) (by
    intro l F g hF hg hg0 hcl
    have hF0 : F 0 = 0 := by
      by_contra hne
      have hnb : ∀ᶠ x in 𝓝 (0 : Fin 1 → ℝ), F x ≠ 0 :=
        hF.continuousAt.eventually_ne hne
      obtain ⟨r, hr, hr'⟩ := Metric.eventually_nhds_iff.mp hnb
      obtain ⟨x, hx, hxr⟩ := Metric.mem_closure_iff.mp hcl r hr
      exact hr' (by simpa [dist_eq_norm] using hxr) hx.1
    by_cases hY : (0 : Fin 1 → ℝ) ∈ BasicSA F g
    · exact ⟨fun _ => 0, analyticAt_const, rfl, 1, one_pos, fun s hs => hY⟩
    · have hclg : (0 : Fin 1 → ℝ) ∈ closure {x : Fin 1 → ℝ | ∀ j, 0 < g j x} :=
        closure_mono (fun x hx => hx.2) hcl
      by_cases hFz : F =ᶠ[𝓝 0] 0
      · obtain ⟨δ, hδ, hside⟩ := one_dim_side g hg hg0 hclg
        rcases hside with hside | hside
        · -- positive side
          obtain ⟨εF, hεF, hεF'⟩ := arc_mem_zero_of_eventually_eq_zero hFz
            ((ContinuousLinearMap.toSpanSingleton ℝ (fun _ : Fin 1 => (1 : ℝ))).analyticAt 0).continuousAt
            (by simp)
          refine ⟨fun s => s • (fun _ : Fin 1 => (1 : ℝ)),
            (ContinuousLinearMap.toSpanSingleton ℝ (fun _ : Fin 1 => (1 : ℝ))).analyticAt 0,
            by simp, min δ εF, lt_min hδ hεF, fun s hs => ⟨?_, ?_⟩⟩
          · exact hεF' s ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_right _ _)⟩
          · intro j
            exact hside s hs.1 (lt_of_lt_of_le hs.2 (min_le_left _ _)) j
        · -- negative side
          obtain ⟨εF, hεF, hεF'⟩ := arc_mem_zero_of_eventually_eq_zero hFz
            ((ContinuousLinearMap.toSpanSingleton ℝ (fun _ : Fin 1 => (-1 : ℝ))).analyticAt 0).continuousAt
            (by simp)
          refine ⟨fun s => s • (fun _ : Fin 1 => (-1 : ℝ)),
            (ContinuousLinearMap.toSpanSingleton ℝ (fun _ : Fin 1 => (-1 : ℝ))).analyticAt 0,
            by simp, min δ εF, lt_min hδ hεF, fun s hs => ⟨?_, ?_⟩⟩
          · exact hεF' s ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_right _ _)⟩
          · intro j
            exact hside s hs.1 (lt_of_lt_of_le hs.2 (min_le_left _ _)) j
      · exact caseB_step F g hF hg hF0 hg0 hFz
          (eventually_ne_zero_of_closure g hclg) hcl CurveSel_zero hW hA hT)

/-- **The one-dimensional induction step**: `CurveSel 1`. -/
theorem curveSel_one (hW : RealWeierstrass) (hA : ArcLift) (hT : TS1) : CurveSel 1 :=
  curveSel_of_curveSelAt0 (curveSelAt0_one hW hA hT)

end Work.WilC4aCS
