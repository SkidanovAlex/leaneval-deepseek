/-
  WilC4aCS.CurveSelStep: assembly of the induction step `CurveSel n → CurveSel (n+1)` for `n ≥ 1`
  (ambient dimension at least two), together with the final deliverable `C4a_CS_step_proved`.

  * At the origin, if the origin already lies in the basic semianalytic set, the constant arc works.
  * In the *reduced* case (every inequality function vanishes at the origin) the inequality functions
    are not identically zero near the origin, `F 0 = 0`, and if `F` is not identically zero as a germ
    the Weierstrass/Tarski–Seidenberg/Puiseux machinery of `CaseB` applies.
  * If `F` does vanish identically, only inequalities are left, and `caseA_equation` manufactures an
    equation (a maximiser of `∏ gⱼ` over the ball cut by `{g ≥ 0}`), reducing to the previous case.
  * Finally, `CurveSelAt0` is transported to an arbitrary centre by translation, and dimension one is
    handled by `CurveSelOne`.
-/
import Submission.Work.WilC4aCS.Helpers
import Submission.Work.WilC4aCS.Setup
import Submission.Work.WilC4aCS.CaseB
import Submission.Work.WilC4aCS.CaseA
import Submission.Work.WilC4aCS.CurveSelOne
import Submission.Work.WilC4aCS.curveSelAt0_of_red

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped BigOperators
open WilkiesConjecture WilkiesDesign WilkiesDesign.CG

namespace Work.WilC4aCS

open WilkiesDesign.CG.C4a
open WilkiesDesign.E

/-- **The reduced core in dimension `n+1` with `n ≥ 1`.** -/
theorem curveSelAt0Red_succ_pos {n : ℕ} (hn : 1 ≤ n) (hW : RealWeierstrass) (hA : ArcLift)
    (hT : TS1) (ih : CurveSel n) : CurveSelAt0Red (n + 1) := by
  intro l F g hF hg hg0 hcl
  have hF0 : F 0 = 0 := eq_zero_of_mem_closure hF hcl
  by_cases hY : (0 : Fin (n + 1) → ℝ) ∈ BasicSA F g
  · exact ⟨fun _ => 0, analyticAt_const, rfl, 1, one_pos, fun s hs => hY⟩
  · have hclg : (0 : Fin (n + 1) → ℝ) ∈
        closure {x : Fin (n + 1) → ℝ | ∀ j, 0 < g j x} :=
      closure_mono (fun x hx => hx.2) hcl
    have hgnz : ∀ j, ¬ (g j =ᶠ[𝓝 0] 0) := eventually_ne_zero_of_closure g hclg
    have hl : 1 ≤ l := by
      rcases Nat.eq_zero_or_pos l with hl0 | hlpos
      · exact absurd ⟨hF0, fun j => (hl0 ▸ j).elim0⟩ hY
      · exact hlpos
    by_cases hFz : F =ᶠ[𝓝 0] 0
    · -- `F` is identically zero: only inequalities remain
      have hm : 2 ≤ n + 1 := by omega
      obtain ⟨E, hEan, hE0, hEnz, hEcl⟩ := caseA_equation hm hl g hg hg0 hclg
      obtain ⟨γ, hγan, hγ0, ε, hε, hγmem⟩ :=
        caseB_step E g hEan hg hE0 hg0 hEnz hgnz hEcl ih hW hA hT
      obtain ⟨εF, hεF, hεF'⟩ := arc_mem_zero_of_eventually_eq_zero hFz hγan.continuousAt hγ0
      refine ⟨γ, hγan, hγ0, min ε εF, lt_min hε hεF, fun s hs => ⟨?_, ?_⟩⟩
      · exact hεF' s ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_right _ _)⟩
      · exact (hγmem s ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩).2
    · -- `F` is a nonzero germ: the Weierstrass machinery applies
      exact caseB_step F g hF hg hF0 hg0 hFz hgnz hcl ih hW hA hT

/-- Curve selection at the origin in dimension `n+1`. -/
theorem curveSelAt0_succ {n : ℕ} (hW : RealWeierstrass) (hA : ArcLift) (hT : TS1)
    (ih : CurveSel n) : CurveSelAt0 (n + 1) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    exact curveSelAt0_one hW hA hT
  · exact curveSelAt0_of_red (curveSelAt0Red_succ_pos hnpos hW hA hT ih)

/-- Curve selection at an arbitrary centre in dimension `n+1`. -/
theorem curveSel_succ {n : ℕ} (hW : RealWeierstrass) (hA : ArcLift) (hT : TS1)
    (ih : CurveSel n) : CurveSel (n + 1) :=
  curveSel_of_curveSelAt0 (curveSelAt0_succ hW hA hT ih)

/-- Curve selection in dimension `0` (a one-point space), proved here so that this chapter is
self-contained (it does not need the wiring file of the area). -/
theorem curveSel_zero : CurveSel 0 := by
  intro l F g q _ _ hq
  have hne : (BasicSA F g).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at hq
    exact hq
  obtain ⟨x, hx⟩ := hne
  have hxq : x = q := Subsingleton.elim x q
  subst hxq
  exact ⟨fun _ => x, analyticAt_const, rfl, 1, one_pos, fun _ _ => hx⟩

/-- **Curve selection in every dimension**, given the three other areas' inputs
(`RealWeierstrass`, `ArcLift`, `TS1`).  This is the top of the chapter. -/
theorem curveSel_all (hW : RealWeierstrass) (hA : ArcLift) (hT : TS1) : ∀ n, CurveSel n := by
  intro n
  induction n with
  | zero => exact curveSel_zero
  | succ k ih => exact curveSel_succ hW hA hT ih

end Work.WilC4aCS

namespace WilkiesDesign.CG.C4a

/-- **The CG hole `C4a_CS_step`.**  From curve selection in dimension `n` we get curve selection in
dimension `n+1`, using real Weierstrass preparation, Tarski–Seidenberg, real Puiseux lifting
(`ArcLift`) and, in the inequality-only case, a maximiser argument plus a manufactured equation. -/
theorem C4a_CS_step_proved (hW : RealWeierstrass) (hA : ArcLift) (hT : TS1) (n : ℕ)
    (ih : CurveSel n) : CurveSel (n + 1) :=
  Work.WilC4aCS.curveSel_succ hW hA hT ih

end WilkiesDesign.CG.C4a
