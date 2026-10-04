import Mathlib
import Submission.Commons.Analysis.ODE.solution_close_of_lipschitz
import Submission.Commons.Analysis.ODE.exists_global_solution_of_lipschitz

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.ODE

open Set Metric Filter
open scoped Topology NNReal

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- **Uniform local existence on a closed ball.**

Let `F : E → E` be `L`-Lipschitz on the closed ball of radius `R` about `z₀` (`R > 0`) and bounded
there by `M ≥ 0`.  Then there is a *uniform* time scale `ρ > 0`, `ρ ≤ R`, such that for every
initial point `p` in the closed ball of radius `R/2` about `z₀` there is a curve `β` with `β 0 = p`
solving `β' = F ∘ β` on the open interval `(-ρ, ρ)` and staying in the closed ball of radius `R`
about `z₀`.

The proof truncates `F` outside the ball by composing with the radial retraction onto the ball, so
that the truncated field is globally `2L`-Lipschitz and globally bounded by `M`; the global
existence theorem for globally Lipschitz fields then gives a solution through every `p`, and the
explicit bound `‖β t - p‖ ≤ M |t|` (mean value inequality) shows that `β` stays in the ball for
`|t| ≤ R/(2(M+1))`, where it solves the original equation. -/
theorem uniform_local_solution_closedBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : E → E} {z₀ : E} {R : ℝ} (hR : 0 < R) {L : NNReal} {M : ℝ} (hM : 0 ≤ M)
    (hLip : LipschitzOnWith L F (Metric.closedBall z₀ R))
    (hbound : ∀ x ∈ Metric.closedBall z₀ R, ‖F x‖ ≤ M) :
    ∃ ρ > (0 : ℝ), ρ ≤ R ∧ ∀ p ∈ Metric.closedBall z₀ (R / 2),
      ∃ β : ℝ → E, β 0 = p ∧
        (∀ t ∈ Set.Ioo (-ρ) ρ, HasDerivAt β (F (β t)) t) ∧
        (∀ t ∈ Set.Ioo (-ρ) ρ, β t ∈ Metric.closedBall z₀ R) := by
  classical
  -- The uniform time scale.
  set ρ : ℝ := R / (2 * (M + 1)) with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; exact div_pos hR (by linarith)
  have hρle : ρ ≤ R := by
    rw [hρdef]
    exact div_le_self hR.le (by linarith)
  have hMρ : M * ρ ≤ R / 2 := by
    rw [hρdef, ← mul_div_assoc]
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 2 * (M + 1))]
    nlinarith [hR, hM]
  refine ⟨ρ, hρpos, hρle, ?_⟩
  intro p hp
  -- The truncated field: retract onto the closed ball `R` about `z₀`, then apply `F`.
  let G : E → E := fun x => z₀ + radialRetract R (x - z₀)
  let Φ : E → E := fun x => F (G x)
  have hG_ball : ∀ x, dist (G x) z₀ ≤ R := fun x => by
    simpa only [G, dist_eq_norm, add_sub_cancel_left]
      using norm_radialRetract_le hR.le (x - z₀)
  have hG_fix : ∀ x, dist x z₀ ≤ R → G x = x := fun x hx => by
    have hx' : ‖x - z₀‖ ≤ R := by rwa [dist_eq_norm] at hx
    simp only [G]
    rw [radialRetract_eq_self (x - z₀) hx', add_sub_cancel]
  have hG_lip : ∀ x y, dist (G x) (G y) ≤ 2 * dist x y := fun x y => by
    have h := dist_radialRetract_le hR.le (x - z₀) (y - z₀)
    have e1 : G x - G y = radialRetract R (x - z₀) - radialRetract R (y - z₀) := by
      simp only [G]; abel
    have e2 : (x - z₀) - (y - z₀) = x - y := by abel
    rw [dist_eq_norm, dist_eq_norm] at h
    rw [e2] at h
    rw [dist_eq_norm, dist_eq_norm, e1]
    exact h
  have hΦ_lip : LipschitzWith (2 * L) Φ := by
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    simp only [Φ]
    have h2 : dist (F (G x)) (F (G y)) ≤ (L : ℝ) * dist (G x) (G y) :=
      hLip.dist_le_mul (G x) (Metric.mem_closedBall.mpr (hG_ball x)) (G y)
        (Metric.mem_closedBall.mpr (hG_ball y))
    calc dist (F (G x)) (F (G y)) ≤ (L : ℝ) * dist (G x) (G y) := h2
      _ ≤ (L : ℝ) * (2 * dist x y) := mul_le_mul_of_nonneg_left (hG_lip x y) L.2
      _ = (2 * L : ℝ) * dist x y := by push_cast; ring
  have hΦbound : ∀ x, ‖Φ x‖ ≤ M := fun x =>
    hbound (G x) (Metric.mem_closedBall.mpr (hG_ball x))
  -- A global solution of the truncated field through `p`.
  obtain ⟨y, hy0, hy⟩ := exists_global_solution_of_lipschitz hΦ_lip p
  -- Mean value bound: `‖y t - p‖ ≤ M |t|`.
  have hderiv_le : ∀ t : ℝ, ‖deriv y t‖ ≤ M := fun t => by
    rw [(hy t).deriv]
    exact hΦbound (y t)
  have hbound_y : ∀ t : ℝ, ‖y t - p‖ ≤ M * |t| := by
    intro t
    rcases le_total 0 t with ht | ht
    · have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := y)
        (s := Set.Icc 0 t) (x := 0) (y := t) (C := M)
        (fun s _ => (hy s).differentiableAt) (fun s _ => hderiv_le s)
        (convex_Icc 0 t) (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht)
      simpa [hy0, Real.norm_eq_abs, abs_of_nonneg ht] using h
    · have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := y)
        (s := Set.Icc t 0) (x := t) (y := 0) (C := M)
        (fun s _ => (hy s).differentiableAt) (fun s _ => hderiv_le s)
        (convex_Icc t 0) (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht)
      have h' : ‖y t - y 0‖ ≤ M * ‖(0:ℝ) - t‖ := by rw [norm_sub_rev]; exact h
      rw [hy0] at h'
      simpa [Real.norm_eq_abs, abs_of_nonpos ht] using h'
  have hp_dist : ‖p - z₀‖ ≤ R / 2 := by
    rw [mem_closedBall, dist_eq_norm] at hp; exact hp
  -- The solution stays in the ball on the uniform window.
  have hy_ball : ∀ t ∈ Set.Ioo (-ρ) ρ, y t ∈ Metric.closedBall z₀ R := by
    intro t ht
    have habs : |t| < ρ := abs_lt.mpr ⟨ht.1, ht.2⟩
    have h1 : ‖y t - p‖ ≤ M * ρ :=
      le_trans (hbound_y t) (mul_le_mul_of_nonneg_left habs.le hM)
    have h2 : ‖y t - p‖ ≤ R / 2 := le_trans h1 hMρ
    have hdecomp : y t - z₀ = (y t - p) + (p - z₀) := by abel
    rw [Metric.mem_closedBall, dist_eq_norm]
    rw [hdecomp]
    calc ‖(y t - p) + (p - z₀)‖ ≤ ‖y t - p‖ + ‖p - z₀‖ := norm_add_le _ _
      _ ≤ R / 2 + R / 2 := by linarith
      _ = R := by ring
  refine ⟨y, hy0, ?_, hy_ball⟩
  intro t ht
  have hmem := hy_ball t ht
  have hfix : Φ (y t) = F (y t) := by
    simp only [Φ]
    rw [hG_fix (y t) (by rwa [Metric.mem_closedBall] at hmem)]
  exact (hy t).congr_deriv hfix

end Commons.Analysis.ODE
