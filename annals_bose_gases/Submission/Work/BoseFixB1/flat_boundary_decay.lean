import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Submission.Work.BoseFixB1.fderiv_eq_zero_exterior
import Submission.Work.BoseFixB1.flat_profile_mvt
import Submission.Work.BoseFixB1.sphere_segment_geometry
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.flat_boundary_decay` — flatness of a `C^k` function at the boundary of a ball

If `f : ℝ³ → F` is `C^k` and vanishes on the closed exterior of the ball of radius `2`, then
`‖f x‖ ≤ C (2 - ‖x‖)^k` for `‖x‖ ≤ 2`, with `C` independent of `x`.

The proof is an induction on `k`:

* `k = 0`: `f` is continuous and the closed ball of radius `2` is compact.
* `k → k+1`: put `g := fderiv ℝ f`.  Then `ContDiff ℝ k g` (`ContDiff.fderiv_right`) and `g`
  vanishes on the closed exterior (`Work.BoseFixB1.fderiv_eq_zero_exterior`); the induction
  hypothesis applied to `g` gives `‖g z‖ ≤ C (2 - ‖z‖)^k` on the ball.  For `x` with
  `‖x‖ ≤ 2` we pick (via `Work.BoseFixB1.sphere_segment_geometry`) a point `y` on the sphere
  of radius `2` with `‖y - x‖ = 2 - ‖x‖` and such that the segment `[x,y]` lies in the ball
  with `‖w‖ ≥ ‖x‖` for all of its points `w`.  The mean value bound
  (`Work.BoseFixB1.flat_profile_mvt`) then gives
  `‖f x‖ = ‖f y - f x‖ ≤ C (2 - ‖x‖)^k ‖y - x‖ = C (2 - ‖x‖)^{k+1}`, because `f y = 0`.
-/

namespace Work.BoseFixB1

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The induction statement, stated with the value space universally quantified so that the
induction hypothesis may be applied to `fderiv ℝ f` (whose value space is `ℝ³ →L[ℝ] F`). -/
private theorem flat_boundary_decay_aux (k : ℕ) :
    ∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ³ → F),
      ContDiff ℝ k f → (∀ x, 2 ≤ ‖x‖ → f x = 0) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ³, ‖x‖ ≤ 2 → ‖f x‖ ≤ C * (2 - ‖x‖) ^ k := by
  induction k with
  | zero =>
    intro F _inst _inst' f hf hzero
    have hcont : Continuous f := contDiff_zero.mp hf
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℝ³) 2).exists_bound_of_continuousOn
      hcont.continuousOn
    refine ⟨C, le_trans (norm_nonneg _) (hC 0 (by simp)), fun x hx => ?_⟩
    simpa using hC x (mem_closedBall_zero_iff.mpr hx)
  | succ k ih =>
    intro F _inst _inst' f hf hzero
    have hg : ContDiff ℝ k (fderiv ℝ f) := hf.fderiv_right (by norm_num)
    have hz : ∀ x, 2 ≤ ‖x‖ → fderiv ℝ f x = 0 :=
      fderiv_eq_zero_exterior f (hf.of_le (by norm_num)) hzero
    obtain ⟨C, hC0, hIH⟩ := ih (fderiv ℝ f) hg hz
    refine ⟨C, hC0, fun x hx => ?_⟩
    have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
    obtain ⟨y, hy2, hyx, hseg⟩ := sphere_segment_geometry x hx
    have hfy : f y = 0 := hzero y hy2.ge
    have hkey := flat_profile_mvt k hdiff hC0 hx hIH hseg
    rw [hfy, zero_sub, norm_neg, hyx] at hkey
    calc ‖f x‖ ≤ C * (2 - ‖x‖) ^ k * (2 - ‖x‖) := hkey
      _ = C * (2 - ‖x‖) ^ (k + 1) := by ring

/-- **Flatness at the boundary of a ball.**  If `f : ℝ³ → F` is `C^k` and vanishes on the
closed exterior of the ball of radius `2`, then `‖f x‖ ≤ C (2 - ‖x‖)^k` for `‖x‖ ≤ 2`, with `C`
independent of `x`.

Suggested route (a self-contained induction on `k`, no Taylor machinery needed):
* `k = 0`: `f` is continuous and the closed ball of radius `2` is compact, so `‖f‖` is bounded
  there (`IsCompact.exists_bound_of_continuousOn`).
* `k → k+1`: let `g := fderiv ℝ f`.  Then `ContDiff ℝ k g` (`ContDiff.fderiv_right`), and `g`
  vanishes on the closed exterior: for `2 < ‖x‖` this is `EventuallyEq.fderiv_eq` (f is locally
  `0` there); at `‖x‖ = 2` use that `g` is continuous (`ContDiff.continuous_fderiv`) and `0` on
  the open exterior, hence `0` on its closure.  Apply the induction hypothesis to `g` to get
  `C_k`; then for `x` with `‖x‖ ≤ 2` use the mean value theorem
  (`Convex.norm_image_sub_le_of_norm_fderiv_le`) on the segment from `x` to `y := 2 • u`
  (`u := ‖x‖⁻¹ • x` a unit vector, or any unit vector when `x = 0`), where `f y = 0` and
  `‖y - x‖ = 2 - ‖x‖`; on that segment `‖w‖ ≥ ‖x‖` so `(2 - ‖w‖)^k ≤ (2 - ‖x‖)^k`.
  The same constant `C_k` works for `k+1`. -/
theorem flat_boundary_decay {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) (f : EuclideanSpace ℝ (Fin 3) → F)
    (hf : ContDiff ℝ k f) (hzero : ∀ x, 2 ≤ ‖x‖ → f x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 2 → ‖f x‖ ≤ C * (2 - ‖x‖) ^ k :=
  flat_boundary_decay_aux k f hf hzero

end Work.BoseFixB1
