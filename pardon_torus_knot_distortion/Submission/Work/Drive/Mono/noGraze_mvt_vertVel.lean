import Mathlib
import Submission.Work.Drive.Mono.NoBend

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion in
open scoped RealInnerProductSpace in
/-- The mean value bound for the orthogonal (vertical) velocity: the map `t ↦ vertVel K e t` is
`M`-Lipschitz on `ℝ`, where `M` bounds the norm of the acceleration `deriv (deriv K.curve)`.

Indeed `vertVel K e = perpProjCLM e ∘ deriv K.curve`, so its derivative is
`vertAcc K e t = perpProj e (deriv (deriv K.curve) t)`, whose norm is at most
`‖deriv (deriv K.curve) t‖ ≤ M` because `perpProj e` is a norm-non-increasing projection
(`norm_perpProj_le`, using `‖e‖ = 1`).  The mean value theorem for vector-valued functions
(`Convex.norm_image_sub_le_of_norm_deriv_le`) then gives the claim. -/
theorem noGraze_mvt_vertVel {K : Knot} {e : R3} (he : ‖e‖ = 1) {M : ℝ}
    (hM : ∀ t : ℝ, ‖deriv (deriv K.curve) t‖ ≤ M) (t t' : ℝ) :
    ‖Work.Drive.Mono.vertVel K e t - Work.Drive.Mono.vertVel K e t'‖ ≤ M * |t - t'| := by
  have hdiff : ∀ x : ℝ, DifferentiableAt ℝ (Work.Drive.Mono.vertVel K e) x :=
    fun x => (Work.Drive.Mono.contDiff_vertVel K e).differentiable (by simp) x
  have hbound : ∀ x : ℝ, ‖deriv (Work.Drive.Mono.vertVel K e) x‖ ≤ M := by
    intro x
    rw [Work.Drive.Mono.deriv_vertVel]
    calc ‖Work.Drive.Mono.vertAcc K e x‖
        = ‖Work.Drive.Mono.perpProj e (deriv (deriv K.curve) x)‖ := rfl
      _ ≤ ‖deriv (deriv K.curve) x‖ := Work.Drive.Mono.norm_perpProj_le he
      _ ≤ M := hM x
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := Work.Drive.Mono.vertVel K e)
      (s := Set.univ) (fun x _ => hdiff x) (fun x _ => hbound x) convex_univ
      (Set.mem_univ t') (Set.mem_univ t)
  rw [Real.norm_eq_abs] at h
  simpa [norm_sub_rev] using h

end Work.Drive.Mono
