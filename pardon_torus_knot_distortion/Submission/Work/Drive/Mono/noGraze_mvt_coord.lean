import Mathlib
import Submission.Work.Drive.Mono.NoGrazeDefs

namespace Work.Drive.Mono

/-!
# Mean value bound for one coordinate of the velocity

If the second derivative of a smooth knot is bounded in norm by `M`, then each
coordinate of the velocity is `M`-Lipschitz.  This is the mean value inequality
applied to the coordinate function `t ↦ (deriv K.curve t) (σ 2)`, whose
derivative is the corresponding coordinate of `deriv (deriv K.curve)`, together
with `|v i| ≤ ‖v‖` for the Euclidean norm on `ℝ³`.
-/

open LeanEval.KnotTheory.PardonDistortion in
theorem noGraze_mvt_coord {K : Knot} {M : ℝ}
    (hM : ∀ t : ℝ, ‖deriv (deriv K.curve) t‖ ≤ M) (σ : Equiv.Perm (Fin 3)) (t t' : ℝ) :
    |(deriv K.curve t) (σ 2) - (deriv K.curve t') (σ 2)| ≤ M * |t - t'| := by
  -- `deriv K.curve` is again `C^∞`, hence differentiable everywhere.
  have hVdiff : ∀ s : ℝ, DifferentiableAt ℝ (deriv K.curve) s := fun s => by
    have h : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (deriv K.curve) :=
      ContDiff.deriv' (n := (⊤ : ℕ∞)) K.smooth
    exact h.differentiable (by simp) |>.differentiableAt (x := s)
  -- the `(σ 2)`-coordinate as a continuous linear functional
  set L : R3 →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) (σ 2) with hL
  set G : ℝ → ℝ := fun s => (deriv K.curve s) (σ 2) with hG
  have hLapp : ∀ d : R3, L d = d (σ 2) := by
    intro d; rw [hL]; exact PiLp.proj_apply 2 (fun _ : Fin 3 => ℝ) (σ 2) d
  have hGfun : G = fun s => L (deriv K.curve s) := by
    funext s; rw [hG, hLapp]
  have hGdiff : ∀ s : ℝ, DifferentiableAt ℝ G s := fun s => by
    rw [hGfun]
    exact L.differentiableAt.comp s (hVdiff s)
  -- the derivative of `G` is the `(σ 2)`-coordinate of the second derivative
  have hGderiv : ∀ s : ℝ, deriv G s = (deriv (deriv K.curve) s) (σ 2) := fun s => by
    rw [hGfun]
    have hV : HasDerivAt (deriv K.curve) (deriv (deriv K.curve) s) s :=
      (hVdiff s).hasFDerivAt.hasDerivAt
    have h := (ContinuousLinearMap.hasFDerivAt L (x := deriv K.curve s)).comp_hasDerivAt s hV
    change deriv (L ∘ deriv K.curve) s = (deriv (deriv K.curve) s) (σ 2)
    rw [h.deriv, hLapp]
  have hbound : ∀ s : ℝ, ‖deriv G s‖ ≤ M := fun s => by
    rw [hGderiv s]
    calc ‖(deriv (deriv K.curve) s) (σ 2)‖ = |(deriv (deriv K.curve) s) (σ 2)| :=
          Real.norm_eq_abs _
      _ ≤ ‖deriv (deriv K.curve) s‖ := by
          simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (deriv (deriv K.curve) s) (σ 2)
      _ ≤ M := hM s
  have key := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
      (f := G) (s := Set.univ) (x := t) (y := t') (C := M)
      (fun x _ => hGdiff x) (fun x _ => hbound x) convex_univ (Set.mem_univ t) (Set.mem_univ t')
  simpa [hG, abs_sub_comm, norm_sub_rev, Real.norm_eq_abs] using key

end Work.Drive.Mono
