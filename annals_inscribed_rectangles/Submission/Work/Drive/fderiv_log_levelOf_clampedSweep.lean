import Mathlib
import Submission.Work.Drive.clampedSweep
import Submission.Work.Drive.clampedSweepChart

/-!
# The `x 2`-derivative of `log (levelOf (clampedSweep c ψ P ·))`

`Work.Drive.clampedSweep c ψ P` (Submission/Work/Drive/clampedSweep.lean) is the radial chain which at
`sweep x = 1` is the plane `P (x 0, x 1)` and at `x 2 = 0` is the shadow of that plane on the level
`c`.  Its radial coordinate is

> `levelOf (clampedSweep c ψ P x) = clampScale c ψ P x * levelOf (P (x 0, x 1))`,
> `clampScale c ψ P x = exp (ψ (x 2) * (log c - log (levelOf (P (x 0, x 1)))))`,

so that

> `log (levelOf (clampedSweep c ψ P x)) = ψ (x 2) * (log c - log (levelOf (P (x 0, x 1))))`
>   `+ log (levelOf (P (x 0, x 1)))`.

Hence its derivative in the sweep direction `EuclideanSpace.single 2 1` — which changes only `x 2` —
is `deriv ψ (x 2) * (log c - log (levelOf (P (x 0, x 1))))`: the projective/radial data of the plane
are *constant* along the sweep direction, so only the cutoff `ψ` contributes.  This is the analytic
input of the genericity computation of `CONCRETE_CHAINS_STATUS.md` §3.
-/

namespace Work.Drive

set_option maxHeartbeats 1600000 in
theorem fderiv_log_levelOf_clampedSweep
    (c : ℝ) (ψ : ℝ → ℝ) (P : EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hψ : ContDiff ℝ Work.Drive.Ctop ψ)
    (x : EuclideanSpace ℝ (Fin 3))
    (hlog : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) Work.Drive.Ctop
      (fun y : EuclideanSpace ℝ (Fin 2) => Real.log (Work.Drive.levelOf (P y)))
      (Work.Drive.mk2 (x 0) (x 1))) :
    fderiv ℝ (fun u : EuclideanSpace ℝ (Fin 3) =>
        Real.log (Work.Drive.levelOf (Work.Drive.clampedSweep c ψ P u))) x
        (EuclideanSpace.single 2 (1 : ℝ))
      = deriv ψ (x 2) * (Real.log c - Real.log (Work.Drive.levelOf (P (Work.Drive.mk2 (x 0) (x 1))))) := by
  set e : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 2 (1 : ℝ) with he_def
  set F : EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun u => Real.log (levelOf (clampedSweep c ψ P u)) with hF_def
  set G : EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun u => Real.log (levelOf (P (mk2 (u 0) (u 1)))) with hG_def
  -- the plane-coordinate map and the plane's logarithmic level are differentiable at `x`
  have hΦ : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin 3) => mk2 (u 0) (u 1)) x :=
    (contMDiffAt_iff_contDiffAt.mp (contMDiffAt_mk2_proj x)).differentiableAt (by simp)
  have hg : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 2) => Real.log (levelOf (P y)))
      (mk2 (x 0) (x 1)) :=
    (contMDiffAt_iff_contDiffAt.mp hlog).differentiableAt (by simp)
  have hG_diff : DifferentiableAt ℝ G x := by
    rw [hG_def]
    exact hg.comp x hΦ
  have hsnd : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin 3) => u 2) x := by
    simpa using (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 2).differentiableAt
  have hψd : DifferentiableAt ℝ ψ (x 2) := (hψ.differentiable (by simp)).differentiableAt
  -- the explicit shape of `log (levelOf (clampedSweep c ψ P ·))`
  have hF_eq : F = fun u => ψ (u 2) * (Real.log c - G u) + G u := by
    rw [hF_def, hG_def]
    funext u
    rw [levelOf_clampedSweep]
    simp only [clampScale]
    rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt (levelOf_pos (P (mk2 (u 0) (u 1))))),
      Real.log_exp]
  have hFdiff' : DifferentiableAt ℝ
      (fun u : EuclideanSpace ℝ (Fin 3) => ψ (u 2) * (Real.log c - G u) + G u) x :=
    ((hψd.comp x hsnd).mul ((differentiableAt_const (Real.log c)).sub hG_diff)).add hG_diff
  have hFdiff : DifferentiableAt ℝ F x := by
    rw [hF_eq]; exact hFdiff'
  -- the directional derivative is the derivative along the curve `t ↦ x + t • e`
  have hlin : HasDerivAt (fun t : ℝ => x + t • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
  have hcomp := (by simpa using hFdiff.hasFDerivAt :
      HasFDerivAt F (fderiv ℝ F x) ((fun t : ℝ => x + t • e) 0)).comp_hasDerivAt (0 : ℝ) hlin
  have h0 : ∀ t : ℝ, (x + t • e) 0 = x 0 := fun t => by simp [he_def]
  have h1 : ∀ t : ℝ, (x + t • e) 1 = x 1 := fun t => by simp [he_def]
  have h2 : ∀ t : ℝ, (x + t • e) 2 = x 2 + t := fun t => by simp [he_def]
  -- along that curve the plane data are constant, so only `ψ` moves
  have hcurve : (fun t : ℝ => F (x + t • e)) =
      fun t => ψ (x 2 + t) * (Real.log c - Real.log (levelOf (P (mk2 (x 0) (x 1)))))
        + Real.log (levelOf (P (mk2 (x 0) (x 1)))) := by
    funext t
    rw [hF_eq]
    simp only [hG_def, h0 t, h1 t, h2 t]
  rw [← hcomp.deriv]
  change deriv (fun t : ℝ => F (x + t • e)) 0 = _
  rw [hcurve]
  have hd : HasDerivAt (fun t : ℝ => ψ (x 2 + t) * (Real.log c - Real.log (levelOf (P (mk2 (x 0) (x 1)))))
      + Real.log (levelOf (P (mk2 (x 0) (x 1)))))
      (deriv ψ (x 2) * (Real.log c - Real.log (levelOf (P (mk2 (x 0) (x 1)))))) 0 := by
    have hψ_at : HasDerivAt ψ (deriv ψ (x 2)) (x 2) := hψd.hasDerivAt
    have h1' : HasDerivAt (fun t : ℝ => x 2 + t) 1 0 := (hasDerivAt_id (0 : ℝ)).const_add (x 2)
    have h2' : HasDerivAt ψ (deriv ψ (x 2)) ((fun t : ℝ => x 2 + t) 0) := by simpa using hψ_at
    have h3 := h2'.comp (0 : ℝ) h1'
    have h4 := h3.mul_const (Real.log c - Real.log (levelOf (P (mk2 (x 0) (x 1)))))
    have h5 := h4.add_const (Real.log (levelOf (P (mk2 (x 0) (x 1)))))
    simpa [mul_one] using h5
  rw [hd.deriv]

end Work.Drive
