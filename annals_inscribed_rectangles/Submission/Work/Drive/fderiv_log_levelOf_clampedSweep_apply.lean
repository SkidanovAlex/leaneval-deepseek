import Mathlib
import Submission.Work.Drive.clampedSweep
import Submission.Work.Drive.clampedSweepChart
import Submission.Work.Drive.fderiv_log_levelOf_clampedSweep
import Submission.Work.Drive.fderiv_const_along

/-!
# The full derivative of `log (levelOf (clampedSweep c ψ P ·))` in an arbitrary direction

`Work.Drive.clampedSweep c ψ P` (`Submission/Work/Drive/clampedSweep.lean`) is the radial chain whose
`x 2 = 1` face is the plane `P` and whose `x 2 = 0` face is the shadow of that plane on the level `c`.
`Work.Drive.log_levelOf_clampedSweep` computes its radial coordinate explicitly:

> `log (levelOf (clampedSweep c ψ P x))
>   = ψ (x 2) * (log c - log (levelOf (P (x 0, x 1)))) + log (levelOf (P (x 0, x 1)))`.

Reading the last term as `(1 - ψ (x 2)) * log (levelOf (P (x 0, x 1)))` plus `ψ (x 2) * log c`, the
function is a sum of

* a purely vertical piece, which depends on the sweep parameter `x 2` only through the cutoff `ψ`, and
* a purely planar piece, `(1 - ψ (x 2))` times the plane's own logarithmic radial coordinate,

so its derivative at `x` in a direction `w` splits accordingly:

> `d (log (levelOf (clampedSweep c ψ P ·))) x w`
>   `= deriv ψ (x 2) * (w 2) * (log c - log (levelOf (P (x 0, x 1))))`
>     `+ (1 - ψ (x 2)) * (d (log (levelOf (P ·))) (x 0, x 1) (w 0, w 1))`.

This is the general-direction form of `Work.Drive.fderiv_log_levelOf_clampedSweep` (which is the case
of the sweep direction `EuclideanSpace.single 2 1`, where the planar part drops out), and it is the
input of the genericity computation of `CONCRETE_CHAINS_STATUS.md` §3 in a direction with a planar
component.
-/

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold

noncomputable section

/-- **The derivative of a real-valued function in a direction is the derivative along the line.**  The
chain rule along `t ↦ x + t • w`, which is the elementary identity underlying the direct computation of
`fderiv` of the clamped sweep. -/
lemma fderiv_apply_eq_deriv_line
    {n : ℕ} {F : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hF : DifferentiableAt ℝ F x) (w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ F x w = deriv (fun t : ℝ => F (x + t • w)) 0 := by
  have hlin : HasDerivAt (fun t : ℝ => x + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x
  have h := (by simpa using hF.hasFDerivAt :
    HasFDerivAt F (fderiv ℝ F x) ((fun t : ℝ => x + t • w) 0)).comp_hasDerivAt (0 : ℝ) hlin
  exact h.deriv.symm

set_option maxHeartbeats 1600000 in
theorem fderiv_log_levelOf_clampedSweep_apply
    (c : ℝ) (ψ : ℝ → ℝ) (P : EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hψ : ContDiff ℝ Work.Drive.Ctop ψ)
    (x w : EuclideanSpace ℝ (Fin 3))
    (hlog : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) Work.Drive.Ctop
      (fun y : EuclideanSpace ℝ (Fin 2) => Real.log (Work.Drive.levelOf (P y)))
      (Work.Drive.mk2 (x 0) (x 1))) :
    fderiv ℝ (fun u : EuclideanSpace ℝ (Fin 3) =>
        Real.log (Work.Drive.levelOf (Work.Drive.clampedSweep c ψ P u))) x w
      = deriv ψ (x 2) * (w 2) * (Real.log c
          - Real.log (Work.Drive.levelOf (P (Work.Drive.mk2 (x 0) (x 1)))))
        + (1 - ψ (x 2)) * (fderiv ℝ
            (fun y : EuclideanSpace ℝ (Fin 2) => Real.log (Work.Drive.levelOf (P y)))
            (Work.Drive.mk2 (x 0) (x 1)) (Work.Drive.mk2 (w 0) (w 1))) := by
  set F : EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun u => Real.log (Work.Drive.levelOf (Work.Drive.clampedSweep c ψ P u)) with hF_def
  -- differentiability of the pieces
  have hΦ : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin 3) => Work.Drive.mk2 (u 0) (u 1)) x :=
    (contMDiffAt_iff_contDiffAt.mp (Work.Drive.contMDiffAt_mk2_proj x)).differentiableAt (by simp)
  have hg : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 2) => Real.log (Work.Drive.levelOf (P y)))
      (Work.Drive.mk2 (x 0) (x 1)) :=
    (contMDiffAt_iff_contDiffAt.mp hlog).differentiableAt (by simp)
  have hGdiff : DifferentiableAt ℝ
      (fun u : EuclideanSpace ℝ (Fin 3) => Real.log (Work.Drive.levelOf (P (Work.Drive.mk2 (u 0) (u 1))))) x := by
    show DifferentiableAt ℝ ((fun y : EuclideanSpace ℝ (Fin 2) => Real.log (Work.Drive.levelOf (P y))) ∘
      (fun u : EuclideanSpace ℝ (Fin 3) => Work.Drive.mk2 (u 0) (u 1))) x
    exact hg.comp x hΦ
  have hsnd : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin 3) => u 2) x := by
    simpa using (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 2).differentiableAt
  have hψd : DifferentiableAt ℝ ψ (x 2) := (hψ.differentiable (by simp)).differentiableAt
  have hψsnd : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin 3) => ψ (u 2)) x := by
    show DifferentiableAt ℝ (ψ ∘ (fun u : EuclideanSpace ℝ (Fin 3) => u 2)) x
    exact hψd.comp x hsnd
  -- the explicit shape of `F`
  have hF_eq : F = fun u : EuclideanSpace ℝ (Fin 3) =>
      ψ (u 2) * (Real.log c - Real.log (Work.Drive.levelOf (P (Work.Drive.mk2 (u 0) (u 1)))))
        + Real.log (Work.Drive.levelOf (P (Work.Drive.mk2 (u 0) (u 1)))) := by
    funext u
    rw [hF_def]
    exact Work.Drive.log_levelOf_clampedSweep c ψ P u
  have hFdiff : DifferentiableAt ℝ F x := by
    rw [hF_eq]
    exact (hψsnd.mul ((differentiableAt_const (Real.log c)).sub hGdiff)).add hGdiff
  -- the same shape along the line `t ↦ x + t • w`
  have hcurve : (fun t : ℝ => F (x + t • w)) = fun t : ℝ =>
      ψ (x 2 + t * w 2) * (Real.log c - Real.log (Work.Drive.levelOf (P (Work.Drive.mk2 (x 0 + t * w 0) (x 1 + t * w 1)))))
        + Real.log (Work.Drive.levelOf (P (Work.Drive.mk2 (x 0 + t * w 0) (x 1 + t * w 1)))) := by
    funext t
    rw [hF_eq]
    simp
  -- the two scalar derivatives along the line
  have hcψ : HasDerivAt (fun t : ℝ => ψ (x 2 + t * w 2)) (deriv ψ (x 2) * w 2) 0 := by
    have hpathψ : HasDerivAt (fun t : ℝ => x 2 + t * w 2) (w 2) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).mul_const (w 2)).const_add (x 2)
    exact (by simpa using hψd.hasDerivAt : HasDerivAt ψ (deriv ψ (x 2))
      ((fun t : ℝ => x 2 + t * w 2) 0)).comp (0:ℝ) hpathψ
  have hcg : HasDerivAt (fun t : ℝ => Real.log (Work.Drive.levelOf (P (Work.Drive.mk2 (x 0 + t * w 0) (x 1 + t * w 1)))))
      (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => Real.log (Work.Drive.levelOf (P y)))
        (Work.Drive.mk2 (x 0) (x 1)) (Work.Drive.mk2 (w 0) (w 1))) 0 := by
    have hmk : ∀ t : ℝ, Work.Drive.mk2 (x 0 + t * w 0) (x 1 + t * w 1)
        = Work.Drive.mk2 (x 0) (x 1) + t • Work.Drive.mk2 (w 0) (w 1) := by
      intro t; ext i; fin_cases i <;> simp [Work.Drive.mk2]
    have hmkpath : HasDerivAt (fun t : ℝ => Work.Drive.mk2 (x 0 + t * w 0) (x 1 + t * w 1))
        (Work.Drive.mk2 (w 0) (w 1)) 0 := by
      rw [show (fun t : ℝ => Work.Drive.mk2 (x 0 + t * w 0) (x 1 + t * w 1))
          = fun t : ℝ => Work.Drive.mk2 (x 0) (x 1) + t • Work.Drive.mk2 (w 0) (w 1) from funext hmk]
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const (Work.Drive.mk2 (w 0) (w 1))).const_add (Work.Drive.mk2 (x 0) (x 1))
    exact (by simpa using hg.hasFDerivAt :
      HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 2) => Real.log (Work.Drive.levelOf (P y)))
        (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => Real.log (Work.Drive.levelOf (P y)))
          (Work.Drive.mk2 (x 0) (x 1)))
        ((fun t : ℝ => Work.Drive.mk2 (x 0 + t * w 0) (x 1 + t * w 1)) 0)).comp_hasDerivAt (0:ℝ) hmkpath
  -- assemble
  rw [fderiv_apply_eq_deriv_line hFdiff w, hcurve]
  have h1 := (hcψ.mul ((hasDerivAt_const (0:ℝ) (Real.log c)).sub hcg)).add hcg
  have hl : HasDerivAt (fun t : ℝ =>
      ψ (x 2 + t * w 2) * (Real.log c - Real.log (Work.Drive.levelOf (P (Work.Drive.mk2 (x 0 + t * w 0) (x 1 + t * w 1)))))
        + Real.log (Work.Drive.levelOf (P (Work.Drive.mk2 (x 0 + t * w 0) (x 1 + t * w 1))))) _ 0 := h1
  rw [hl.deriv]
  simp
  ring

end

end Work.Drive
