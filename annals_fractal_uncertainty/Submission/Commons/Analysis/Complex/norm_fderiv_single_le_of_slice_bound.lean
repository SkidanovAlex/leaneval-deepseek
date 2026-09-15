import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Liouville

namespace Commons.Analysis.Complex

theorem norm_fderiv_single_le_of_slice_bound {d : ℕ} {g : (Fin d → ℂ) → ℂ}
    {z : Fin d → ℂ} {r C : ℝ} (hr : 0 < r) (j : Fin d)
    (hgd : DifferentiableAt ℂ g z)
    (hslice : DifferentiableOn ℂ (fun w : ℂ => g (z + w • Pi.single j (1 : ℂ))) (Metric.ball 0 r))
    (hcont : ContinuousOn (fun w : ℂ => g (z + w • Pi.single j (1 : ℂ))) (Metric.closedBall 0 r))
    (hC : ∀ w : ℂ, ‖w‖ = r → ‖g (z + w • Pi.single j (1 : ℂ))‖ ≤ C) :
    ‖(fderiv ℂ g z) (Pi.single j (1 : ℂ))‖ ≤ C / r := by
  set f : ℂ → ℂ := fun w => g (z + w • Pi.single j (1 : ℂ)) with hf_def
  -- directional derivative of `g` at `z` along `Pi.single j 1` is the derivative at `0`
  -- of the one-variable slice `f`.
  have hφ : HasDerivAt (fun w : ℂ => z + w • Pi.single j (1 : ℂ)) (Pi.single j (1 : ℂ)) 0 := by
    have h1 : HasDerivAt (fun w : ℂ => w • (Pi.single j (1:ℂ) : Fin d → ℂ)) (Pi.single j (1:ℂ)) 0 := by
      simpa using (hasDerivAt_id (0:ℂ)).smul_const (Pi.single j (1:ℂ) : Fin d → ℂ)
    simpa using h1.const_add z
  have hgz : HasFDerivAt g (fderiv ℂ g z) ((fun w : ℂ => z + w • Pi.single j (1:ℂ)) 0) := by
    have : (fun w : ℂ => z + w • Pi.single j (1:ℂ)) 0 = z := by simp
    rw [this]; exact hgd.hasFDerivAt
  have hcomp := hgz.comp_hasDerivAt (0:ℂ) hφ
  have hfd : HasDerivAt f ((fderiv ℂ g z) (Pi.single j (1:ℂ))) 0 := by
    rw [hf_def]
    simpa only [Function.comp_def] using hcomp
  have hderiv : deriv f 0 = (fderiv ℂ g z) (Pi.single j (1:ℂ)) := hfd.deriv
  rw [← hderiv]
  -- Cauchy's estimate for the first derivative of the slice `f` on the disc of radius `r`.
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
  · rw [hf_def]
    exact DiffContOnCl.mk_ball hslice hcont
  · intro w hw
    rw [hf_def]
    apply hC w
    simpa [mem_sphere_iff_norm] using hw

end Commons.Analysis.Complex