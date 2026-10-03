import Mathlib

namespace Work.Motion

/-- Auxiliary: the affine map `u ↦ c + R * u` has derivative `R` at every point. -/
theorem hasDerivAt_affine (c : ℂ) (R : ℝ) (w : ℂ) :
    HasDerivAt (fun u : ℂ => c + (R : ℂ) * u) (R : ℂ) w := by
  simpa using ((hasDerivAt_id w).const_mul (R : ℂ)).const_add c

/-- Chain rule for `u ↦ f (c + R * u)`:
the derivative at `w` is `deriv f (c + R * w) * R`. -/
theorem deriv_affine_comp {f : ℂ → ℂ} {c : ℂ} {R : ℝ} {w : ℂ}
    (hd : DifferentiableAt ℂ f (c + (R : ℂ) * w)) :
    deriv (fun u : ℂ => f (c + (R : ℂ) * u)) w
      = deriv f (c + (R : ℂ) * w) * (R : ℂ) := by
  have hcomp : HasDerivAt (fun u : ℂ => f (c + (R : ℂ) * u))
      (deriv f (c + (R : ℂ) * w) * (R : ℂ)) w :=
    hd.hasDerivAt.comp w (hasDerivAt_affine c R w)
  exact hcomp.deriv

/-- Rescaling/precomposing by the affine change of variable `u ↦ c + R * u` and
normalising by a factor `M` scales the derivative by `R / M`. -/
theorem deriv_rescale {f : ℂ → ℂ} {c : ℂ} {R M : ℝ} {w : ℂ}
    (hd : DifferentiableAt ℂ f (c + (R : ℂ) * w)) :
    deriv (fun u => (f (c + (R : ℂ) * u) - c) / (M : ℂ)) w
      = (R : ℂ) / (M : ℂ) * deriv f (c + (R : ℂ) * w) := by
  have hcomp : HasDerivAt (fun u : ℂ => f (c + (R : ℂ) * u))
      (deriv f (c + (R : ℂ) * w) * (R : ℂ)) w :=
    hd.hasDerivAt.comp w (hasDerivAt_affine c R w)
  have h2 : HasDerivAt (fun u : ℂ => (f (c + (R : ℂ) * u) - c) / (M : ℂ))
      ((deriv f (c + (R : ℂ) * w) * (R : ℂ)) / (M : ℂ)) w :=
    (hcomp.sub_const c).div_const (M : ℂ)
  rw [h2.deriv]
  ring

end Work.Motion
