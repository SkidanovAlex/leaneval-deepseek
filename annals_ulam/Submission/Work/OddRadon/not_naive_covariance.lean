import Mathlib
import Submission.Work.OddRadon.Core
import Submission.Work.OddRadon.Reduction
import Submission.Work.OddRadon.sphereArea_one

/-!
# The *naive* covariance form of the spherical Radon transform is false

`sphericalRadon` satisfies the covariance law
`𝓡 (g ∘ L) ξ = 𝓡 g (L ξ)` for every linear isometry equivalence `L`
(`Work.OddRadon.sphericalRadon_comp_isometry`).  The *naive* form
`𝓡 (g ∘ L) (L ξ) = 𝓡 g ξ` — with `L` applied to the evaluation point instead of to the point
at which `𝓡 g` is evaluated — is **false**, and that is what this file records: it is the
reason the paper's Step 3 has to keep track of the direction at which the transform is
evaluated.

Concretely, take `L` to be the cyclic permutation of the coordinates of `ℝ⁴`,
`LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finRotate 4)`, so that `L (L (e0 4)) = e₂`, and
`g w = (w 0) ^ 2`.  By the one-variable reduction `sphericalRadon_rotationInvariant`,

* `𝓡 g (e0 4) = radonProfile 4 (· ^ 2) 0 = 0` (the equator of `e0` lies in `w 0 = 0`),
* `𝓡 g (e₂)   = radonProfile 4 (· ^ 2) 1 = (2π)·(2/3) ≠ 0`.

Hence `𝓡 (g ∘ L) (L (e0 4)) = 𝓡 g (L (L (e0 4))) = 𝓡 g (e₂) ≠ 𝓡 g (e0 4)`.
-/

noncomputable section

open scoped RealInnerProductSpace Pointwise Interval Topology

namespace Work.OddRadon

theorem not_naive_covariance :
    ∃ (L : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
      (g : EuclideanSpace ℝ (Fin 4) → ℝ),
      sphericalRadon 4 (fun x => g (L x)) (L (e0 4)) ≠ sphericalRadon 4 g (e0 4) := by
  -- The radial profile `γ t = t ^ 2`, kept opaque so that `g = fun w => γ (w 0)` matches the
  -- reduction `sphericalRadon_rotationInvariant` syntactically.
  set γ : ℝ → ℝ := fun t : ℝ => t ^ 2 with hγdef
  -- The cyclic permutation of the four coordinates of `ℝ⁴`.
  set L : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finRotate 4) with hLdef
  set g : EuclideanSpace ℝ (Fin 4) → ℝ :=
    (fun w : EuclideanSpace ℝ (Fin 4) => γ (w 0)) with hgdef
  refine ⟨L, g, ?_⟩
  have hγcont : Continuous γ := by rw [hγdef]; exact continuous_id.pow 2
  -- `L` sends `e₀ ↦ e₁ ↦ e₂`, in particular `L (L (e0 4)) = e₂ = single 2 1`.
  have hL2 : L (L (e0 4)) = EuclideanSpace.single (2 : Fin 4) (1 : ℝ) := by
    rw [hLdef]; rw [e0]; simp
  -- `𝓡 g e₂ = radonProfile 4 (· ^ 2) 1 = (2π) * (2/3)`.
  have hred1 : sphericalRadon 4 g (EuclideanSpace.single (2 : Fin 4) (1 : ℝ))
      = 2 * Real.pi * (2 / 3) := by
    rw [hgdef]
    rw [sphericalRadon_rotationInvariant 4 (by norm_num) hγcont (by simp)]
    simp
    rw [hγdef, radonProfile, sphereArea_one]
    norm_num
  -- `𝓡 g e₀ = radonProfile 4 (· ^ 2) 0 = 0`.
  have hred0 : sphericalRadon 4 g (e0 4) = 0 := by
    rw [hgdef]
    rw [sphericalRadon_rotationInvariant 4 (by norm_num) hγcont (e0_norm 4)]
    simp [e0, hγdef, radonProfile]
  -- Covariance moves `L` onto the evaluation point, producing `L (L (e0 4)) = e₂`.
  rw [sphericalRadon_comp_isometry 4 L g (L (e0 4)), hL2, hred1, hred0]
  intro h
  have hp : (0 : ℝ) < 2 * Real.pi * (2 / 3) := by positivity
  linarith

end Work.OddRadon
