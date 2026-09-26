import ChallengeDeps
import Submission.Basic
import Submission.Work.Core.Torus

/-!
# Extracting the geometric data from the hypothesis of the challenge

The hypothesis of `pardon_torus_knot_distortion` says that some ambient isotopy
`Φ`, at time `1`, carries the curve of `K` onto the standard `(p,q)`-torus curve,
up to an orientation-preserving reparametrisation `σ` of the circle.

Since an ambient isotopy is a smooth path of diffeomorphisms of `ℝ³`, the map
`ψ := Φ.Hinv 1` is a diffeomorphism of `ℝ³` isotopic to the identity, and the
hypothesis says exactly that

  `K.curve t = ψ (standardTorusCurve p q (σ.f t))`.

Thus the image of `K` is the image of the standard torus curve under a
diffeomorphism of `ℝ³`, i.e. it lies on the embedded torus `ψ(T)` where `T` is
the standard torus of revolution, and its class in that torus is the `(p,q)`
class.  These are the data used by the geometric/topological argument.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Submission

/-- Swapping the two maps of an ambient isotopy yields again an ambient isotopy:
the inverse family of an ambient isotopy is itself an ambient isotopy starting at
the identity. -/
noncomputable def swapIsotopy (Φ : AmbientIsotopy) : AmbientIsotopy where
  H := Φ.Hinv
  Hinv := Φ.H
  smooth := Φ.smooth_inv
  smooth_inv := Φ.smooth
  inv_left := Φ.inv_right
  inv_right := Φ.inv_left
  start := by
    funext x
    have h := Φ.inv_left 0 x
    rw [Φ.start] at h
    simpa using h

/-- **Extraction of the parametrisation.**  Under the hypothesis of the challenge,
the curve of `K` is obtained from the standard torus curve by applying the
diffeomorphism `ψ = Φ.Hinv 1` and the reparametrisation `σ`. -/
theorem curve_eq_inv_comp {p q : ℕ} (Φ : AmbientIsotopy) (σ : CircleReparam)
    (K : Knot) (h : ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)) :
    ∀ t, K.curve t = Φ.Hinv 1 (standardTorusCurve p q (σ.f t)) := by
  intro t
  rw [← h t]
  exact (Φ.inv_left 1 (K.curve t)).symm

set_option maxHeartbeats 1000000 in
/-- The image of `K` is contained in the embedded torus `ψ(T)` obtained by
applying the diffeomorphism `ψ = Φ.Hinv 1` to the standard torus of revolution
`T = range torusMap`. -/
theorem image_subset_torus {p q : ℕ} (Φ : AmbientIsotopy) (σ : CircleReparam)
    (K : Knot) (h : ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)) :
    Set.range K.curve ⊆
      (Φ.Hinv 1) '' Work.Core.standardTorus := by
  rintro x ⟨t, rfl⟩
  refine ⟨Work.Core.torusMap ((p : ℝ) * σ.f t) ((q : ℝ) * σ.f t), ?_, ?_⟩
  · exact ⟨((p : ℝ) * σ.f t, (q : ℝ) * σ.f t), rfl⟩
  show Φ.Hinv 1 (Work.Core.torusMap ((p : ℝ) * σ.f t) ((q : ℝ) * σ.f t)) = K.curve t
  rw [← Work.Core.standardTorusCurve_eq_torusMap]
  exact (curve_eq_inv_comp Φ σ K h t).symm

/-- The parametrisation of `K` factors through the standard torus curve with the
explicit `(p,q)` parameter, transported by `ψ`: the lift of the curve of `K` to
the parameter torus is `t ↦ (p * σ.f t, q * σ.f t)`. -/
theorem lift_comp {p q : ℕ} (Φ : AmbientIsotopy) (σ : CircleReparam)
    (K : Knot) (h : ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)) :
    ∀ t, K.curve t =
      Φ.Hinv 1 (Work.Core.torusMap ((p : ℝ) * σ.f t) ((q : ℝ) * σ.f t)) := by
  intro t
  rw [← Work.Core.standardTorusCurve_eq_torusMap]
  exact curve_eq_inv_comp Φ σ K h t

end Submission
