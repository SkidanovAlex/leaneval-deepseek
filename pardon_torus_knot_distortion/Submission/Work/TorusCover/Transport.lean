import Submission.Work.TorusCover.Basic
import Submission.Work.TorusCover.Standard
import Submission.Work.TorusCover.hasWinding_comp_circleReparam

/-!
# Transporting the winding vector

The winding vector of a closed curve depends only on the curve and on the parametrisation, and
it is transported through a *change of the ambient map* and through an orientation-preserving
reparametrisation of the circle:

* `Work.TorusCover.hasWinding_comp_left`: if `γ` has winding vector `v` for the parametrisation
  `psi`, then the curve `t ↦ Ψ (γ t)` has the same winding vector `v` for the parametrisation
  `(x, y) ↦ Ψ (psi x y)` (the same lift `Λ` witnesses both statements).  This is the change of
  parametrisation along an ambient diffeomorphism, as in
  `psi = Φ.Hinv 1 ∘ torusMap`;
* `Work.TorusCover.hasWinding_comp_circleReparam`: precomposing with an orientation-preserving
  reparametrisation `σ : CircleReparam` does not change the winding vector, since `σ.f` advances
  by `2π` over one period;
* `Work.TorusCover.hasWinding_comp_standardTorusCurve`: the combination of the two, in the shape
  needed for Pardon's theorem: the curve `t ↦ Ψ (standardTorusCurve p q (σ.f t))` has winding
  vector `(p, q)` for the parametrisation `(x, y) ↦ Ψ (torusMap x y)`.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.TorusCover

noncomputable section

/-- **Change of the ambient map.**  If `Λ` is a periodic lift of `γ` through `psi`, then `Λ` is
also a periodic lift of `t ↦ Ψ (γ t)` through `(x, y) ↦ Ψ (psi x y)`, with the same winding
vector. -/
theorem hasWinding_comp_left {psi : ℝ → ℝ → R3} {γ : ℝ → R3} {v : ℤ × ℤ} {Ψ : R3 → R3}
    (h : HasWinding psi γ v) : HasWinding (fun x y => Ψ (psi x y)) (fun t => Ψ (γ t)) v := by
  obtain ⟨Λ, hL, hshift⟩ := h
  exact ⟨Λ, ⟨hL.1, fun t => by simpa using congrArg Ψ (hL.2 t)⟩, hshift⟩

/-- **The winding vector of the ambient image of the standard `(p,q)` curve.**  For any
`Ψ : R3 → R3` and any orientation-preserving reparametrisation `σ` of the circle, the curve
`t ↦ Ψ (standardTorusCurve p q (σ.f t))` has winding vector `(p, q)` with respect to the
parametrisation `(x, y) ↦ Ψ (torusMap x y)`.

This is the shape in which the winding vector is needed for a knot that is the image of the
standard torus knot under a diffeomorphism of `ℝ³`. -/
theorem hasWinding_comp_standardTorusCurve (p q : ℕ) (Ψ : R3 → R3)
    (σ : CircleReparam) :
    HasWinding (fun x y => Ψ (Work.Core.torusMap x y))
      (fun t => Ψ (standardTorusCurve p q (σ.f t))) ((p : ℤ), (q : ℤ)) :=
  hasWinding_comp_left
    (_root_.Work.TorusCover.hasWinding_comp_circleReparam
      (hasWinding_standardTorusCurve p q) σ)

end

end Work.TorusCover
