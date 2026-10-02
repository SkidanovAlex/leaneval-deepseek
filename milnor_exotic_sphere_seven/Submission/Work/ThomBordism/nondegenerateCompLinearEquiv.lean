import Mathlib
import Submission.Work.Bordism.Middle

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Non-degeneracy is invariant under linear isomorphisms

The radical of a quadratic form is trivial once and for all if and only if the radical of the form
precomposed with a linear *equivalence* is trivial:

`Work.ThomBordism.nondegenerate_comp_linearEquiv`.

The auxiliary computation is `Work.ThomBordism.associated_comp_apply`: the associated bilinear form
of `Q.comp f` is the associated form of `Q` evaluated on the images, i.e.

`associated (Q.comp f) x y = associated Q (f x) (f y)`.

This is the algebraic input of the transportation of the middle intersection form along a
homeomorphism (`Work.ThomBordism.nondegenerateOfIso`).
-/

namespace Work.ThomBordism

open Work.SignatureBordism

/-- **The associated bilinear form of a precomposition.**  For a quadratic form `Q` on `W` and a
linear map `f : V →ₗ W`, the associated bilinear form of `Q.comp f` on `V` is the associated form of
`Q` evaluated on `f x` and `f y`. -/
theorem associated_comp_apply {𝕜 V W : Type*} [CommRing 𝕜] [Invertible (2 : 𝕜)]
    [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]
    (Q : QuadraticForm 𝕜 W) (f : V →ₗ[𝕜] W) (x y : V) :
    QuadraticMap.associated (Q.comp f) x y = QuadraticMap.associated Q (f x) (f y) := by
  rw [QuadraticMap.associated_apply 𝕜, QuadraticMap.associated_apply 𝕜, QuadraticMap.comp_apply,
    QuadraticMap.comp_apply, QuadraticMap.comp_apply, map_add]

/-- **Non-degeneracy is invariant under a linear equivalence.**  For a linear equivalence
`e : V ≃ₗ[𝕜] W` and a quadratic form `Q` on `W`, the form `Q.comp e` on `V` is non-degenerate if
and only if `Q` is. -/
theorem nondegenerate_comp_linearEquiv {𝕜 V W : Type*} [CommRing 𝕜] [Invertible (2 : 𝕜)]
    [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]
    (Q : QuadraticForm 𝕜 W) (e : V ≃ₗ[𝕜] W) :
    Work.Bordism.Nondegenerate (Q.comp (e : V →ₗ[𝕜] W)) ↔ Work.Bordism.Nondegenerate Q := by
  constructor
  · intro h x hx
    have hx' : ∀ y : V, QuadraticMap.associated (Q.comp (e : V →ₗ[𝕜] W)) (e.symm x) y = 0 := by
      intro y
      have h2 : QuadraticMap.associated (Q.comp (e : V →ₗ[𝕜] W)) (e.symm x) y
          = QuadraticMap.associated Q x ((e : V → W) y) := by
        rw [associated_comp_apply]
        simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      rw [h2]
      exact hx ((e : V → W) y)
    have h1 : e.symm x = 0 := h (e.symm x) hx'
    have h2 : x = (e : V → W) (e.symm x) := (LinearEquiv.apply_symm_apply e x).symm
    rw [h1] at h2
    rw [LinearEquiv.map_zero] at h2
    exact h2
  · intro h x hx
    have hx' : ∀ z : W, QuadraticMap.associated Q ((e : V → W) x) z = 0 := by
      intro z
      have h2 : QuadraticMap.associated (Q.comp (e : V →ₗ[𝕜] W)) x ((e.symm : W → V) z)
          = QuadraticMap.associated Q ((e : V → W) x) z := by
        rw [associated_comp_apply]
        simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      rw [← h2]
      exact hx ((e.symm : W → V) z)
    have h1 : (e : V → W) x = 0 := h _ hx'
    have h2 : ((e.symm : W → V) ((e : V → W) x)) = x := LinearEquiv.symm_apply_apply e x
    rw [h1] at h2
    rw [LinearEquiv.map_zero] at h2
    exact h2.symm

end Work.ThomBordism
