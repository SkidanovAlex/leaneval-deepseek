/-
# `Work.FTS.PressureOn.materialDeriv_eq_gradient_sub_cross`

The pointwise vector identity underlying the "material derivative" form of the Euler equation,

  `(u·∇)u = ∇(‖u‖²/2) − u × (∇×u)`,

i.e.

  `fderiv ℝ u x (u x) = gradient (fun y => ‖u y‖ ^ 2 / 2) x − crossVec (u x) (vorticity u x)`.

## Route

Everything is reduced to coordinates in `Fin 3 → ℝ`, where the identity becomes the elementary
statement `curl_inner_core` about an abstract linear map `B`, and is then transported back through
the canonical identification `WithLp.ofLp : ℝ³ ≃ₗ[ℝ] (Fin 3 → ℝ)`.

* `inner_gradient_left` (`⟪∇f x, y⟫ = fderiv ℝ f x y`) together with `HasFDerivAt.norm_sq` computes
  the gradient term: `⟪∇(‖u·‖²/2) x, w⟫ = ⟪(Du) w, u x⟫`.
* `curlVec D = ∑ᵢ eᵢ × (D eᵢ)` is the curl of the linear field `D`; `inner_crossVec_curlVec`
  is the coordinate identity `⟪a × curlVec D, w⟫ = ⟪D w, a⟫ − ⟪D a, w⟫`, whose content is
  `curl_inner_core`.
* The conclusion follows from the nondegeneracy of the inner product (`ext_inner_right`).
-/
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.LinearAlgebra.CrossProduct
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity
open scoped Matrix

set_option autoImplicit false

namespace Work.FTS.PressureOn

/-- **The curl of a linear field as a continuous linear map of its derivative**:
`curlVec D = ∑ᵢ eᵢ × (D eᵢ)`, i.e. `FiniteTimeSingularity.vorticity (fun x => D x)` evaluated
anywhere. -/
noncomputable def curlVec (D : R3 →L[ℝ] R3) : R3 :=
  WithLp.toLp 2 (∑ i : Fin 3, e i ⨯₃ (D (e i)))

/-- The derivative `D : ℝ³ →L[ℝ] ℝ³`, transported to the coordinate space `Fin 3 → ℝ` along the
canonical linear equivalence `WithLp.ofLp`.  By construction
`conjLin D f = (D (WithLp.toLp 2 f)).ofLp`. -/
noncomputable def conjLin (D : R3 →L[ℝ] R3) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
  (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap.comp
    (D.toLinearMap.comp (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap)

theorem conjLin_apply (D : R3 →L[ℝ] R3) (f : Fin 3 → ℝ) :
    conjLin D f = (D (WithLp.toLp 2 f)).ofLp := rfl

/-- **The inner product of `R3`-vectors is their coordinatewise sum of products.** -/
theorem inner_eq_sum (x y : R3) : inner ℝ x y = ∑ i : Fin 3, x.ofLp i * y.ofLp i := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [RCLike.inner_apply', starRingEnd_apply, star_trivial]

/-- The same, with the first vector written as `WithLp.toLp 2 F`. -/
theorem inner_toLp_left (F : Fin 3 → ℝ) (y : R3) :
    inner ℝ ((WithLp.toLp 2 F : R3)) y = ∑ i, F i * y.ofLp i := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [RCLike.inner_apply', starRingEnd_apply, star_trivial]

/-- **The coordinate core of the identity.**  For an abstract linear map `B` on `Fin 3 → ℝ`,
written `M r s := B (Pi.single s 1) r` for its matrix in the standard basis,

`∑ᵣ (p × (∑ᵢ eᵢ × (B eᵢ)))ᵣ qᵣ = ∑ᵣ (B q)ᵣ pᵣ − ∑ᵣ (B p)ᵣ qᵣ`,

the coordinates of `⟪a × curl D, w⟫ = ⟪D w, a⟫ − ⟪D a, w⟫`.  The proof expands `B f r` as the
matrix–vector product `∑ₛ M r s * f s` (from `f = ∑ₛ f s • eₛ` and linearity), computes the curl
`∑ᵢ eᵢ × (B eᵢ) = (M 2 1 − M 1 2, M 0 2 − M 2 0, M 1 0 − M 0 1)`, and closes the resulting
polynomial identity by `ring`. -/
theorem curl_inner_core (B : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) (p q : Fin 3 → ℝ) :
    (∑ r : Fin 3,
        crossProduct p (∑ i : Fin 3, crossProduct (Pi.single i (1:ℝ)) (B (Pi.single i (1:ℝ)))) r
          * q r)
      = (∑ r : Fin 3, B q r * p r) - (∑ r : Fin 3, B p r * q r) := by
  set M : Fin 3 → Fin 3 → ℝ := fun r s => B (Pi.single s (1:ℝ)) r with hM
  have hBsing : ∀ s : Fin 3, B (Pi.single s (1:ℝ)) = fun r => M r s := by
    intro s; funext r; rw [hM]
  have hB : ∀ (f : Fin 3 → ℝ) (r : Fin 3), B f r = ∑ s, M r s * f s := by
    intro f r
    have hbasis : f = ∑ s, f s • Pi.single s (1:ℝ) := by
      ext t; simp [Pi.single_apply, Finset.sum_ite_eq]
    conv_lhs => rw [hbasis]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul, hM]
    ring
  have hc : (∑ i : Fin 3, crossProduct (Pi.single i (1:ℝ)) (B (Pi.single i (1:ℝ))))
      = ![M 2 1 - M 1 2, M 0 2 - M 2 0, M 1 0 - M 0 1] := by
    ext r
    fin_cases r <;> simp [hBsing, Fin.sum_univ_three, cross_apply]
  rw [hc]
  simp only [hB, Fin.sum_univ_three, cross_apply]
  norm_num
  ring

/-- **The derivative of `‖u·‖²/2`.**  If `u` has derivative `D` at `x`, then the derivative of
`y ↦ ‖u y‖²/2` at `x`, evaluated at `w`, is `⟪D w, u x⟫`. -/
theorem fderiv_norm_sq_half_apply {u : R3 → R3} {x : R3} {D : R3 →L[ℝ] R3}
    (hu : HasFDerivAt u D x) (w : R3) :
    fderiv ℝ (fun y => ‖u y‖ ^ 2 / 2) x w = inner ℝ (D w) (u x) := by
  have h1 : HasFDerivAt (fun y => ‖u y‖ ^ 2) (2 • ((innerSL ℝ) (u x) ∘SL D)) x := hu.norm_sq
  have h2 : HasFDerivAt (fun y => ‖u y‖ ^ 2 / 2)
      ((2:ℝ)⁻¹ • (2 • ((innerSL ℝ) (u x) ∘SL D))) x := by
    have := h1.const_mul ((2:ℝ)⁻¹)
    simpa [div_eq_inv_mul] using this
  rw [h2.fderiv]
  simp only [smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply, innerSL_apply_apply]
  rw [real_inner_comm (u x) (D w)]
  ring

/-- **The coordinate form of `⟪a × (∇×u), w⟫ = ⟪(Du) w, a⟫ − ⟪(Du) a, w⟫`** for a linear field
with derivative `D`:  `⟪crossVec a (curlVec D), w⟫ = ⟪D w, a⟫ − ⟪D a, w⟫`.

This is `curl_inner_core` transported along `WithLp.ofLp` (the two sides are even definitionally
equal after that transport, which is why the first three steps are `rfl`). -/
theorem inner_crossVec_curlVec (D : R3 →L[ℝ] R3) (a w : R3) :
    inner ℝ (crossVec a (curlVec D)) w = inner ℝ (D w) a - inner ℝ (D a) w := by
  have hcross : crossVec a (curlVec D) = WithLp.toLp 2 (crossProduct a.ofLp
      (∑ i : Fin 3, crossProduct (Pi.single i (1:ℝ)) (conjLin D (Pi.single i (1:ℝ))))) := rfl
  have hDw : D w = WithLp.toLp 2 (conjLin D (w.ofLp)) := rfl
  have hDa : D a = WithLp.toLp 2 (conjLin D (a.ofLp)) := rfl
  rw [hcross, hDw, hDa, inner_toLp_left, inner_toLp_left, inner_toLp_left]
  exact curl_inner_core (conjLin D) a.ofLp w.ofLp

/-- **The material derivative is the gradient of the kinetic energy minus the cross product with
the vorticity**:  `(u·∇)u = ∇(‖u‖²/2) − u × (∇×u)`, i.e.
`fderiv ℝ u x (u x) = gradient (fun y => ‖u y‖²/2) x − crossVec (u x) (vorticity u x)`.

Proved by testing against an arbitrary `w` with `ext_inner_right`: the left side is
`⟪(Du) (u x), w⟫`, the gradient term is `⟪(Du) w, u x⟫` (`inner_gradient_left` +
`fderiv_norm_sq_half_apply`), and the cross-product term is handled by
`inner_crossVec_curlVec`. -/
theorem materialDeriv_eq_gradient_sub_cross {u : R3 → R3} {x : R3}
    (hu : HasFDerivAt u (fderiv ℝ u x) x) :
    fderiv ℝ u x (u x)
      = gradient (fun y => ‖u y‖ ^ 2 / 2) x - crossVec (u x) (FiniteTimeSingularity.vorticity u x) := by
  refine ext_inner_right ℝ fun w => ?_
  rw [inner_sub_left, inner_gradient_left, fderiv_norm_sq_half_apply hu w]
  have hv : FiniteTimeSingularity.vorticity u x = curlVec (fderiv ℝ u x) := rfl
  rw [hv, inner_crossVec_curlVec]
  ring

end Work.FTS.PressureOn
