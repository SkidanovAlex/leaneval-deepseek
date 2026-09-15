import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# The Laplacian of a `C²` function along the complex line `ζ ↦ z + ζ • v`

Let `E` be a real normed space and `u : E → ℝ` be `C²` at `z ∈ E`.  For a vector `v ∈ E`, consider
the function of the complex variable `ζ`

`φ(ζ) = u (z + ζ • v)`.

Its real Laplacian at `0` is the sum of the second derivatives of `u` at `z` in the two orthogonal
directions `v` and `I • v`:

`Δ φ (0) = D²u(z)[v, v] + D²u(z)[I • v, I • v]`.

This is the two-dimensional (complex line) case of the standard fact that the Laplacian is the
trace of the Hessian: the parametrisation `ζ ↦ z + ζ • v` identifies `ℂ` with the real plane spanned
by `v` and `I • v` (with the real orthonormal basis `1, I` on `ℂ`), and the Laplacian on `ℂ` is
`∂²/∂1² + ∂²/∂I²`.

The auxiliary results proved here are the second-order chain rules that make this computation
possible:

* `iteratedFDeriv_two_comp_clm`: composing a `C²` function with a continuous linear map on the
  right multiplies the second iterated derivative by that map on both arguments;
* `iteratedFDeriv_two_comp_add_clm`: the same, including the translation by a constant `z`.
-/

open scoped RealInnerProductSpace InnerProductSpace

namespace Commons.Analysis.Calculus

/-- **Second-order chain rule for composition with a continuous linear map.**

If `u : E → ℝ` is `C²` at `L y` and `L : G →L[ℝ] E` is a continuous linear map, then the second
iterated derivative of `u ∘ L` at `y`, evaluated on the diagonal `![w, w]`, is the second iterated
derivative of `u` at `L y` evaluated on `![L w, L w]`.

In other words, the Hessian of `u ∘ L` at `y` is the Hessian of `u` at `L y` pulled back along `L`
on both slots. -/
theorem iteratedFDeriv_two_comp_clm {G E : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {u : E → ℝ} (L : G →L[ℝ] E) (y : G) (w : G)
    (hu : ContDiffAt ℝ 2 u (L y)) :
    (iteratedFDeriv ℝ 2 (u ∘ L) y) ![w, w] = (iteratedFDeriv ℝ 2 u (L y)) ![L w, L w] := by
  obtain ⟨U, hUo, hyU, huU⟩ := hu.contDiffOn' le_rfl (by simp)
  rw [Set.insert_eq_of_mem (Set.mem_univ _), Set.univ_inter] at huU
  have hcomp := L.iteratedFDerivWithin_comp_right (s := U) huU hUo.uniqueDiffOn
      (hUo.preimage L.continuous).uniqueDiffOn hyU (i := 2) le_rfl
  have h1 : iteratedFDerivWithin ℝ 2 (u ∘ L) (L ⁻¹' U) y = iteratedFDeriv ℝ 2 (u ∘ L) y :=
    (iteratedFDerivWithin_of_isOpen (f := u ∘ L) 2 (hUo.preimage L.continuous)) hyU
  have h2 : iteratedFDerivWithin ℝ 2 u U (L y) = iteratedFDeriv ℝ 2 u (L y) :=
    (iteratedFDerivWithin_of_isOpen (f := u) 2 hUo) hyU
  rw [h1, h2] at hcomp
  rw [hcomp, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  fin_cases i <;> simp

/-- **Second-order chain rule for the affine parametrisation `ζ ↦ z + L ζ`.**

If `u : E → ℝ` is `C²` at `z` and `L : G →L[ℝ] E` is a continuous linear map, then the second
iterated derivative at `0` of `ζ ↦ u (z + L ζ)`, evaluated on the diagonal `![w, w]`, is the second
iterated derivative of `u` at `z` evaluated on `![L w, L w]`. -/
theorem iteratedFDeriv_two_comp_add_clm {G E : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {u : E → ℝ} {z : E} (hu : ContDiffAt ℝ 2 u z)
    (L : G →L[ℝ] E) (w : G) :
    (iteratedFDeriv ℝ 2 (fun ζ : G => u (z + L ζ)) 0) ![w, w]
      = (iteratedFDeriv ℝ 2 u z) ![L w, L w] := by
  have hu'' : ContDiffAt ℝ 2 u (z + 0) := by simpa using hu
  have h1 : ContDiffAt ℝ 2 (fun η : E => z + η) 0 := by fun_prop
  have hu'0 : ContDiffAt ℝ 2 (fun η : E => u (z + η)) 0 := hu''.comp (0 : E) h1
  have hu' : ContDiffAt ℝ 2 (fun η : E => u (z + η)) (L 0) := by simpa using hu'0
  rw [show (fun ζ : G => u (z + L ζ)) = (fun η : E => u (z + η)) ∘ L from rfl]
  rw [iteratedFDeriv_two_comp_clm L 0 w hu']
  simp only [map_zero]
  rw [iteratedFDeriv_comp_add_left (f := u) 2 z 0]
  simp

/-- The Laplacian on `ℂ` of `ζ ↦ u (z + ζ • v)` at `0` is the sum of the second derivatives of `u`
at `z` in the directions `v` and `Complex.I • v`. -/
theorem laplacian_comp_add_smul {d : ℕ} {u : EuclideanSpace ℂ (Fin d) → ℝ}
    {z v : EuclideanSpace ℂ (Fin d)} (hu : ContDiffAt ℝ 2 u z) :
    Laplacian.laplacian (fun ζ : ℂ => u (z + ζ • v)) 0 =
      (iteratedFDeriv ℝ 2 u z) ![v, v]
        + (iteratedFDeriv ℝ 2 u z) ![Complex.I • v, Complex.I • v] := by
  -- `ζ ↦ ζ • v` is the continuous linear map `(ContinuousLinearMap.lsmul ℝ ℂ).flip v`
  have hψ : (fun ζ : ℂ => u (z + ζ • v)) =
      fun ζ : ℂ => u (z + ((ContinuousLinearMap.lsmul ℝ ℂ).flip v) ζ) := by
    funext ζ
    rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply]
  rw [hψ, InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only
  -- the two second derivatives along the real orthonormal basis `1, I` of `ℂ`
  rw [iteratedFDeriv_two_comp_add_clm hu ((ContinuousLinearMap.lsmul ℝ ℂ).flip v) (1 : ℂ),
      iteratedFDeriv_two_comp_add_clm hu ((ContinuousLinearMap.lsmul ℝ ℂ).flip v) Complex.I]
  simp [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply]

end Commons.Analysis.Calculus
