import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Commons.Analysis.Calculus.FDeriv.hasFDerivAt_iteratedFDeriv_apply

/-!
# The directional derivative of the squared gradient along an orthonormal basis

For a `C²` function `u` on an open set `s`, the function
`z ↦ ∑ k, ((fderiv ℝ u z) (v k)) ^ 2` (the squared length of the gradient expressed in an
orthonormal basis `v`) has directional derivative at `x` in direction `w` given by

`2 * ∑ k, (fderiv ℝ u x) (v k) * ((iteratedFDeriv ℝ 2 u x) ![w, v k])`.

Each summand `z ↦ ((fderiv ℝ u z) (v k)) ^ 2` is differentiated with the chain rule
(`HasFDerivAt.pow`), using `hasFDerivAt_iteratedFDeriv_apply` for the derivative of
`z ↦ (fderiv ℝ u z) (v k)`.
-/

namespace Commons.Analysis.Calculus.FDeriv

open scoped RealInnerProductSpace in
open scoped BigOperators in
theorem fderiv_grad_sq_directional {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℝ E) {s : Set E} {u : E → ℝ} {x : E}
    (hs : IsOpen s) (hx : x ∈ s) (hu : ContDiffOn ℝ 2 u s) (w : E) :
    fderiv ℝ (fun z => ∑ k : ι, ((fderiv ℝ u z) (v k)) ^ 2) x w =
      2 * ∑ k : ι, (fderiv ℝ u x) (v k) * ((iteratedFDeriv ℝ 2 u x) ![w, v k]) := by
  -- The derivative of each summand `z ↦ ((fderiv ℝ u z) (v k)) ^ 2`.
  have hterm : ∀ k : ι, HasFDerivAt (fun z => ((fderiv ℝ u z) (v k)) ^ 2)
      (((2 : ℝ) * ((fderiv ℝ u x) (v k))) •
        (((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => E) ℝ) ![v k]).comp
          (ContinuousMultilinearMap.curryLeft (iteratedFDeriv ℝ 2 u x)))) x := by
    intro k
    have h := (hasFDerivAt_iteratedFDeriv_apply (E := E) hs hx (n := 1) hu
      (![v k] : Fin 1 → E)).pow 2
    simpa using h
  rw [fderiv_fun_sum (u := Finset.univ)
      (A := fun k (z : E) => ((fderiv ℝ u z) (v k)) ^ 2)
      (fun k _ => (hterm k).differentiableAt)]
  rw [sum_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [(hterm k).fderiv, smul_apply, ContinuousLinearMap.comp_apply]
  simp only [ContinuousMultilinearMap.curryLeft_apply, ContinuousMultilinearMap.apply_apply]
  rw [show (Fin.cons w ![v k] : Fin 2 → E) = ![w, v k] from rfl]
  ring

end Commons.Analysis.Calculus.FDeriv