import Mathlib
import Submission.Work.NN.Newton.DefectDefs

/-!
# `dOne` of the `∂̄`-operator of the coordinate datum

This file computes the exterior derivative of the `(0,1)`-form
`z' ↦ ∂̄_{Jstd + A} z'_l` at a point `z`, evaluated on the pair `(X, Y)`.

Since the differential of the `l`-th coordinate functional is constant (`fderiv_lamC`), the
pointwise value of the form is simply

`∂̄_{Jstd + A} z'_l (w) = (i/2)·λ_l(A z' w)`,

so that the derivative in `z'` is `(i/2)·λ_l((DA_z X) w)`.  Antisymmetrising in `(X, Y)` gives
the claimed identity, with `LD A z l X Y = λ_l((DA_z X) Y)` the "linearised datum" of
`DefectDefs`.

These are the two computational inputs of the quadratic defect expansion
(`coordDatum_defect_quadratic`).
-/

namespace Work.NN.Newton.Defect

/-- The pointwise value of the coordinate `∂̄`-form: since `u = λ_l` has constant differential,
`∂̄_{Jstd + A} λ_l` reduces to `(i/2)·λ_l ∘ (A z')`. -/
lemma dbarCn_JstdCn_add_zcoord {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n) (l : Fin n)
    (z w : Work.NN.Core.Cn n) :
    Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) (fun y => y l) z w
      = (Complex.I / 2) * Work.NN.Newton.lamC l (A z w) := by
  rw [Work.NN.Core.dbarCn_apply, Work.NN.Newton.fderiv_lamC]
  simp only [Work.NN.Newton.lamC_apply, Pi.add_apply, add_apply,
    Work.NN.Core.JstdCn_apply, Pi.smul_apply, smul_eq_mul, map_add]
  ring_nf
  simp only [pow_two, Complex.I_mul_I]
  ring

/-- The `z'`-derivative of the coefficient `z' ↦ ∂̄_{Jstd + A} z'_l (w)`. -/
lemma fderiv_dbarCn_zcoord {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n) (l : Fin n)
    {z : Work.NN.Core.Cn n} (hA : DifferentiableAt ℝ A z) (w : Work.NN.Core.Cn n)
    (X : Work.NN.Core.Cn n) :
    fderiv ℝ (fun z' => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) (fun y => y l) z' w) z X
      = (Complex.I / 2) * Work.NN.Newton.lamC l ((fderiv ℝ A z X) w) := by
  have h1 : HasFDerivAt (fun z' : Work.NN.Core.Cn n => A z' w) ((fderiv ℝ A z).flip w) z := by
    have hc := hA.hasFDerivAt.clm_apply (hasFDerivAt_const w z)
    simpa using hc
  have h2 : HasFDerivAt (fun z' => Work.NN.Newton.lamC l (A z' w))
      ((Work.NN.Newton.lamC l).comp ((fderiv ℝ A z).flip w)) z :=
    (Work.NN.Newton.lamC l).hasFDerivAt.comp z h1
  have hfun : (fun z' => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) (fun y => y l) z' w)
      = fun z' => (Complex.I / 2) * Work.NN.Newton.lamC l (A z' w) :=
    funext fun z' => dbarCn_JstdCn_add_zcoord A l z' w
  rw [hfun, fderiv_const_mul h2.differentiableAt]
  rw [smul_apply, smul_eq_mul, h2.fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]

theorem dOne_dbarCn_zcoord {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (l : Fin n) {z : Work.NN.Core.Cn n} (hA : DifferentiableAt ℝ A z)
    (X Y : Work.NN.Core.Cn n) :
    Work.NN.Final.dOne
        (fun z' => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A)
          (fun y : Work.NN.Core.Cn n => y l) z') z X Y
      = (Complex.I / 2) * (Work.NN.Newton.LD A z l X Y - Work.NN.Newton.LD A z l Y X) := by
  have hXY := fderiv_dbarCn_zcoord A l hA Y X
  have hYX := fderiv_dbarCn_zcoord A l hA X Y
  simp only [Work.NN.Final.dOne, Work.NN.Newton.LD, Work.NN.Newton.LDv]
  rw [hXY, hYX]
  ring

end Work.NN.Newton.Defect
