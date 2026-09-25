import Mathlib
import Submission.Work.NN.Newton.DefectDefs

/-!
# Expansion of the flat `∂̄`-defect of the coordinate datum

This module computes the flat `∂̄`-defect `∂̄_j F^{(l)}_k − ∂̄_k F^{(l)}_j` of the coordinate
datum `F^{(l)}_m = Lcoef A (·l) m = (i/2)·(A z e_m)_l` purely in terms of the first derivative of
`A`, showing that it equals `(i/4)` times the "Nijenhuis" expression

`defectExpr A z l j k = λ(DA[e_j]e_k) − λ(DA[e_k]e_j) + i·λ(DA[i e_j]e_k) − i·λ(DA[i e_k]e_j)`,

where `λ = (·l)` and `LD A z l X Y = λ((DA_z X) Y)`.

This is the linear part of the quadratic defect estimate
`Work.NN.Newton.coordDatum_defect_quadratic`: combining it with the integrability identity
`Work.NN.Newton.Defect.defect_algebra` (which expresses `defectExpr` through the quadratic
remainder `TA`, using `J² = −1`) yields the claimed `a²`-bound for the defect.

## Contents

* `fderiv_lamCA`, `fderiv_const_mul_lamCA`: the chain rule for `z ↦ λ(A z w)`, i.e.
  `fderiv (z ↦ λ(A z w)) z X = λ((DA_z X) w)`: this is the only analytic input.
* `dbar_half_form`, `ddbar_algebra`: the elementary algebra `i² = −1` identities computing the
  `(0,1)`-derivative and the defect.
* `dbarCoord_coordDatum`: the `j`-th `∂̄`-derivative of the `m`-th coefficient of the coordinate
  datum.
* `ddbar_coordDatum_expansion`: the statement requested by the caller.
-/

namespace Work.NN.Newton.Defect

noncomputable section

/-- The chain rule for `z ↦ λ(A z w)`, where `λ = lamC l` is a complex-linear coordinate
functional: its derivative at `z` in the direction `X` is `λ((DA_z X) w)`. -/
lemma fderiv_lamCA {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (l : Fin n) (w : Work.NN.Core.Cn n) {z : Work.NN.Core.Cn n}
    (hA : DifferentiableAt ℝ A z) (X : Work.NN.Core.Cn n) :
    fderiv ℝ (fun z' => Work.NN.Newton.lamC l (A z' w)) z X
      = Work.NN.Newton.lamC l ((fderiv ℝ A z X) w) := by
  have hAw : HasFDerivAt (fun y => A y w) ((fderiv ℝ A z).flip w) z := by
    have hc : HasFDerivAt A (fderiv ℝ A z) z := hA.hasFDerivAt
    have hu : HasFDerivAt (fun _ : Work.NN.Core.Cn n => w)
      (0 : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n) z := hasFDerivAt_const w z
    have h := hc.clm_apply hu
    simpa using h
  have h2 : HasFDerivAt (fun y => Work.NN.Newton.lamC l (A y w))
      ((Work.NN.Newton.lamC l).comp ((fderiv ℝ A z).flip w)) z :=
    (ContinuousLinearMap.hasFDerivAt (Work.NN.Newton.lamC l)).comp z hAw
  rw [h2.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.flip_apply]

/-- The same chain rule with a constant factor `c` in front of `λ(A z w)`. -/
lemma fderiv_const_mul_lamCA {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (l : Fin n) (w : Work.NN.Core.Cn n) {z : Work.NN.Core.Cn n}
    (hA : DifferentiableAt ℝ A z) (c : ℂ) (X : Work.NN.Core.Cn n) :
    fderiv ℝ (fun z' => c * Work.NN.Newton.lamC l (A z' w)) z X
      = c * Work.NN.Newton.lamC l ((fderiv ℝ A z X) w) := by
  have hAw : HasFDerivAt (fun y => A y w) ((fderiv ℝ A z).flip w) z := by
    have hc : HasFDerivAt A (fderiv ℝ A z) z := hA.hasFDerivAt
    have hu : HasFDerivAt (fun _ : Work.NN.Core.Cn n => w)
      (0 : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n) z := hasFDerivAt_const w z
    have h := hc.clm_apply hu
    simpa using h
  have h2 : HasFDerivAt (fun y => Work.NN.Newton.lamC l (A y w))
      ((Work.NN.Newton.lamC l).comp ((fderiv ℝ A z).flip w)) z :=
    (ContinuousLinearMap.hasFDerivAt (Work.NN.Newton.lamC l)).comp z hAw
  have h3 : HasFDerivAt (fun y => c * Work.NN.Newton.lamC l (A y w))
      (c • ((Work.NN.Newton.lamC l).comp ((fderiv ℝ A z).flip w))) z := h2.const_mul c
  rw [h3.fderiv]
  simp only [smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul]

/-- The `(0,1)`-derivative of `½((i/2)X + i·(i/2)Y)`: using `i² = −1` this is
`(i/4)X − (1/4)Y`.  This is the pair of directions `X`, `Y` of the two summands of
`∂̄_j u = ½(D_{e_j}u + i·D_{i e_j}u)`. -/
lemma dbar_half_form (X Y : ℂ) :
    (1/2:ℂ) * ((Complex.I/2) * X + Complex.I * ((Complex.I/2) * Y))
      = (Complex.I/4) * X - (1/4) * Y := by
  have h1 : Complex.I * (Complex.I/2) = -(1/2) := by
    calc Complex.I * (Complex.I/2) = (Complex.I * Complex.I)/2 := by ring
      _ = (-1)/2 := by rw [Complex.I_mul_I]
      _ = -(1/2) := by ring
  rw [← mul_assoc, h1]
  ring

/-- The elementary algebra of the defect: in terms of the four `LD`-entries
`A = λ(DA[e_j]e_k)`, `B = λ(DA[e_k]e_j)`, `C = λ(DA[i e_j]e_k)`, `D = λ(DA[i e_k]e_j)`,
the difference `∂̄_j F_k − ∂̄_k F_j` equals `(i/4)·(A − B + i C − i D)`. -/
lemma ddbar_algebra (A B C D : ℂ) :
    ((Complex.I/4)*A - (1/4)*C) - ((Complex.I/4)*B - (1/4)*D)
      = (Complex.I/4)*(A - B + Complex.I*C - Complex.I*D) := by
  linear_combination (norm := ring_nf) (-(1/4)*(C - D)) * Complex.I_mul_I

/-- The `j`-th flat `∂̄`-derivative of the `m`-th coefficient of the coordinate datum:
`∂̄_j F^{(l)}_m = (i/4)·λ(DA[e_j]e_m) − (1/4)·λ(DA[i e_j]e_m)`. -/
lemma dbarCoord_coordDatum {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (l m j : Fin n) {z : Work.NN.Core.Cn n} (hA : DifferentiableAt ℝ A z) :
    Work.CR.Flat.dbarCoord j (Work.NN.Newton.coordDatum A l m) z
      = (Complex.I/4) * Work.NN.Newton.LD A z l (Work.NN.Newton.evec j) (Work.NN.Newton.evec m)
        - (1/4) * Work.NN.Newton.LD A z l (Work.NN.Newton.ievec j) (Work.NN.Newton.evec m) := by
  rw [Work.CR.Flat.dbarCoord]
  have hfun : Work.NN.Newton.coordDatum A l m
      = fun y => (Complex.I/2) * Work.NN.Newton.lamC l (A y (Work.NN.Newton.evec m)) := by
    funext y; exact Work.NN.Newton.coordDatum_eq A l m y
  rw [hfun]
  simp only [Work.NN.Newton.evec, Work.NN.Newton.ievec]
  rw [fderiv_const_mul_lamCA A l (Pi.single m 1) hA (Complex.I/2) (Pi.single j 1),
      fderiv_const_mul_lamCA A l (Pi.single m 1) hA (Complex.I/2) (Pi.single j Complex.I)]
  simp only [Work.NN.Newton.LD, Work.NN.Newton.LDv]
  exact dbar_half_form _ _

/-- **Expansion of the flat `∂̄`-defect of the coordinate datum.**

For `A` differentiable at `z`, the `(j,k)`-coefficient of the flat `∂̄`-defect of the coordinate
datum `F^{(l)}_m = Lcoef A (·l) m` is `(i/4)` times the Nijenhuis-type expression `defectExpr`:
every term is linear in `DA_z`. -/
theorem ddbar_coordDatum_expansion {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n) (l j k : Fin n)
    {z : Work.NN.Core.Cn n} (hA : DifferentiableAt ℝ A z) :
    Work.NN.Final.ddbar (Work.NN.Core.JstdCn n) (Work.NN.Newton.coordDatum A l) j k z
      = (Complex.I / 4) * Work.NN.Newton.defectExpr A z l j k := by
  rw [Work.NN.Final.ddbar_std]
  rw [dbarCoord_coordDatum A l k j hA, dbarCoord_coordDatum A l j k hA]
  rw [Work.NN.Newton.defectExpr]
  exact ddbar_algebra _ _ _ _

end

end Work.NN.Newton.Defect
