import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Polydisc

/-!
# Smoothness of the coefficients of the perturbed `∂̄`-operator

`dbarCn (JstdCn n + A) u z (Pi.single j 1)` is the `j`-th coefficient (in the real basis
`e_j`) of the `(0,1)`-form `∂̄_{Jstd + A} u` of the perturbed structure `Jstd + A`.  By
`dbarCoef_lin` it splits as

  `dbarCoord j u z + Lcoef A u j z`,

the sum of the flat `(0,1)`-derivative of `u` and the *first-order* perturbation term
`(i/2)·du_z(A z e_j)`.  Both terms are built from `fderiv ℝ u` and `A` by evaluation and
multiplication, so if `u` is `C^{k+1}` on the open set `Ω` (its differential then being
`C^k` there, `ContDiffOn.fderiv_of_isOpen`) and `A` is globally `C^{k+1}` (hence `C^k`
on `Ω`), the coefficient is `C^k` on `Ω`.
-/

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Core

lemma contDiffOn_dbarCn_coeff {n : ℕ} {Ω : Set (Work.NN.Core.Cn n)} (hΩ : IsOpen Ω) (k : ℕ)
    {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    (hA : ContDiff ℝ ((k+1 : ℕ) : WithTop ℕ∞) A)
    {u : Work.NN.Core.Cn n → ℂ} (hu : ContDiffOn ℝ ((k+1 : ℕ) : WithTop ℕ∞) u Ω) (j : Fin n) :
    ContDiffOn ℝ ((k : ℕ) : WithTop ℕ∞)
      (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z (Pi.single j (1:ℂ))) Ω := by
  -- `((k : ℕ) : WithTop ℕ∞) + 1 = ((k+1 : ℕ) : WithTop ℕ∞)`: the derivative drops one order.
  have hko : ((k : ℕ) : WithTop ℕ∞) + 1 = ((k+1 : ℕ) : WithTop ℕ∞) := by
    push_cast; ring
  have hle : ((k : ℕ) : WithTop ℕ∞) ≤ ((k+1 : ℕ) : WithTop ℕ∞) := by
    rw [← hko]; exact le_add_of_nonneg_right (by simp)
  -- differentiability data
  have hku : ContDiffOn ℝ ((k : ℕ) : WithTop ℕ∞) (fderiv ℝ u) Ω :=
    hu.fderiv_of_isOpen hΩ (le_of_eq hko)
  have hkA : ContDiffOn ℝ ((k : ℕ) : WithTop ℕ∞) A Ω :=
    (hA.contDiffOn).of_le hle
  -- split the coefficient into the flat part and the (first-order) perturbation part
  have hsplit : (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z (Pi.single j (1:ℂ)))
      = fun z => Work.CR.Flat.dbarCoord j u z + Lcoef A u j z := by
    funext z; rw [dbarCoef_lin]
  rw [hsplit]
  -- the flat `(0,1)`-derivative `dbarCoord j u = (1/2)(du(e_j) + i·du(i·e_j))`
  have hcoord : ContDiffOn ℝ ((k : ℕ) : WithTop ℕ∞) (fun z => Work.CR.Flat.dbarCoord j u z) Ω := by
    have h1 : ContDiffOn ℝ ((k:ℕ):WithTop ℕ∞)
        (fun z => (fderiv ℝ u z) (Pi.single j (1:ℂ))) Ω := hku.clm_apply contDiffOn_const
    have h2 : ContDiffOn ℝ ((k:ℕ):WithTop ℕ∞)
        (fun z => (fderiv ℝ u z) (Pi.single j (Complex.I:ℂ))) Ω := hku.clm_apply contDiffOn_const
    have h := (contDiffOn_const (c := (1/2:ℂ))).mul
      (h1.add ((contDiffOn_const (c := Complex.I)).mul h2))
    simpa [Work.CR.Flat.dbarCoord] using h
  -- the perturbation term `Lcoef A u j = (i/2)·du(A z e_j)`
  have hAe : ContDiffOn ℝ ((k:ℕ):WithTop ℕ∞)
      (fun z => A z (Pi.single j (1:ℂ))) Ω := hkA.clm_apply contDiffOn_const
  have hL : ContDiffOn ℝ ((k:ℕ):WithTop ℕ∞) (fun z => Lcoef A u j z) Ω := by
    have h := (contDiffOn_const (c := (Complex.I/2))).mul (hku.clm_apply hAe)
    simpa [Lcoef] using h
  exact hcoord.add hL

end Work.NN.Core
