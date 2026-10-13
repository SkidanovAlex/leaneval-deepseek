/-
Copyright: work module for the Elgindi finite-time singularity project.

# Auxiliary vocabulary for the estimate `|F_*(z)·sin 2θ|_{H^k} ≤ C_k |F|_{H^k}`

This module collects the two definitions shared by the proof of

  `Work.FTS.EllipticEst.Fstar_Hk_le`:
`|F_*(F)·sin 2θ|_{H^k} ≤ C_k |F|_{H^k}` for `0 < α ≤ 1`, `C_k` independent of `α`.

The point of the estimate is that `F_*(z) = ∫_0^{π/2} F(z,θ) sinθ cos²θ dθ` is a
*radial* function, so that the product `F_*(z)·sin 2θ` is of the separated form
`φ(z)·χ(θ)`.  Both `D_z = z∂_z` and `D_θ = sin(2θ)∂_θ` then act on the two factors
separately:

* `D_θ^j (φ(z)·χ(θ)) = φ(z)·(D_θ^j χ)(θ)`, so the angular factor of the `j`-th
  angular derivative is `D_θ^j (sin 2θ)` — recorded as the function `sinProf j`;
* `D_z^j (φ(z)·χ(θ)) = (z∂_z)^j φ(z)·χ(θ)`, and the radial coefficient `(z∂_z)^j φ`
  turns out to be the *angular moment of the `j`-th `D_z`-derivative of `F`*,
  `PsiInt F j z = ∫_0^{π/2} D_z^j F(z,θ) sinθcos²θ dθ` (`DzIter_PsiInt_mul` in
  `DzIterPsiIntMul`).  Applying Cauchy–Schwarz to that moment
  (`PsiInt_sq_mul_w_le`) is the whole radial content of the estimate; the angular
  content is the boundedness of `sinProf j·sin(2θ)^{-γ/2}` (`SinProfSqRpowLe`).

## Main definitions

* `sinProf i θ = D_θ^i (sin 2θ)` (the angular profile).
* `PsiInt u j z = ∫_θ D_z^j u z θ · sinθ cos²θ dθ` (the radial moment).

## Main auxiliary results (proved elsewhere, all under this namespace)

* `SinProfSqRpowLe.sinProf_sq_mul_rpow_le`
* `PsiIntHasDerivAt.hasDerivAt_PsiInt`
* `DzIterPsiIntMul.DzIter_PsiInt_mul`
* `PsiIntSqMulWLe.PsiInt_sq_mul_w_le`
* `zTermEqOn.zTerm_eq_on`, `mixedTermEqOn.mixedTerm_eq_on`
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The angular profile `D_θ^i (sin 2θ)` -/

/-- `D_θ^i (sin 2θ)`: the angular profile of `D_z^j D_θ^i (φ(z)·sin 2θ)`. -/
def sinProf (i : ℕ) (θ : ℝ) : ℝ :=
  Work.Spaces.DthIter i (fun _ θ' => Real.sin (2 * θ')) 0 θ

@[simp] theorem sinProf_zero (θ : ℝ) : sinProf 0 θ = Real.sin (2 * θ) := by
  simp [sinProf]

/-! ## `D_θ` ignores a radial factor -/

/-- `D_θ (φ(z)·χ(z,θ)) = φ(z)·D_θ χ(z,θ)`: the operator `D_θ` sees only the angular
variable, and a factor depending on `z` alone passes through unchanged. -/
theorem Dth_radial_mul (φ : ℝ → ℝ) (χ : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => φ z * χ z θ) = fun z θ => φ z * Work.Spaces.Dth χ z θ := by
  funext z θ
  have h : deriv (fun θ' => φ z * χ z θ') θ = φ z * deriv (fun θ' => χ z θ') θ :=
    deriv_const_mul_field (φ z) (v := fun θ' => χ z θ')
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [h]
  ring

/-- Iterated form of `Dth_radial_mul`. -/
theorem DthIter_radial_mul (φ : ℝ → ℝ) (χ : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun z θ => φ z * χ z θ)
      = fun z θ => φ z * Work.Spaces.DthIter i χ z θ := by
  induction i with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
      exact Dth_radial_mul φ (Work.Spaces.DthIter n χ)

/-- A function of the angle alone has a `D_θ`-iterate which does not depend on `z`. -/
theorem DthIter_z_indep (h : ℝ → ℝ) (i : ℕ) :
    ∀ z θ : ℝ, Work.Spaces.DthIter i (fun _ θ' => h θ') z θ
      = Work.Spaces.DthIter i (fun _ θ' => h θ') 0 θ := by
  induction i with
  | zero => intro z θ; rfl
  | succ n ih =>
      intro z θ
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      have hfun : (fun θ' => Work.Spaces.DthIter n (fun _ θ' => h θ') z θ')
          = (fun θ' => Work.Spaces.DthIter n (fun _ θ' => h θ') 0 θ') :=
        funext (fun θ' => ih z θ')
      rw [hfun]

/-- The angular profile of the concrete function `fun z θ => Real.sin (2*θ)` is
`sinProf i`. -/
theorem DthIter_sin_eq_sinProf (i : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter i (fun z θ => Real.sin (2 * θ)) z θ = sinProf i θ := by
  have h := DthIter_z_indep (fun θ => Real.sin (2 * θ)) i z θ
  simpa [sinProf] using h

/-! ## The radial moment `∫_θ D_z^j u z θ · sinθcos²θ dθ` -/

/-- The `j`-th radial moment of `u`: `PsiInt u j z = ∫_θ D_z^j u z θ · sinθcos²θ dθ`.
For `j = 0` this is the angular moment `F_*` (`PsiInt_eq_Fstar`); for `j ≥ 1` it is the
radial coefficient of `D_z^j (F_*·χ)` (`DzIter_PsiInt_mul`). -/
def PsiInt (u : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.Spaces.DzIter j u z θ * Work.Elliptic.sinCos2 θ

theorem PsiInt_eq_Fstar (u : ℝ → ℝ → ℝ) (z : ℝ) :
    PsiInt u 0 z = Work.Elliptic.Fstar u z := rfl

end Work.FTS.EllipticEst
