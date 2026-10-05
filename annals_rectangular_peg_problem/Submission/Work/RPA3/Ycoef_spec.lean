import Mathlib
import Submission.Work.RPA3.follow_family_defs

/-!
# RPA3, D3 (follow the family): the coefficient identity `Ycoef_spec`

`Ycoef L H τ x t` is the Gram-inverse of the pair `(∂_xℓ, ∂_tℓ)` applied to the pairings of the
defect `W = X_H ∘ ℓ - ∂_τℓ`; it is therefore the coefficient vector of the orthogonal projection
of `W` onto the (Lagrangian) plane `span(∂_xℓ, ∂_tℓ)`.  The content of `Ycoef_spec` is that this
projection already *is* `W`, i.e. that `W` lies in the plane.

The two hypotheses `hgen` say that the directional derivatives of `H` along the family equal the
symplectic pairings with `∂_τℓ`.  Combined with `ω(X_H, v) = -dH(v)` (`symp_hamVF`) this gives the
`ω`-orthogonality of `W` to `∂_xℓ` and to `∂_tℓ`; since `span(∂_xℓ, ∂_tℓ)` is Lagrangian
(`LagFamilyAll.lag`, `LagFamilyAll.imm`), `lagrangian_orthogonal` puts `W` in the plane, and the
Gram formula reproduces it.

The only analytic input is the chain rule identifying `dH(∂_xℓ)` with `deriv (H ∘ ℓ)`; this is
`fderiv_H_slice_dX` / `fderiv_H_slice_dT` below.
-/

open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPA3

/-- Chain rule along the `x`-direction of the family: `dH(∂_xℓ)` is the derivative of
`s ↦ H τ (ℓ τ (x+s, t))` at `0`. -/
theorem fderiv_H_slice_dX (H : ℝ → PS → ℝ)
    (hH : ContDiff ℝ 4 (fun z : ℝ × PS => H z.1 z.2))
    (L : LagFamilyAll) (τ x t : ℝ) :
    fderiv ℝ (H τ) (L.ℓ τ (x, t)) (dX L τ x t)
      = deriv (fun s => H τ (L.ℓ τ (x + s, t))) 0 := by
  have hHdiff : DifferentiableAt ℝ (H τ) (L.ℓ τ (x, t)) := by
    have hF : DifferentiableAt ℝ (fun z : ℝ × PS => H z.1 z.2) (τ, L.ℓ τ (x, t)) :=
      hH.differentiable (by norm_num) |>.differentiableAt
    have hs : DifferentiableAt ℝ (fun y : PS => (τ, y)) (L.ℓ τ (x, t)) := by fun_prop
    have := hF.comp (L.ℓ τ (x, t)) hs
    simpa [Function.comp_def] using this
  have hcurve : HasDerivAt (fun s : ℝ => L.ℓ τ (x + s, t)) (dX L τ x t) 0 := by
    have hdiff : DifferentiableAt ℝ (fun y : ℝ => L.ℓ τ (y, t)) x := by
      have hF : DifferentiableAt ℝ (fun z : ℝ × (ℝ × ℝ) => L.ℓ z.1 z.2) (τ, (x, t)) :=
        L.smooth.differentiable (by norm_num) |>.differentiableAt
      have hs : DifferentiableAt ℝ (fun y : ℝ => (τ, (y, t))) x := by fun_prop
      have := hF.comp x hs
      simpa [Function.comp_def] using this
    have hl : HasFDerivAt (fun y : ℝ => L.ℓ τ (y, t))
        (fderiv ℝ (fun y : ℝ => L.ℓ τ (y, t)) x) (x + 0) := by
      simpa using hdiff.hasFDerivAt
    have hinner : HasDerivAt (fun s : ℝ => x + s) 1 0 := (hasDerivAt_id (0:ℝ)).const_add x
    have h := hl.comp_hasDerivAt 0 hinner
    simpa [dX, Function.comp_def, fderiv_apply_one_eq_deriv] using h
  have hl2 : HasFDerivAt (H τ) (fderiv ℝ (H τ) (L.ℓ τ (x, t))) (L.ℓ τ (x + 0, t)) := by
    simpa using hHdiff.hasFDerivAt
  have hcomp := hl2.comp_hasDerivAt 0 hcurve
  have := hcomp.deriv
  simpa [Function.comp_def] using this.symm

/-- Chain rule along the `t`-direction of the family: `dH(∂_tℓ)` is the derivative of
`s ↦ H τ (ℓ τ (x, t+s))` at `0`. -/
theorem fderiv_H_slice_dT (H : ℝ → PS → ℝ)
    (hH : ContDiff ℝ 4 (fun z : ℝ × PS => H z.1 z.2))
    (L : LagFamilyAll) (τ x t : ℝ) :
    fderiv ℝ (H τ) (L.ℓ τ (x, t)) (dT L τ x t)
      = deriv (fun s => H τ (L.ℓ τ (x, t + s))) 0 := by
  have hHdiff : DifferentiableAt ℝ (H τ) (L.ℓ τ (x, t)) := by
    have hF : DifferentiableAt ℝ (fun z : ℝ × PS => H z.1 z.2) (τ, L.ℓ τ (x, t)) :=
      hH.differentiable (by norm_num) |>.differentiableAt
    have hs : DifferentiableAt ℝ (fun y : PS => (τ, y)) (L.ℓ τ (x, t)) := by fun_prop
    have := hF.comp (L.ℓ τ (x, t)) hs
    simpa [Function.comp_def] using this
  have hcurve : HasDerivAt (fun s : ℝ => L.ℓ τ (x, t + s)) (dT L τ x t) 0 := by
    have hdiff : DifferentiableAt ℝ (fun y : ℝ => L.ℓ τ (x, y)) t := by
      have hF : DifferentiableAt ℝ (fun z : ℝ × (ℝ × ℝ) => L.ℓ z.1 z.2) (τ, (x, t)) :=
        L.smooth.differentiable (by norm_num) |>.differentiableAt
      have hs : DifferentiableAt ℝ (fun y : ℝ => (τ, (x, y))) t := by fun_prop
      have := hF.comp t hs
      simpa [Function.comp_def] using this
    have hl : HasFDerivAt (fun y : ℝ => L.ℓ τ (x, y))
        (fderiv ℝ (fun y : ℝ => L.ℓ τ (x, y)) t) (t + 0) := by
      simpa using hdiff.hasFDerivAt
    have hinner : HasDerivAt (fun s : ℝ => t + s) 1 0 := (hasDerivAt_id (0:ℝ)).const_add t
    have h := hl.comp_hasDerivAt 0 hinner
    simpa [dT, Function.comp_def, fderiv_apply_one_eq_deriv] using h
  have hl2 : HasFDerivAt (H τ) (fderiv ℝ (H τ) (L.ℓ τ (x, t))) (L.ℓ τ (x, t + 0)) := by
    simpa using hHdiff.hasFDerivAt
  have hcomp := hl2.comp_hasDerivAt 0 hcurve
  have := hcomp.deriv
  simpa [Function.comp_def] using this.symm

/-- The defect `W = X_H ∘ ℓ - ∂_τℓ` is `ω`-orthogonal to `∂_xℓ`. -/
theorem symp_Wvec_dX (L : LagFamilyAll) (H : ℝ → PS → ℝ)
    (hH : ContDiff ℝ 4 (fun z : ℝ × PS => H z.1 z.2))
    (hgen : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x t,
      deriv (fun s => H τ (L.ℓ τ (x + s, t))) 0 =
        -symp (dTau L τ x t) (dX L τ x t) ∧
      deriv (fun s => H τ (L.ℓ τ (x, t + s))) 0 =
        -symp (dTau L τ x t) (dT L τ x t))
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (x t : ℝ) :
    symp (Wvec L H τ x t) (dX L τ x t) = 0 := by
  have hder : deriv (fun s => H τ (L.ℓ τ (x + s, t))) 0
      = -symp (dTau L τ x t) (dX L τ x t) := (hgen τ hτ x t).1
  have hc := fderiv_H_slice_dX H hH L τ x t
  rw [Wvec, symp_sub_left, symp_hamVF, hc, hder]
  ring

/-- The defect `W = X_H ∘ ℓ - ∂_τℓ` is `ω`-orthogonal to `∂_tℓ`. -/
theorem symp_Wvec_dT (L : LagFamilyAll) (H : ℝ → PS → ℝ)
    (hH : ContDiff ℝ 4 (fun z : ℝ × PS => H z.1 z.2))
    (hgen : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x t,
      deriv (fun s => H τ (L.ℓ τ (x + s, t))) 0 =
        -symp (dTau L τ x t) (dX L τ x t) ∧
      deriv (fun s => H τ (L.ℓ τ (x, t + s))) 0 =
        -symp (dTau L τ x t) (dT L τ x t))
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (x t : ℝ) :
    symp (Wvec L H τ x t) (dT L τ x t) = 0 := by
  have hder : deriv (fun s => H τ (L.ℓ τ (x, t + s))) 0
      = -symp (dTau L τ x t) (dT L τ x t) := (hgen τ hτ x t).2
  have hc := fderiv_H_slice_dT H hH L τ x t
  rw [Wvec, symp_sub_left, symp_hamVF, hc, hder]
  ring

theorem Ycoef_spec (L : LagFamilyAll) (H : ℝ → PS → ℝ)
    (hH : ContDiff ℝ 4 (fun z : ℝ × PS => H z.1 z.2))
    (hgen : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x t,
      deriv (fun s => H τ (L.ℓ τ (x + s, t))) 0 =
        -symp (dTau L τ x t) (dX L τ x t) ∧
      deriv (fun s => H τ (L.ℓ τ (x, t + s))) 0 =
        -symp (dTau L τ x t) (dT L τ x t))
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (x t : ℝ) :
    (Ycoef L H τ x t).1 • dX L τ x t + (Ycoef L H τ x t).2 • dT L τ x t
      = Wvec L H τ x t := by
  have hWX : symp (Wvec L H τ x t) (dX L τ x t) = 0 := symp_Wvec_dX L H hH hgen τ hτ x t
  have hWT : symp (Wvec L H τ x t) (dT L τ x t) = 0 := symp_Wvec_dT L H hH hgen τ hτ x t
  have hind : ∀ a b : ℝ, a • dX L τ x t + b • dT L τ x t = 0 → a = 0 ∧ b = 0 :=
    fun a b h => L.imm τ x t a b h
  have hlag : symp (dX L τ x t) (dT L τ x t) = 0 := L.lag τ x t
  obtain ⟨a, b, hab⟩ :=
    lagrangian_orthogonal (dX L τ x t) (dT L τ x t) hind hlag (Wvec L H τ x t) hWX hWT
  have hipX : ip (Wvec L H τ x t) (dX L τ x t)
      = a * gramA L τ x t + b * gramB L τ x t := by
    rw [hab, gramA, gramB, ip_add_left, ip_smul_left, ip_smul_left,
      ip_comm (dT L τ x t) (dX L τ x t)]
  have hipT : ip (Wvec L H τ x t) (dT L τ x t)
      = a * gramB L τ x t + b * gramC L τ x t := by
    rw [hab, gramB, gramC, ip_add_left, ip_smul_left, ip_smul_left]
  have hdet : gramDet L τ x t ≠ 0 := (gramDet_pos L τ x t).ne'
  have h1 : (Ycoef L H τ x t).1 = a := by
    simp only [Ycoef]
    rw [hipX, hipT]
    rw [div_eq_iff hdet]
    simp only [gramDet]
    ring
  have h2 : (Ycoef L H τ x t).2 = b := by
    simp only [Ycoef]
    rw [hipX, hipT]
    rw [div_eq_iff hdet]
    simp only [gramDet]
    ring
  rw [h1, h2]
  exact hab.symm

end Work.RPA3
