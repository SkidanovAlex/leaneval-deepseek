import Mathlib
import Submission.Work.RPA3.TubularDefs
import Submission.Work.RPA3.Symp

open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPA3

/-!
# Smoothness of the tubular map

The tubular parametrisation `θ(τ,x,t,ξ) = ℓ τ (x,t) + J(ξ₁ ∂_xℓ(τ)(x,t) + ξ₂ ∂_tℓ(τ)(x,t))`
is `C⁷` as soon as the family `ℓ` is `C⁸`: the family part is `C⁸`, each slice derivative loses one
order of regularity, and `J` is linear continuous.

The two slice derivatives are obtained from `ContDiff.fderiv_apply` applied to the (curried)
partial maps `(τ,x,t) ↦ ℓ τ (·,t)` and `(τ,x,t) ↦ ℓ τ (x,·)`: their Fréchet derivative at the
point in question, evaluated at `1`, *is* the one-dimensional `deriv` by
`fderiv_apply_one_eq_deriv` (which holds by `rfl`).
-/

/-- `J(q,p) = (p,-q)` bundled as a continuous linear map; its value is `Work.RPA3.J`. -/
def thetaJclm : PS →L[ℝ] PS :=
  (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ)).prod
    (-(ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ)))

@[simp] theorem thetaJclm_apply (x : PS) : thetaJclm x = J x := by
  have h : thetaJclm x = (x.2, -x.1) := rfl
  rw [h]; rfl

/-- The linear reindexing `(τ, ((x,t),ξ)) ↦ (τ, (x,t))`, used to pull the slice derivatives back to
the strip coordinates of `theta`. -/
def thetaPsi : (ℝ × PS) →L[ℝ] (ℝ × ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ PS).prod
    ((ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ)).comp (ContinuousLinearMap.snd ℝ ℝ PS))

@[simp] theorem thetaPsi_apply (w : ℝ × PS) : thetaPsi w = (w.1, w.2.1) := by
  simp [thetaPsi]

/-- The slice derivative `(τ,x,t) ↦ ∂_x ℓ τ (x,t)` is `C⁷`. -/
theorem contDiff_sliceDerivX (L : LagFamilyAll) :
    ContDiff ℝ 7 (fun p : ℝ × ℝ × ℝ => deriv (fun y => L.ℓ p.1 (y, p.2.2)) p.2.1) := by
  have hf : ContDiff ℝ 8
      (Function.uncurry (fun (x : ℝ × ℝ × ℝ) (y : ℝ) => L.ℓ x.1 (y, x.2.2))) := by
    have hΨ : ContDiff ℝ 8
        (fun q : (ℝ × ℝ × ℝ) × ℝ => ((q.1.1, (q.2, q.1.2.2)) : ℝ × (ℝ × ℝ))) := by fun_prop
    have := L.smooth.comp hΨ
    convert this using 1
    funext q
    rfl
  have hg : ContDiff ℝ 7 (fun x : ℝ × ℝ × ℝ => x.2.1) := by fun_prop
  have hk : ContDiff ℝ 7 (fun _ : ℝ × ℝ × ℝ => (1 : ℝ)) := contDiff_const
  have hmain := ContDiff.fderiv_apply
    (f := fun (x : ℝ × ℝ × ℝ) (y : ℝ) => L.ℓ x.1 (y, x.2.2)) hf hg hk (by norm_num)
  simpa only [fderiv_apply_one_eq_deriv] using hmain

/-- The slice derivative `(τ,x,t) ↦ ∂_t ℓ τ (x,t)` is `C⁷`. -/
theorem contDiff_sliceDerivT (L : LagFamilyAll) :
    ContDiff ℝ 7 (fun p : ℝ × ℝ × ℝ => deriv (fun s => L.ℓ p.1 (p.2.1, s)) p.2.2) := by
  have hf : ContDiff ℝ 8
      (Function.uncurry (fun (x : ℝ × ℝ × ℝ) (y : ℝ) => L.ℓ x.1 (x.2.1, y))) := by
    have hΨ : ContDiff ℝ 8
        (fun q : (ℝ × ℝ × ℝ) × ℝ => ((q.1.1, (q.1.2.1, q.2)) : ℝ × (ℝ × ℝ))) := by fun_prop
    have := L.smooth.comp hΨ
    convert this using 1
    funext q
    rfl
  have hg : ContDiff ℝ 7 (fun x : ℝ × ℝ × ℝ => x.2.2) := by fun_prop
  have hk : ContDiff ℝ 7 (fun _ : ℝ × ℝ × ℝ => (1 : ℝ)) := contDiff_const
  have hmain := ContDiff.fderiv_apply
    (f := fun (x : ℝ × ℝ × ℝ) (y : ℝ) => L.ℓ x.1 (x.2.1, y)) hf hg hk (by norm_num)
  simpa only [fderiv_apply_one_eq_deriv] using hmain

/-- `thetaZ` is `C⁷` in the joint variables `(τ,z)`. -/
theorem contDiff_thetaZ (L : LagFamilyAll) :
    ContDiff ℝ 7 (fun w : ℝ × PS => thetaZ L w.1 w.2) := by
  have hℓ : ContDiff ℝ 7 (fun w : ℝ × PS => L.ℓ w.1 (w.2.1.1, w.2.1.2)) := by
    have hψ : ContDiff ℝ 8 (fun w : ℝ × PS => ((w.1, w.2.1) : ℝ × (ℝ × ℝ))) := by fun_prop
    exact (L.smooth.comp hψ).of_le (by norm_num)
  have hDx : ContDiff ℝ 7
      (fun w : ℝ × PS => deriv (fun y => L.ℓ w.1 (y, w.2.1.2)) w.2.1.1) := by
    have h := ContDiff.comp_continuousLinearMap (g := thetaPsi) (contDiff_sliceDerivX L)
    simpa only [Function.comp_def, thetaPsi_apply] using h
  have hDt : ContDiff ℝ 7
      (fun w : ℝ × PS => deriv (fun s => L.ℓ w.1 (w.2.1.1, s)) w.2.1.2) := by
    have h := ContDiff.comp_continuousLinearMap (g := thetaPsi) (contDiff_sliceDerivT L)
    simpa only [Function.comp_def, thetaPsi_apply] using h
  have h1 : ContDiff ℝ 7
      (fun w : ℝ × PS => w.2.2.1 • deriv (fun y => L.ℓ w.1 (y, w.2.1.2)) w.2.1.1) :=
    (by fun_prop : ContDiff ℝ 7 (fun w : ℝ × PS => w.2.2.1)).smul hDx
  have h2 : ContDiff ℝ 7
      (fun w : ℝ × PS => w.2.2.2 • deriv (fun s => L.ℓ w.1 (w.2.1.1, s)) w.2.1.2) :=
    (by fun_prop : ContDiff ℝ 7 (fun w : ℝ × PS => w.2.2.2)).smul hDt
  have h3 : ContDiff ℝ 7 (fun w : ℝ × PS =>
      J (w.2.2.1 • deriv (fun y => L.ℓ w.1 (y, w.2.1.2)) w.2.1.1 +
         w.2.2.2 • deriv (fun s => L.ℓ w.1 (w.2.1.1, s)) w.2.1.2)) := by
    have h := thetaJclm.contDiff.comp (h1.add h2)
    simpa only [thetaJclm_apply, Function.comp_def] using h
  simp only [thetaZ, theta]
  exact hℓ.add h3

/-- The tubular map `θ(τ,x,t,ξ) = ℓ τ (x,t) + J(ξ₁ ∂_xℓ + ξ₂ ∂_tℓ)` is `C⁷` when `ℓ` is `C⁸`.

Proof: `ℓ` is `C⁸`, hence the slice derivatives `(τ,x,t) ↦ ∂_xℓ` and `(τ,x,t) ↦ ∂_tℓ` are `C⁷`
(`ContDiff.deriv` on the slices); `J` is linear continuous; `θ` is a sum of a `C⁸` map and a `C⁷`
map multiplied by the smooth scalar functions `ξ₁, ξ₂`.  `thetaZ` and `thetaP` are the same
expression in other coordinates. -/
theorem contDiff_thetaP (L : Work.RPA3.LagFamilyAll) :
    ContDiff ℝ 7 (fun w : ℝ × Work.RPA3.PS => Work.RPA3.thetaP L w) := by
  have hZ := contDiff_thetaZ L
  have := contDiff_fst.prodMk hZ
  simpa only [thetaP] using this

end Work.RPA3
