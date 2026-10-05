import Mathlib
import Submission.Work.RPA3.TubularDefs
import Submission.Work.RPA3.Symp
import Submission.Work.RPA3.contDiff_thetaP

namespace Work.RPA3

open scoped ContDiff

set_option autoImplicit false

noncomputable section

/-!
# RPA3, D2: `thetaP` is a local diffeomorphism where the four columns are independent

The map `thetaP L : ℝ × PS → ℝ × PS` is `w = (τ, ((x,t),ξ)) ↦ (τ, θ(τ,x,t,ξ))`, and
`θ(τ,x,t,ξ) = ℓ τ (x,t) + J(ξ₁ ∂_xℓ + ξ₂ ∂_tℓ)`.  Its derivative at `w` is block triangular,
with the first diagonal block `1` (the `τ`-coordinate is fixed) and the second diagonal block the
derivative `D_z(thetaZ)` of `Z ↦ θ(τ,Z)` at `Z = ((x,t),ξ)`, whose matrix in the basis
`(1,0), (0,1), (1,0), (0,1)` of `PS = (ℝ×ℝ) × (ℝ×ℝ)` is the four columns
`∂_xθ, ∂_tθ, ∂_{ξ₁}θ, ∂_{ξ₂}θ` of `ColumnsIndependent L τ x t ξ`.
Indeed, evaluating `fderiv ℝ (fun Z => thetaZ L τ Z) Z` along the four coordinate lines (which is
`deriv` of the restriction to the line, by `DifferentiableAt.lineDeriv_eq_fderiv`) gives exactly
those four partial derivatives, and `fderiv` is linear.

Hence, if those four columns are independent, the derivative of `thetaP L` at `w` is injective;
on the finite-dimensional space `ℝ × PS` an injective linear endomorphism is bijective, and a
bijective continuous linear map between complete spaces is a continuous linear equivalence
(`ContinuousLinearEquiv.ofBijective`).  The `HasFDerivAt` statement is transported through the
coercion with `ContinuousLinearEquiv.coe_ofBijective`.
-/

/-- The Fréchet derivative evaluated along a line is the derivative of the restriction of the map
to that line. -/
private lemma fderiv_apply_eq_deriv_line {F : PS → PS} {z v : PS} (hd : DifferentiableAt ℝ F z) :
    fderiv ℝ F z v = deriv (fun t : ℝ => F (z + t • v)) 0 := by
  rw [← DifferentiableAt.lineDeriv_eq_fderiv hd]
  rfl

/-- Shifting the origin in a one-dimensional derivative: `deriv (f (c + ·)) 0 = deriv f c`. -/
private lemma deriv_const_add_zero (f : ℝ → PS) (c : ℝ) :
    deriv (fun t : ℝ => f (c + t)) 0 = deriv f c := by
  have h : (fun t : ℝ => f (c + t)) = fun t : ℝ => f (t + c) := by
    funext t; rw [add_comm]
  rw [h, deriv_comp_add_const]
  simp

/-- `Z ↦ thetaZ L τ Z` is differentiable (it is `thetaZ L` with the first variable frozen, and
`thetaZ L` is `C⁷` in the joint variables by `contDiff_thetaZ`). -/
private lemma differentiableAt_thetaZ_fixed (L : LagFamilyAll) (τ : ℝ) (Z : PS) :
    DifferentiableAt ℝ (fun Z : PS => thetaZ L τ Z) Z := by
  have hdiff : Differentiable ℝ (fun w : ℝ × PS => thetaZ L w.1 w.2) :=
    (contDiff_thetaZ L).differentiable (by norm_num)
  have hpair : HasFDerivAt (fun Z : PS => (τ, Z))
      ((0 : PS →L[ℝ] ℝ).prod (1 : PS →L[ℝ] PS)) Z :=
    (hasFDerivAt_const τ Z).prodMk (hasFDerivAt_id Z)
  exact ((hdiff.differentiableAt.hasFDerivAt).comp Z hpair).differentiableAt

/-- The `x`-column of the derivative of `Z ↦ θ(τ,Z)`: `∂_xθ`. -/
private lemma fderiv_thetaZ_eX (L : LagFamilyAll) (τ x t : ℝ) (ξ : ℝ × ℝ) :
    fderiv ℝ (fun Z : PS => thetaZ L τ Z) ((x, t), ξ) (((1 : ℝ), 0), (0 : ℝ × ℝ))
      = deriv (fun y => theta L τ y t ξ) x := by
  rw [fderiv_apply_eq_deriv_line (differentiableAt_thetaZ_fixed L τ _)]
  have hfun : (fun s : ℝ => thetaZ L τ (((x, t), ξ) + s • (((1 : ℝ), 0), (0 : ℝ × ℝ))))
      = fun s : ℝ => (fun y => theta L τ y t ξ) (x + s) := by
    funext s; simp [thetaZ]
  rw [hfun]
  exact deriv_const_add_zero (fun y => theta L τ y t ξ) x

/-- The `t`-column of the derivative of `Z ↦ θ(τ,Z)`: `∂_tθ`. -/
private lemma fderiv_thetaZ_eT (L : LagFamilyAll) (τ x t : ℝ) (ξ : ℝ × ℝ) :
    fderiv ℝ (fun Z : PS => thetaZ L τ Z) ((x, t), ξ) (((0 : ℝ), 1), (0 : ℝ × ℝ))
      = deriv (fun s => theta L τ x s ξ) t := by
  rw [fderiv_apply_eq_deriv_line (differentiableAt_thetaZ_fixed L τ _)]
  have hfun : (fun s : ℝ => thetaZ L τ (((x, t), ξ) + s • (((0 : ℝ), 1), (0 : ℝ × ℝ))))
      = fun s : ℝ => (fun y => theta L τ x y ξ) (t + s) := by
    funext s; simp [thetaZ]
  rw [hfun]
  exact deriv_const_add_zero (fun y => theta L τ x y ξ) t

/-- The `ξ₁`-column of the derivative of `Z ↦ θ(τ,Z)`: `∂_{ξ₁}θ`. -/
private lemma fderiv_thetaZ_eξ1 (L : LagFamilyAll) (τ x t : ℝ) (ξ : ℝ × ℝ) :
    fderiv ℝ (fun Z : PS => thetaZ L τ Z) ((x, t), ξ) (((0 : ℝ × ℝ), ((1 : ℝ), 0)))
      = deriv (fun u => theta L τ x t (u, ξ.2)) ξ.1 := by
  rw [fderiv_apply_eq_deriv_line (differentiableAt_thetaZ_fixed L τ _)]
  have hfun : (fun s : ℝ => thetaZ L τ (((x, t), ξ) + s • (((0 : ℝ × ℝ), ((1 : ℝ), 0)))))
      = fun s : ℝ => (fun u => theta L τ x t (u, ξ.2)) (ξ.1 + s) := by
    funext s
    have harg' : (((x, t), ξ) + s • (((0 : ℝ × ℝ), ((1 : ℝ), 0)))) = ((x, t), (ξ.1 + s, ξ.2)) := by
      ext <;> simp
    simp only [thetaZ, harg']
  rw [hfun]
  exact deriv_const_add_zero (fun u => theta L τ x t (u, ξ.2)) ξ.1

/-- The `ξ₂`-column of the derivative of `Z ↦ θ(τ,Z)`: `∂_{ξ₂}θ`. -/
private lemma fderiv_thetaZ_eξ2 (L : LagFamilyAll) (τ x t : ℝ) (ξ : ℝ × ℝ) :
    fderiv ℝ (fun Z : PS => thetaZ L τ Z) ((x, t), ξ) (((0 : ℝ × ℝ), ((0 : ℝ), 1)))
      = deriv (fun u => theta L τ x t (ξ.1, u)) ξ.2 := by
  rw [fderiv_apply_eq_deriv_line (differentiableAt_thetaZ_fixed L τ _)]
  have hfun : (fun s : ℝ => thetaZ L τ (((x, t), ξ) + s • (((0 : ℝ × ℝ), ((0 : ℝ), 1)))))
      = fun s : ℝ => (fun u => theta L τ x t (ξ.1, u)) (ξ.2 + s) := by
    funext s
    have harg' : (((x, t), ξ) + s • (((0 : ℝ × ℝ), ((0 : ℝ), 1)))) = ((x, t), (ξ.1, ξ.2 + s)) := by
      ext <;> simp
    simp only [thetaZ, harg']
  rw [hfun]
  exact deriv_const_add_zero (fun u => theta L τ x t (ξ.1, u)) ξ.2

/-- The derivative of `Z ↦ θ(τ,Z)` at `Z = ((x,t),ξ)`, evaluated at an arbitrary `v : PS`: the
linear combination of the four columns with the coordinates of `v`. -/
private lemma fderiv_thetaZ_apply (L : LagFamilyAll) (τ x t : ℝ) (ξ : ℝ × ℝ) (v : PS) :
    fderiv ℝ (fun Z : PS => thetaZ L τ Z) ((x, t), ξ) v
      = v.1.1 • deriv (fun y => theta L τ y t ξ) x
      + v.1.2 • deriv (fun s => theta L τ x s ξ) t
      + v.2.1 • deriv (fun u => theta L τ x t (u, ξ.2)) ξ.1
      + v.2.2 • deriv (fun u => theta L τ x t (ξ.1, u)) ξ.2 := by
  have hdecomp : v = v.1.1 • (((1 : ℝ), 0), (0 : ℝ × ℝ))
      + v.1.2 • (((0 : ℝ), 1), (0 : ℝ × ℝ))
      + v.2.1 • (((0 : ℝ × ℝ), ((1 : ℝ), 0)))
      + v.2.2 • (((0 : ℝ × ℝ), ((0 : ℝ), 1))) := by
    ext <;> simp
  conv_lhs => rw [hdecomp]
  simp only [map_add, map_smul, fderiv_thetaZ_eX, fderiv_thetaZ_eT, fderiv_thetaZ_eξ1,
    fderiv_thetaZ_eξ2]

/-- **D2, the tubular map is a local diffeomorphism.**  If the four columns of the derivative of
`θ` are independent at `(τ,x,t,ξ)` (hypothesis `hind`, available on the strip from
`theta_columns_independent`), then the derivative of `thetaP L` at `w = (τ,((x,t),ξ))` is an
invertible continuous linear map, i.e. `IsLocDiffeoAt L w`.

Proof: the derivative of `thetaP L : ℝ × PS → ℝ × PS` at `w` is block triangular with diagonal
blocks `1` and `D_z(thetaZ)`, where `D_z(thetaZ)` maps `(a,b,η)` to
`a ∂_xθ + b ∂_tθ + η₁ ∂_{ξ₁}θ + η₂ ∂_{ξ₂}θ`, injective by `hind`.  An injective linear map between
finite-dimensional spaces of the same dimension is bijective, and `HasFDerivAt` of `thetaP` comes
from `ContDiff ℝ 7 (thetaP L)`.  Finish with `ContinuousLinearMap.linearEquivOfInjective` or
`ContinuousLinearEquiv.ofBijective` (or `LinearEquiv.ofInjective` plus continuity of the inverse in
finite dimension). -/
theorem thetaP_hasFDerivAt_equiv (L : Work.RPA3.LagFamilyAll) (ε : ℝ)
    (hind : ∀ τ ∈ Set.Icc (-1 : ℝ) 2, ∀ x t, |x| ≤ L.X0 + 1 → ∀ ξ : ℝ × ℝ, ‖ξ‖ < ε →
      Work.RPA3.ColumnsIndependent L τ x t ξ)
    (w : ℝ × Work.RPA3.PS) (hτ : w.1 ∈ Set.Icc (-1 : ℝ) 2) (hx : |w.2.1.1| ≤ L.X0 + 1)
    (hξ : ‖w.2.2‖ < ε) : Work.RPA3.IsLocDiffeoAt L w := by
  -- `thetaZ L` is `C⁷` in the joint variables, hence differentiable at `w`
  have hGdiff : DifferentiableAt ℝ (fun w' : ℝ × PS => thetaZ L w'.1 w'.2) w :=
    ((contDiff_thetaZ L).differentiable (by norm_num)).differentiableAt
  -- the affine map `Z ↦ (w.1, Z)` is linear with derivative `0 × id`
  have hpair : HasFDerivAt (fun Z : PS => (w.1, Z))
      ((0 : PS →L[ℝ] ℝ).prod (1 : PS →L[ℝ] PS)) w.2 :=
    (hasFDerivAt_const w.1 w.2).prodMk (hasFDerivAt_id w.2)
  have hcomp := (hGdiff.hasFDerivAt).comp w.2 hpair
  have hcomp' : HasFDerivAt (fun Z : PS => thetaZ L w.1 Z)
      ((fderiv ℝ (fun w' : ℝ × PS => thetaZ L w'.1 w'.2) w).comp
        ((0 : PS →L[ℝ] ℝ).prod (1 : PS →L[ℝ] PS))) w.2 := by
    simpa only [Function.comp_def] using hcomp
  -- hence the frozen derivative is the derivative of `thetaZ L` restricted to `{w.1} × PS`
  have hchain : fderiv ℝ (fun Z : PS => thetaZ L w.1 Z) w.2
      = (fderiv ℝ (fun w' : ℝ × PS => thetaZ L w'.1 w'.2) w).comp
        ((0 : PS →L[ℝ] ℝ).prod (1 : PS →L[ℝ] PS)) :=
    hcomp'.fderiv
  -- the derivative of `thetaP L` at `w`
  have hThetaP : HasFDerivAt (thetaP L)
      ((ContinuousLinearMap.fst ℝ ℝ PS).prod
        (fderiv ℝ (fun w' : ℝ × PS => thetaZ L w'.1 w'.2) w)) w := by
    have h2 : HasFDerivAt (fun w' : ℝ × PS => (w'.1, thetaZ L w'.1 w'.2))
        ((ContinuousLinearMap.fst ℝ ℝ PS).prod
          (fderiv ℝ (fun w' : ℝ × PS => thetaZ L w'.1 w'.2) w)) w :=
      (ContinuousLinearMap.fst ℝ ℝ PS).hasFDerivAt.prodMk hGdiff.hasFDerivAt
    exact h2
  -- that derivative is injective: the first block is the identity, the second is the matrix of
  -- the four columns, which is injective by `hind`
  have hDker : ∀ v : ℝ × PS,
      ((ContinuousLinearMap.fst ℝ ℝ PS).prod
        (fderiv ℝ (fun w' : ℝ × PS => thetaZ L w'.1 w'.2) w)) v = 0 → v = 0 := by
    intro v hv
    have hv1 : v.1 = 0 := by
      have := congrArg Prod.fst hv
      simpa [ContinuousLinearMap.prod_apply] using this
    have hv2 : v.2 = 0 := by
      have h2 : fderiv ℝ (fun w' : ℝ × PS => thetaZ L w'.1 w'.2) w v = 0 := by
        have := congrArg Prod.snd hv
        simpa [ContinuousLinearMap.prod_apply] using this
      have hv_eq : v = (0, v.2) := Prod.ext hv1 rfl
      rw [hv_eq] at h2
      have hzero : ((0 : PS →L[ℝ] ℝ).prod (1 : PS →L[ℝ] PS)) v.2 = (0, v.2) := by
        rw [ContinuousLinearMap.prod_apply]
        simp
      have hchain_apply : fderiv ℝ (fun w' : ℝ × PS => thetaZ L w'.1 w'.2) w (0, v.2)
          = fderiv ℝ (fun Z : PS => thetaZ L w.1 Z) w.2 v.2 := by
        calc fderiv ℝ (fun w' : ℝ × PS => thetaZ L w'.1 w'.2) w (0, v.2)
            = ((fderiv ℝ (fun w' : ℝ × PS => thetaZ L w'.1 w'.2) w).comp
                ((0 : PS →L[ℝ] ℝ).prod (1 : PS →L[ℝ] PS))) v.2 := by
                rw [ContinuousLinearMap.comp_apply, hzero]
          _ = fderiv ℝ (fun Z : PS => thetaZ L w.1 Z) w.2 v.2 := by rw [← hchain]
      rw [hchain_apply] at h2
      have hform : fderiv ℝ (fun Z : PS => thetaZ L w.1 Z) w.2 v.2
          = v.2.1.1 • deriv (fun y => theta L w.1 y w.2.1.2 w.2.2) w.2.1.1
          + v.2.1.2 • deriv (fun s => theta L w.1 w.2.1.1 s w.2.2) w.2.1.2
          + v.2.2.1 • deriv (fun u => theta L w.1 w.2.1.1 w.2.1.2 (u, w.2.2.2)) w.2.2.1
          + v.2.2.2 • deriv (fun u => theta L w.1 w.2.1.1 w.2.1.2 (w.2.2.1, u)) w.2.2.2 :=
        fderiv_thetaZ_apply L w.1 w.2.1.1 w.2.1.2 w.2.2 v.2
      rw [hform] at h2
      obtain ⟨ha, hb, hc, hd⟩ := hind w.1 hτ w.2.1.1 w.2.1.2 hx w.2.2 hξ
        v.2.1.1 v.2.1.2 v.2.2.1 v.2.2.2 h2
      exact Prod.ext (Prod.ext ha hb) (Prod.ext hc hd)
    exact Prod.ext hv1 hv2
  have hinj : Function.Injective
      ((ContinuousLinearMap.fst ℝ ℝ PS).prod
        (fderiv ℝ (fun w' : ℝ × PS => thetaZ L w'.1 w'.2) w)) := by
    intro v v' hvv
    have h0 : ((ContinuousLinearMap.fst ℝ ℝ PS).prod
        (fderiv ℝ (fun w' : ℝ × PS => thetaZ L w'.1 w'.2) w)) (v - v') = 0 := by
      rw [map_sub, hvv, sub_self]
    exact sub_eq_zero.mp (hDker (v - v') h0)
  -- an injective endomorphism of a finite-dimensional space is bijective, hence a continuous
  -- linear equivalence
  refine ⟨ContinuousLinearEquiv.ofBijective _ (LinearMap.ker_eq_bot.mpr hinj) ?_, ?_⟩
  · exact LinearMap.range_eq_top.mpr
      ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hinj)
  · rw [ContinuousLinearEquiv.coe_ofBijective]
    exact hThetaP

end

end Work.RPA3
