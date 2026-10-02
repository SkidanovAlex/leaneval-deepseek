import Mathlib
import Submission.Work.PTGeometric.FDerivInChart

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.PTGeometric

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

noncomputable section

/-- **The coordinate `y ↦ y.1 0` is differentiable at every point of the half-space**, including
boundary points, with `EuclideanHalfSpace N` carrying its model structure
`modelWithCornersEuclideanHalfSpace N`.  It is the composite of `coordFun N` with
`Subtype.val = ⇑(extChartAt _ x)` (the preferred chart is the inclusion), using
`contMDiffAt_extChartAt`. -/
theorem mdifferentiableAt_halfSpace_coord {N : ℕ} [NeZero N] (x : EuclideanHalfSpace N) :
    MDifferentiableAt (modelWithCornersEuclideanHalfSpace N) (modelWithCornersSelf ℝ ℝ)
      (fun y : EuclideanHalfSpace N => y.1 0) x := by
  have hsub : MDifferentiableAt (modelWithCornersEuclideanHalfSpace N)
      (𝓘(ℝ, EuclideanSpace ℝ (Fin N))) (fun y : EuclideanHalfSpace N => y.1) x := by
    have h := contMDiffAt_extChartAt (I := modelWithCornersEuclideanHalfSpace N) (x := x)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
    have hfun : (↑(extChartAt (modelWithCornersEuclideanHalfSpace N) x) :
        EuclideanHalfSpace N → EuclideanSpace ℝ (Fin N)) = fun y => y.1 := by
      funext y; rfl
    rw [hfun] at h
    exact h.mdifferentiableAt (by simp)
  have hcf : MDifferentiableAt (𝓘(ℝ, EuclideanSpace ℝ (Fin N))) (𝓘(ℝ,ℝ))
      (⇑(coordFun N)) (x.1) :=
    (ContinuousLinearMap.hasFDerivAt (coordFun N) (x := x.1)).differentiableAt.mdifferentiableAt
  exact hcf.comp x hsub

/-- **The chain rule for `f ∘ (coordinate)` at a boundary point.**  For a smooth `f : ℝ → ℝ` and a
boundary point `x` (`x.1 0 = 0`) of the half-space,
`mfderiv (y ↦ f (y.1 0)) x = deriv f 0 • mfderiv (y ↦ y.1 0) x`.

(This is the chain rule `mfderiv_comp_apply` together with `deriv f 0 = (fderiv ℝ f 0) 1`; the
value `f 0` is irrelevant, as it should be.) -/
theorem mfderiv_chain_coord {N : ℕ} [NeZero N] (f : ℝ → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) {x : EuclideanHalfSpace N}
    (hx : x.1 0 = 0) :
    mfderiv (modelWithCornersEuclideanHalfSpace N) (modelWithCornersSelf ℝ ℝ)
        (fun y : EuclideanHalfSpace N => f (y.1 0)) x
      = deriv f 0 • mfderiv (modelWithCornersEuclideanHalfSpace N) (modelWithCornersSelf ℝ ℝ)
          (fun y : EuclideanHalfSpace N => y.1 0) x := by
  have hcoord := mdifferentiableAt_halfSpace_coord (N := N) x
  have hfm : MDifferentiableAt (𝓘(ℝ,ℝ)) (𝓘(ℝ,ℝ)) f
      ((fun y : EuclideanHalfSpace N => y.1 0) x) :=
    hf.contMDiff.mdifferentiableAt (by simp)
  have hLf : mfderiv (𝓘(ℝ,ℝ)) (𝓘(ℝ,ℝ)) f 0 = deriv f 0 • (1 : ℝ →L[ℝ] ℝ) := by
    rw [mfderiv_eq_fderiv]
    apply ContinuousLinearMap.ext
    intro y
    change fderiv ℝ f 0 y = (deriv f 0 • (1 : ℝ →L[ℝ] ℝ)) y
    rw [smul_apply, fderiv_eq_smul_deriv, one_apply_eq_self]
    exact (mul_comm (deriv f 0) y).symm
  apply ContinuousLinearMap.ext
  intro v
  rw [show (fun y : EuclideanHalfSpace N => f (y.1 0))
      = f ∘ (fun y : EuclideanHalfSpace N => y.1 0) from rfl]
  refine (mfderiv_comp_apply x hfm hcoord v).trans ?_
  have hLf' : mfderiv (𝓘(ℝ,ℝ)) (𝓘(ℝ,ℝ)) f (x.1 0) = deriv f 0 • (1 : ℝ →L[ℝ] ℝ) := by
    rw [hx]; exact hLf
  erw [hLf']
  rfl

/-- **Scalar multiples of a real-valued function.**  For a real-valued `g` differentiable at `x`,
`mfderiv (a • g) x = a • mfderiv g x`.  (Write `a • g` as the composite of the continuous linear
map `a • 1` with `g` and use the chain rule.) -/
theorem mfderiv_const_smul_real {N : ℕ} [NeZero N] (g : EuclideanHalfSpace N → ℝ) (a : ℝ)
    {x : EuclideanHalfSpace N}
    (hg : MDifferentiableAt (modelWithCornersEuclideanHalfSpace N)
      (modelWithCornersSelf ℝ ℝ) g x) :
    mfderiv (modelWithCornersEuclideanHalfSpace N) (modelWithCornersSelf ℝ ℝ) (a • g) x
      = a • mfderiv (modelWithCornersEuclideanHalfSpace N) (modelWithCornersSelf ℝ ℝ) g x := by
  have hL : MDifferentiableAt (𝓘(ℝ,ℝ)) (𝓘(ℝ,ℝ)) (⇑(a • (1 : ℝ →L[ℝ] ℝ))) (g x) :=
    (ContinuousLinearMap.hasFDerivAt (a • (1 : ℝ →L[ℝ] ℝ))
      (x := g x)).differentiableAt.mdifferentiableAt
  have hL' : mfderiv (𝓘(ℝ,ℝ)) (𝓘(ℝ,ℝ)) (⇑(a • (1 : ℝ →L[ℝ] ℝ))) (g x)
      = a • (1 : ℝ →L[ℝ] ℝ) := by
    rw [mfderiv_eq_fderiv]
    exact (ContinuousLinearMap.hasFDerivAt (a • (1 : ℝ →L[ℝ] ℝ)) (x := g x)).fderiv
  apply ContinuousLinearMap.ext
  intro v
  rw [show (a • g) = (⇑(a • (1 : ℝ →L[ℝ] ℝ))) ∘ g from rfl]
  rw [mfderiv_comp_apply x hL hg v]
  rw [hL']
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The derivative of the source-region modification at a boundary point.**  Let `ρ` be smooth on
the half-space with `mfderiv ρ x = 0` at a boundary point `x` (`x.1 0 = 0`), and let `ψ`, `χ` be
smooth functions of one variable with `deriv ψ 0 = 1`, `deriv χ 0 = 0`.  Then the modification
`y ↦ ρ y - c * ψ (y.1 0) - s * χ (y.1 0)` has the same derivative at `x` as `y ↦ -c * (y.1 0)`:
only the linear terms survive, and `ψ`, `χ` contribute through their derivatives at `0`.

`set_option backward.isDefEq.respectTransparency false` is needed only because the tangent spaces
`TangentSpace 𝓘 (…)` of the model space are only *definitionally* equal to `ℝ`. -/
theorem mfderiv_sourceRegionPhi_boundary {N : ℕ} [NeZero N] (ρ : EuclideanHalfSpace N → ℝ)
    (hρsm : ContMDiff (modelWithCornersEuclideanHalfSpace N) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    (ψ χ : ℝ → ℝ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hψ1 : deriv ψ 0 = 1) (hχ1 : deriv χ 0 = 0)
    (c s : ℝ) {x : EuclideanHalfSpace N} (hx : x.1 0 = 0)
    (hρx : mfderiv (modelWithCornersEuclideanHalfSpace N) (modelWithCornersSelf ℝ ℝ) ρ x = 0) :
    mfderiv (modelWithCornersEuclideanHalfSpace N) (modelWithCornersSelf ℝ ℝ)
        (fun y => ρ y - c * ψ (y.1 0) - s * χ (y.1 0)) x
      = (-c) • mfderiv (modelWithCornersEuclideanHalfSpace N) (modelWithCornersSelf ℝ ℝ)
          (fun y => y.1 0) x := by
  have hρm : MDifferentiableAt (modelWithCornersEuclideanHalfSpace N) (𝓘(ℝ,ℝ)) ρ x :=
    hρsm.contMDiffAt.mdifferentiableAt (by simp)
  have hψm : MDifferentiableAt (𝓘(ℝ,ℝ)) (𝓘(ℝ,ℝ)) ψ
      ((fun y : EuclideanHalfSpace N => y.1 0) x) := hψ.contMDiff.mdifferentiableAt (by simp)
  have hχm : MDifferentiableAt (𝓘(ℝ,ℝ)) (𝓘(ℝ,ℝ)) χ
      ((fun y : EuclideanHalfSpace N => y.1 0) x) := hχ.contMDiff.mdifferentiableAt (by simp)
  -- differentiability of the two scalar pieces and of their `a • _` multiples
  have hA : MDifferentiableAt (modelWithCornersEuclideanHalfSpace N) (𝓘(ℝ,ℝ))
      (fun y : EuclideanHalfSpace N => ψ (y.1 0)) x :=
    MDifferentiableAt.comp x hψm (mdifferentiableAt_halfSpace_coord x)
  have hB : MDifferentiableAt (modelWithCornersEuclideanHalfSpace N) (𝓘(ℝ,ℝ))
      (fun y : EuclideanHalfSpace N => χ (y.1 0)) x :=
    MDifferentiableAt.comp x hχm (mdifferentiableAt_halfSpace_coord x)
  have hLc : MDifferentiableAt (𝓘(ℝ,ℝ)) (𝓘(ℝ,ℝ)) (⇑(c • (1 : ℝ →L[ℝ] ℝ)))
      ((fun y : EuclideanHalfSpace N => ψ (y.1 0)) x) :=
    (ContinuousLinearMap.hasFDerivAt (c • (1 : ℝ →L[ℝ] ℝ))
      (x := (fun y : EuclideanHalfSpace N => ψ (y.1 0)) x)).differentiableAt.mdifferentiableAt
  have hLs : MDifferentiableAt (𝓘(ℝ,ℝ)) (𝓘(ℝ,ℝ)) (⇑(s • (1 : ℝ →L[ℝ] ℝ)))
      ((fun y : EuclideanHalfSpace N => χ (y.1 0)) x) :=
    (ContinuousLinearMap.hasFDerivAt (s • (1 : ℝ →L[ℝ] ℝ))
      (x := (fun y : EuclideanHalfSpace N => χ (y.1 0)) x)).differentiableAt.mdifferentiableAt
  have hcA : MDifferentiableAt (modelWithCornersEuclideanHalfSpace N) (𝓘(ℝ,ℝ))
      (c • (fun y : EuclideanHalfSpace N => ψ (y.1 0))) x :=
    MDifferentiableAt.comp x (g := ⇑(c • (1 : ℝ →L[ℝ] ℝ))) hLc hA
  have hsB : MDifferentiableAt (modelWithCornersEuclideanHalfSpace N) (𝓘(ℝ,ℝ))
      (s • (fun y : EuclideanHalfSpace N => χ (y.1 0))) x :=
    MDifferentiableAt.comp x (g := ⇑(s • (1 : ℝ →L[ℝ] ℝ))) hLs hB
  have hsub1 : MDifferentiableAt (modelWithCornersEuclideanHalfSpace N) (𝓘(ℝ,ℝ))
      (ρ - c • (fun y : EuclideanHalfSpace N => ψ (y.1 0))) x := hρm.sub hcA
  -- expand the function and apply linearity of `mfderiv`
  apply ContinuousLinearMap.ext
  intro v
  rw [show (fun y : EuclideanHalfSpace N => ρ y - c * ψ (y.1 0) - s * χ (y.1 0))
      = (ρ - c • (fun y : EuclideanHalfSpace N => ψ (y.1 0)))
        - s • (fun y : EuclideanHalfSpace N => χ (y.1 0)) from rfl]
  rw [mfderiv_sub hsub1 hsB, mfderiv_sub hρm hcA,
      mfderiv_const_smul_real (fun y : EuclideanHalfSpace N => ψ (y.1 0)) c hA,
      mfderiv_const_smul_real (fun y : EuclideanHalfSpace N => χ (y.1 0)) s hB]
  rw [hρx, mfderiv_chain_coord ψ hψ hx, mfderiv_chain_coord χ hχ hx, hχ1, hψ1]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, one_smul, zero_smul]
  simp [sub_eq_add_neg]

end

end Work.PTGeometric
