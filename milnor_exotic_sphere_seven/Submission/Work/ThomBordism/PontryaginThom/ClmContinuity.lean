import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

/-!
# Continuity of a family of continuous linear maps on `ℝⁿ` by its columns

A family `L : X → (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)` of continuous linear maps between the coordinate
spaces `ℝᵐ` and `ℝⁿ` is continuous in the operator-norm topology **iff** its columns
`x ↦ L x (Pi.single j 1)` are continuous, for the finitely many `j : Fin m`.

The point is that the space of continuous linear maps from the finite-dimensional space `ℝᵐ` is
homeomorphic to the product of `m` copies of `ℝⁿ` — Mathlib's continuous linear equivalence
`ContinuousLinearEquiv.piRing` — so checking continuity of the *columns* (and of these entrywise)
suffices.  This is the tool that turns the (pointwise) computation rules of a family of projections
(`Work.ThomBordism.PontryaginThom.Complement`) into the continuity of the corresponding
transition functions of a vector bundle.
-/

namespace Work.ThomBordism.PontryaginThom

open scoped Topology

noncomputable section

/-- The `j`-th column of a continuous linear map `ℝᵐ →L[ℝ] ℝⁿ`, as the `piRing` coordinate. -/
theorem piRing_apply_single {m n : ℕ} (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) (j : Fin m) :
    (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (ι := Fin m) (E := (Fin n → ℝ))) L j
      = L (Pi.single j 1) := by
  simp only [ContinuousLinearEquiv.piRing, ContinuousLinearEquiv.coe_mk,
    LinearEquiv.trans_apply, LinearEquiv.piRing_apply]
  have h1 : (⇑(LinearMap.toContinuousLinearMap.symm L : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
      = ⇑L := by
    rw [← LinearMap.coe_toContinuousLinearMap' (LinearMap.toContinuousLinearMap.symm L),
      LinearEquiv.apply_symm_apply]
  exact congrFun h1 (Pi.single j 1)

/-- **A family of continuous linear maps `ℝᵐ → ℝⁿ` is continuous iff its columns are.** -/
theorem continuous_clm_iff_continuous_apply_single {X : Type*} [TopologicalSpace X] {m n : ℕ}
    (L : X → (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) :
    Continuous L ↔ ∀ j : Fin m, Continuous (fun x => L x (Pi.single j 1)) := by
  constructor
  · intro h j
    exact ((ContinuousLinearMap.apply ℝ (Fin n → ℝ) (Pi.single j 1)).continuous.comp h)
  · intro h
    have he : Continuous (fun x =>
        (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (ι := Fin m) (E := (Fin n → ℝ))) (L x)) := by
      rw [continuous_pi_iff]
      intro j
      have hcol : (fun x => (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (ι := Fin m)
          (E := (Fin n → ℝ))) (L x) j) = fun x => L x (Pi.single j 1) := by
        funext x
        exact piRing_apply_single (L x) j
      rw [hcol]
      exact h j
    have h2 := (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (ι := Fin m)
      (E := (Fin n → ℝ))).symm.continuous.comp he
    convert h2 using 1
    ext x
    simp

/-- **A family of linear maps `ℝᵐ →ₗ ℝⁿ` is continuous as a family of continuous linear maps iff
its columns are.**  Companion of `continuous_clm_iff_continuous_apply_single` for families given as
`LinearMap`s (the form in which the projections of `Complement.lean` are stated). -/
theorem continuous_toContinuousLinearMap_iff {X : Type*} [TopologicalSpace X] {m n : ℕ}
    (L : X → (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    Continuous (fun x => LinearMap.toContinuousLinearMap (L x))
      ↔ ∀ j : Fin m, Continuous (fun x => L x (Pi.single j 1)) := by
  rw [continuous_clm_iff_continuous_apply_single (fun x => LinearMap.toContinuousLinearMap (L x))]
  constructor
  · intro h j
    refine h j |>.congr ?_
    intro x
    rw [LinearMap.coe_toContinuousLinearMap']
  · intro h j
    refine (h j).congr ?_
    intro x
    rw [LinearMap.coe_toContinuousLinearMap']

end

end Work.ThomBordism.PontryaginThom
