/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Divisors with `ℓ(D) = 1`

If `D` is an effective divisor with `ℓ(D) = 1`, then the only rational functions whose poles
are bounded by `D` are the constants (`exists_algebraMap_eq_of_mem_L_of_finrank_eq_one`):
`L(D)` contains the constants and has `F`-dimension one.  Consequently an effective divisor
linearly equivalent to `D` is `D` itself (`linEquiv_eq_of_ell_eq_one`): if `D' = D - div z` is
effective then `z⁻¹ ∈ L(D)`, hence `z⁻¹` is a constant and `div z = 0`.
-/
import Mathlib
import Submission.Work.GCBasics.DivApi

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.GCBasics

open Work.CurveBasics

noncomputable section

/-- If `D` is effective and `ℓ(D) = 1`, every element of the Riemann-Roch space `L(D)` is a
constant: the constants sit inside `L(D)` (`Curve.algebraMap_mem_L`) and `L(D)` is
one-dimensional, so `L(D) = F ∙ 1`. -/
theorem exists_algebraMap_eq_of_mem_L_of_finrank_eq_one {F : Type u} [Field F] (C' : Curve F)
    {D : Curve.Div C'} (hD : D.IsEffective) (h1 : Module.finrank F (Curve.L C' D) = 1)
    {x : C'.functionField} (hx : x ∈ Curve.L C' D) :
    ∃ c : F, x = algebraMap F C'.functionField c := by
  -- `1` lies in `L D` because `D` is effective
  have hmem1 : (1 : C'.functionField) ∈ Curve.L C' D := by
    rw [← map_one (algebraMap F C'.functionField)]
    exact Curve.algebraMap_mem_L C' hD 1
  have hv : (⟨1, hmem1⟩ : ↥(Curve.L C' D)) ≠ 0 := by
    intro hh
    have : ((⟨1, hmem1⟩ : ↥(Curve.L C' D)) : C'.functionField) = 0 := by rw [hh]; rfl
    exact one_ne_zero this
  -- `L D` is spanned by its nonzero vector `1`
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' (⟨1, hmem1⟩ : ↥(Curve.L C' D)) hv).mp h1 ⟨x, hx⟩
  refine ⟨c, ?_⟩
  have h2 := congrArg (fun y : ↥(Curve.L C' D) => (y : C'.functionField)) hc
  simpa only [Submodule.coe_smul, Subtype.coe_mk, Algebra.smul_def, mul_one] using h2.symm

/-- **An effective divisor with `ℓ(D) = 1` has no effective divisor linearly equivalent to it
other than itself.** -/
theorem linEquiv_eq_of_ell_eq_one {K : Type _} [Field K] {C : Work.CurveBasics.Curve K}
    {F : Type _} [Field F] [Algebra K F] {D D' : Work.GCBasics.Dv C F}
    (hD : Work.CurveBasics.Curve.Div.IsEffective D) (h : Work.GCBasics.ell C D = 1)
    (hD' : Work.CurveBasics.Curve.Div.IsEffective D')
    (he : Work.GCBasics.LinEquiv C D D') : D = D' := by
  -- `D' = D - div z` for some nonzero rational function `z`
  obtain ⟨z, hz, hdiv⟩ := he
  -- the inverse function has divisor `D' - D`
  have hz' : Curve.div (Curve.baseChange C F) z⁻¹ = D' - D := by
    rw [Work.CurveBasics.Order.div_inv (Curve.baseChange C F) hz, hdiv]; abel
  -- hence `z⁻¹ ∈ L D`, because `D' = div z⁻¹ + D` is effective
  have hmem : z⁻¹ ∈ Curve.L (Curve.baseChange C F) D := by
    rw [Curve.mem_L_iff]
    refine Or.inr ?_
    have h2 : Curve.div (Curve.baseChange C F) z⁻¹ + D = D' := by rw [hz']; abel
    rw [h2]; exact hD'
  -- `ℓ(D) = 1` forces `z⁻¹` to be a constant, so its divisor vanishes
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_mem_L_of_finrank_eq_one (Curve.baseChange C F) hD h hmem
  have hz0 : Curve.div (Curve.baseChange C F) z⁻¹ = 0 := by
    rw [hc]; exact Work.CurveBasics.Order.div_algebraMap_eq_zero _ c
  have hsub : D' - D = 0 := by rw [← hz', hz0]
  exact (sub_eq_zero.mp hsub).symm

end

end Work.GCBasics
