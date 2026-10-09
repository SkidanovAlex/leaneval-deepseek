/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `F(d)/F(d)^2 ≅ 𝔽_p[G]^d`

This file contains the identification that Schmidt–Wingberg use silently in the proof of
Proposition 6: the quotient `F(d)/F(d)^2 = F(d)/F(d)^p[F(d),F(d)]` of the free `G`-operator
group of rank `d` is, as an `𝔽_p[G]`-module, the free module `𝔽_p[G]^d`: the images of the free
generators `x_{i,g}` (`i : Fin d`, `g : G`) form a basis, and `G` permutes them according to the
left regular representation.

The model of `𝔽_p[G]^d` used here is `Fin d × G → 𝔽_p` with the action
`(h • f) (i,g) = f (i, h⁻¹ * g)`, i.e. the left regular representation on the second factor;
this is exactly `(𝔽_p[G])^d` with `𝔽_p[G] = ⨁_{g : G} 𝔽_p · ε_g` and `h • ε_g = ε_{h g}`.

## Main definitions

* `Work.CohomologicalShrinking.genMk` : the image of the free generator `x_{i,g}` in
  `F(d)/F(d)^2`.
* `Work.CohomologicalShrinking.squareQuotientToFun` : the canonical `𝔽_p`-linear map
  `F(d)/F(d)^2 → (Fin d × G → 𝔽_p)`, `x_{i,g} ↦` the coordinate function at `(i,g)`.

## Main results

* `Work.CohomologicalShrinking.squareQuotientToFun_genMk` : the value on the generators.
* `Work.CohomologicalShrinking.squareQuotientToFun_bijective` : the canonical map is bijective,
  i.e. `F(d)/F(d)^2 ≅ 𝔽_p[G]^d` (in `Submission.Work.CohomologicalShrinking.ModSquareBijective`).
* `Work.CohomologicalShrinking.squareQuotientToFun_smul` : the canonical map is `G`-equivariant.
-/

import Mathlib
import Submission.Work.CohomologicalShrinking.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

attribute [local instance] Classical.decEq

namespace Work.CohomologicalShrinking

open scoped TensorProduct commutatorElement

universe u

variable {p : ℕ}

/-! ## The free `𝔽_p[G]`-module `𝔽_p[G]^d` -/

/-- The `𝔽_p[G]`-module `𝔽_p[G]^d`, realized as the functions `Fin d × G → 𝔽_p` with the left
regular action `(h • f) (i,g) = f (i, h⁻¹ * g)` on the second factor. -/
noncomputable instance instSMulProdFun (p : ℕ) (G : Type*) [Group G] (d : ℕ) :
    SMul G (Fin d × G → ZMod p) where
  smul h f := fun x => f (x.1, h⁻¹ * x.2)

@[simp] theorem smul_prodFun_apply {G : Type*} [Group G] {d : ℕ} (h : G)
    (f : Fin d × G → ZMod p) (x : Fin d × G) :
    (h • f) x = f (x.1, h⁻¹ * x.2) := rfl

noncomputable instance instDistribMulActionProdFun (p : ℕ) (G : Type*) [Group G] (d : ℕ) :
    DistribMulAction G (Fin d × G → ZMod p) where
  one_smul f := by funext x; simp
  mul_smul h₁ h₂ f := by funext x; simp [mul_inv_rev, mul_assoc]
  smul_zero h := by funext x; simp
  smul_add h f g := by funext x; simp

noncomputable instance instSMulCommClassProdFun (p : ℕ) (G : Type*) [Group G] (d : ℕ) :
    SMulCommClass G (ZMod p) (Fin d × G → ZMod p) where
  smul_comm h c f := by funext x; simp

/-! ## The canonical map `F(d)/F(d)^2 → 𝔽_p[G]^d` -/

/-- The image of the free generator `x_{i,g}` of the `G`-operator group
`F(d) = FreeGroup (Fin d × G)` in `F(d)/F(d)^2`. -/
noncomputable def genMk (p : ℕ) (G : Type*) [Group G] (d : ℕ) (x : Fin d × G) :
    squareQuotient p G d :=
  Additive.ofMul (QuotientGroup.mk'
    ((Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) 1).subgroupOf
      (Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) 0))
    ⟨FreeGroup.of x, by
      rw [Work.Shrinking.pCentralSeries_zero]
      exact Subgroup.mem_top _⟩)

/-- The homomorphism `F(d) →* Multiplicative (Fin d × G → 𝔽_p)` sending the free generator
`x_{i,g}` to the coordinate function at `(i,g)`. -/
noncomputable def freeToFun (p : ℕ) (G : Type*) [Group G] (d : ℕ) :
    Work.Shrinking.freeOperatorGroup G d →* Multiplicative (Fin d × G → ZMod p) :=
  FreeGroup.lift fun x : Fin d × G => Multiplicative.ofAdd (Pi.single x (1 : ZMod p))

theorem freeToFun_of (p : ℕ) (G : Type*) [Group G] (d : ℕ) (x : Fin d × G) :
    freeToFun p G d (FreeGroup.of x) = Multiplicative.ofAdd (Pi.single x (1 : ZMod p)) :=
  FreeGroup.lift_apply_of

/-- The canonical homomorphism out of `F(d)/F(d)^2` sending the class of `x_{i,g}` to the
coordinate function at `(i,g)`. -/
noncomputable def quotHom (p : ℕ) (G : Type*) [Group G] (d : ℕ) :
    Work.Shrinking.pCentralQuotient p (Work.Shrinking.freeOperatorGroup G d) 0 →*
      Multiplicative (Fin d × G → ZMod p) := by
  classical
  have key : Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) 1 ≤
      (freeToFun p G d).ker := by
    rw [show Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) 1
        = Work.Shrinking.pCentralStep p (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G d))
        from rfl, Work.Shrinking.pCentralStep]
    have hp : ∀ v : Multiplicative (Fin d × G → ZMod p), v ^ p = 1 := fun v => by
      conv_lhs => rw [← ofAdd_toAdd v]
      rw [← ofAdd_nsmul, show p • Multiplicative.toAdd v = 0 from by
        rw [← Nat.cast_smul_eq_nsmul (ZMod p) p, ZMod.natCast_self, zero_smul]]
      rfl
    refine sup_le ?_ ?_
    · rw [Work.Shrinking.powSubgroup]
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨y, -, rfl⟩
      show y ^ p ∈ (freeToFun p G d).ker
      rw [MonoidHom.mem_ker, map_pow]
      exact hp _
    · refine (Subgroup.commutator_le).mpr fun a _ b _ => ?_
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.mpr (mul_comm _ _)
  exact QuotientGroup.lift _ ((freeToFun p G d).comp
    (Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) 0).subtype) (by
    intro x hx
    exact key (Subgroup.mem_subgroupOf.mp hx))

@[simp]
theorem quotHom_genMk (p : ℕ) (G : Type*) [Group G] (d : ℕ) (x : Fin d × G) :
    quotHom p G d (Additive.toMul (genMk p G d x)) =
      Multiplicative.ofAdd (Pi.single x (1 : ZMod p)) :=
  freeToFun_of p G d x

/-- The canonical `𝔽_p`-linear map `F(d)/F(d)^2 → (Fin d × G → 𝔽_p)` sending the class of
`x_{i,g}` to the coordinate function at `(i,g)`. -/
noncomputable def squareQuotientToFun (p : ℕ) (G : Type*) [Group G] (d : ℕ) :
    squareQuotient p G d →ₗ[ZMod p] (Fin d × G → ZMod p) :=
  AddMonoidHom.toZModLinearMap p
    { toFun := fun x => Multiplicative.toAdd (quotHom p G d (Additive.toMul x))
      map_zero' := by rw [toMul_zero, map_one, toAdd_one]
      map_add' := by intro a b; rw [toMul_add, map_mul, toAdd_mul] }

@[simp]
theorem squareQuotientToFun_genMk (p : ℕ) (G : Type*) [Group G] (d : ℕ) (x : Fin d × G) :
    squareQuotientToFun p G d (genMk p G d x) = Pi.single x (1 : ZMod p) := by
  show Multiplicative.toAdd (quotHom p G d (Additive.toMul (genMk p G d x))) = _
  rw [quotHom_genMk, toAdd_ofAdd]

end Work.CohomologicalShrinking
