/-
Copyright (c) 2025. All rights reserved.

# The Shapiro lift of a `2`-cochain on `U ≤ G` to a `2`-cochain on `G` with values in
`Coind_U^G M`

For a group `G`, a subgroup `U ≤ G` and a `U`-module `M`, the coinduced module is

  `Coind_U^G M = { f : G → M // ∀ g u, f (g * u) = u⁻¹ • f g }`

with the `G`-action `(g • f) x = f (g⁻¹ * x)` (`Submission/Work/SSGRoute/PT/ClassFormation.lean`).

Given a `2`-cochain `a : U × U → M` on `U`, this file defines its **Shapiro lift**

  `shapiroLift a (g, h) = (x ↦ coord x • a (A g (xU), A h (g⁻¹ • xU)))`,

where `secC` is a set-theoretic section of `G → G ⧸ U` (sending the trivial coset to `1`),
`A g C = (secC C)⁻¹ * g * secC (g⁻¹ • C) ∈ U` are the `U`-coordinates of `g` at the coset `C`
(`Submission/Work/SSGRoute/ShapiroSetup.lean`) and `coord x = x⁻¹ * secC (xU) ∈ U`
(`Submission/Work/SSGRoute/PT/shapiro_defs.lean`).

The point of the `coord x` factor is that it makes the function satisfy the defining relation of
the coinduced module: `f (x * u) = u⁻¹ • f x`, since `coord (x*u) = u⁻¹ * coord x` and
`(x*u)U = xU` (`coord_mul`, `coset_mul`).  Evaluating at the section representative `secC C`
(where `coord` is `1`) gives back the value of `a`:

  `shapiroLift a (g, h) (secC C) = a (A g C, A h (g⁻¹ • C))`

and at the identity element of `G` (with `g = u`, `h = v` in `U`) this is exactly `a (u, v)`.

This file contains the definition and the elementary identities about it; the cocycle condition
and the local constancy of `shapiroLift` are the modules
`Submission/Work/SSGRoute/PT/shapiro_H2_cocycle.lean` and
`Submission/Work/SSGRoute/PT/shapiro_H2_locconst.lean`.
-/
import Mathlib
import Submission.Work.SSGRoute.PT.ClassFormation
import Submission.Work.SSGRoute.PT.shapiro_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped Classical

namespace Work.SSGRoute.PT

noncomputable section

variable {G : Type*} [Group G] (U : Subgroup G)
variable {M : Type*} [AddCommGroup M] [DistribMulAction U M]

/-- The underlying function of the Shapiro lift: `x ↦ coord U x • a (A g (xU), A h (g⁻¹ • xU))`. -/
def shapiroFun (a : U × U → M) (p : G × G) : G → M :=
  fun x => coord U x • a (Shapiro.A 0 G U p.1 (x : G ⧸ U),
      Shapiro.A 0 G U p.2 (p.1⁻¹ • (x : G ⧸ U)))

theorem shapiroFun_mem_coind (a : U × U → M) (p : G × G) :
    shapiroFun U a p ∈ coindSub G U M := by
  intro x u
  simp only [shapiroFun]
  rw [coset_mul U x u, coord_mul U x u, mul_smul]

/-- **The Shapiro lift** of a `2`-cochain `a` on `U` to a `2`-cochain on `G` with values in the
coinduced module `Coind_U^G M`: the element of `Coind_U^G M` attached to `(g,h)` is the function
`x ↦ coord U x • a (A g (xU), A h (g⁻¹ • xU))`. -/
def shapiroLift (a : U × U → M) : G × G → Coind G U M :=
  fun p => ⟨shapiroFun U a p, shapiroFun_mem_coind U a p⟩

@[simp] theorem shapiroLift_apply (a : U × U → M) (g h x : G) :
    (shapiroLift U a (g, h) : G → M) x
      = coord U x • a (Shapiro.A 0 G U g (x : G ⧸ U),
          Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U))) := rfl

/-! ## The coordinates `coord` and `secC` -/

/-- `coord` at the identity element is `1`. -/
theorem coord_one : coord U (1 : G) = 1 := by
  apply Subtype.ext
  rw [coe_coord, inv_one, one_mul, ← basePoint_eq, secC_basePoint]
  rfl

/-- `coord` at a section representative `secC C` is `1`. -/
theorem coord_secC (C : G ⧸ U) : coord U (secC U C) = 1 := by
  apply Subtype.ext
  rw [coe_coord, secC_mk U C]
  simp

/-- `secC (xU) = x * coord x`. -/
theorem secC_eq_mul_coord (x : G) : secC U (x : G ⧸ U) = x * (coord U x : G) := by
  rw [coe_coord]
  group

/-- `x = secC (xU) * (coord x)⁻¹`. -/
theorem eq_secC_mul_coord_inv (x : G) :
    x = secC U (x : G ⧸ U) * (coord U x : G)⁻¹ := by
  rw [secC_eq_mul_coord U x]
  group

/-! ## The `G`-action on the coinduced module in coordinates -/

/-- **The action of `G` on `Coind_U^G M` in coordinates**: the `coord`-factor is moved onto the
value, the section representative of the twisted coset carries the value of `f`. -/
theorem Coind.smul_apply_coord (f : Coind G U M) (g x : G) :
    (g • f) x = (coord U x * Shapiro.A 0 G U g (x : G ⧸ U)) •
      f (secC U (g⁻¹ • (x : G ⧸ U))) := by
  have hA : (g⁻¹ * secC U (x : G ⧸ U)) * (Shapiro.A 0 G U g (x : G ⧸ U) : G)
      = secC U (g⁻¹ • (x : G ⧸ U)) := by
    rw [mul_assoc, ← secC_mul_A U g (x : G ⧸ U), ← mul_assoc, inv_mul_cancel, one_mul]
  have key : (g⁻¹ * x) * ↑(coord U x * Shapiro.A 0 G U g (x : G ⧸ U))
      = secC U (g⁻¹ • (x : G ⧸ U)) := by
    calc (g⁻¹ * x) * ↑(coord U x * Shapiro.A 0 G U g (x : G ⧸ U))
        = (g⁻¹ * (x * (coord U x : G))) * (Shapiro.A 0 G U g (x : G ⧸ U) : G) := by
          rw [Subgroup.coe_mul]
          group
      _ = (g⁻¹ * secC U (x : G ⧸ U)) * (Shapiro.A 0 G U g (x : G ⧸ U) : G) := by
          rw [secC_eq_mul_coord U x]
      _ = secC U (g⁻¹ • (x : G ⧸ U)) := hA
  have hx : g⁻¹ * x
      = secC U (g⁻¹ • (x : G ⧸ U)) * ↑(coord U x * Shapiro.A 0 G U g (x : G ⧸ U))⁻¹ :=
    eq_mul_inv_of_mul_eq key
  rw [Coind.smul_apply, hx, Coind.coe_mul]
  simp

/-- The Shapiro lift evaluated at a section representative. -/
theorem shapiroLift_secC (a : U × U → M) (g h : G) (C : G ⧸ U) :
    (shapiroLift U a (g, h) : G → M) (secC U C)
      = a (Shapiro.A 0 G U g C, Shapiro.A 0 G U h (g⁻¹ • C)) := by
  rw [shapiroLift_apply, coord_secC, secC_mk, one_smul]

/-- The action of `G` on the Shapiro lift, expanded into the values of `a`. -/
theorem shapiroLift_smul_apply (a : U × U → M) (g h k x : G) :
    (g • shapiroLift U a (h, k)) x
      = (coord U x * Shapiro.A 0 G U g (x : G ⧸ U))
          • a (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)),
              Shapiro.A 0 G U k (h⁻¹ • (g⁻¹ • (x : G ⧸ U)))) := by
  rw [Coind.smul_apply_coord, shapiroLift_secC]

/-! ## The `U`-coordinates of an element of a subgroup acting trivially on the coset space -/

/-- A section representative is the `sec` of the coset space. -/
theorem secC_eq_sec (C : G ⧸ U) : secC U C = Shapiro.sec 0 G U C := rfl

/-- If `v` acts trivially on the coset space, then the `U`-coordinate of `v` at a coset is the
conjugate `(sec C)⁻¹ * v * sec C` of `v`. -/
theorem coe_A_eq_of_smul_eq_sec {V : Subgroup G}
    (hV : ∀ v ∈ V, ∀ C : G ⧸ U, (v : G)⁻¹ • C = C) (v : V) (C : G ⧸ U) :
    (Shapiro.A 0 G U (v : G) C : G)
      = (Shapiro.sec 0 G U C)⁻¹ * (v : G) * Shapiro.sec 0 G U C := by
  rw [Shapiro.coe_A, hV v v.2 C]

/-- If `v` acts trivially on the coset space, then the `U`-coordinate of `v` at a coset is the
conjugate `(secC C)⁻¹ * v * secC C` of `v`. -/
theorem coe_A_eq_of_smul_eq {V : Subgroup G}
    (hV : ∀ v ∈ V, ∀ C : G ⧸ U, (v : G)⁻¹ • C = C) (v : V) (C : G ⧸ U) :
    (Shapiro.A 0 G U (v : G) C : G) = (secC U C)⁻¹ * (v : G) * secC U C := by
  rw [coe_A_eq_of_smul_eq_sec U hV v C, secC_eq_sec U C]

/-- The conjugate `(secC C)⁻¹ * v * secC C` of an element `v` of a subgroup acting trivially on
the coset space, as an element of `U`. -/
noncomputable def conjBySecC {V : Subgroup G}
    (hV : ∀ v ∈ V, ∀ C : G ⧸ U, (v : G)⁻¹ • C = C) (v : V) (C : G ⧸ U) : U :=
  ⟨(secC U C)⁻¹ * (v : G) * secC U C, by
    have h : (Shapiro.A 0 G U (v : G) C : G) = (secC U C)⁻¹ * (v : G) * secC U C :=
      coe_A_eq_of_smul_eq U hV v C
    rw [← h]
    exact (Shapiro.A 0 G U (v : G) C).2⟩

@[simp] theorem coe_conjBySecC {V : Subgroup G}
    (hV : ∀ v ∈ V, ∀ C : G ⧸ U, (v : G)⁻¹ • C = C) (v : V) (C : G ⧸ U) :
    (conjBySecC U hV v C : G) = (secC U C)⁻¹ * (v : G) * secC U C := rfl

/-- Multiplicativity of the `U`-coordinates, in the form used for the local constancy of the
Shapiro lift: moving the second argument by an element of a subgroup acting trivially on the coset
space only conjugates the `U`-coordinate. -/
theorem A_mul_eq_mul_conjBySecC {V : Subgroup G}
    (hV : ∀ v ∈ V, ∀ C : G ⧸ U, (v : G)⁻¹ • C = C) (g : G) (v : V) (C : G ⧸ U) :
    Shapiro.A 0 G U (g * (v : G)) C = Shapiro.A 0 G U g C * conjBySecC U hV v (g⁻¹ • C) := by
  apply Subtype.ext
  simp only [A_mul' U g (v : G) C, Subgroup.coe_mul,
    coe_A_eq_of_smul_eq U hV v (g⁻¹ • C), coe_conjBySecC]

/-- Passing from `g` to `g * v` with `v` acting trivially on the coset space does not change the
twisted coset. -/
theorem inv_mul_smul_coset_of_smul_eq {V : Subgroup G}
    (hV : ∀ v ∈ V, ∀ C : G ⧸ U, (v : G)⁻¹ • C = C) (g : G) (v : V) (C : G ⧸ U) :
    (g * (v : G))⁻¹ • C = g⁻¹ • C := by
  rw [mul_inv_rev, mul_smul]
  exact hV v v.2 (g⁻¹ • C)

end

end Work.SSGRoute.PT
