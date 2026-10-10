import Mathlib.Tactic.Group
import Mathlib.GroupTheory.GroupAction.Quotient
import Submission.Work.SSGRoute.PT.ClassFormation
import Submission.Work.SSGRoute.ShapiroSetup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Shapiro's lemma for the coinduced module: the definitions

For a group `G`, a subgroup `U ≤ G` and a `U`-module `M`, the coinduced module
`Coind G U M = {f : G → M // ∀ g u, f (g * u) = u⁻¹ • f g}` sits inside `G → M`
(`Submission/Work/SSGRoute/PT/ClassFormation.lean`).  This file sets up the dictionary used to
construct the *inverse* of the Shapiro map

  `H¹(U, M) → H¹(G, Coind G U M)`

at the level of cochains: a section `secC` of the coset projection `G → G ⧸ U`, the
`U`-coordinate `coord x = x⁻¹ * secC (x U)`, and, for a cochain `φ : U → M`, the cochain

  `coindCocycle U φ g = (x ↦ coord x • φ (A g (x U)))`

where `A g C = (secC C)⁻¹ * g * secC (g⁻¹ • C) ∈ U` is the `U`-coordinate of `g` at the coset `C`
(`Submission/Work/SSGRoute/ShapiroSetup.lean`).

The two identities that make this work are

* `coord U (g⁻¹ * x) = coord U x * A g (x U)` (`coord_smul`), i.e. `coord` is equivariant, and
* `A` is multiplicative, `A (g * h) C = A g C * A h (g⁻¹ • C)` (`Shapiro.A_mul`),
* `g * secC (g⁻¹ • C) = secC C * A g C` (`Shapiro.sec_mul_A`).

They are what turn the crossed-homomorphism identity for `φ` into the crossed-homomorphism
identity for `coindCocycle U φ`.
-/

set_option linter.unusedSectionVars false

open scoped Classical

namespace Work.SSGRoute.PT

noncomputable section

variable {G : Type*} [Group G] (U : Subgroup G)

/-- A chosen representative of the coset `C : G ⧸ U`, with the trivial coset represented by `1`. -/
def secC : G ⧸ U → G := Shapiro.sec 0 G U

theorem secC_mk (C : G ⧸ U) : ((secC U C : G) : G ⧸ U) = C := Shapiro.mk_sec 0 G U C

theorem secC_basePoint : secC U (Shapiro.basePoint 0 G U) = 1 := Shapiro.sec_basePoint 0 G U

/-- The `U`-coordinate `x⁻¹ * secC (x U)` of `x`. -/
def coord (x : G) : U :=
  ⟨x⁻¹ * secC U (x : G ⧸ U), by
    have h : (((secC U (x : G ⧸ U)) : G) : G ⧸ U) = (x : G ⧸ U) := secC_mk U _
    have h2 : QuotientGroup.leftRel U (secC U (x : G ⧸ U)) x := Quotient.exact h
    rw [QuotientGroup.leftRel_apply] at h2
    simpa using inv_mem h2⟩

theorem coe_coord (x : G) : (coord U x : G) = x⁻¹ * secC U (x : G ⧸ U) := rfl

/-- Membership in the coset is membership in `U`, read on the left: `a U = b U ↔ a⁻¹ * b ∈ U`. -/
theorem coset_eq_iff (a b : G) : ((a : G ⧸ U) = (b : G ⧸ U)) ↔ a⁻¹ * b ∈ U := by
  rw [Quotient.eq'']
  exact QuotientGroup.leftRel_apply

/-- Multiplying on the right by an element of `U` does not change the coset. -/
theorem coset_mul (x : G) (u : U) : ((x * (u : G) : G) : G ⧸ U) = (x : G ⧸ U) := by
  have h : QuotientGroup.leftRel U (x * (u : G)) x := by
    rw [QuotientGroup.leftRel_apply]
    simpa using inv_mem u.2
  exact Quotient.sound h

/-- The coset of `g⁻¹ * x` is `g⁻¹ • (x U)`. -/
theorem coset_smul (g x : G) : (((g⁻¹ * x : G)) : G ⧸ U) = g⁻¹ • (x : G ⧸ U) := by
  rw [MulAction.Quotient.smul_coe U g⁻¹ x, smul_eq_mul]

theorem coord_mul (x : G) (u : U) : coord U (x * (u : G)) = u⁻¹ * coord U x := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_coord]
  rw [coset_mul U x u]
  group

/-- **Equivariance of `coord`**: `coord U (g⁻¹ * x) = coord U x * A g (x U)`. -/
theorem coord_smul (g x : G) :
    coord U (g⁻¹ * x) = coord U x * Shapiro.A 0 G U g (x : G ⧸ U) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, coe_coord, coe_coord, coset_smul U g x, Shapiro.coe_A]
  simp only [secC]
  group

/-- The `U`-coordinate of the identity element is `1`. -/
theorem A_one (C : G ⧸ U) : Shapiro.A 0 G U (1 : G) C = 1 := by
  apply Subtype.ext
  rw [Shapiro.coe_A]
  simp

/-- `A` is multiplicative in its second variable along the coset action:
`A (g * h) C = A g C * A h (g⁻¹ • C)`. -/
theorem A_mul' (g h : G) (C : G ⧸ U) :
    Shapiro.A 0 G U (g * h) C = Shapiro.A 0 G U g C * Shapiro.A 0 G U h (g⁻¹ • C) :=
  Shapiro.A_mul 0 G U g h C

/-- The defining relation between `secC` and `A`: `g * secC (g⁻¹ • C) = secC C * A g C`. -/
theorem secC_mul_A (g : G) (C : G ⧸ U) :
    g * secC U (g⁻¹ • C) = secC U C * (Shapiro.A 0 G U g C : G) :=
  Shapiro.sec_mul_A 0 G U g C

/-- At the trivial coset, `A u = u`. -/
theorem A_basePoint (u : U) : Shapiro.A 0 G U (u : G) (Shapiro.basePoint 0 G U) = u :=
  Shapiro.A_basePoint 0 G U u

/-- `basePoint` is the coset of `1`. -/
theorem basePoint_eq : Shapiro.basePoint 0 G U = ((1 : G) : G ⧸ U) := rfl

variable {M : Type*} [AddCommGroup M] [DistribMulAction U M]

/-- **The Shapiro cochain** of a cochain `φ : U → M` on the coinduced module:
`g ↦ (x ↦ coord U x • φ (A g (x U)))`. -/
def coindCocycle (φ : U → M) : G → Coind G U M :=
  fun g => ⟨fun x => coord U x • φ (Shapiro.A 0 G U g (x : G ⧸ U)), by
    intro x u
    have hc : (((x * (u : G) : G)) : G ⧸ U) = (x : G ⧸ U) := coset_mul U x u
    show coord U (x * (u : G)) • φ (Shapiro.A 0 G U g ((x * (u : G) : G) : G ⧸ U))
        = u⁻¹ • (coord U x • φ (Shapiro.A 0 G U g (x : G ⧸ U)))
    rw [hc, coord_mul U x u, mul_smul]
  ⟩

@[simp] theorem coindCocycle_apply (φ : U → M) (g x : G) :
    (coindCocycle U φ g : G → M) x = coord U x • φ (Shapiro.A 0 G U g (x : G ⧸ U)) := rfl

/-- The Shapiro cochain at the identity coset: `coindCocycle U φ u` evaluated at `1` is `φ u`. -/
theorem coindCocycle_one_apply (φ : U → M) (u : U) :
    (coindCocycle U φ (u : G) : G → M) (1 : G) = φ u := by
  rw [coindCocycle_apply]
  have h2 : Shapiro.A 0 G U (u : G) (((1 : G)) : G ⧸ U) = u :=
    Shapiro.A_basePoint 0 G U u
  have h3 : coord U (1 : G) = 1 := by
    apply Subtype.ext
    rw [coe_coord]
    simp only [secC, inv_one, one_mul]
    exact Shapiro.sec_basePoint 0 G U
  rw [h2, h3, one_smul]

end

end Work.SSGRoute.PT
