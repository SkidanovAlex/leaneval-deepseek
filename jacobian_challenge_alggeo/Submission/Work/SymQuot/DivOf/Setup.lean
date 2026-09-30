/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The rings attached to a point of `Symⁿ C` (area SY, the `divOf` construction)

This file starts the construction of the *divisor of a point* of `Symⁿ C`
(`Work.SpecLin.SymGeom.divOf`).  See `Submission/Work/SymQuot/NOTES.md` for the plan.

Fix `p : Spec F ⟶ Symⁿ C`.  The charts of `Symⁿ C` cover, and a morphism out of the one-point
scheme `Spec F` factors through any open containing its image, so there is an affine open
`V ⊆ C` with `p` landing in the chart of `U := piOpen C.toOver V n ⊆ Cⁿ`; that chart is
`Spec A` with `A = Γ(Cⁿ, U)^{S_n}`.

The construction uses the intermediate quotient by the subgroup `S_{n-1} ⊆ S_n` fixing the last
coordinate: the ring `A' = Γ(Cⁿ, U)^{S_{n-1}}` is the chart ring of `Sym^{n-1} C × C`, and
`O := A' ⊗_A F` (the fibre of `Spec A' ⟶ Spec A` over `p`) is the ring `Γ(D, O_D)` of the
(unknown) divisor `D = divOf p`, of dimension `n`.

* `GAction.comap` — restriction of a scheme action along a group homomorphism;
* `lastIdx`, `symStab`, `stabAction` — the subgroup `S_{n-1} ⊆ S_n` and its action on `Cⁿ`;
* `chartInvariants`, `subgroupInvariants` — the rings `A` and `A'`;
* `subgroupInvariants_le` — `A ⊆ A'`;
* `coordMap` — the last-coordinate pullback `Γ(C,V) → A'`;
-/
import Submission.Work.SymQuot.Sym
import Submission.Work.SymQuot.Chart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot

/-- Restriction of an action of a group on a scheme along a group homomorphism. -/
def GAction.comap {G : Type*} [Group G] {G' : Type*} [Group G'] {X : Scheme.{u}}
    (A : GAction G X) (φ : G' →* G) : GAction G' X where
  hom g := A.hom (φ g)
  inv g := A.inv (φ g)
  hom_inv g := A.hom_inv (φ g)
  inv_hom g := A.inv_hom (φ g)
  hom_one := by simp
  hom_mul g h := by simpa only [map_mul] using A.hom_mul (φ g) (φ h)

namespace GAction

variable {G : Type*} [Group G] {G' : Type*} [Group G'] {X : Scheme.{u}} (A : GAction G X)

@[simp] lemma comap_hom (φ : G' →* G) (g : G') : (A.comap φ).hom g = A.hom (φ g) := rfl

@[simp] lemma comap_inv (φ : G' →* G) (g : G') : (A.comap φ).inv g = A.inv (φ g) := rfl

end GAction

variable {K : Type u} [Field K]

/-- The last index `n-1` of `Fin n`, for `n ≠ 0`. -/
def lastIdx (n : ℕ) [NeZero n] : Fin n :=
  Fin.cast (Nat.sub_add_cancel (Nat.pos_of_neZero n)) (Fin.last (n - 1))

@[simp] lemma lastIdx_val (n : ℕ) [NeZero n] : (lastIdx n).val = n - 1 := by
  simp [lastIdx]

/-- The subgroup `S_{n-1} ⊆ S_n` of permutations fixing the last coordinate. -/
def symStab (n : ℕ) [NeZero n] : Subgroup (Equiv.Perm (Fin n)) :=
  MulAction.stabilizer (Equiv.Perm (Fin n)) (lastIdx n)

@[simp] lemma mem_symStab {n : ℕ} [NeZero n] {σ : Equiv.Perm (Fin n)} :
    σ ∈ symStab n ↔ σ (lastIdx n) = lastIdx n := Iff.rfl

variable (C : Work.CurveBasics.Curve K) (n : ℕ) [NeZero n]

/-- The action of `S_{n-1} ⊆ S_n` on the `n`-fold product `Cⁿ`.

The group is `ULift`-ed for the same reason as in `symAction`: the objects of `Sch K` live in
`Type u` while `Equiv.Perm (Fin n)` lives in `Type 0`. -/
noncomputable def stabAction : GAction (ULift.{u} ↥(symStab n)) (prod C.toOver n).left :=
  (symAction C n).comap
    { toFun := fun σ => ULift.up ((σ.down : ↥(symStab n)) : Equiv.Perm (Fin n))
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

variable {C n}

@[simp] lemma stabAction_hom (σ : ULift.{u} ↥(symStab n)) :
    (stabAction C n).hom σ
      = (symAction C n).hom (ULift.up ((σ.down : ↥(symStab n)) : Equiv.Perm (Fin n))) := rfl

/-- The chart ring `A = Γ(Cⁿ, U)^{S_n}` of an invariant open `U ⊆ Cⁿ`. -/
noncomputable abbrev chartInvariants (U : (prod C.toOver n).left.Opens)
    (hU : (symAction C n).IsInvariantOpen U) : Subring Γ((prod C.toOver n).left, U) :=
  (symAction C n).invariants U hU

/-- The subgroup action is invariant on the same opens: an open invariant under `S_n` is
invariant under `S_{n-1} ⊆ S_n`. -/
theorem stabInvariant (U : (prod C.toOver n).left.Opens) (hU : (symAction C n).IsInvariantOpen U) :
    (stabAction C n).IsInvariantOpen U :=
  fun σ => hU (ULift.up ((σ.down : ↥(symStab n)) : Equiv.Perm (Fin n)))

/-- The ring `A' = Γ(Cⁿ, U)^{S_{n-1}}` of invariants of the subgroup
`S_{n-1} ⊆ S_n` fixing the last coordinate. -/
noncomputable def subgroupInvariants (U : (prod C.toOver n).left.Opens)
    (hU : (symAction C n).IsInvariantOpen U) : Subring Γ((prod C.toOver n).left, U) :=
  (stabAction C n).invariants U (stabInvariant (C := C) (n := n) U hU)

@[simp] lemma subgroupInvariants_def (U : (prod C.toOver n).left.Opens)
    (hU : (symAction C n).IsInvariantOpen U) :
    subgroupInvariants (C := C) (n := n) U hU
      = (stabAction C n).invariants U (stabInvariant (C := C) (n := n) U hU) := rfl

end Work.SymQuot
