/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The action of a quotient group on the orbits of a normal subgroup

Let `N ◁ G` and let `X` be a `G`-set.  The quotient group `G ⧸ N` acts on the set
`MulAction.orbitRel.Quotient N X` of `N`-orbits of `X`, by `(gN) • (N·x) = N·(g·x)`.

This is the action used in the corrected form of Serre §5 / JL Lemma 4.1 (the vertex set of the
quotient tree is the set of orbits of the normal subgroup), see
`Submission.Work.ORBassSerre.Assembly.quotientTreeByNormalClosureOfElliptic_corrected`.

The construction: the `G`-action on the `N`-orbits (`orbitMap`) is trivial on `N`
(`orbitMap_eq_self_of_mem`), so it descends along the surjection `G →* G ⧸ N`
(`MulAction.ofEndHom` + `QuotientGroup.lift`).

## Main definitions and results

* `Work.ORBassSerre.orbitMap`, `Work.ORBassSerre.orbitMapHom` : the `G`-action on `N`-orbits;
* `Work.ORBassSerre.instMulActionQuotientOrbit` : the induced `G ⧸ N`-action;
* `Work.ORBassSerre.quotient_smul_mk` : `(gN) • (N·x) = N·(g·x)`.
-/
import Submission.Work.ORBassSerre.Action.QuotientReverse
import Mathlib.GroupTheory.GroupAction.OfQuotient

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

namespace Work.ORBassSerre

open Quiver

section QuotientAction

variable {G : Type u} {X : Type u} [Group G] [MulAction G X] (N : Subgroup G) [N.Normal]

/-- The `N`-orbit relation is compatible with the `G`-action. -/
theorem orbitRel_smul {g : G} {a b : X} (h : MulAction.orbitRel N X a b) :
    MulAction.orbitRel N X (g • a) (g • b) := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h ⊢
  obtain ⟨n, hn⟩ := h
  refine ⟨⟨g * (n : G) * g⁻¹, (inferInstance : N.Normal).conj_mem (n : G) n.2 g⟩, ?_⟩
  rw [Subgroup.mk_smul, mul_smul, mul_smul, inv_smul_smul, ← Subgroup.smul_def, hn]

/-- The map induced by `g : G` on the `N`-orbits of `X`. -/
def orbitMap (g : G) :
    MulAction.orbitRel.Quotient N X → MulAction.orbitRel.Quotient N X :=
  Quotient.map (fun x => g • x) (fun _ _ h => orbitRel_smul N h)

@[simp] theorem orbitMap_mk (g : G) (x : X) :
    orbitMap (X := X) N g (Quotient.mk'' x) = Quotient.mk'' (g • x) :=
  Quotient.map_mk _ _ _

theorem orbitMap_one_apply (q : MulAction.orbitRel.Quotient N X) :
    orbitMap (X := X) N (1 : G) q = q :=
  Quotient.inductionOn q (fun (x : X) => by rw [orbitMap_mk, one_smul])

theorem orbitMap_mul_apply (g h : G) (q : MulAction.orbitRel.Quotient N X) :
    orbitMap (X := X) N (g * h) q = orbitMap (X := X) N g (orbitMap (X := X) N h q) :=
  Quotient.inductionOn q (fun (x : X) => by rw [orbitMap_mk, orbitMap_mk, orbitMap_mk, mul_smul])

theorem orbitMap_one : orbitMap (X := X) N (1 : G) = id :=
  funext (orbitMap_one_apply N)

theorem orbitMap_mul (g h : G) :
    orbitMap (X := X) N (g * h) = orbitMap (X := X) N g ∘ orbitMap (X := X) N h :=
  funext (orbitMap_mul_apply N g h)

/-- The `G`-action on the `N`-orbits of `X`, as a homomorphism to `Function.End`. -/
def orbitMapHom : G →* Function.End (MulAction.orbitRel.Quotient N X) where
  toFun := orbitMap (X := X) N
  map_one' := orbitMap_one N
  map_mul' g h := funext (orbitMap_mul_apply N g h)

@[simp] theorem orbitMapHom_apply (g : G) (q : MulAction.orbitRel.Quotient N X) :
    orbitMapHom N g q = orbitMap (X := X) N g q := rfl

instance instMulActionOrbit : MulAction G (MulAction.orbitRel.Quotient N X) :=
  MulAction.ofEndHom (orbitMapHom N)

/-- The `G`-action on the `N`-orbits is trivial on `N`. -/
theorem orbitMap_eq_self_of_mem (n : G) (hn : n ∈ N) (q : MulAction.orbitRel.Quotient N X) :
    orbitMap (X := X) N n q = q := by
  refine Quotient.inductionOn q (fun x => ?_)
  rw [orbitMap_mk]
  refine Quotient.sound (show MulAction.orbitRel N X (n • x) x from ?_)
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨⟨n, hn⟩, rfl⟩

@[simp] theorem orbit_smul_eq_self_of_mem (n : G) (hn : n ∈ N)
    (q : MulAction.orbitRel.Quotient N X) : n • q = q := by
  show orbitMapHom N n q = q
  exact orbitMap_eq_self_of_mem N n hn q

/-- The `G ⧸ N`-action on the `N`-orbits of `X`, as a homomorphism to `Function.End`. -/
def quotientOrbitHom : G ⧸ N →* Function.End (MulAction.orbitRel.Quotient N X) :=
  QuotientGroup.lift N (orbitMapHom N) (by
    intro n hn
    funext q
    exact orbitMap_eq_self_of_mem N n hn q)

instance instMulActionQuotientOrbit : MulAction (G ⧸ N) (MulAction.orbitRel.Quotient N X) :=
  MulAction.ofEndHom (quotientOrbitHom N)

@[simp] theorem quotientOrbitHom_mk (g : G) :
    quotientOrbitHom N (QuotientGroup.mk' N g) = orbitMapHom (X := X) N g := rfl

/-- The `G ⧸ N`-action on `N`-orbits, computed on representatives. -/
theorem quotient_smul_mk (g : G) (x : X) :
    (QuotientGroup.mk' N g) • (Quotient.mk'' x : MulAction.orbitRel.Quotient N X) =
      Quotient.mk'' (g • x) := by
  change (quotientOrbitHom N (QuotientGroup.mk' N g)) (Quotient.mk'' x) = Quotient.mk'' (g • x)
  rw [quotientOrbitHom_mk, orbitMapHom_apply, orbitMap_mk]

/-- Elements of `N` act trivially in the quotient. -/
theorem quotient_smul_eq_self_of_mem (n : G) (hn : n ∈ N)
    (q : MulAction.orbitRel.Quotient N X) : (QuotientGroup.mk' N n) • q = q := by
  have h : (QuotientGroup.mk' N n : G ⧸ N) = 1 := by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff (N := N) n).mpr hn
  rw [h, one_smul]

end QuotientAction

end Work.ORBassSerre
