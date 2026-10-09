/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Level-wise Galois cohomology `H²(·, Z/p)`

This file sets up the *level-wise* cohomology on which the Brauer/local-global development of
`Submission/Work/BrauerHasse/` is built.  For a group `G` (in practice the Galois group of a
finite Galois extension) we put

`H2 p G = groupCohomology (trivial (Z/p) G (Z/p)) 2`,

the second cohomology of `G` with coefficients in the trivial module `Z/p`, computed with
Mathlib's inhomogeneous cochain complex.  Since every representation occurring here is trivial,
all maps we need are instances of Mathlib's `groupCohomology.map f φ n` for a group
homomorphism `f` and an identity morphism of trivial representations.  Packaging this once as
`H2.map` has the effect that *restriction* (`H2.res` along a subgroup inclusion) and *inflation*
(`H2.inf` along a quotient) are the same construction, and all compatibility statements reduce to
`groupCohomology.map_comp`.

## Universe convention

Mathlib's group cohomology requires the coefficient ring and the group to live in the same
universe, while the Galois groups of the intended application live in the universe of the field.
We therefore use `Coeff p = ULift (ZMod p)` as coefficient ring, so that `Coeff p` and any group
`G : Type u` lie in the same universe `u`.  Nothing below depends on the choice of lift.

## Main definitions

* `NK.BrauerHasse.Coeff p` — the coefficient ring `Z/p` lifted to the universe of the group;
* `NK.BrauerHasse.H2 p G` — `H²(G, Z/p)` (as an object of `ModuleCat (Coeff p)`);
* `NK.BrauerHasse.H2.map f` — functoriality in the group;
* `NK.BrauerHasse.H2.res S` — restriction to a subgroup;
* `NK.BrauerHasse.H2.inf S` — inflation along `G →* G ⧸ S`.
-/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory Representation groupCohomology Rep

set_option autoImplicit false

universe u

namespace NK.BrauerHasse

/-- The coefficient ring `Z/p`, lifted into the universe of the group so that Mathlib's group
cohomology functoriality applies. -/
abbrev Coeff (p : ℕ) : Type u := ULift.{u} (ZMod p)

/-- The second cohomology of `G` with coefficients in the trivial module `Z/p`. -/
noncomputable abbrev H2 (p : ℕ) (G : Type u) [Group G] : ModuleCat (Coeff.{u} p) :=
  groupCohomology (Rep.trivial (Coeff.{u} p) G (Coeff.{u} p)) 2

/-- The structural morphism of trivial representations: for `f : G →* H` the trivial
`Z/p`-representation of `H`, restricted along `f`, is the trivial representation of `G`.  It is
literally an identity morphism (its source is only *definitionally* the trivial representation),
which makes all compatibilities below computable. -/
noncomputable def trivHom {p : ℕ} {G H : Type u} [Group G] [Group H] (f : G →* H) :
    Rep.res f (Rep.trivial (Coeff.{u} p) H (Coeff.{u} p)) ⟶
      Rep.trivial (Coeff.{u} p) G (Coeff.{u} p) :=
  (𝟙 (Rep.trivial (Coeff.{u} p) G (Coeff.{u} p)) :
    Rep.res f (Rep.trivial (Coeff.{u} p) H (Coeff.{u} p)) ⟶
      Rep.trivial (Coeff.{u} p) G (Coeff.{u} p))

lemma trivHom_comp {p : ℕ} {G₁ G₂ G₃ : Type u} [Group G₁] [Group G₂] [Group G₃]
    (f : G₂ →* G₃) (g : G₁ →* G₂) :
    trivHom (p := p) (f.comp g) =
      (resFunctor g).map (trivHom (p := p) f) ≫ trivHom (p := p) g := by
  apply Rep.hom_ext
  rfl

/-- **Functoriality of `H²(·, Z/p)`.**  A group homomorphism `f : G →* H` induces a map
`H²(H, Z/p) ⟶ H²(G, Z/p)`. -/
noncomputable def H2.map {p : ℕ} {G H : Type u} [Group G] [Group H] (f : G →* H) :
    H2 p H ⟶ H2 p G :=
  groupCohomology.map f (trivHom f) 2

@[simp]
lemma H2.map_apply {p : ℕ} {G H : Type u} [Group G] [Group H] (f : G →* H) (x : H2 p H) :
    (H2.map f).hom x = (groupCohomology.map f (trivHom f) 2).hom x := rfl

/-- `H2.map` of the identity is the identity. -/
@[simp]
lemma H2.map_id {p : ℕ} {G : Type u} [Group G] :
    H2.map (p := p) (MonoidHom.id G) = 𝟙 (H2 p G) := by
  have h : trivHom (p := p) (MonoidHom.id G) =
      𝟙 (Rep.trivial (Coeff.{u} p) G (Coeff.{u} p)) := rfl
  rw [H2.map, h, groupCohomology.map_id]

/-- **Functoriality of `H2.map` in the group.**  Composition of group homomorphisms corresponds to
composition of the induced maps on cohomology; every compatibility statement in this development
is an instance of this lemma. -/
lemma H2.map_comp {p : ℕ} {G₁ G₂ G₃ : Type u} [Group G₁] [Group G₂] [Group G₃]
    (f : G₂ →* G₃) (g : G₁ →* G₂) :
    H2.map (p := p) (f.comp g) = H2.map (p := p) f ≫ H2.map (p := p) g := by
  rw [H2.map, H2.map, H2.map, trivHom_comp, groupCohomology.map_comp]

/-- `H2.map` is insensitive to the representative of a group homomorphism. -/
lemma H2.map_congr {p : ℕ} {G H : Type u} [Group G] [Group H] {f g : G →* H} (h : f = g) :
    H2.map (p := p) f = H2.map (p := p) g := by
  subst h; rfl

/-- Restriction along the inclusion of a subgroup. -/
noncomputable def H2.res {p : ℕ} {G : Type u} [Group G] (S : Subgroup G) :
    H2 p G ⟶ H2 p S :=
  H2.map S.subtype

/-- Inflation along the quotient map `G →* G ⧸ S` for a normal subgroup `S`. -/
noncomputable def H2.inf {p : ℕ} {G : Type u} [Group G] (S : Subgroup G) [S.Normal] :
    H2 p (G ⧸ S) ⟶ H2 p G :=
  H2.map (QuotientGroup.mk' S)

/-- Restriction in a tower of subgroups. -/
lemma H2.res_comp {p : ℕ} {G : Type u} [Group G] {S T : Subgroup G} (h : S ≤ T) :
    H2.res (p := p) S = H2.res (p := p) T ≫ H2.map (p := p) (Subgroup.inclusion h) := by
  rw [H2.res, H2.res, ← H2.map_comp]
  congr 1

end NK.BrauerHasse
