/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Functoriality of `Rat(U)` in the group `U`

`Rat(U)` is functorial not only in group *isomorphisms* (`Rat/Transport`:
`Rat.transportRingEquiv`) but in *arbitrary group homomorphisms*: the universal property of
`Rat(U)` produces, for every `f : N →* N'`, a ring homomorphism

`RatU.mapHom f : Rat(N) →+* Rat(N')`,

namely the unique morphism of rational `N`-semirings for the rational structure on `Rat(N')`
obtained by pulling back its `N'`-action along `f` (`Rat.comapHom f`).

In particular `RatU.ofSubgroup V = RatU.mapHom V.subtype`, and `Rat.transportRingEquiv e`
agrees with `RatU.mapHom ↑e`; this makes `ofSubgroup` and the transport of
`Rat/exists_ringEquiv_of_mulEquiv.lean` two instances of a single construction, which is what
makes the *naturality* statements below (subgroups mapped along `f`, inclusions) formal
consequences of functoriality.

The properties recorded here are:

* `RatU.mapHom_ofGroup` : `mapHom f (ofGroup u) = ofGroup (f u)`;
* `RatU.mapHom_id`, `RatU.mapHom_comp` : functoriality;
* `Rat.treeOfRat_mapHom` : `mapHom f` preserves the complexity `Tree` (delegated, in
  `Rat/treeOfRat_mapHom.lean`);
* `RatU.mapHom_ofSubgroup` : naturality for the canonical maps `ofSubgroup` (delegated, in
  `Rat/mapHom_ofSubgroup.lean`);
* `RatU.ofSubgroup_eq_mapHom`, `RatU.ofSubgroup_mapHom_inclusion`, `Rat.transport_eq_mapHom`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Rat.Restrict
import Submission.Work.ORHughesFree.Rat.exists_ringEquiv_of_mulEquiv

set_option autoImplicit false

namespace Work.ORHughesFree

namespace Rat

variable {N N' : Type} [Group N] [Group N']

/-- The rational `N`-semiring structure on `Rat(N')` obtained by pulling back the `N'`-action
along a group homomorphism `f : N →* N'`.  For `f = V.subtype : ↥V →* N` this is exactly
`RatU.restrictScalars V` (see `RatU.ofSubgroup_eq_mapHom`), so that the canonical maps
`RatU.ofSubgroup V` and the transports of `Rat.exists_ringEquiv_of_mulEquiv` are both instances of
the single functor `RatU.mapHom`. -/
noncomputable def comapHom (f : N →* N') : RationalUSemiring N (RatU N') where
  ratOp := (RatU.rational (U := N')).ratOp
  ratOp_zero := (RatU.rational (U := N')).ratOp_zero
  smul u x := (RatU.rational (U := N')).smul (f u) x
  smulRight x u := (RatU.rational (U := N')).smulRight x (f u)
  smul_eq_mul u r := (RatU.rational (U := N')).smul_eq_mul (f u) r
  smulRight_eq_mul r u := (RatU.rational (U := N')).smulRight_eq_mul r (f u)
  smul_mul u v := by
    simpa only [map_mul] using (RatU.rational (U := N')).smul_mul (f u) (f v)
  smul_one_one := by
    simpa only [map_one] using (RatU.rational (U := N')).smul_one_one
  smulRight_one_one := by
    simpa only [map_one] using (RatU.rational (U := N')).smulRight_one_one
  smulRight_one u := by
    simpa only [map_one] using (RatU.rational (U := N')).smulRight_one (f u)
  rat_smul u v r := by
    rw [map_inv, map_inv]
    exact (RatU.rational (U := N')).rat_smul (f u) (f v) r

@[simp] theorem comapHom_ratOp (f : N →* N') :
    (comapHom f).ratOp = (RatU.rational (U := N')).ratOp := rfl

@[simp] theorem comapHom_smul (f : N →* N') (u : N) (x : RatU N') :
    (comapHom f).smul u x = (RatU.rational (U := N')).smul (f u) x := rfl

@[simp] theorem comapHom_smulRight (f : N →* N') (x : RatU N') (u : N) :
    (comapHom f).smulRight x u = (RatU.rational (U := N')).smulRight x (f u) := rfl

end Rat

namespace RatU

variable {N N' N'' : Type} [Group N] [Group N'] [Group N'']

/-- **Functoriality of `Rat(-)` in an arbitrary group homomorphism**: the ring homomorphism
`Rat(N) →+* Rat(N')` induced by `f : N →* N'` through the universal property of `Rat(N)` and the
rational `N`-structure `Rat.comapHom f` on `Rat(N')`. -/
noncomputable def mapHom (f : N →* N') : RatU N →+* RatU N' :=
  RatU.lift (RatU N') (Rat.comapHom f)

/-- `RatU.mapHom f` is the unique morphism of rational `N`-semirings `Rat(N) → Rat(N')` for the
structure `Rat.comapHom f`. -/
theorem mapHom_isHom (f : N →* N') :
    IsRationalUSemiringHom (RatU.rational (U := N)) (Rat.comapHom f) (RatU.mapHom f) :=
  RatU.lift_isHom (RatU N') (Rat.comapHom f)

@[simp] theorem mapHom_one (f : N →* N') : RatU.mapHom f 1 = 1 := map_one _

/-- `RatU.mapHom f` sends the image of a group element to the image of its image. -/
theorem mapHom_ofGroup (f : N →* N') (u : N) :
    RatU.mapHom f (RatU.ofGroup u) = RatU.ofGroup (f u) := by
  rw [RatU.ofGroup_eq_rational u, (RatU.mapHom_isHom f).map_smul, map_one]
  rfl

/-- `RatU.mapHom` of the identity is the identity. -/
@[simp] theorem mapHom_id : RatU.mapHom (MonoidHom.id N) = RingHom.id (RatU N) := by
  refine (RatU.lift_unique (RatU N) (Rat.comapHom (MonoidHom.id N)) (RingHom.id (RatU N))
    ?_).symm
  exact ⟨fun x => rfl, fun u x => rfl, fun x u => rfl⟩

/-- **Functoriality**: `RatU.mapHom` respects composition. -/
theorem mapHom_comp (f : N →* N') (g : N' →* N'') :
    (RatU.mapHom (g.comp f) : RatU N →+* RatU N'') = (RatU.mapHom g).comp (RatU.mapHom f) := by
  refine (RatU.lift_unique (RatU N'') (Rat.comapHom (g.comp f)) _ ?_).symm
  refine ⟨?_, ?_, ?_⟩
  · intro x
    simp only [RingHom.comp_apply]
    rw [(RatU.mapHom_isHom f).map_rat x, Rat.comapHom_ratOp f,
      (RatU.mapHom_isHom g).map_rat (RatU.mapHom f x), Rat.comapHom_ratOp g,
      Rat.comapHom_ratOp (g.comp f)]
  · intro u x
    simp only [RingHom.comp_apply]
    rw [(RatU.mapHom_isHom f).map_smul u x, Rat.comapHom_smul f,
      (RatU.mapHom_isHom g).map_smul (f u) (RatU.mapHom f x), Rat.comapHom_smul g,
      Rat.comapHom_smul (g.comp f)]
    rfl
  · intro x u
    simp only [RingHom.comp_apply]
    rw [(RatU.mapHom_isHom f).map_smulRight x u, Rat.comapHom_smulRight f,
      (RatU.mapHom_isHom g).map_smulRight (RatU.mapHom f x) (f u),
      Rat.comapHom_smulRight g, Rat.comapHom_smulRight (g.comp f)]
    rfl

/-- **`ofSubgroup` is `mapHom` of the inclusion**: the canonical map `Rat(V) → Rat(N)` for a
subgroup `V ≤ N` is the functor `RatU.mapHom` evaluated at `V.subtype`. -/
theorem ofSubgroup_eq_mapHom (V : Subgroup N) :
    (RatU.ofSubgroup V : RatU ↥V →+* RatU N) = RatU.mapHom V.subtype := by
  have h : RatU.restrictScalars V = Rat.comapHom V.subtype := by
    refine RationalUSemiring.ext ?_ ?_ ?_
    · rfl
    · funext v x; rfl
    · funext x v; rfl
  unfold RatU.ofSubgroup RatU.mapHom
  rw [h]

/-- `Rat(U)` is functorial in an inclusion of subgroups: the map `Rat(W) → Rat(S)` induced by
`W ≤ S` is compatible with the canonical maps into `Rat(N)`. -/
theorem ofSubgroup_mapHom_inclusion {W S : Subgroup N} (h : W ≤ S) (x : RatU ↥W) :
    RatU.ofSubgroup S (RatU.mapHom (Subgroup.inclusion h) x) = RatU.ofSubgroup W x := by
  have hcomp : S.subtype.comp (Subgroup.inclusion h) = W.subtype := by
    ext w; rfl
  have h1 : RatU.mapHom S.subtype (RatU.mapHom (Subgroup.inclusion h) x)
      = RatU.mapHom (S.subtype.comp (Subgroup.inclusion h)) x := by
    rw [RatU.mapHom_comp (Subgroup.inclusion h) S.subtype]
    rfl
  have h2 : RatU.ofSubgroup S (RatU.mapHom (Subgroup.inclusion h) x)
      = RatU.mapHom S.subtype (RatU.mapHom (Subgroup.inclusion h) x) := by
    rw [RatU.ofSubgroup_eq_mapHom S]
  rw [h2, h1, hcomp, ← RatU.ofSubgroup_eq_mapHom W]

end RatU

namespace Rat

variable {N N' : Type} [Group N] [Group N']

/-- The transport `Rat.transport e` of `Rat/exists_ringEquiv_of_mulEquiv.lean` is the functor
`RatU.mapHom` evaluated at the homomorphism underlying `e`. -/
theorem transport_eq_mapHom (e : N ≃* N') :
    (Rat.transport e : RatU N →+* RatU N') = RatU.mapHom (e : N →* N') := by
  have h : Rat.comap e = Rat.comapHom (e : N →* N') := by
    refine RationalUSemiring.ext ?_ ?_ ?_
    · rfl
    · funext u x; rfl
    · funext x u; rfl
  unfold RatU.mapHom Rat.transport
  rw [h]

end Rat

end Work.ORHughesFree
