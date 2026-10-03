/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Functoriality of `Rat(U)` in the group `U`

`Rat(U)` is the *initial* rational `U`-semiring ([JZLA20, Lemma 4.2]).  It is therefore functorial
in `U`: a group isomorphism `e : U ≃* V` transports the rational `V`-semiring structure of `Rat(V)`
along `e`, and the universal property produces a ring isomorphism `Rat(U) ≃+* Rat(V)`.

The two additional properties recorded here are the ones used later in the paper's argument:

* the isomorphism is compatible with the canonical images of the groups,
  `E (ofGroup u) = ofGroup (e u)`;
* it preserves the complexity `Tree` of [JZLA20, Lemma 4.3].

Both are consequences of the *uniqueness* part of the universal property of `Rat(U)`
(`RatU.lift_unique`).
-/
import Mathlib
import Submission.Work.ORHughesFree.Rat.Source
import Submission.Work.ORHughesFree.Rat.RTerm
import Submission.Work.ORHughesFree.Rat.OfGroup
import Submission.Work.ORHughesFree.Rat.ratComplexity_model

set_option autoImplicit false

namespace Work.ORHughesFree.Rat

open Work.ORHughesFree

variable {U V : Type} [Group U] [Group V]

/-! ### Transporting the rational structure along a group isomorphism -/

/-- **Transport of the rational `V`-semiring structure of `Rat(V)` along `e : U ≃* V`**: the
underlying ring is `Rat(V)`, and the `U`-biset structure is obtained from the `V`-biset structure
by acting through `e`. -/
noncomputable def comap (e : U ≃* V) : RationalUSemiring U (RatU V) where
  ratOp := (RatU.rational (U := V)).ratOp
  ratOp_zero := (RatU.rational (U := V)).ratOp_zero
  smul u x := (RatU.rational (U := V)).smul (e u) x
  smulRight x u := (RatU.rational (U := V)).smulRight x (e u)
  smul_eq_mul u r := (RatU.rational (U := V)).smul_eq_mul (e u) r
  smulRight_eq_mul r u := (RatU.rational (U := V)).smulRight_eq_mul r (e u)
  smul_mul u v := by
    show (RatU.rational (U := V)).smul (e (u * v)) 1 =
      (RatU.rational (U := V)).smul (e u) 1 * (RatU.rational (U := V)).smul (e v) 1
    rw [map_mul, (RatU.rational (U := V)).smul_mul]
  smul_one_one := by
    show (RatU.rational (U := V)).smul (e 1) 1 = 1
    rw [map_one, (RatU.rational (U := V)).smul_one_one]
  smulRight_one_one := by
    show (RatU.rational (U := V)).smulRight 1 (e 1) = 1
    rw [map_one, (RatU.rational (U := V)).smulRight_one_one]
  smulRight_one u := by
    show (RatU.rational (U := V)).smulRight 1 (e u) =
      (RatU.rational (U := V)).smul (e u) 1
    rw [(RatU.rational (U := V)).smulRight_one]
  rat_smul u v r := by
    show (RatU.rational (U := V)).ratOp
        ((RatU.rational (U := V)).smul (e u) ((RatU.rational (U := V)).smulRight r (e v))) =
      (RatU.rational (U := V)).smulRight
        ((RatU.rational (U := V)).smul (e v⁻¹) ((RatU.rational (U := V)).ratOp r)) (e u⁻¹)
    rw [(RatU.rational (U := V)).rat_smul, MulEquiv.map_inv, MulEquiv.map_inv]

/-- The ring homomorphism `Rat(U) →+* Rat(V)` induced by a group isomorphism `e : U ≃* V`,
via the universal property of `Rat(U)` applied to `Rat(V)` with its transported rational
`U`-semiring structure (`comap e`). -/
noncomputable def transport (e : U ≃* V) : RatU U →+* RatU V :=
  RatU.lift (RatU V) (comap e)

theorem transport_rat (e : U ≃* V) (x : RatU U) :
    transport e (RatU.ratOp x) = RatU.ratOp (transport e x) :=
  (RatU.lift_isHom (RatU V) (comap e)).map_rat x

theorem transport_smul (e : U ≃* V) (u : U) (x : RatU U) :
    transport e (RatU.smul u x) = RatU.smul (e u) (transport e x) :=
  (RatU.lift_isHom (RatU V) (comap e)).map_smul u x

theorem transport_smulRight (e : U ≃* V) (x : RatU U) (u : U) :
    transport e (RatU.smulRight x u) = RatU.smulRight (transport e x) (e u) :=
  (RatU.lift_isHom (RatU V) (comap e)).map_smulRight x u

/-! ### The two composites are the identity

`transport e.symm ∘ transport e` and `transport e ∘ transport e.symm` are both morphisms of
rational semirings out of an initial object, hence the identity by `RatU.lift_unique`. -/

theorem transport_comp_symm (e : U ≃* V) :
    (transport e.symm).comp (transport e) = RingHom.id (RatU U) := by
  have hid : IsRationalUSemiringHom (RatU.rational (U := U)) (RatU.rational (U := U))
      (RingHom.id (RatU U)) := ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  have hcomp : IsRationalUSemiringHom (RatU.rational (U := U)) (RatU.rational (U := U))
      ((transport e.symm).comp (transport e)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      show transport e.symm (transport e (RatU.ratOp x)) =
        RatU.ratOp (transport e.symm (transport e x))
      rw [transport_rat e x, transport_rat e.symm (transport e x)]
    · intro u x
      show transport e.symm (transport e (RatU.smul u x)) =
        RatU.smul u (transport e.symm (transport e x))
      rw [transport_smul e u x, transport_smul e.symm (e u) (transport e x),
        MulEquiv.symm_apply_apply]
    · intro x u
      show transport e.symm (transport e (RatU.smulRight x u)) =
        RatU.smulRight (transport e.symm (transport e x)) u
      rw [transport_smulRight e x u, transport_smulRight e.symm (transport e x) (e u),
        MulEquiv.symm_apply_apply]
  rw [RatU.lift_unique (RatU U) (RatU.rational (U := U)) _ hcomp,
    (RatU.lift_unique (RatU U) (RatU.rational (U := U)) (RingHom.id (RatU U)) hid).symm]

theorem transport_symm_comp (e : U ≃* V) :
    (transport e).comp (transport e.symm) = RingHom.id (RatU V) := by
  have hid : IsRationalUSemiringHom (RatU.rational (U := V)) (RatU.rational (U := V))
      (RingHom.id (RatU V)) := ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  have hcomp : IsRationalUSemiringHom (RatU.rational (U := V)) (RatU.rational (U := V))
      ((transport e).comp (transport e.symm)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro y
      show transport e (transport e.symm (RatU.ratOp y)) =
        RatU.ratOp (transport e (transport e.symm y))
      rw [transport_rat e.symm y, transport_rat e (transport e.symm y)]
    · intro v y
      show transport e (transport e.symm (RatU.smul v y)) =
        RatU.smul v (transport e (transport e.symm y))
      rw [transport_smul e.symm v y, transport_smul e (e.symm v) (transport e.symm y),
        MulEquiv.apply_symm_apply]
    · intro y v
      show transport e (transport e.symm (RatU.smulRight y v)) =
        RatU.smulRight (transport e (transport e.symm y)) v
      rw [transport_smulRight e.symm y v, transport_smulRight e (transport e.symm y) (e.symm v),
        MulEquiv.apply_symm_apply]
  rw [RatU.lift_unique (RatU V) (RatU.rational (U := V)) _ hcomp,
    (RatU.lift_unique (RatU V) (RatU.rational (U := V)) (RingHom.id (RatU V)) hid).symm]

/-- The ring isomorphism `Rat(U) ≃+* Rat(V)` induced by a group isomorphism `e : U ≃* V`. -/
noncomputable def transportRingEquiv (e : U ≃* V) : RatU U ≃+* RatU V :=
  RingEquiv.mk
    { toFun := transport e
      invFun := transport e.symm
      left_inv := fun x => by
        have h := DFunLike.congr_fun (transport_comp_symm e) x
        simpa [RingHom.comp_apply] using h
      right_inv := fun x => by
        have h := DFunLike.congr_fun (transport_symm_comp e) x
        simpa [RingHom.comp_apply] using h }
    (fun x y => map_mul (transport e) x y)
    (fun x y => map_add (transport e) x y)

@[simp] theorem transportRingEquiv_apply (e : U ≃* V) (x : RatU U) :
    transportRingEquiv e x = transport e x := rfl

/-- The isomorphism `Rat(U) ≃+* Rat(V)` carries `ofGroup u` to `ofGroup (e u)`. -/
theorem transportRingEquiv_ofGroup (e : U ≃* V) (u : U) :
    transportRingEquiv e (RatU.ofGroup u) = RatU.ofGroup (e u) := by
  rw [transportRingEquiv_apply, RatU.ofGroup_def, RatU.ofGroup_def, transport_smul e u 1,
    map_one]

/-! ### The isomorphism preserves the complexity `Tree` -/

/-- The composite `Tree ∘ transport e : Rat(U) → T` is a morphism of rational `U`-semirings from
`Rat(U)` to the trees (with their trivial action), so it is the universal map `Tree`. -/
theorem treeOfRat_transport (e : U ≃* V) (x : RatU U) :
    Rat.treeOfRat V (transport e x) = Rat.treeOfRat U x := by
  have hTree : IsRationalUSemiringHom (RatU.rational (U := U)) (treeRational (U := U))
      ((RatU.lift Tree (treeRational (U := V))).comp (transport e)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro y
      show RatU.lift Tree (treeRational (U := V)) (transport e (RatU.ratOp y)) =
        (treeRational (U := U)).ratOp (RatU.lift Tree (treeRational (U := V)) (transport e y))
      rw [transport_rat e y]
      exact (RatU.lift_isHom Tree (treeRational (U := V))).map_rat (transport e y)
    · intro u y
      show RatU.lift Tree (treeRational (U := V)) (transport e (RatU.smul u y)) =
        (treeRational (U := U)).smul u (RatU.lift Tree (treeRational (U := V)) (transport e y))
      rw [transport_smul e u y]
      exact (RatU.lift_isHom Tree (treeRational (U := V))).map_smul (e u) (transport e y)
    · intro y u
      show RatU.lift Tree (treeRational (U := V)) (transport e (RatU.smulRight y u)) =
        (treeRational (U := U)).smulRight (RatU.lift Tree (treeRational (U := V)) (transport e y)) u
      rw [transport_smulRight e y u]
      exact (RatU.lift_isHom Tree (treeRational (U := V))).map_smulRight (transport e y) (e u)
  have heq := RatU.lift_unique (Tree) (treeRational (U := U))
    ((RatU.lift Tree (treeRational (U := V))).comp (transport e)) hTree
  have hx := DFunLike.congr_fun heq x
  simpa only [Rat.treeOfRat, RingHom.comp_apply] using hx

/-- The isomorphism `Rat(U) ≃+* Rat(V)` preserves the complexity `Tree`. -/
theorem treeOfRat_transportRingEquiv (e : U ≃* V) (x : RatU U) :
    Rat.treeOfRat V (transportRingEquiv e x) = Rat.treeOfRat U x := by
  rw [transportRingEquiv_apply]
  exact treeOfRat_transport e x

theorem exists_ringEquiv_of_mulEquiv {U V : Type} [Group U] [Group V] (e : U ≃* V) :
    ∃ E : Work.ORHughesFree.RatU U ≃+* Work.ORHughesFree.RatU V,
      (∀ u : U, E (Work.ORHughesFree.RatU.ofGroup u) = Work.ORHughesFree.RatU.ofGroup (e u)) ∧
      (∀ x : Work.ORHughesFree.RatU U,
        Work.ORHughesFree.Rat.treeOfRat V (E x) = Work.ORHughesFree.Rat.treeOfRat U x) :=
  ⟨transportRingEquiv e, fun u => transportRingEquiv_ofGroup e u,
    fun x => treeOfRat_transportRingEquiv e x⟩

end Work.ORHughesFree.Rat
