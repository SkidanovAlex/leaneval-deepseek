/-
Copyright (c) 2025. All rights reserved.

# `H¹` of a group with trivial coefficients

For a group `G` and an additive commutative group `A` with the **trivial** action
(`TrivMod G A`), the low-degree complex of `Work/GroupCohomology/Basic.lean` degenerates:

* the coboundary `d⁰ a = (g ↦ g • a - a)` vanishes identically, so `B¹(G, A) = 0`;
* the `1`-cocycle condition `f (g * h) = g • f h + f g` becomes `f (g * h) = f h + f g`,
  i.e. `f` is exactly an additive homomorphism `Additive G →+ A` on the additive group
  underlying `G`.

Consequently

`H¹(G, A) ≅ Additive G →+ A`,   `H1_trivMod_addEquiv`,

an isomorphism of additive groups; this is the `H¹` companion of the cyclic computation
`H²(ℤ/n, A) ≅ A/nA` in `Submission/Work/GroupCohomology/H2_cyclic_trivial.lean`.
-/
import Mathlib
import Submission.Work.GroupCohomology.Cyclic
import Submission.Work.GroupCohomology.Basic
import Submission.Work.GroupCohomology.H1pi_eq_zero_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

/-- With trivial coefficients the `0`th coboundary vanishes identically, hence `B¹ = 0`. -/
theorem B1_trivMod_eq_bot (G : Type*) (A : Type*) [Group G] [AddCommGroup A] :
    B1 G (TrivMod G A) = ⊥ := by
  rw [AddSubgroup.eq_bot_iff_forall]
  intro f hf
  obtain ⟨a, ha⟩ := (mem_B1_iff (G := G) (A := TrivMod G A) f).mp hf
  rw [← ha]
  funext g
  simp [d0_apply]

/-- With trivial coefficients the crossed homomorphism condition is additive in the group law
of `G` (in the "wrong" order, which is irrelevant as `A` is commutative). -/
theorem mem_Z1_trivMod_iff (G : Type*) (A : Type*) [Group G] [AddCommGroup A]
    (f : G → TrivMod G A) :
    f ∈ Z1 G (TrivMod G A) ↔ ∀ g h : G, f (g * h) = f h + f g := Iff.rfl

/-- The `1`-cocycles with trivial coefficients are exactly the additive homomorphisms on the
additive group underlying `G`: `f ↦ (g ↦ f g)`. -/
noncomputable def trivZ1ToAddHom (G : Type*) (A : Type*) [Group G] [AddCommGroup A] :
    Z1 G (TrivMod G A) →+ (Additive G →+ A) where
  toFun f :=
    { toFun := fun g => (f : G → TrivMod G A) (Additive.toMul g)
      map_zero' := by
        show (f : G → TrivMod G A) (Additive.toMul (0 : Additive G)) = 0
        rw [show (0 : Additive G) = Additive.ofMul 1 from rfl, toMul_ofMul]
        exact Z1.map_one G (TrivMod G A) f.2
      map_add' := fun x y => by
        have h := (mem_Z1_trivMod_iff G A (f : G → TrivMod G A)).mp f.2
          (Additive.toMul x) (Additive.toMul y)
        show (f : G → TrivMod G A) (Additive.toMul x * Additive.toMul y) =
          (f : G → TrivMod G A) (Additive.toMul x) + (f : G → TrivMod G A) (Additive.toMul y)
        rw [h, add_comm] }
  map_zero' := by
    apply AddMonoidHom.ext
    intro g
    show ((0 : Z1 G (TrivMod G A)) : G → TrivMod G A) (Additive.toMul g) = 0
    simp
  map_add' := fun f f' => by
    apply AddMonoidHom.ext
    intro g
    show (((f + f') : Z1 G (TrivMod G A)) : G → TrivMod G A) (Additive.toMul g) =
      (f : G → TrivMod G A) (Additive.toMul g) + (f' : G → TrivMod G A) (Additive.toMul g)
    simp

/-- Conversely, an additive homomorphism on the additive group underlying `G` is a `1`-cocycle
with trivial coefficients: `φ ↦ (g ↦ φ g)`. -/
noncomputable def addHomToTrivZ1 (G : Type*) (A : Type*) [Group G] [AddCommGroup A] :
    (Additive G →+ A) →+ Z1 G (TrivMod G A) where
  toFun φ :=
    ⟨fun g => φ (Additive.ofMul g), by
      intro g h
      show φ (Additive.ofMul (g * h)) = φ (Additive.ofMul h) + φ (Additive.ofMul g)
      rw [ofMul_mul, map_add, add_comm]⟩
  map_zero' := by
    refine Subtype.ext ?_
    funext g
    show (0 : Additive G →+ A) (Additive.ofMul g) = 0
    simp
  map_add' := fun φ ψ => by
    refine Subtype.ext ?_
    funext g
    show (φ + ψ) (Additive.ofMul g) = φ (Additive.ofMul g) + ψ (Additive.ofMul g)
    simp

theorem addHomToTrivZ1_left_inv (G : Type*) (A : Type*) [Group G] [AddCommGroup A]
    (f : Z1 G (TrivMod G A)) :
    addHomToTrivZ1 G A (trivZ1ToAddHom G A f) = f := by
  refine Subtype.ext ?_
  funext g
  show (f : G → TrivMod G A) (Additive.toMul (Additive.ofMul g)) = (f : G → TrivMod G A) g
  rw [toMul_ofMul]

theorem trivZ1ToAddHom_right_inv (G : Type*) (A : Type*) [Group G] [AddCommGroup A]
    (φ : Additive G →+ A) :
    trivZ1ToAddHom G A (addHomToTrivZ1 G A φ) = φ := by
  apply AddMonoidHom.ext
  intro g
  show φ (Additive.ofMul (Additive.toMul g)) = φ g
  rw [ofMul_toMul]

/-- `Z¹(G, A) ≃+ (Additive G →+ A)` for trivial coefficients. -/
noncomputable def trivZ1AddEquiv (G : Type*) (A : Type*) [Group G] [AddCommGroup A] :
    Z1 G (TrivMod G A) ≃+ (Additive G →+ A) where
  toFun := trivZ1ToAddHom G A
  invFun := addHomToTrivZ1 G A
  map_add' := (trivZ1ToAddHom G A).map_add
  left_inv := addHomToTrivZ1_left_inv G A
  right_inv := trivZ1ToAddHom_right_inv G A

/-- `H¹` of a group with coefficients in a trivial module is the additive group of
homomorphisms `Additive G →+ A`. -/
theorem H1_trivMod_addEquiv (G : Type*) (A : Type*) [Group G] [AddCommGroup A] :
    Nonempty (Work.GroupCohomology.H1 G (Work.GroupCohomology.TrivMod G A) ≃+
      (Additive G →+ A)) := by
  have hbot : (B1 G (TrivMod G A)).comap (Z1 G (TrivMod G A)).subtype = ⊥ := by
    rw [B1_trivMod_eq_bot G A]
    ext x
    simp
  refine ⟨?_⟩
  show ((Z1 G (TrivMod G A) : AddSubgroup (G → TrivMod G A)) ⧸
      ((B1 G (TrivMod G A)).comap (Z1 G (TrivMod G A)).subtype)) ≃+ (Additive G →+ A)
  rw [hbot]
  exact (QuotientAddGroup.quotientBot).trans (trivZ1AddEquiv G A)

end Work.GroupCohomology
