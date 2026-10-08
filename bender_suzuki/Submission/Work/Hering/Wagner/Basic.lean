import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Toolkit for Wagner's proposition (Peterfalvi I §1, p.188)

This file sets up the vocabulary used in the formalisation of Wagner's proposition
(`Work.Hering.Wagner.WagnerProp`): the action of `GL(V)` on the Grassmannians and on the
nonzero vectors of a finite-dimensional `𝔽₂`-space, the number of orbits of a subgroup on an
invariant subset, and the elementary counting lemmas that go with them.

Everything is run for `V` a finite-dimensional vector space over `ZMod 2`.
-/

set_option autoImplicit false

namespace Work.Hering.Wagner

open Module Submodule

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-! ## `GL(V)` is finite when `V` is -/

instance instFiniteLinearEquiv [Finite V] : Finite (V ≃ₗ[ZMod 2] V) :=
  Finite.of_injective (fun f : V ≃ₗ[ZMod 2] V => (f : V → V))
    (fun f g h => LinearEquiv.ext (fun x => congrFun h x))

noncomputable instance instFintypeLinearEquiv [Finite V] : Fintype (V ≃ₗ[ZMod 2] V) :=
  Fintype.ofFinite _

/-- Subgroups of a finite group are finite. -/
noncomputable instance instFintypeSubgroupOfFinite {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) : Fintype H := Fintype.ofFinite H

/-! ## Grassmannians -/

/-- `Grass V d` is the type of `d`-dimensional submodules of `V`. -/
abbrev Grass (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] (d : ℕ) : Type _ :=
  { P : Submodule (ZMod 2) V // finrank (ZMod 2) P = d }

namespace Grass

variable {d : ℕ}

instance instSMul : SMul (V ≃ₗ[ZMod 2] V) (Grass V d) where
  smul g P := ⟨P.1.map (g : V →ₗ[ZMod 2] V), by rw [LinearEquiv.finrank_map_eq, P.2]⟩

theorem smul_val (g : V ≃ₗ[ZMod 2] V) (P : Grass V d) :
    (g • P).1 = P.1.map (g : V →ₗ[ZMod 2] V) := rfl

instance instMulAction : MulAction (V ≃ₗ[ZMod 2] V) (Grass V d) where
  one_smul P := Subtype.ext (by ext x; simp [smul_val])
  mul_smul g h P := Subtype.ext (by
    rw [smul_val, smul_val, smul_val, ← Submodule.map_comp]
    rfl)

noncomputable instance instFintype [Finite V] : Fintype (Grass V d) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  exact Fintype.ofInjective (fun P : Grass V d => (P.1 : Set V)) (fun a b h =>
    Subtype.ext (SetLike.ext (fun x => Iff.of_eq (congrFun h x))))

end Grass

/-- The nonzero vectors of `V`, as a `GL(V)`-set. -/
abbrev Pts (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] : Type _ := {x : V // x ≠ 0}

namespace Pts

instance instSMul : SMul (V ≃ₗ[ZMod 2] V) (Pts V) where
  smul g x := ⟨g x.1, fun h => x.2 (g.injective (by simpa using h))⟩

@[simp] theorem smul_val (g : V ≃ₗ[ZMod 2] V) (x : Pts V) : (g • x).1 = g x.1 := rfl

instance instMulAction : MulAction (V ≃ₗ[ZMod 2] V) (Pts V) where
  one_smul x := Subtype.ext (by rw [smul_val]; simp)
  mul_smul g h x := Subtype.ext (by rw [smul_val, smul_val, smul_val, LinearEquiv.mul_apply])

noncomputable instance instFintype [Finite V] : Fintype (Pts V) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  exact Fintype.ofInjective (fun x : Pts V => x.1) Subtype.coe_injective

end Pts

/-- The hyperplanes of `V`, i.e. its codimension-one submodules. -/
abbrev Hyp (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] : Type _ :=
  Grass V (finrank (ZMod 2) V - 1)

/-- The setwise stabiliser of a submodule `U` in `GL(V)`. -/
def stabSub (U : Submodule (ZMod 2) V) : Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {g | U.map (g : V →ₗ[ZMod 2] V) = U}
  one_mem' := by
    show U.map ((1 : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = U
    rw [show ((1 : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = LinearMap.id from rfl,
      Submodule.map_id]
  mul_mem' := by
    intro g h hg hh
    show U.map ((g * h : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = U
    rw [show ((g * h : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V)
        = (g : V →ₗ[ZMod 2] V) ∘ₛₗ (h : V →ₗ[ZMod 2] V) from rfl,
      Submodule.map_comp, hh, hg]
  inv_mem' := by
    intro g hg
    show U.map ((g⁻¹ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = U
    conv_lhs => rw [← hg]
    rw [← Submodule.map_comp]
    have : ((g⁻¹ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) ∘ₛₗ (g : V →ₗ[ZMod 2] V)
        = LinearMap.id := by
      ext x; simp
    rw [this, Submodule.map_id]

theorem mem_stabSub {U : Submodule (ZMod 2) V} {g : V ≃ₗ[ZMod 2] V} :
    g ∈ stabSub U ↔ U.map (g : V →ₗ[ZMod 2] V) = U := Iff.rfl

/-- The stabiliser in a subgroup `H ≤ GL(V)` of a vector `a`.  This is written as a subgroup of
`GL(V)` (rather than of `H`) because that is the form in which it acts below. -/
def stabPt (H : Subgroup (V ≃ₗ[ZMod 2] V)) (a : V) : Subgroup (V ≃ₗ[ZMod 2] V) :=
  H ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 2] V) a

theorem mem_stabPt {H : Subgroup (V ≃ₗ[ZMod 2] V)} {a : V} {g : V ≃ₗ[ZMod 2] V} :
    g ∈ stabPt H a ↔ g ∈ H ∧ g a = a := Iff.rfl

/-! ## Orbit counting -/

section Orbit

variable {G : Type*} [Group G] {α : Type*} [MulAction G α]

/-- The action of `H` on an `H`-invariant subset. -/
def mulActionSubtype (H : Subgroup G) (S : Set α) [MulAction G α]
    (hS : ∀ g ∈ H, ∀ x ∈ S, g • x ∈ S) : MulAction H ↥S :=
  { smul := fun g x => ⟨(g : G) • (x : α), hS g g.2 x x.2⟩
    one_smul := fun x => Subtype.ext (by
      show ((1 : H) : G) • ((x : ↥S) : α) = (x : α)
      simp)
    mul_smul := fun g₁ g₂ x => Subtype.ext (by
      show ((g₁ * g₂ : H) : G) • ((x : ↥S) : α)
        = ((g₁ : G) • ((g₂ : G) • ((x : ↥S) : α)))
      exact mul_smul (g₁ : G) (g₂ : G) (x : α)) }

/-- The orbit relation of a subgroup `H` on a subset `S`.  Invariance of `S` is *not* needed for
this to be an equivalence relation, so the definition of `orbCount` below does not involve a
proof, which keeps rewriting with it free of proof-term issues. -/
def orbitRelOn (H : Subgroup G) (S : Set α) : Setoid ↥S where
  r x y := ∃ g ∈ H, (g : G) • (x : α) = (y : α)
  iseqv :=
    ⟨fun x => ⟨1, H.one_mem, one_smul _ _⟩,
     fun {x y} h => by
       obtain ⟨g, hg, hgx⟩ := h
       exact ⟨g⁻¹, H.inv_mem hg, by rw [← hgx]; simp⟩,
     fun {x y z} hxy hyz => by
       obtain ⟨g, hg, hgx⟩ := hxy
       obtain ⟨h, hh, hhy⟩ := hyz
       exact ⟨h * g, H.mul_mem hh hg, by rw [mul_smul, hgx, hhy]⟩⟩

/-- The number of orbits of `H` on a subset `S` of a `G`-set `α`. -/
noncomputable def orbCount (H : Subgroup G) (α : Type*) [MulAction G α] (S : Set α) : ℕ :=
  Nat.card (Quotient (orbitRelOn H S))

/-- If every two points of `S` are related by an element of `H`, then `H` has exactly one orbit
on `S`. -/
theorem orbCount_eq_one_of_transitive (H : Subgroup G) {S : Set α} (hne : S.Nonempty)
    (htrans : ∀ x ∈ S, ∀ y ∈ S, ∃ g ∈ H, (g : G) • x = y) : orbCount H α S = 1 := by
  classical
  haveI : Subsingleton (Quotient (orbitRelOn H S)) := by
    constructor
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro x y
    rw [Quotient.eq]
    obtain ⟨g, hgH, hg⟩ := htrans x.1 x.2 y.1 y.2
    exact ⟨g, hgH, hg⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨Quotient.mk _ ⟨hne.some, hne.some_mem⟩⟩⟩

/-- A single orbit means transitivity. -/
theorem transitive_of_orbCount_eq_one (H : Subgroup G) {S : Set α} (h1 : orbCount H α S = 1) :
    ∀ x ∈ S, ∀ y ∈ S, ∃ g ∈ H, (g : G) • x = y := by
  classical
  have hsub : Subsingleton (Quotient (orbitRelOn H S)) := (Nat.card_eq_one_iff_unique.mp h1).1
  intro x hx y hy
  exact Quotient.eq.mp (hsub.elim (a := Quotient.mk _ (⟨x, hx⟩ : ↥S))
    (b := Quotient.mk _ (⟨y, hy⟩ : ↥S)))

/-- There is at least one orbit on a nonempty subset. -/
theorem one_le_orbCount_of_nonempty [Finite α] (H : Subgroup G) {S : Set α} (hne : S.Nonempty) :
    1 ≤ orbCount H α S := by
  classical
  haveI : Nonempty ↥S := hne.to_subtype
  haveI : Finite ↥S := Finite.of_injective (Subtype.val) Subtype.coe_injective
  haveI : Nonempty (Quotient (orbitRelOn H S)) :=
    ⟨Quotient.mk _ (Classical.arbitrary ↥S)⟩
  haveI : Finite (Quotient (orbitRelOn H S)) := Quotient.finite _
  rw [orbCount]
  exact Nat.card_pos (α := Quotient (orbitRelOn H S))

/-- The `g`-fixed points of a subset, as a subtype. -/
abbrev fixedSubtype (H : Subgroup G) (S : Set α) (g : H) : Type _ :=
  {x : α // x ∈ S ∧ (g : G) • x = x}

/-- The order of a finite subgroup is positive. -/
theorem natCard_pos_of_fintype (H : Subgroup G) [Fintype H] : 0 < Nat.card H := by
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_pos_iff.mpr ⟨1⟩

/-- **Burnside's lemma**, in the form used below: the number of orbits of `H` on an invariant
subset `S`, times the order of `H`, is the sum over `g ∈ H` of the number of `g`-fixed points
of `S`. -/
theorem orbCount_mul_card [Fintype G] [Fintype α] (H : Subgroup G) [Fintype H] {S : Set α}
    (hS : ∀ g ∈ H, ∀ x ∈ S, g • x ∈ S) :
    (∑ g : H, Nat.card (fixedSubtype H S g)) = orbCount H α S * Nat.card H := by
  classical
  letI := mulActionSubtype H S hS
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group H ↥S
  have hq : Nat.card (Quotient (orbitRelOn H S)) =
      Nat.card (Quotient (MulAction.orbitRel H ↥S)) := by
    refine Nat.card_congr (Quotient.congr (Equiv.refl ↥S) (fun a b => ?_))
    rw [MulAction.orbitRel_apply]
    constructor
    · rintro ⟨g, hg, hgx⟩
      refine ⟨⟨g⁻¹, H.inv_mem hg⟩, ?_⟩
      refine Subtype.ext ?_
      show ((g⁻¹ : G)) • (b : α) = (a : α)
      rw [← hgx]; simp
    · rintro ⟨g, hg⟩
      refine ⟨(g⁻¹ : H), (g⁻¹ : H).2, ?_⟩
      show ((g⁻¹ : G)) • (a : α) = (b : α)
      have hval : ((g : H) : G) • (b : α) = (a : α) := congrArg Subtype.val hg
      rw [← hval]; simp
  have hcard : ∀ g : H, Fintype.card ↑(MulAction.fixedBy ↥S g) =
      Nat.card (fixedSubtype H S g) := by
    intro g
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, congrArg Subtype.val x.2⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext x.2.2⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun x => Subtype.ext rfl }
  rw [orbCount, hq, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← hburn]
  exact Finset.sum_congr rfl (fun g _ => (hcard g).symm)

/-- **Orbit counts add over a disjoint invariant union.** -/
theorem orbCount_union [Fintype G] [Fintype α] (H : Subgroup G) [Fintype H] {S T : Set α}
    (hST : Disjoint S T) (hS : ∀ g ∈ H, ∀ x ∈ S, g • x ∈ S)
    (hT : ∀ g ∈ H, ∀ x ∈ T, g • x ∈ T)
    (hU : ∀ g ∈ H, ∀ x ∈ S ∪ T, g • x ∈ S ∪ T) :
    orbCount H α (S ∪ T) = orbCount H α S + orbCount H α T := by
  classical
  have hbU := orbCount_mul_card H hU
  have hbS := orbCount_mul_card H hS
  have hbT := orbCount_mul_card H hT
  have hterm : ∀ g : H, Nat.card (fixedSubtype H (S ∪ T) g) =
      Nat.card (fixedSubtype H S g) + Nat.card (fixedSubtype H T g) := by
    intro g
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    have hd : Disjoint (fun x => x ∈ S ∧ (g : G) • x = x)
        (fun x => x ∈ T ∧ (g : G) • x = x) :=
      hST.mono (fun x hx => hx.1) (fun x hx => hx.1)
    have hmain := Fintype.card_subtype_or_disjoint (fun x => x ∈ S ∧ (g : G) • x = x)
      (fun x => x ∈ T ∧ (g : G) • x = x) hd
    have h1 : Fintype.card (fixedSubtype H (S ∪ T) g) =
        Fintype.card {x : α // (x ∈ S ∧ (g : G) • x = x) ∨ (x ∈ T ∧ (g : G) • x = x)} :=
      Fintype.card_congr (Equiv.subtypeEquivRight (fun y => by
        simp only [Set.mem_union, or_and_right]))
    rw [h1, hmain]
  have hsum : (∑ g : H, Nat.card (fixedSubtype H (S ∪ T) g)) =
      (∑ g : H, Nat.card (fixedSubtype H S g)) + ∑ g : H, Nat.card (fixedSubtype H T g) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun g _ => hterm g)
  have hfinal : orbCount H α (S ∪ T) * Nat.card H =
      (orbCount H α S + orbCount H α T) * Nat.card H := by
    rw [add_mul, ← hbS, ← hbT, ← hsum, hbU]
  exact Nat.mul_right_cancel (natCard_pos_of_fintype H) hfinal

/-- Removing a fixed point decreases the number of orbits by one. -/
theorem orbCount_eq_succ_of_union_singleton [Fintype G] [Fintype α] (H : Subgroup G)
    [Fintype H] {S : Set α} {x : α} (hx : x ∉ S) (hfix : ∀ g ∈ H, g • x = x)
    (hS : ∀ g ∈ H, ∀ y ∈ S, g • y ∈ S)
    (hU : ∀ g ∈ H, ∀ y ∈ S ∪ {x}, g • y ∈ S ∪ {x}) :
    orbCount H α (S ∪ {x}) = orbCount H α S + 1 := by
  classical
  have hdisj : Disjoint S ({x} : Set α) := Set.disjoint_singleton_right.mpr hx
  have hT : ∀ g ∈ H, ∀ y ∈ ({x} : Set α), g • y ∈ ({x} : Set α) := by
    intro g hg y hy
    rw [Set.mem_singleton_iff] at hy ⊢
    rw [hy, hfix g hg]
  rw [orbCount_union H hdisj hS hT hU]
  congr 1
  exact orbCount_eq_one_of_transitive H ⟨x, by simp⟩
    (fun y hy z hz => ⟨1, H.one_mem, by
      simp only [Set.mem_singleton_iff] at hy hz
      rw [hy, hz]; simp⟩)

end Orbit

end Work.Hering.Wagner
