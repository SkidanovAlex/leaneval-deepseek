/-
Copyright (c) 2025. All rights reserved.

# Group cohomology in low degrees, with additive coefficients

Inhomogeneous cochain complex of a group `G` with coefficients in an additive commutative group
`A` carrying a `DistribMulAction G A` (equivalently a module over `ℤ[G]`).  Universe-polymorphic:
`G` and `A` may live in any universes.

* `C⁰(G, A) = A`, `C¹(G, A) = (G → A)`, `C²(G, A) = (G × G → A)`, `C³(G, A) = (G × G × G → A)`
* `d⁰ a g = g • a - a`
* `d¹ f (g, h) = g • f h - f (g * h) + f g`
* `d² c (g, h, k) = g • c (h, k) - c (g * h, k) + c (g, h * k) - c (g, h)`

hence the cocycle conditions in their conventional form

* `f ∈ Z¹ ↔ ∀ g h, f (g * h) = g • f h + f g`
* `c ∈ Z² ↔ ∀ g h k, c (g * h, k) + c (g, h) = g • c (h, k) + c (g, h * k)`

and `H¹ = Z¹/B¹`, `H² = Z²/B²` as additive groups.

NOTE.  Mathlib's `groupCohomology` (for `Rep ℤ G`) contains the same constructions, but its API
requires `G`, the coefficients and the base ring to live in the *same* universe, so it does not
apply to `G : Type u` with `u ≠ 0`.  The present development is self-contained.
-/
import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v w

namespace Work.GroupCohomology

variable (G : Type u) (A : Type v) [Group G] [AddCommGroup A] [DistribMulAction G A]

/-! ## The coboundary maps -/

/-- The `0`th coboundary `d⁰ : A → (G → A)`, `a ↦ (g ↦ g • a - a)`. -/
def d0 : A →+ (G → A) where
  toFun a g := g • a - a
  map_zero' := by funext g; simp
  map_add' a b := by funext g; simp only [Pi.add_apply, smul_add, add_sub_add_comm]

/-- The `1`st coboundary `d¹ : (G → A) → (G × G → A)`,
`f ↦ ((g, h) ↦ g • f h - f (g * h) + f g)`. -/
def d1 : (G → A) →+ (G × G → A) where
  toFun f p := p.1 • f p.2 - f (p.1 * p.2) + f p.1
  map_zero' := by funext p; simp
  map_add' f f' := by
    funext p
    simp only [Pi.add_apply, smul_add]
    abel

/-- The `2`nd coboundary `d² : (G × G → A) → (G × G × G → A)`,
`c ↦ ((g, h, k) ↦ g • c (h, k) - c (g * h, k) + c (g, h * k) - c (g, h))`. -/
def d2 : (G × G → A) →+ (G × G × G → A) where
  toFun c p := p.1 • c (p.2.1, p.2.2) - c (p.1 * p.2.1, p.2.2)
    + c (p.1, p.2.1 * p.2.2) - c (p.1, p.2.1)
  map_zero' := by funext p; simp
  map_add' c c' := by
    funext p
    simp only [Pi.add_apply, smul_add]
    abel

@[simp] theorem d0_apply (a : A) (g : G) : d0 G A a g = g • a - a := rfl

@[simp] theorem d1_apply (f : G → A) (g h : G) : d1 G A f (g, h) = g • f h - f (g * h) + f g := rfl

@[simp] theorem d2_apply (c : G × G → A) (g h k : G) :
    d2 G A c (g, h, k) = g • c (h, k) - c (g * h, k) + c (g, h * k) - c (g, h) := rfl

/-! ## Cocycles -/

/-- A `1`-cochain satisfying the `1`-cocycle condition, i.e. an additive crossed homomorphism
(a derivation) `G → A`; these are exactly the elements of `Z¹`. -/
def IsCrossedHom (f : G → A) : Prop := ∀ g h : G, f (g * h) = g • f h + f g

/-- The `1`-cocycles `Z¹(G, A)`, as an additive subgroup of `C¹(G, A) = (G → A)`. -/
def Z1 : AddSubgroup (G → A) where
  carrier := {f | IsCrossedHom G A f}
  zero_mem' := by intro g h; simp
  add_mem' := by
    intro f f' hf hf' g h
    simp only [Pi.add_apply] at hf hf' ⊢
    rw [hf g h, hf' g h, smul_add]
    abel
  neg_mem' := by
    intro f hf g h
    simp only [Pi.neg_apply] at hf ⊢
    rw [hf g h, smul_neg]
    abel

/-- The `2`-cocycles `Z²(G, A)`, as an additive subgroup of `C²(G, A) = (G × G → A)`. -/
def Z2 : AddSubgroup (G × G → A) where
  carrier := {c | ∀ g h k : G, c (g * h, k) + c (g, h) = g • c (h, k) + c (g, h * k)}
  zero_mem' := by intro g h k; simp
  add_mem' := by
    intro c c' hc hc' g h k
    simp only [Pi.add_apply]
    calc c (g * h, k) + c' (g * h, k) + (c (g, h) + c' (g, h))
        = (c (g * h, k) + c (g, h)) + (c' (g * h, k) + c' (g, h)) := by abel
      _ = (g • c (h, k) + c (g, h * k)) + (g • c' (h, k) + c' (g, h * k)) := by
            rw [hc g h k, hc' g h k]
      _ = g • (c (h, k) + c' (h, k)) + (c (g, h * k) + c' (g, h * k)) := by
            rw [smul_add]; abel
  neg_mem' := by
    intro c hc g h k
    simp only [Pi.neg_apply]
    calc -c (g * h, k) + -c (g, h) = -(c (g * h, k) + c (g, h)) := by abel
      _ = -(g • c (h, k) + c (g, h * k)) := by rw [hc g h k]
      _ = g • -c (h, k) + -c (g, h * k) := by rw [neg_add, smul_neg]

@[simp] theorem mem_Z1_iff (f : G → A) : f ∈ Z1 G A ↔ IsCrossedHom G A f := Iff.rfl

@[simp] theorem mem_Z2_iff (c : G × G → A) :
    c ∈ Z2 G A ↔ ∀ g h k : G, c (g * h, k) + c (g, h) = g • c (h, k) + c (g, h * k) := Iff.rfl

theorem Z1_eq_ker_d1 : Z1 G A = (d1 G A).ker := by
  ext f
  rw [mem_Z1_iff, AddMonoidHom.mem_ker, funext_iff]
  constructor
  · intro hf p
    obtain ⟨g, h⟩ := p
    simp only [Pi.zero_apply, d1_apply, IsCrossedHom] at hf ⊢
    rw [hf g h]
    abel
  · intro hf g h
    have h1 : g • f h - f (g * h) + f g = 0 := hf (g, h)
    have h2 : g • f h + f g - f (g * h) = 0 := by rw [← h1]; abel
    exact (sub_eq_zero.mp h2).symm

theorem Z2_eq_ker_d2 : Z2 G A = (d2 G A).ker := by
  ext c
  rw [mem_Z2_iff, AddMonoidHom.mem_ker, funext_iff]
  constructor
  · intro hc p
    obtain ⟨g, h, k⟩ := p
    simp only [Pi.zero_apply, d2_apply]
    have h2 : g • c (h, k) + c (g, h * k) - (c (g * h, k) + c (g, h)) = 0 := by
      rw [hc g h k]; abel
    convert h2 using 1
    abel
  · intro hc g h k
    have h1 : g • c (h, k) - c (g * h, k) + c (g, h * k) - c (g, h) = 0 := hc (g, h, k)
    have h2 : g • c (h, k) + c (g, h * k) - (c (g * h, k) + c (g, h)) = 0 := by
      rw [← h1]; abel
    exact (sub_eq_zero.mp h2).symm

/-! ## Elementary consequences of the cocycle conditions -/

theorem Z1.map_one {f : G → A} (hf : f ∈ Z1 G A) : f 1 = 0 := by
  have h : f 1 = f 1 + f 1 := by simpa using hf 1 1
  have h2 : f 1 + 0 = f 1 + f 1 := by rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

theorem Z1.map_inv {f : G → A} (hf : f ∈ Z1 G A) (g : G) : g • f g⁻¹ = -f g := by
  have h : g • f g⁻¹ + f g = 0 := by
    have h2 := hf g g⁻¹
    rw [mul_inv_cancel, Z1.map_one G A hf] at h2
    exact h2.symm
  have h' : g • f g⁻¹ - (-f g) = 0 := by rw [sub_neg_eq_add]; exact h
  exact sub_eq_zero.mp h'

theorem Z2.map_one_fst {c : G × G → A} (hc : c ∈ Z2 G A) (g : G) :
    c (1, g) = c (1, 1) := by
  have h : c (1, g) + c (1, 1) = c (1, g) + c (1, g) := by simpa using hc 1 1 g
  exact (add_left_cancel h).symm

theorem Z2.map_one_snd {c : G × G → A} (hc : c ∈ Z2 G A) (g : G) :
    c (g, 1) = g • c (1, 1) := by
  have h : c (g, 1) + c (g, 1) = g • c (1, 1) + c (g, 1) := by simpa using hc g 1 1
  exact add_right_cancel h

/-! ## Coboundaries -/

/-- The `1`-coboundaries `B¹(G, A) = im d⁰`. -/
def B1 : AddSubgroup (G → A) := (d0 G A).range

/-- The `2`-coboundaries `B²(G, A) = im d¹`. -/
def B2 : AddSubgroup (G × G → A) := (d1 G A).range

theorem mem_B1_iff (f : G → A) : f ∈ B1 G A ↔ ∃ a : A, d0 G A a = f := Iff.rfl

theorem mem_B2_iff (c : G × G → A) : c ∈ B2 G A ↔ ∃ f : G → A, d1 G A f = c := Iff.rfl

theorem d1_d0 (a : A) : d1 G A (d0 G A a) = 0 := by
  funext p
  obtain ⟨g, h⟩ := p
  simp only [d1_apply, d0_apply, Pi.zero_apply, smul_sub, mul_smul]
  abel

theorem d2_d1 (f : G → A) : d2 G A (d1 G A f) = 0 := by
  funext p
  obtain ⟨g, h, k⟩ := p
  simp only [d1_apply, d2_apply, Pi.zero_apply, smul_sub, smul_add, mul_smul, mul_assoc]
  abel

theorem B1_le_Z1 : B1 G A ≤ Z1 G A := by
  intro f hf
  obtain ⟨a, rfl⟩ := hf
  rw [mem_Z1_iff]
  intro g h
  simp only [d0_apply, smul_sub, mul_smul]
  abel

theorem B2_le_Z2 : B2 G A ≤ Z2 G A := by
  intro c hc
  obtain ⟨f, rfl⟩ := hc
  rw [Z2_eq_ker_d2]
  exact AddMonoidHom.mem_ker.mpr (d2_d1 G A f)

theorem d0_mem_Z1 (a : A) : d0 G A a ∈ Z1 G A := B1_le_Z1 G A ⟨a, rfl⟩

theorem d1_mem_Z2 (f : G → A) : d1 G A f ∈ Z2 G A := B2_le_Z2 G A ⟨f, rfl⟩

/-! ## `H¹` and `H²` -/

/-- `H¹(G, A) = Z¹(G, A)/B¹(G, A)`, as an additive group. -/
abbrev H1 : Type (max u v) :=
  (Z1 G A : AddSubgroup (G → A)) ⧸ ((B1 G A).comap (Z1 G A).subtype)

/-- `H²(G, A) = Z²(G, A)/B²(G, A)`, as an additive group. -/
abbrev H2 : Type (max u v) :=
  (Z2 G A : AddSubgroup (G × G → A)) ⧸ ((B2 G A).comap (Z2 G A).subtype)

/-- The quotient map `Z¹(G, A) → H¹(G, A)`. -/
noncomputable def H1π : (Z1 G A) →+ H1 G A :=
  QuotientAddGroup.mk' ((B1 G A).comap (Z1 G A).subtype)

/-- The quotient map `Z²(G, A) → H²(G, A)`. -/
noncomputable def H2π : (Z2 G A) →+ H2 G A :=
  QuotientAddGroup.mk' ((B2 G A).comap (Z2 G A).subtype)

end Work.GroupCohomology
