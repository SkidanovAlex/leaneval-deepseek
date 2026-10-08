/-
# Area `PSU3`: the Bender–Suzuki group of "case c"

This file starts the chapter of mathematics needed by the area `PSU3` of the
Bender–Suzuki project: the *coordinate* description of `PSU(3,q)` (q even) used by
Peterfalvi II, Ch. VI §3 and Ch. VII, namely the Suzuki group

`Q = {(x,y) ∈ E × E | y + y^q = x^{1+q}},   E = GF(q²),  q = 2ⁿ`

with the composition law

`(x,z) * (y,u) = (x + y, z + u + x·y^q)`.

The main mathematical facts of the chapter are

* `Work.PSU3.SZ` — the group `Q` (a `structure` with a `Group` instance), its
  centre `Work.PSU3.SZ.Q0 = {(0,y)}` and the Hermitian relation `SZ.herm`;
* `Work.PSU3.SZMatrix` — the isomorphism with the upper unitriangular matrices
  fixing the anti-diagonal Hermitian form, and hence the embedding into
  `LeanEval.GroupTheory.Defs.PSU3Model n`;
* `Work.PSU3.SZ.fMap` — the map `f(x,y) = (x/y, 1/y)`, an involutive
  fixed-point-free permutation of `(SZ)ˣ` — the map `f` of Peterfalvi II Ch. VII §1;
* `Work.PSU3.SZ.torusAction` — the action of `Eˣ` by `(x,y) ↦ (ax, a^{1+σ}y)` (the
  group `KW ≤ Eˣ` of Peterfalvi II Ch. VII §1).

Conventions. The field involution plays the role of `x ↦ x^q` in `GF(q²)`; it is a
*ring* homomorphism with `σ (σ x) = x`. All the algebra in this file only uses
`σ(x+y) = σx + σy`, `σ(xy) = σx·σy` and `σ² = 1`. Statements needing characteristic
two (the Hermitian form, the formula `f(x,y) = (x/y,1/y)` in its model form) carry
the hypothesis `[CharP E 2]` explicitly.
-/
import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.PSU3

/-! ## The Frobenius involution of `GF(q²)` -/

/-- A field equipped with a distinguished involutive automorphism `σ`, the
`q`-power Frobenius `x ↦ x^q` of `GF(q²)`. -/
class FrobeniusInvolution (E : Type*) [Field E] where
  /-- The distinguished involution `x ↦ x^q`. -/
  σ : E →+* E
  /-- `σ` is an involution. -/
  σ_invol : ∀ x : E, σ (σ x) = x

variable {E : Type*} [Field E]

/-- The distinguished involution `x ↦ x^q`. -/
def σE [FrobeniusInvolution E] : E →+* E := FrobeniusInvolution.σ

@[simp] lemma σE_σE [FrobeniusInvolution E] (x : E) : σE (σE x) = x :=
  FrobeniusInvolution.σ_invol x

@[simp] lemma σE_add [FrobeniusInvolution E] (x y : E) : σE (x + y) = σE x + σE y :=
  map_add _ _ _

@[simp] lemma σE_mul [FrobeniusInvolution E] (x y : E) : σE (x * y) = σE x * σE y :=
  map_mul _ _ _

@[simp] lemma σE_zero [FrobeniusInvolution E] : σE (0 : E) = 0 := map_zero _

@[simp] lemma σE_one [FrobeniusInvolution E] : σE (1 : E) = 1 := map_one _

@[simp] lemma σE_neg [FrobeniusInvolution E] (x : E) : σE (-x) = -σE x := map_neg _ _

@[simp] lemma σE_inv [FrobeniusInvolution E] (x : E) : σE x⁻¹ = (σE x)⁻¹ := map_inv₀ _ _

/-! ## The group `Q` of case c -/

/-- The Bender–Suzuki group of case c: `{(x,y) ∈ E² | y + y^q = x^{1+q}}` with the
law `(x,z)(y,u) = (x+y, z+u+x·y^q)`.  This is Peterfalvi's `Q = S₁` (his Ch. VI §3),
the Sylow 2-subgroup of `PSU(3,q)` realised as a Suzuki 2-group of order `q³`. -/
structure SZ (E : Type*) [Field E] [FrobeniusInvolution E] where
  /-- First coordinate: the image of the element in `Q/Q₀ ≅ E`. -/
  x : E
  /-- Second coordinate. -/
  y : E
  /-- The Hermitian relation `y + y^q = x^{1+q}`. -/
  herm : y + σE y = x * σE x

namespace SZ

variable {E : Type*} [Field E] [FrobeniusInvolution E]

@[ext]
theorem ext {p q : SZ E} (hx : p.x = q.x) (hy : p.y = q.y) : p = q := by
  cases p; cases q; simp_all

instance instMul : Mul (SZ E) where
  mul p q :=
    ⟨p.x + q.x, p.y + q.y + p.x * σE q.x, by
      simp only [map_add, map_mul, σE_σE]
      linear_combination p.herm + q.herm⟩

instance instOne : One (SZ E) := ⟨⟨0, 0, by simp⟩⟩

instance instInv : Inv (SZ E) where
  inv p :=
    ⟨-p.x, -p.y + p.x * σE p.x, by
      simp only [map_add, map_neg, map_mul, σE_σE]
      linear_combination -p.herm⟩

instance instInhabited : Inhabited (SZ E) := ⟨1⟩

@[simp] lemma mul_x (p q : SZ E) : (p * q).x = p.x + q.x := rfl

@[simp] lemma mul_y (p q : SZ E) : (p * q).y = p.y + q.y + p.x * σE q.x := rfl

@[simp] lemma one_x : (1 : SZ E).x = 0 := rfl

@[simp] lemma one_y : (1 : SZ E).y = 0 := rfl

@[simp] lemma inv_x (p : SZ E) : p⁻¹.x = -p.x := rfl

@[simp] lemma inv_y (p : SZ E) : p⁻¹.y = -p.y + p.x * σE p.x := rfl

instance instGroup : Group (SZ E) :=
  Group.ofLeftAxioms
    (by
      intro a b c
      ext <;> simp only [mul_x, mul_y, map_add, map_mul] <;> ring)
    (by intro a; ext <;> simp only [mul_x, mul_y, one_x, one_y, zero_add, zero_mul]; ring)
    (by
      intro a
      ext <;>
        simp only [mul_x, mul_y, inv_x, inv_y, one_x, one_y, map_neg, map_add, map_mul,
          σE_σE, neg_mul] <;>
        ring)

lemma eq_iff {p q : SZ E} : p = q ↔ p.x = q.x ∧ p.y = q.y :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun h => ext h.1 h.2⟩

lemma eq_one_iff {p : SZ E} : p = 1 ↔ p.x = 0 ∧ p.y = 0 := by
  rw [eq_iff]; simp

@[simp] lemma mk_x (a b : E) (h : b + σE b = a * σE a) : (⟨a, b, h⟩ : SZ E).x = a := rfl

@[simp] lemma mk_y (a b : E) (h : b + σE b = a * σE a) : (⟨a, b, h⟩ : SZ E).y = b := rfl

/-- Two elements with the same `x`-coordinate differ by an element of `Q₀`. -/
lemma sub_x {p q : SZ E} (h : p.x = q.x) : (p * q⁻¹).x = 0 := by simp [h]

/-- The `y`-difference of two elements with the same `x`-coordinate is fixed by `σ`. -/
lemma sub_y_add_σ {p q : SZ E} (h : p.x = q.x) :
    (p * q⁻¹).y + σE (p * q⁻¹).y = 0 := by
  simpa [sub_x h] using (p * q⁻¹).herm

/-- `Q₀ = {(0,y)}`: the subgroup of elements with zero `x`-coordinate.  It is the centre
of `SZ` (see `Work.PSU3.SZ.mem_center_iff`) and is isomorphic to the fixed field of `σ`. -/
def Q0 : Subgroup (SZ E) where
  carrier := {p | p.x = 0}
  mul_mem' := by
    intro p q hp hq
    simp only [Set.mem_ofPred_eq] at hp hq
    simp [hp, hq]
  one_mem' := rfl
  inv_mem' := by
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp
    simp [hp]

@[simp] lemma mem_Q0_iff (p : SZ E) : p ∈ Q0 ↔ p.x = 0 := Iff.rfl

end SZ

end Work.PSU3
