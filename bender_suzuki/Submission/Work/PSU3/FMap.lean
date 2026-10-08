/-
# The map `f`, the torus action and the centre of the case-c group

Peterfalvi II, Ch. VII §1 attaches to a split rank-one group a map
`f : Q# → Q#` characterised by `t x t = g(x) h(x) t f(x)`.  In the model
`Q = SZ E` (case c) this map is

`f(x,y) = (x/y, 1/y)`,

an involutive fixed-point-free permutation of `(SZ E)ˣ`.

This file *defines* `f` and the action of `Eˣ` by `(x,y) ↦ (ax, a^{1+σ} y)`
(the group `KW ≤ Eˣ` of Peterfalvi II Ch. VII §1), together with their defining
component formulas; the algebraic properties are stated for the fleet.
-/
import Submission.Work.PSU3.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.PSU3

variable {E : Type*} [Field E] [FrobeniusInvolution E]

namespace SZ

/-- An element of `SZ` is trivial iff its second coordinate is zero. -/
lemma eq_one_of_y_eq_zero {p : SZ E} (hy : p.y = 0) : p = 1 := by
  have h : p.x * σE p.x = 0 := by
    have hh := p.herm
    rw [hy, map_zero, add_zero] at hh
    exact hh.symm
  rw [eq_one_iff, hy]
  refine ⟨?_, rfl⟩
  rcases mul_eq_zero.mp h with h | h
  · exact h
  · exact σE.injective (by rw [h, map_zero])

lemma y_ne_zero_of_ne_one {p : SZ E} (hp : p ≠ 1) : p.y ≠ 0 :=
  fun h => hp (eq_one_of_y_eq_zero h)

/-- The map `f(x,y) = (x/y, 1/y)` of Peterfalvi II Ch. VII §1, defined on `Q#`. -/
def fMap (p : SZ E) (hp : p ≠ 1) : SZ E :=
  ⟨p.x / p.y, p.y⁻¹, by
    have hy := y_ne_zero_of_ne_one hp
    have hσy : σE p.y ≠ 0 := fun h => hy (σE.injective (by rw [h, map_zero]))
    rw [σE_inv, map_div₀]
    field_simp
    linear_combination p.herm⟩

@[simp] lemma fMap_x (p : SZ E) (hp : p ≠ 1) : (fMap p hp).x = p.x / p.y := rfl

@[simp] lemma fMap_y (p : SZ E) (hp : p ≠ 1) : (fMap p hp).y = p.y⁻¹ := rfl

/-- The action of `Eˣ` on `SZ` by `(x,y) ↦ (ax, a^{1+σ} y)`.  This is Peterfalvi's
group `KW ≤ Eˣ` (his Ch. VI §3 / Ch. VII §1) acting on `Q = S₁`. -/
def torusAct (a : Eˣ) (p : SZ E) : SZ E :=
  ⟨(a : E) * p.x, ((a : E) * σE (a : E)) * p.y, by
    simp only [map_mul, σE_σE]
    linear_combination ((a : E) * σE (a : E)) * p.herm⟩

@[simp] lemma torusAct_x (a : Eˣ) (p : SZ E) : (torusAct a p).x = (a : E) * p.x := rfl

@[simp] lemma torusAct_y (a : Eˣ) (p : SZ E) :
    (torusAct a p).y = ((a : E) * σE (a : E)) * p.y := rfl

end SZ

end Work.PSU3
