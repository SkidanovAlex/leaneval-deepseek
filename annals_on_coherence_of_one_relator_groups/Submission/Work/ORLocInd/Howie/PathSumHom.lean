/-
# The homomorphism `F(Γ)_v →* ℤ` induced by a balanced labelling

A *labelling* `θ : E(Γ) → ℤ` of a graph `Γ` which is *balanced* (`θ (e⁻¹) = - θ e`) has a
well-defined *level* `pathSum θ p` on paths, which is additive under the free-groupoid product
`pmul` (`pathSum_pmul`: cancelling a backtrack does not change the level).  Consequently the level
of a reduced closed path at `v` is a homomorphism

`pathSumHom θ hθ v : F(Γ)_v →* Multiplicative ℤ,   p ↦ ofAdd (pathSum θ p)`,

from the vertex group of the free groupoid at `v` to the integers.  This is the homomorphism whose
kernel contains the relators of a presentation on which `θ` vanishes, and hence which descends to
the presented groupoid `π₁(⟨Γ | R⟩, v)`; it is the map whose surjectivity onto `ℤ` is the
*indicable* conclusion of Howie's Case 1 (`Work.ORLocInd.Howie.indicable_of_labelling`).

## Contents

* `pathSum_pmul` — the level of a product is the sum of the levels;
* `pathSumHom` — the labelling homomorphism `F(Γ)_v →* Multiplicative ℤ`;
* `pathSumHom_apply`, `pathSumHom_eq_one_iff` — its values, and the identification of its kernel
  with the set of closed paths of level `0`.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Basic
import Submission.Work.ORLocInd.Howie.Cover
import Submission.Work.ORLocInd.Howie.CoverGraph

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-- **The level of a product of paths is the sum of the levels.**  Because `pmul p q` is obtained
from `p.comp q` by cancelling backtracks, and cancelling a backtrack does not change the level
(`pathSum_of_reducesTo`, using that `θ` is balanced), the level of the product is the level of the
concatenation. -/
theorem pathSum_pmul (θ : Quiver.Total V → ℤ) (hθ : IsBalanced θ) {a b c : V}
    (p : Quiver.Path a b) (q : Quiver.Path b c) :
    pathSum θ (pmul p q) = pathSum θ p + pathSum θ q := by
  rw [pmul, ← pathSum_of_reducesTo θ hθ (reducesTo_red (p.comp q)), pathSum_comp]

/-- The homomorphism `F(Γ)_v →* Multiplicative ℤ` induced by a balanced labelling `θ` of the
arrows: a reduced closed path at `v` is sent to the exponential of its level. -/
noncomputable def pathSumHom (θ : Quiver.Total V → ℤ) (hθ : IsBalanced θ) (v : V) :
    VertexGroup v →* Multiplicative ℤ where
  toFun g := Multiplicative.ofAdd (pathSum θ g.1)
  map_one' := by rw [VertexGroup.coe_one, pathSum_nil, ofAdd_zero]
  map_mul' g h := by rw [VertexGroup.coe_mul, pathSum_pmul θ hθ, ofAdd_add]

/-- The value of `pathSumHom` on a reduced closed path. -/
@[simp] theorem pathSumHom_apply (θ : Quiver.Total V → ℤ) (hθ : IsBalanced θ) (v : V)
    (g : VertexGroup v) :
    pathSumHom θ hθ v g = Multiplicative.ofAdd (pathSum θ g.1) := rfl

/-- The kernel of `pathSumHom θ hθ v` consists of the reduced closed paths at `v` of level `0`. -/
theorem pathSumHom_eq_one_iff (θ : Quiver.Total V → ℤ) (hθ : IsBalanced θ) (v : V)
    (g : VertexGroup v) :
    pathSumHom θ hθ v g = 1 ↔ pathSum θ g.1 = 0 := by
  rw [pathSumHom_apply]
  constructor
  · intro h
    have := congrArg Multiplicative.toAdd h
    simpa using this
  · intro h
    rw [h, ofAdd_zero]

end Work.ORLocInd.Howie
