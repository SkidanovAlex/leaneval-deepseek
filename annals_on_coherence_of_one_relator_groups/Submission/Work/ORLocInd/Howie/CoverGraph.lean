/-
# The cyclic cover of a graph along a `ℤ`-labelling

A *labelling* of `Γ` is a function `θ` on the arrows with `θ (e⁻¹) = - θ e`.  Its *cyclic cover*
`Γ̃` has vertex set `V × ℤ` and, for every arrow `e : a → b` of `Γ` and every level `n : ℤ`, an arrow
`(e, n) : (a, n) → (b, n + θ e)`.  Reversal is `(e, n)⁻¹ = (e⁻¹, n + θ e)`, so that the lift of a
reduced path is reduced.

The *lift* of a path `p : a → b` beginning at `(a, n)` is the unique path of `Γ̃` projecting to `p`,
and it ends at `(b, n + pathSum θ p)`.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Cover

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-- A balanced labelling of the arrows of `Γ` by the integers. -/
structure Labelling (V : Type u) [Quiver V] [Quiver.HasInvolutiveReverse V] where
  /-- the label of an arrow -/
  toFun : Quiver.Total V → ℤ
  /-- the labelling is additive under reversal -/
  balanced : ∀ e : Quiver.Total V, toFun (Quiver.totalReverse e) = - toFun e

namespace Labelling

variable (L : Labelling V)

instance : CoeFun (Labelling V) (fun _ => Quiver.Total V → ℤ) := ⟨Labelling.toFun⟩

theorem isBalanced : IsBalanced L.toFun := L.balanced

@[simp] theorem apply_totalReverse (e : Quiver.Total V) : L (Quiver.totalReverse e) = - L e :=
  L.balanced e

end Labelling

/-- The vertices of the cyclic cover. -/
structure CoverVertex (L : Labelling V) where
  /-- the vertex of the base graph -/
  vert : V
  /-- the level -/
  level : ℤ

/-- The arrows of the cyclic cover: an arrow of `Γ` together with the level of its source. -/
def CoverHom (L : Labelling V) (p q : CoverVertex L) : Type u :=
  {e : Quiver.Total V // e.left = p.vert ∧ e.right = q.vert ∧ q.level = p.level + L e}

instance coverQuiver (L : Labelling V) : Quiver (CoverVertex L) :=
  ⟨fun p q => CoverHom L p q⟩

instance coverReverse (L : Labelling V) : Quiver.HasInvolutiveReverse (CoverVertex L) where
  reverse' := fun {p q} f =>
    ⟨Quiver.totalReverse f.1, by
      obtain ⟨e, h1, h2, h3⟩ := f
      refine ⟨?_, ?_, ?_⟩
      · simpa [Quiver.totalReverse] using h2
      · simpa [Quiver.totalReverse] using h1
      · have h3' : q.level = p.level + L e := h3
        have : p.level = q.level + -L e := by omega
        simpa using this⟩
  inv' := fun {p q} f => Subtype.ext (Quiver.totalReverse_involutive f.1)

/-- The projection of the cyclic cover onto the base graph. -/
def coverProjArrow {L : Labelling V} {p q : CoverVertex L} (f : p ⟶ q) : p.vert ⟶ q.vert :=
  Quiver.homOfEq f.1.hom f.2.1 f.2.2.1

/-- The lift of a path to the cyclic cover. -/
noncomputable def liftPath (L : Labelling V) :
    ∀ {a b : V} (p : Quiver.Path a b) (n : ℤ),
      Quiver.Path (⟨a, n⟩ : CoverVertex L) ⟨b, n + pathSum L.toFun p⟩
  | _, _, .nil, n => by
      rw [pathSum_nil, add_zero]
      exact Quiver.Path.nil
  | _, _, .cons p e, n => by
      rw [pathSum_cons, ← add_assoc]
      exact (liftPath L p n).cons ⟨Quiver.Total.mk _ _ e, rfl, rfl, rfl⟩

end Work.ORLocInd.Howie
