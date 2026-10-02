import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The cone on a space, and triviality of homotopy groups by transport along a retraction

This file provides two tools used by `Work.Stems.subsingleton_of_contractible`.

* `Work.Stems.Cone X` — the cone `(X × I)/(X × {1})` on `X`, with its apex and the inclusion
  of the base `X ≅ X × {0}`.
* `Work.Stems.subsingleton_of_retract` — if `r ∘ i = id` for continuous maps `i : C(X, Y)`,
  `r : C(Y, X)`, then triviality of `π_N(Y, i x)` implies triviality of `π_N(X, x)`.  The point
  is that a homotopy rel boundary in `Y` is transported to `X` by postcomposition with `r`,
  because `r` fixes the (image of the) base point `i x` and all the boundary values lie there.
-/

open scoped Topology Topology.Homotopy unitInterval
open ContinuousMap

namespace Work.Stems

/-! ## Transport of triviality along a retraction -/

/-- If `r ∘ i = id` and `π_N` of `Y` at `i x` is trivial, then `π_N` of `X` at `x` is trivial. -/
theorem subsingleton_of_retract {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (i : C(X, Y)) (r : C(Y, X)) (hri : r.comp i = ContinuousMap.id X)
    {x : X} (h : Subsingleton (HomotopyGroup N Y (i x))) :
    Subsingleton (HomotopyGroup N X x) := by
  change Subsingleton (Quotient (GenLoop.Homotopic.setoid N x))
  refine ⟨fun a b => ?_⟩
  induction a using Quotient.inductionOn with
  | h p => induction b using Quotient.inductionOn with
    | h q =>
      have key : (⟦(⟨i.comp p.1, fun y hy => by rw [ContinuousMap.comp_apply, p.2 y hy]⟩ :
          ↑(Ω^ N Y (i x)))⟧ : HomotopyGroup N Y (i x)) =
          ⟦(⟨i.comp q.1, fun y hy => by rw [ContinuousMap.comp_apply, q.2 y hy]⟩ :
          ↑(Ω^ N Y (i x)))⟧ :=
        @Subsingleton.elim _ h _ _
      have hp : GenLoop.Homotopic (⟨i.comp p.1, fun y hy => by rw [ContinuousMap.comp_apply, p.2 y hy]⟩ :
          ↑(Ω^ N Y (i x))) ⟨i.comp q.1, fun y hy => by rw [ContinuousMap.comp_apply, q.2 y hy]⟩ :=
        Quotient.exact key
      obtain ⟨H⟩ := hp
      have h1 : (r.comp (i.comp p.1)) = p.1 := by
        rw [← ContinuousMap.comp_assoc, hri, ContinuousMap.id_comp]
      have h2 : (r.comp (i.comp q.1)) = q.1 := by
        rw [← ContinuousMap.comp_assoc, hri, ContinuousMap.id_comp]
      exact Quotient.sound ⟨(H.compContinuousMap r).cast h1 h2⟩

/-! ## The cone -/

/-- The equivalence relation on `X × I` which collapses `X × {1}` to a point. -/
def coneSetoid (X : Type*) : Setoid (X × I) where
  r a b := a = b ∨ (a.2 = 1 ∧ b.2 = 1)
  iseqv := ⟨fun a => Or.inl rfl,
    fun h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr ⟨h.2, h.1⟩),
    fun h1 h2 => by
      rcases h1 with h1 | ⟨h1a, h1b⟩
      · subst h1; exact h2
      · rcases h2 with h2 | ⟨h2a, h2b⟩
        · subst h2; exact Or.inr ⟨h1a, h1b⟩
        · exact Or.inr ⟨h1a, h2b⟩⟩

/-- The cone on `X`, i.e. `X × I` with `X × {1}` collapsed to a point. -/
abbrev Cone (X : Type*) : Type _ := Quotient (coneSetoid X)

/-- The apex of the cone (all points of `X × {1}` have the same class). -/
def coneApex {X : Type*} (x : X) : Cone X := Quotient.mk'' (x, 1)

/-- The inclusion of the base `X ≅ X × {0}` into the cone. -/
def coneIncl {X : Type*} (a : X) : Cone X := Quotient.mk'' (a, 0)

theorem coneApex_eq {X : Type*} (a b : X) : coneApex a = coneApex b :=
  Quotient.sound (Or.inr ⟨rfl, rfl⟩)

end Work.Stems
