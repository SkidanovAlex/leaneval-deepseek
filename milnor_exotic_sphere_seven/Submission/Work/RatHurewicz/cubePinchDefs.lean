import Mathlib
import Submission.Work.Stems.Cubical.CubeFace

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The "pinched cube" vocabulary for the homotopy addition theorem

`InSkel k z` says that `z : I^{k+1}` lies in the `(k-1)`-skeleton (two of its coordinates are `0` or
`1`).  A cube `g` which is `x₀` on that skeleton has based `k`-cubes as its `2(k+1)` faces, and
`faceCube k g h i b` is the `(i,b)`-face as an element of `GenLoop (Fin k) X x₀`.

The signs `(-1)^i` (on the `b = 0` face) and `-(-1)^i` (on the `b = 1` face) are those of the
cubical boundary operator `Work.Stems.Cubical.cubD`.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz

noncomputable section

/-- A point of `I^{n+1}` is in the `(n-1)`-skeleton iff two distinct coordinates are `0` or `1`. -/
def InSkel (n : ℕ) (z : IC (n + 1)) : Prop :=
  ∃ j j' : Fin (n + 1), j ≠ j' ∧ (z j = 0 ∨ z j = 1) ∧ (z j' = 0 ∨ z j' = 1)

/-- The `i`-th coordinate of a face inclusion is the inserted value. -/
theorem faceFun_apply_same {n : ℕ} (i : Fin (n + 1)) (x : unitInterval) (u : IC n) :
    faceFun i x u i = x :=
  @Fin.insertNth_apply_same n (fun _ => unitInterval) i x u

/-- The coordinates of a face inclusion away from `i` are the coordinates of the point. -/
theorem faceFun_apply_succAbove {n : ℕ} (i : Fin (n + 1)) (x : unitInterval) (u : IC n)
    (m : Fin n) : faceFun i x u (i.succAbove m) = u m :=
  @Fin.insertNth_apply_succAbove n (fun _ => unitInterval) i x u m

/-- The `(i,b)`-face of a cube which is `x₀` on the `(n-1)`-skeleton, as a based `n`-cube. -/
def faceCube (n : ℕ) {X : Type} [TopologicalSpace X] {x₀ : X} (g : C(IC (n + 1), X))
    (h : ∀ z : IC (n + 1), InSkel n z → g z = x₀) (i : Fin (n + 1)) (b : Bool) :
    GenLoop (Fin n) X x₀ :=
  ⟨g.comp (faceCM i (if b then 1 else 0)), by
    intro u hu
    obtain ⟨m, hm⟩ := hu
    refine h (faceCM i (if b then 1 else 0) u)
      ⟨i, i.succAbove m, (Fin.succAbove_ne i m).symm, ?_, ?_⟩
    · rcases b with _ | _
      · exact Or.inl (by rw [faceCM_apply, faceFun_apply_same]; rfl)
      · exact Or.inr (by rw [faceCM_apply, faceFun_apply_same]; rfl)
    · rcases hm with hm | hm
      · exact Or.inl (by rw [faceCM_apply, faceFun_apply_succAbove]; exact hm)
      · exact Or.inr (by rw [faceCM_apply, faceFun_apply_succAbove]; exact hm)⟩

end

end Work.RatHurewicz
