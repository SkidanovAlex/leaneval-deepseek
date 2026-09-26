import Mathlib

/-!
# The cutting identity for loops

Core of the reduction of an arbitrary loop to a product of conjugates of *simple* closed loops
(step (B) of `NH_STATE.md`).

If a loop splits as `γ = α · δ · β` at a point `p` (`α : x → p`, `δ : p → p`, `β : p → x`), then
`γ` is null-homotopic as soon as the sub-loop `δ` and the complementary loop `α · β` are.

The further content of step (B) -- that a non-simple closed *polygonal* loop has such a splitting
with strictly fewer double points, so that strong induction applies -- is purely combinatorial and
is not formalised here.
-/

namespace Work.Smooth.JordanSeparation

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- **The cutting identity.**  If a loop `α · δ · β` splits at `p` into a sub-loop `δ` at `p` and
the complementary loop `α · β` at `x`, and both are null-homotopic, then so is `α · δ · β`. -/
theorem nullhomotopic_trans_trans_of_nullhomotopic {x p : X} (α : Path x p) (δ : Path p p)
    (β : Path p x) (hδ : δ.Homotopic (Path.refl p)) (hαβ : (α.trans β).Homotopic (Path.refl x)) :
    (α.trans (δ.trans β)).Homotopic (Path.refl x) := by
  have h1 : (δ.trans β).Homotopic β :=
    Path.Homotopic.trans (Path.Homotopic.hcomp hδ (Path.Homotopic.refl β))
      (Path.Homotopic.refl_trans β)
  have h2 : (α.trans (δ.trans β)).Homotopic (α.trans β) :=
    Path.Homotopic.hcomp (Path.Homotopic.refl α) h1
  exact Path.Homotopic.trans h2 hαβ

/-- **Reassociation form.**  `α · (δ · β)` is homotopic to `(α · δ) · β`; combined with the
cutting identity this lets one move the sub-loop `δ` to the front. -/
theorem homotopic_trans_assoc_trans {x p : X} (α : Path x p) (δ : Path p p) (β : Path p x) :
    (α.trans (δ.trans β)).Homotopic ((α.trans δ).trans β) :=
  (Path.Homotopic.trans_assoc α δ β).symm

end

end Work.Smooth.JordanSeparation
