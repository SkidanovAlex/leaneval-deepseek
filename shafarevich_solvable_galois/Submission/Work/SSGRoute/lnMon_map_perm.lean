import Mathlib
import Submission.Work.SSGRoute.freeAssocMap
import Submission.Work.SSGRoute.freeAssocMap_wordEl
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `σ`-compatibility of the left-nested commutator monomial

`lnMon w = [[...[x₁,x₂],…],x_j]` is the left-nested bracket monomial attached to a word `w`
inside the free associative algebra `FreeAssoc X = ℤ[FreeMonoid X]`, and `freeAssocMap σ` is the
`ℤ`-algebra endomorphism induced by a permutation `σ` of the generators.  Because `lnMon` is built
out of the algebra operations together with the generators `wordEl [x]`, and `freeAssocMap σ` is a
ring homomorphism carrying `wordEl [x]` to `wordEl [σ x]`, the two commute:

`lnMon (w.map σ) = freeAssocMap σ (lnMon w)`.

The proof is the generic commutation of `freeAssocMap σ` with a fold (proved below) applied to the
particular fold defining `lnMon`.
-/

noncomputable section

namespace Work.SSGRoute

open Work.SSGRoute.prop5

/-- **Folding commutes with the induced algebra map.**  If a binary operation `f` on `FreeAssoc X`
is `σ`-compatible in the sense that `freeAssocMap σ (f acc y) = f (freeAssocMap σ acc) (σ y)`,
then applying `freeAssocMap σ` to a left fold is the same as folding the mapped list after
applying `freeAssocMap σ` to the initial accumulator, i.e.

`freeAssocMap σ (l.foldl f a) = (l.map σ).foldl f (freeAssocMap σ a)`. -/
theorem foldl_freeAssocMap {X : Type*} (σ : X ≃ X)
    (f : FreeAssoc X → X → FreeAssoc X)
    (h : ∀ acc y, freeAssocMap σ (f acc y) = f (freeAssocMap σ acc) (σ y))
    (a : FreeAssoc X) (l : List X) :
    freeAssocMap σ (l.foldl f a) = (l.map σ).foldl f (freeAssocMap σ a) := by
  induction l generalizing a with
  | nil => rfl
  | cons y rest ih =>
      rw [List.foldl_cons, List.map_cons, List.foldl_cons, ih, h]

theorem lnMon_map_perm {X : Type*} (σ : X ≃ X) (w : List X) :
    Work.SSGRoute.prop5.lnMon (w.map σ)
      = Work.SSGRoute.prop5.freeAssocMap σ (Work.SSGRoute.prop5.lnMon w) := by
  cases w with
  | nil => rfl
  | cons x rest =>
      -- `freeAssocMap σ` intertwines the bracketing step `acc ↦ [acc, y]`.
      have h : ∀ (acc : FreeAssoc X) (y : X),
          freeAssocMap σ (acc * wordEl [y] - wordEl [y] * acc)
            = (freeAssocMap σ acc) * wordEl [σ y] - wordEl [σ y] * (freeAssocMap σ acc) := by
        intro acc y
        simp
      simp only [List.map_cons]
      -- unfold both `lnMon` applications into their defining folds
      rw [show Work.SSGRoute.prop5.lnMon (σ x :: rest.map σ)
            = (rest.map σ).foldl (fun acc y => acc * wordEl [y] - wordEl [y] * acc)
                (wordEl [σ x]) from rfl]
      rw [show Work.SSGRoute.prop5.lnMon (x :: rest)
            = rest.foldl (fun acc y => acc * wordEl [y] - wordEl [y] * acc)
                (wordEl [x]) from rfl]
      rw [foldl_freeAssocMap σ (fun acc y => acc * wordEl [y] - wordEl [y] * acc) h (wordEl [x]) rest,
          Work.SSGRoute.freeAssocMap_wordEl]
      rfl

end Work.SSGRoute
