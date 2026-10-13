import Submission.Work.WilkiesB.Defs
import Submission.Work.WilkiesB.ExpExistI_inter
import Submission.Work.WilkiesB.ExpExistI_union
import Submission.Work.WilkiesB.ExpExistI_pullback
import Submission.Work.WilkiesB.ExpExistI_existsBlock
import Submission.Work.WilkiesB.ExpExistI_projLast
import Submission.Work.WilkiesB.ExpExistI_compl

/-!
# Area B (syntax) — closure properties of `ExpExistI`

`ExpExistI` is closed under the Boolean operations (intersection, union, complement given
Wilkie's complement theorem `hW`), under pullback along a map of index types, and under
existential quantification over a block of coordinates.

The lemmas `ExpExistI_univ` and `ExpExistI_empty` are proved here; the rest are proved in the
sibling modules and re-exported in the `ExpExistI` namespace so that they can be used as
`hX.inter hY`, `hX.compl hW`, etc.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open FirstOrder FirstOrder.Language
open MvPolynomial

namespace Work.WilkiesB

variable {κ μ ν : Type*}

/-! ## The two constants -/

/-- The whole space is existentially definable. -/
theorem ExpExistI_univ : ExpExistI (Set.univ : Set (κ → ℝ)) := by
  refine ⟨PEmpty, inferInstance, 0, ?_⟩
  ext z
  refine ⟨fun _ => ⟨PEmpty.elim, by simp⟩, fun _ => trivial⟩

/-- The empty set is existentially definable. -/
theorem ExpExistI_empty : ExpExistI (∅ : Set (κ → ℝ)) := by
  refine ⟨PEmpty, inferInstance, 1, ?_⟩
  ext z
  show (z ∈ (∅ : Set (κ → ℝ))) ↔ (∃ y : PEmpty → ℝ, expEval (Sum.elim z y) 1 = 0)
  exact ⟨False.elim, fun ⟨y, hy⟩ => one_ne_zero (by simpa only [expEval_one] using hy)⟩

namespace ExpExistI

/-- Closure under binary intersection. -/
theorem inter {X Y : Set (κ → ℝ)} (hX : ExpExistI X) (hY : ExpExistI Y) :
    ExpExistI (X ∩ Y) := ExpExistI_inter hX hY

/-- Closure under binary union. -/
theorem union {X Y : Set (κ → ℝ)} (hX : ExpExistI X) (hY : ExpExistI Y) :
    ExpExistI (X ∪ Y) := ExpExistI_union hX hY

/-- Closure under pullback along a map of index types. -/
theorem pullback (f : κ → ν) {X : Set (κ → ℝ)} (hX : ExpExistI X) :
    ExpExistI {z : ν → ℝ | z ∘ f ∈ X} := ExpExistI_pullback f hX

/-- Closure under existential quantification over a finite block of coordinates. -/
theorem existsBlock [Fintype μ] {X : Set ((κ ⊕ μ) → ℝ)} (hX : ExpExistI X) :
    ExpExistI {z : κ → ℝ | ∃ u : μ → ℝ, Sum.elim z u ∈ X} :=
  ExpExistI_existsBlock hX

/-- Closure under existential quantification over a single coordinate. -/
theorem projLast {X : Set ((κ ⊕ Fin 1) → ℝ)} (hX : ExpExistI X) :
    ExpExistI {z : κ → ℝ | ∃ a : ℝ, Sum.elim z (fun _ : Fin 1 => a) ∈ X} :=
  ExpExistI_projLast hX

/-- Closure under complement, given Wilkie's complement theorem `hW`. -/
theorem compl [Fintype κ] {X : Set (κ → ℝ)}
    (hW : ∀ (n : ℕ) (Y : Set (Fin n → ℝ)), WilkiesDesign.ExpExist Y → WilkiesDesign.ExpExist Yᶜ)
    (hX : ExpExistI X) : ExpExistI Xᶜ := ExpExistI_compl hW hX

end ExpExistI

/-! ## Renaming along an equivalence of index types -/

/-- `ExpExistI` is invariant under an equivalence of index types. -/
theorem ExpExistI_preimage_equiv (e : κ ≃ ν) {X : Set (κ → ℝ)} (hX : ExpExistI X) :
    ExpExistI {z : ν → ℝ | z ∘ ⇑e ∈ X} := ExpExistI.pullback ⇑e hX

/-- The inverse direction of `ExpExistI_preimage_equiv`. -/
theorem ExpExistI_of_preimage_equiv (e : κ ≃ ν) {X : Set (κ → ℝ)}
    (h : ExpExistI {z : ν → ℝ | z ∘ ⇑e ∈ X}) : ExpExistI X := by
  refine (ExpExistI.pullback ⇑e.symm h).of_eq ?_
  ext u
  show ((u ∘ ⇑e.symm) ∘ ⇑e ∈ X) ↔ (u ∈ X)
  have hcomp : (u ∘ ⇑e.symm) ∘ ⇑e = u := by funext i; simp
  rw [hcomp]

end Work.WilkiesB
