/-
Area DSCOH (curric-46) — the normalization comparison: tuple-level vocabulary.

This file sets up the concrete tuple-indexed Čech complexes that mediate between Mathlib's
unnormalized Čech complex `cechComplexFunctor U` (indexed by all tuples `Fin (n+1) → ι`,
repetitions allowed) and the alternating (subset/ordered) Čech complex `Work.DSCOH.altCech`.

* `AllIdx n` : all tuples `Fin (n+1) → ι`;
* `SemiIdx n` : nondecreasing tuples (the "semi-ordered" complex);
* `OrdIdx n` : strictly increasing tuples (the "ordered" complex, i.e. the subsets);

with, for a tuple `x`, the open `tupleOp U x = ∏ᶜ a, U (x a)` (the intersection) and the module
`tupleMod P U x = P.obj (op (tupleOp U x))`, so that the all-tuples term of Mathlib's complex in
degree `n` is the product of `tupleMod P U x` over `x : AllIdx n` *definitionally*.
-/
import Mathlib

namespace Work.DSCOH.Norm

open CategoryTheory Limits Opposite TopologicalSpace
open scoped Simplicial BigOperators

set_option backward.isDefEq.respectTransparency false

universe u v w

variable {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
variable {ι : Type w}

/-! ## The index sets -/

/-- The index type of the `n`-th term of the unnormalized Čech complex: all `(n+1)`-tuples. -/
abbrev AllIdx (ι : Type*) (n : ℕ) := Fin (n + 1) → ι

/-- The index type of the `n`-th term of the semi-ordered Čech complex: nondecreasing tuples. -/
abbrev SemiIdx (ι : Type*) [Preorder ι] (n : ℕ) := {x : Fin (n + 1) → ι // Monotone x}

/-- The index type of the `n`-th term of the ordered (alternating) Čech complex: strictly
increasing tuples. -/
abbrev OrdIdx (ι : Type*) [Preorder ι] (n : ℕ) := {x : Fin (n + 1) → ι // StrictMono x}

/-! ## Deleting an entry -/

/-- Delete the `b`-th entry of a tuple.  `Fin.succAbove b : Fin n → Fin (n+1)` is the
order embedding whose range is the complement of `b`. -/
def del {n : ℕ} (x : Fin (n + 2) → ι) (b : Fin (n + 2)) : Fin (n + 1) → ι :=
  fun a => x (b.succAbove a)

@[simp]
lemma del_apply {n : ℕ} (x : Fin (n + 2) → ι) (b : Fin (n + 2)) (a : Fin (n + 1)) :
    del x b a = x (b.succAbove a) := rfl

/-- The deletion of a nondecreasing tuple is nondecreasing. -/
lemma monotone_del [Preorder ι] {n : ℕ} (x : Fin (n + 2) → ι) (b : Fin (n + 2))
    (hx : Monotone x) : Monotone (del x b) :=
  hx.comp (Fin.strictMono_succAbove b).monotone

/-- The deletion of a strictly increasing tuple is strictly increasing. -/
lemma strictMono_del [Preorder ι] {n : ℕ} (x : Fin (n + 2) → ι) (b : Fin (n + 2))
    (hx : StrictMono x) : StrictMono (del x b) :=
  hx.comp (Fin.strictMono_succAbove b)

/-! ## The open and the module of a tuple -/

/-- The open of a tuple: the product (i.e. the intersection) of the `U (x a)`. -/
noncomputable def tupleOp (U : ι → Opens X) {n : ℕ} (x : Fin (n + 1) → ι) : Opens X :=
  ∏ᶜ fun a => U (x a)

/-- The module attached to a tuple: the sections of `P` over the open of the tuple. -/
noncomputable def tupleMod (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)
    {n : ℕ} (x : Fin (n + 1) → ι) : ModuleCat A :=
  P.obj (op (tupleOp U x))

end Work.DSCOH.Norm
