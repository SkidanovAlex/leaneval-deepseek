/-
  WilC5 — `leEL` is preserved by *arbitrary* `LRc`-embeddings.

  `LRc` has no relation symbols, so the order of a model of `TR` is the quantifier-free
  definable order `leEL x y := ∃ z, z * z = y - x` (`LRcOps.lean`).  A quantifier-free
  definable predicate is preserved by *every* embedding (not merely by the elementary ones,
  for which this is `Work.WilC5.elem_leEL`): an `LRc`-embedding `e : M ↪ N` commutes with the
  ring operations, hence

      `a ≤ b` ⟹ (witness `z` with `z * z = b - a`) ⟹ `e z * e z = e b - e a` ⟹ `e a ≤ e b`.

  The three commutation lemmas `map_addEL`, `map_negEL`, `map_mulEL` are the only content;
  `subEL` is `addEL` followed by `negEL`.
-/
import Mathlib
import Submission.Work.WilC5.tr_leE_axioms

set_option autoImplicit false
noncomputable section

open FirstOrder FirstOrder.Language WilkiesDesign WilkiesDesign.CG

namespace Work.WilC5

section MapOps

variable {M N : Type} [LRc.Structure M] [LRc.Structure N]

/-- An `LRc`-embedding commutes with addition. -/
theorem map_addEL (e : LRc.Embedding M N) (x y : M) :
    e (addEL x y) = addEL (e x) (e y) := by
  simp only [addEL, e.map_fun]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- An `LRc`-embedding commutes with negation. -/
theorem map_negEL (e : LRc.Embedding M N) (x : M) :
    e (negEL x) = negEL (e x) := by
  simp only [negEL, e.map_fun]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- An `LRc`-embedding commutes with multiplication. -/
theorem map_mulEL (e : LRc.Embedding M N) (x y : M) :
    e (mulEL x y) = mulEL (e x) (e y) := by
  simp only [mulEL, e.map_fun]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- An `LRc`-embedding commutes with subtraction. -/
theorem map_subEL (e : LRc.Embedding M N) (x y : M) :
    e (subEL x y) = subEL (e x) (e y) := by
  simp only [subEL]
  rw [map_addEL, map_negEL]

end MapOps

theorem embedding_map_leEL {M N : Type}
    [FirstOrder.Language.Structure WilkiesDesign.CG.LRc M]
    [FirstOrder.Language.Structure WilkiesDesign.CG.LRc N]
    (e : WilkiesDesign.CG.LRc.Embedding M N) {a b : M}
    (h : Work.WilC5.leEL a b) : Work.WilC5.leEL (e a) (e b) := by
  obtain ⟨z, hz⟩ := h
  refine ⟨e z, ?_⟩
  have h' : e (mulEL z z) = e (subEL b a) := congrArg e hz
  rwa [map_mulEL, map_subEL] at h'

end Work.WilC5
