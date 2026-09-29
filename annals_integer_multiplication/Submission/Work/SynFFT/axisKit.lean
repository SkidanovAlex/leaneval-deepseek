import Mathlib
import Submission.HvdH.Interfaces

/-!
# The transpose word `Work.SynFFT.HasAxisTranspose`: pure list layer

`HasAxisTranspose` (`Submission/Work/SynFFT/axisDefs.lean`) asks for a StackLang word sending
`ofList es` to `ofList (List.flatten (HvdH.slices A t B es))` in time
`O(N·(L+1)·log t + N·log N)` (`N = A*t*B`, `L` bounding the encoded size of the elements).

The word implemented here transposes **blockwise**, with one contiguous merge tree per block:

* `ofList es` is cut into `A` consecutive **blocks** of `t*B` elements (`blocksOf`);
* each block is cut into `t` consecutive **rows** of `B` elements (`rowsOf`) and each row is
  *exploded* into its `B` singleton columns (`exploded`): the leaf of the recursion;
* iterating `mLevel` (merge adjacent groups by elementwise concatenation `zipCat`) until one group
  remains yields the `B` columns of the block, each of length `t`;
* flattening twice concatenates the columns of all blocks in order.

Pure content of the correctness proof: `mAll (ps.map cols) = [cols ps.flatten]`
(`mAll_map_cols`, i.e. associativity of `zipCat`), and the identification of `cols (rowsOf t B blk)`
with the columns of the `t × B` matrix (`slices_connection`).
-/

set_option autoImplicit false

namespace Work.SynFFT

open HvdH

/-! ## Pure list functions -/

/-- Elementwise concatenation of two lists of rows (i.e. of two lists of columns of matrices with
the same number of rows); an empty list is a unit on either side. -/
def zipCat : List (List Val) → List (List Val) → List (List Val)
  | [], G => G
  | G, [] => G
  | r₁ :: t₁, r₂ :: t₂ => (r₁ ++ r₂) :: zipCat t₁ t₂

@[simp] theorem zipCat_nil_left (G : List (List Val)) : zipCat [] G = G := rfl

@[simp] theorem zipCat_nil_right (G : List (List Val)) : zipCat G [] = G := by
  cases G with
  | nil => rfl
  | cons r t => rfl

/-- A row, exploded into the group of its singleton columns (the transpose of a `1 × B` matrix). -/
def exploded (r : List Val) : List (List Val) := r.map (fun x => [x])

/-- The columns of a matrix given as a list of rows of equal length, by the leaf/merge recursion:
explode the first row and merge it with the columns of the rest. -/
def cols : List (List Val) → List (List Val)
  | [] => []
  | r :: rs => zipCat (exploded r) (cols rs)

/-- A group (list of rows / columns) as a value: `ofList (group.map ofList)`. -/
def grpVal (g : List (List Val)) : Val := ofList (g.map ofList)

/-- The state of one block of the transpose word (its list of groups) as a value. -/
def stateVal (gs : List (List (List Val))) : Val := ofList (gs.map grpVal)

/-- One merge level: merge adjacent groups with `zipCat` (a dangling last group is kept). -/
def mLevel : List (List (List Val)) → List (List (List Val))
  | [] => []
  | [G] => [G]
  | G₁ :: G₂ :: rest => zipCat G₁ G₂ :: mLevel rest

/-- Pair adjacent pieces (the last one is kept alone): the piece-partition counterpart of
`mLevel`. -/
def pairUp : List (List (List Val)) → List (List (List Val))
  | [] => []
  | [p] => [p]
  | p₁ :: p₂ :: rest => (p₁ ++ p₂) :: pairUp rest

/-- `k` merge levels. -/
def iter : ℕ → List (List (List Val)) → List (List (List Val))
  | 0, Gs => Gs
  | k + 1, Gs => iter k (mLevel Gs)

/-- The result of the merge phase: iterate `mLevel` until at most one group is left (a list of
length `n` needs at most `n` levels). -/
def mAll (Gs : List (List (List Val))) : List (List (List Val)) := iter Gs.length Gs

/-- The `a`-th **block** of the flat array: a consecutive chunk of `t*B` elements. -/
def blocksOf (A t B : ℕ) (es : List Val) : List (List Val) :=
  (List.range A).map (fun a => (es.drop (a * (t * B))).take (t * B))

/-- The `j`-th **row** of a block: a consecutive chunk of `B` elements. -/
def rowsOf (t B : ℕ) (blk : List Val) : List (List Val) :=
  (List.range t).map (fun j => (blk.drop (j * B)).take B)

/-- Consecutive chunks of size `S` (empty when `S = 0`). -/
def chunkList (S : ℕ) (xs : List Val) : List (List Val) :=
  (List.range (xs.length / S)).map (fun i => (xs.drop (i * S)).take S)

/-! ## Basic facts -/

/-- `zipCat` is associative (the conventions on the empty list make the degenerate cases work). -/
theorem zipCat_assoc (A B C : List (List Val)) :
    zipCat (zipCat A B) C = zipCat A (zipCat B C) := by
  induction A generalizing B C with
  | nil => simp
  | cons r t ih =>
    cases B with
    | nil => simp
    | cons s B' =>
      cases C with
      | nil => simp
      | cons u C' =>
        simp only [zipCat]
        rw [List.append_assoc, ih]

theorem cols_nil : cols ([] : List (List Val)) = [] := rfl

theorem cols_singleton (r : List Val) : cols [r] = exploded r := by
  simp only [cols, zipCat_nil_right]

/-- `cols` of a concatenation of row lists is the `zipCat` of the `cols`. -/
theorem cols_append (p q : List (List Val)) : cols (p ++ q) = zipCat (cols p) (cols q) := by
  induction p with
  | nil => simp [cols]
  | cons r rs ih => simp only [List.cons_append, cols, ih, ← zipCat_assoc]

@[simp] theorem mLevel_nil : mLevel ([] : List (List (List Val))) = [] := rfl

@[simp] theorem mLevel_singleton (G : List (List Val)) : mLevel [G] = [G] := rfl

@[simp] theorem mLevel_cons_cons (G₁ G₂ : List (List Val)) (Gs : List (List (List Val))) :
    mLevel (G₁ :: G₂ :: Gs) = zipCat G₁ G₂ :: mLevel Gs := rfl

theorem mLevel_length : ∀ Gs : List (List (List Val)), (mLevel Gs).length = (Gs.length + 1) / 2
  | [] => by simp
  | [G] => by simp
  | G₁ :: G₂ :: rest => by
      have ih := mLevel_length rest
      simp only [mLevel_cons_cons, List.length_cons, ih]
      omega

@[simp] theorem iter_zero (Gs : List (List (List Val))) : iter 0 Gs = Gs := rfl

theorem iter_succ (k : ℕ) (Gs : List (List (List Val))) :
    iter (k + 1) Gs = iter k (mLevel Gs) := rfl

@[simp] theorem mAll_nil : mAll ([] : List (List (List Val))) = [] := rfl

@[simp] theorem mAll_singleton (G : List (List Val)) : mAll [G] = [G] := rfl

/-- `mLevel` on a list of `cols` is the `cols` of the pairwise-concatenated pieces. -/
theorem mLevel_map_cols : ∀ ps : List (List (List Val)),
    mLevel (ps.map cols) = (pairUp ps).map cols
  | [] => by simp [mLevel, pairUp]
  | [p] => by simp [mLevel, pairUp]
  | p :: p₂ :: rest => by
      have ih := mLevel_map_cols rest
      simp only [List.map_cons, mLevel_cons_cons, pairUp]
      rw [ih, ← cols_append]

theorem pairUp_length : ∀ ps : List (List (List Val)), (pairUp ps).length = (ps.length + 1) / 2
  | [] => by simp [pairUp]
  | [p] => by simp [pairUp]
  | p₁ :: p₂ :: rest => by
      have ih := pairUp_length rest
      simp only [pairUp, List.length_cons, ih]
      omega

theorem pairUp_flatten : ∀ ps : List (List (List Val)), (pairUp ps).flatten = ps.flatten
  | [] => by simp [pairUp]
  | [p] => by simp [pairUp]
  | p₁ :: p₂ :: rest => by
      have ih := pairUp_flatten rest
      simp only [pairUp, List.flatten_cons, ih, List.append_assoc]

end Work.SynFFT
