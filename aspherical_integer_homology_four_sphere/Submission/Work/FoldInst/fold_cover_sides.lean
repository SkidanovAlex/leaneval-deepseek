/-
# The side cover of `M̄`: every point of `Q̄` has the tight sides of a fold wall

The main statement: if `y ∈ Q̄`, there is a fold class `i` and a sign index `r` such that the set of
sides tight at `y` is exactly the set of walls `foldWalls i r`.

The proof reduces the statement to a finite verification:
* the six coordinate pairs of the 24-cell; `positiveSide p` is the side of `Q` with normal
  `e_i + e_j` on the pair `p = {i,j}`, and `supFst`/`supSnd` are the two coordinates on which the
  normal of a side is non-zero (`sideNormal S (supFst S) = ±1`, `sideNormal S (supSnd S) = ±1`);
* with `σ = Qbar_signOfPoint y` (the sign pattern of `y`) and `g` its group element, a side `S` is
  tight at `y` iff it is the image under the sign change `σ` of the positive side of a pair on which
  `|y|` is *maximal* (`|y i| + |y j| = 1`); the set `E` of such pairs is *pairwise intersecting*,
  because two disjoint pairs would give `∑ |y i| ≥ 2 > 8/5` while `y ∈ Q̄` forces `∑ |y i| ≤ 8/5`;
* a pairwise intersecting set of pairs of a 4-element set is one of 27 shapes (checked finitely, by
  `decide`): empty, a single pair, a pair of intersecting pairs, or a star/triangle of three pairs;
* for each of these 27 shapes and each of the 16 sign patterns a fold class and a sign index are
  exhibited whose walls are exactly the corresponding sides (the finite tables `wOne`, `wTwo`,
  `wThree` and the `decide`-checked theorems `checkOne`, `checkTwo`, `checkThree`).
-/
import Mathlib
import Submission.Work.FoldInst.FoldPiece
import Submission.Work.FoldInst.Qbar_geometry

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

noncomputable section

open Matrix
open scoped Matrix

namespace Work.FoldInst

namespace FoldCover

/-! ### The six coordinate pairs and their positive sides -/

/-- The pairs `{i,j} ⊂ Fin 4`, in the order `(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)`. -/
def pairFst : Fin 6 → Fin 4 := ![0,0,0,1,1,2]

/-- The second coordinate of a pair. -/
def pairSnd : Fin 6 → Fin 4 := ![1,2,3,2,3,3]

/-- The side of `Q` whose normal is `e_{pairFst p} + e_{pairSnd p}`. -/
def positiveSide : Fin 6 → Fin 24 := ![0,4,12,8,16,20]

theorem pairFst_ne_pairSnd (p : Fin 6) : pairFst p ≠ pairSnd p := by decide +revert

theorem sideNormal_positiveSide (p : Fin 6) (k : Fin 4) :
    sideNormal (positiveSide p) k =
      (if k = pairFst p then 1 else 0) + (if k = pairSnd p then 1 else 0) := by decide +revert

theorem positiveSide_injective : Function.Injective positiveSide := by decide +revert

theorem positiveSide_eq_iff (p q : Fin 6) : positiveSide p = positiveSide q ↔ p = q :=
  ⟨fun h => positiveSide_injective h, fun h => by rw [h]⟩

/-! ### The support of a side -/

/-- The first coordinate of the support of the normal of a side. -/
def supFst : Fin 24 → Fin 4 := ![0,0,0,0,0,0,0,0,1,1,1,1,0,0,0,0,1,1,1,1,2,2,2,2]

/-- The second coordinate of the support of the normal of a side. -/
def supSnd : Fin 24 → Fin 4 := ![1,1,1,1,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,3,3,3]

theorem supFst_ne_supSnd (S : Fin 24) : supFst S ≠ supSnd S := by decide +revert

/-- The normal of a side is supported on the two coordinates `supFst S`, `supSnd S`. -/
theorem sideNormal_decomp (S : Fin 24) (k : Fin 4) :
    sideNormal S k = (if k = supFst S then sideNormal S (supFst S) else 0) +
      (if k = supSnd S then sideNormal S (supSnd S) else 0) := by decide +revert

theorem sideNormal_supFst_pm (S : Fin 24) :
    sideNormal S (supFst S) = 1 ∨ sideNormal S (supFst S) = -1 := by decide +revert

theorem sideNormal_supSnd_pm (S : Fin 24) :
    sideNormal S (supSnd S) = 1 ∨ sideNormal S (supSnd S) = -1 := by decide +revert

theorem sideNormal_eq_zero (S : Fin 24) (k : Fin 4) (h1 : k ≠ supFst S) (h2 : k ≠ supSnd S) :
    sideNormal S k = 0 := by
  rw [sideNormal_decomp S k]
  simp [h1, h2]

/-! ### Which pairs of sides intersect -/

/-- Do the supports of two sides meet?  (`true` unless the two pairs are complementary.) -/
def interPair (p q : Fin 6) : Bool :=
  (pairFst p == pairFst q) || (pairFst p == pairSnd q) || (pairSnd p == pairFst q) ||
    (pairSnd p == pairSnd q)

theorem interPair_true_iff (p q : Fin 6) :
    interPair p q = true ↔
      (pairFst p = pairFst q ∨ pairFst p = pairSnd q ∨ pairSnd p = pairFst q ∨
        pairSnd p = pairSnd q) := by decide +revert

theorem interPair_false_iff (p q : Fin 6) :
    interPair p q = false ↔
      (pairFst p ≠ pairFst q ∧ pairFst p ≠ pairSnd q ∧ pairSnd p ≠ pairFst q ∧
        pairSnd p ≠ pairSnd q) := by decide +revert

theorem interPair_refl (p : Fin 6) : interPair p p = true := by decide +revert

/-- A pair of coordinates determines the pair index. -/
theorem pair_exists (i j : Fin 4) (hij : i ≠ j) :
    ∃ q : Fin 6, (pairFst q = i ∧ pairSnd q = j) ∨ (pairFst q = j ∧ pairSnd q = i) := by
  decide +revert

theorem sidePerm_sideNormal_positiveSide (g : Fin 4 → ZMod 2) (p : Fin 6) (k : Fin 4) :
    sideNormal (sidePerm g (positiveSide p)) k =
      (if k = pairFst p then signVec g k else 0) + (if k = pairSnd p then signVec g k else 0) := by
  rw [sideNormal_sidePerm, sideNormal_positiveSide]
  by_cases h1 : k = pairFst p <;> by_cases h2 : k = pairSnd p <;>
    simp [h1, h2, pairFst_ne_pairSnd p, Ne.symm (pairFst_ne_pairSnd p)]


/-! ### The finite cover: the witness tables

For each of the 27 shapes of a pairwise intersecting set of pairs and each of the 16 sign patterns,
`wOne`, `wTwo`, `wThree` record a fold class and the `Fin 8` label of a sign index whose walls are
exactly the corresponding sides.  The three tables are indexed by `(shape, enc g)` flattened. -/

/-- The sign index `Fin (foldCodim i) → Bool` of a wall-reflection pattern `j : Fin 8` (`j`'s bit at
the position of the `u`-th wall says whether that wall is negated). -/
def rOf (i : Fin 98) (j : Fin 8) : Fin (foldCodim i) → Bool :=
  fun u => (j.val / 2 ^ (foldWallPos i (Fin.castLE (foldCodim_le i) u)).val) % 2 = 1

def idx1 (p : Fin 6) (gi : Fin 16) : Fin 96 :=
  ⟨p.val * 16 + gi.val, by have := p.isLt; have := gi.isLt; omega⟩

def idx2 (a : Fin 12) (gi : Fin 16) : Fin 192 :=
  ⟨a.val * 16 + gi.val, by have := a.isLt; have := gi.isLt; omega⟩

def idx3 (a : Fin 8) (gi : Fin 16) : Fin 128 :=
  ⟨a.val * 16 + gi.val, by have := a.isLt; have := gi.isLt; omega⟩

/-- The twelve pairs of intersecting coordinate pairs, first coordinates. -/
def pOf1 : Fin 12 → Fin 6 := ![0,0,0,0,1,1,1,2,2,3,3,4]

/-- The twelve pairs of intersecting coordinate pairs, second coordinates. -/
def pOf2 : Fin 12 → Fin 6 := ![1,2,3,4,2,3,5,4,5,4,5,5]

/-- The eight pairwise intersecting triples of pairs, first elements. -/
def triFst : Fin 8 → Fin 6 := ![0,0,0,0,1,1,2,3]

/-- The eight pairwise intersecting triples of pairs, second elements. -/
def triSnd : Fin 8 → Fin 6 := ![1,1,2,3,2,3,4,4]

/-- The eight pairwise intersecting triples of pairs, third elements. -/
def triTrd : Fin 8 → Fin 6 := ![2,3,4,4,5,5,5,5]
def wOne : Fin 96 → Fin 98 × Fin 8 :=
  ![((1 : Fin 98), (0 : Fin 8)), ((1 : Fin 98), (1 : Fin 8)), ((2 : Fin 98), (0 : Fin 8)), ((2 : Fin 98), (1 : Fin 8)), ((1 : Fin 98), (0 : Fin 8)), ((1 : Fin 98), (1 : Fin 8)), ((2 : Fin 98), (0 : Fin 8)), ((2 : Fin 98), (1 : Fin 8)), ((1 : Fin 98), (0 : Fin 8)), ((1 : Fin 98), (1 : Fin 8)), ((2 : Fin 98), (0 : Fin 8)), ((2 : Fin 98), (1 : Fin 8)), ((1 : Fin 98), (0 : Fin 8)), ((1 : Fin 98), (1 : Fin 8)), ((2 : Fin 98), (0 : Fin 8)), ((2 : Fin 98), (1 : Fin 8)), ((3 : Fin 98), (0 : Fin 8)), ((4 : Fin 98), (0 : Fin 8)), ((3 : Fin 98), (0 : Fin 8)), ((4 : Fin 98), (0 : Fin 8)), ((3 : Fin 98), (2 : Fin 8)), ((4 : Fin 98), (2 : Fin 8)), ((3 : Fin 98), (2 : Fin 8)), ((4 : Fin 98), (2 : Fin 8)), ((3 : Fin 98), (0 : Fin 8)), ((4 : Fin 98), (0 : Fin 8)), ((3 : Fin 98), (0 : Fin 8)), ((4 : Fin 98), (0 : Fin 8)), ((3 : Fin 98), (2 : Fin 8)), ((4 : Fin 98), (2 : Fin 8)), ((3 : Fin 98), (2 : Fin 8)), ((4 : Fin 98), (2 : Fin 8)), ((9 : Fin 98), (0 : Fin 8)), ((10 : Fin 98), (0 : Fin 8)), ((9 : Fin 98), (0 : Fin 8)), ((10 : Fin 98), (0 : Fin 8)), ((9 : Fin 98), (0 : Fin 8)), ((10 : Fin 98), (0 : Fin 8)), ((9 : Fin 98), (0 : Fin 8)), ((10 : Fin 98), (0 : Fin 8)), ((10 : Fin 98), (2 : Fin 8)), ((9 : Fin 98), (2 : Fin 8)), ((10 : Fin 98), (2 : Fin 8)), ((9 : Fin 98), (2 : Fin 8)), ((10 : Fin 98), (2 : Fin 8)), ((9 : Fin 98), (2 : Fin 8)), ((10 : Fin 98), (2 : Fin 8)), ((9 : Fin 98), (2 : Fin 8)), ((5 : Fin 98), (0 : Fin 8)), ((5 : Fin 98), (0 : Fin 8)), ((6 : Fin 98), (0 : Fin 8)), ((6 : Fin 98), (0 : Fin 8)), ((6 : Fin 98), (4 : Fin 8)), ((6 : Fin 98), (4 : Fin 8)), ((5 : Fin 98), (4 : Fin 8)), ((5 : Fin 98), (4 : Fin 8)), ((5 : Fin 98), (0 : Fin 8)), ((5 : Fin 98), (0 : Fin 8)), ((6 : Fin 98), (0 : Fin 8)), ((6 : Fin 98), (0 : Fin 8)), ((6 : Fin 98), (4 : Fin 8)), ((6 : Fin 98), (4 : Fin 8)), ((5 : Fin 98), (4 : Fin 8)), ((5 : Fin 98), (4 : Fin 8)), ((13 : Fin 98), (0 : Fin 8)), ((13 : Fin 98), (0 : Fin 8)), ((13 : Fin 98), (4 : Fin 8)), ((13 : Fin 98), (4 : Fin 8)), ((13 : Fin 98), (0 : Fin 8)), ((13 : Fin 98), (0 : Fin 8)), ((13 : Fin 98), (4 : Fin 8)), ((13 : Fin 98), (4 : Fin 8)), ((14 : Fin 98), (0 : Fin 8)), ((14 : Fin 98), (0 : Fin 8)), ((14 : Fin 98), (4 : Fin 8)), ((14 : Fin 98), (4 : Fin 8)), ((14 : Fin 98), (0 : Fin 8)), ((14 : Fin 98), (0 : Fin 8)), ((14 : Fin 98), (4 : Fin 8)), ((14 : Fin 98), (4 : Fin 8)), ((15 : Fin 98), (0 : Fin 8)), ((15 : Fin 98), (0 : Fin 8)), ((15 : Fin 98), (0 : Fin 8)), ((15 : Fin 98), (0 : Fin 8)), ((16 : Fin 98), (0 : Fin 8)), ((16 : Fin 98), (0 : Fin 8)), ((16 : Fin 98), (0 : Fin 8)), ((16 : Fin 98), (0 : Fin 8)), ((15 : Fin 98), (4 : Fin 8)), ((15 : Fin 98), (4 : Fin 8)), ((15 : Fin 98), (4 : Fin 8)), ((15 : Fin 98), (4 : Fin 8)), ((16 : Fin 98), (4 : Fin 8)), ((16 : Fin 98), (4 : Fin 8)), ((16 : Fin 98), (4 : Fin 8)), ((16 : Fin 98), (4 : Fin 8))]

def wTwo : Fin 192 → Fin 98 × Fin 8 :=
  ![((17 : Fin 98), (0 : Fin 8)), ((17 : Fin 98), (1 : Fin 8)), ((24 : Fin 98), (0 : Fin 8)), ((24 : Fin 98), (1 : Fin 8)), ((17 : Fin 98), (2 : Fin 8)), ((17 : Fin 98), (3 : Fin 8)), ((24 : Fin 98), (2 : Fin 8)), ((24 : Fin 98), (3 : Fin 8)), ((17 : Fin 98), (0 : Fin 8)), ((17 : Fin 98), (1 : Fin 8)), ((24 : Fin 98), (0 : Fin 8)), ((24 : Fin 98), (1 : Fin 8)), ((17 : Fin 98), (2 : Fin 8)), ((17 : Fin 98), (3 : Fin 8)), ((24 : Fin 98), (2 : Fin 8)), ((24 : Fin 98), (3 : Fin 8)), ((20 : Fin 98), (0 : Fin 8)), ((20 : Fin 98), (1 : Fin 8)), ((21 : Fin 98), (3 : Fin 8)), ((21 : Fin 98), (2 : Fin 8)), ((20 : Fin 98), (0 : Fin 8)), ((20 : Fin 98), (1 : Fin 8)), ((21 : Fin 98), (3 : Fin 8)), ((21 : Fin 98), (2 : Fin 8)), ((21 : Fin 98), (0 : Fin 8)), ((21 : Fin 98), (1 : Fin 8)), ((20 : Fin 98), (3 : Fin 8)), ((20 : Fin 98), (2 : Fin 8)), ((21 : Fin 98), (0 : Fin 8)), ((21 : Fin 98), (1 : Fin 8)), ((20 : Fin 98), (3 : Fin 8)), ((20 : Fin 98), (2 : Fin 8)), ((18 : Fin 98), (0 : Fin 8)), ((18 : Fin 98), (1 : Fin 8)), ((19 : Fin 98), (5 : Fin 8)), ((19 : Fin 98), (4 : Fin 8)), ((19 : Fin 98), (0 : Fin 8)), ((19 : Fin 98), (1 : Fin 8)), ((18 : Fin 98), (5 : Fin 8)), ((18 : Fin 98), (4 : Fin 8)), ((18 : Fin 98), (0 : Fin 8)), ((18 : Fin 98), (1 : Fin 8)), ((19 : Fin 98), (5 : Fin 8)), ((19 : Fin 98), (4 : Fin 8)), ((19 : Fin 98), (0 : Fin 8)), ((19 : Fin 98), (1 : Fin 8)), ((18 : Fin 98), (5 : Fin 8)), ((18 : Fin 98), (4 : Fin 8)), ((22 : Fin 98), (0 : Fin 8)), ((22 : Fin 98), (1 : Fin 8)), ((22 : Fin 98), (4 : Fin 8)), ((22 : Fin 98), (5 : Fin 8)), ((22 : Fin 98), (0 : Fin 8)), ((22 : Fin 98), (1 : Fin 8)), ((22 : Fin 98), (4 : Fin 8)), ((22 : Fin 98), (5 : Fin 8)), ((23 : Fin 98), (0 : Fin 8)), ((23 : Fin 98), (1 : Fin 8)), ((23 : Fin 98), (4 : Fin 8)), ((23 : Fin 98), (5 : Fin 8)), ((23 : Fin 98), (0 : Fin 8)), ((23 : Fin 98), (1 : Fin 8)), ((23 : Fin 98), (4 : Fin 8)), ((23 : Fin 98), (5 : Fin 8)), ((31 : Fin 98), (0 : Fin 8)), ((32 : Fin 98), (3 : Fin 8)), ((31 : Fin 98), (0 : Fin 8)), ((32 : Fin 98), (3 : Fin 8)), ((31 : Fin 98), (1 : Fin 8)), ((32 : Fin 98), (2 : Fin 8)), ((31 : Fin 98), (1 : Fin 8)), ((32 : Fin 98), (2 : Fin 8)), ((32 : Fin 98), (0 : Fin 8)), ((31 : Fin 98), (3 : Fin 8)), ((32 : Fin 98), (0 : Fin 8)), ((31 : Fin 98), (3 : Fin 8)), ((32 : Fin 98), (1 : Fin 8)), ((31 : Fin 98), (2 : Fin 8)), ((32 : Fin 98), (1 : Fin 8)), ((31 : Fin 98), (2 : Fin 8)), ((29 : Fin 98), (0 : Fin 8)), ((30 : Fin 98), (6 : Fin 8)), ((30 : Fin 98), (0 : Fin 8)), ((29 : Fin 98), (6 : Fin 8)), ((29 : Fin 98), (2 : Fin 8)), ((30 : Fin 98), (4 : Fin 8)), ((30 : Fin 98), (2 : Fin 8)), ((29 : Fin 98), (4 : Fin 8)), ((29 : Fin 98), (0 : Fin 8)), ((30 : Fin 98), (6 : Fin 8)), ((30 : Fin 98), (0 : Fin 8)), ((29 : Fin 98), (6 : Fin 8)), ((29 : Fin 98), (2 : Fin 8)), ((30 : Fin 98), (4 : Fin 8)), ((30 : Fin 98), (2 : Fin 8)), ((29 : Fin 98), (4 : Fin 8)), ((33 : Fin 98), (0 : Fin 8)), ((38 : Fin 98), (0 : Fin 8)), ((33 : Fin 98), (0 : Fin 8)), ((38 : Fin 98), (0 : Fin 8)), ((33 : Fin 98), (1 : Fin 8)), ((38 : Fin 98), (1 : Fin 8)), ((33 : Fin 98), (1 : Fin 8)), ((38 : Fin 98), (1 : Fin 8)), ((33 : Fin 98), (4 : Fin 8)), ((38 : Fin 98), (4 : Fin 8)), ((33 : Fin 98), (4 : Fin 8)), ((38 : Fin 98), (4 : Fin 8)), ((33 : Fin 98), (5 : Fin 8)), ((38 : Fin 98), (5 : Fin 8)), ((33 : Fin 98), (5 : Fin 8)), ((38 : Fin 98), (5 : Fin 8)), ((47 : Fin 98), (0 : Fin 8)), ((50 : Fin 98), (0 : Fin 8)), ((47 : Fin 98), (4 : Fin 8)), ((50 : Fin 98), (4 : Fin 8)), ((47 : Fin 98), (0 : Fin 8)), ((50 : Fin 98), (0 : Fin 8)), ((47 : Fin 98), (4 : Fin 8)), ((50 : Fin 98), (4 : Fin 8)), ((50 : Fin 98), (6 : Fin 8)), ((47 : Fin 98), (6 : Fin 8)), ((50 : Fin 98), (2 : Fin 8)), ((47 : Fin 98), (2 : Fin 8)), ((50 : Fin 98), (6 : Fin 8)), ((47 : Fin 98), (6 : Fin 8)), ((50 : Fin 98), (2 : Fin 8)), ((47 : Fin 98), (2 : Fin 8)), ((48 : Fin 98), (0 : Fin 8)), ((49 : Fin 98), (6 : Fin 8)), ((48 : Fin 98), (0 : Fin 8)), ((49 : Fin 98), (6 : Fin 8)), ((49 : Fin 98), (0 : Fin 8)), ((48 : Fin 98), (6 : Fin 8)), ((49 : Fin 98), (0 : Fin 8)), ((48 : Fin 98), (6 : Fin 8)), ((48 : Fin 98), (4 : Fin 8)), ((49 : Fin 98), (2 : Fin 8)), ((48 : Fin 98), (4 : Fin 8)), ((49 : Fin 98), (2 : Fin 8)), ((49 : Fin 98), (4 : Fin 8)), ((48 : Fin 98), (2 : Fin 8)), ((49 : Fin 98), (4 : Fin 8)), ((48 : Fin 98), (2 : Fin 8)), ((39 : Fin 98), (0 : Fin 8)), ((39 : Fin 98), (0 : Fin 8)), ((39 : Fin 98), (2 : Fin 8)), ((39 : Fin 98), (2 : Fin 8)), ((40 : Fin 98), (3 : Fin 8)), ((40 : Fin 98), (3 : Fin 8)), ((40 : Fin 98), (1 : Fin 8)), ((40 : Fin 98), (1 : Fin 8)), ((40 : Fin 98), (0 : Fin 8)), ((40 : Fin 98), (0 : Fin 8)), ((40 : Fin 98), (2 : Fin 8)), ((40 : Fin 98), (2 : Fin 8)), ((39 : Fin 98), (3 : Fin 8)), ((39 : Fin 98), (3 : Fin 8)), ((39 : Fin 98), (1 : Fin 8)), ((39 : Fin 98), (1 : Fin 8)), ((41 : Fin 98), (0 : Fin 8)), ((41 : Fin 98), (0 : Fin 8)), ((42 : Fin 98), (0 : Fin 8)), ((42 : Fin 98), (0 : Fin 8)), ((42 : Fin 98), (5 : Fin 8)), ((42 : Fin 98), (5 : Fin 8)), ((41 : Fin 98), (5 : Fin 8)), ((41 : Fin 98), (5 : Fin 8)), ((41 : Fin 98), (4 : Fin 8)), ((41 : Fin 98), (4 : Fin 8)), ((42 : Fin 98), (4 : Fin 8)), ((42 : Fin 98), (4 : Fin 8)), ((42 : Fin 98), (1 : Fin 8)), ((42 : Fin 98), (1 : Fin 8)), ((41 : Fin 98), (1 : Fin 8)), ((41 : Fin 98), (1 : Fin 8)), ((55 : Fin 98), (0 : Fin 8)), ((55 : Fin 98), (0 : Fin 8)), ((55 : Fin 98), (2 : Fin 8)), ((55 : Fin 98), (2 : Fin 8)), ((56 : Fin 98), (0 : Fin 8)), ((56 : Fin 98), (0 : Fin 8)), ((56 : Fin 98), (2 : Fin 8)), ((56 : Fin 98), (2 : Fin 8)), ((55 : Fin 98), (4 : Fin 8)), ((55 : Fin 98), (4 : Fin 8)), ((55 : Fin 98), (6 : Fin 8)), ((55 : Fin 98), (6 : Fin 8)), ((56 : Fin 98), (4 : Fin 8)), ((56 : Fin 98), (4 : Fin 8)), ((56 : Fin 98), (6 : Fin 8)), ((56 : Fin 98), (6 : Fin 8))]

def wThree : Fin 128 → Fin 98 × Fin 8 :=
  ![((61 : Fin 98), (4 : Fin 8)), ((61 : Fin 98), (5 : Fin 8)), ((66 : Fin 98), (3 : Fin 8)), ((66 : Fin 98), (2 : Fin 8)), ((61 : Fin 98), (6 : Fin 8)), ((61 : Fin 98), (7 : Fin 8)), ((66 : Fin 98), (1 : Fin 8)), ((66 : Fin 98), (0 : Fin 8)), ((66 : Fin 98), (4 : Fin 8)), ((66 : Fin 98), (5 : Fin 8)), ((61 : Fin 98), (3 : Fin 8)), ((61 : Fin 98), (2 : Fin 8)), ((66 : Fin 98), (6 : Fin 8)), ((66 : Fin 98), (7 : Fin 8)), ((61 : Fin 98), (1 : Fin 8)), ((61 : Fin 98), (0 : Fin 8)), ((57 : Fin 98), (4 : Fin 8)), ((57 : Fin 98), (5 : Fin 8)), ((57 : Fin 98), (3 : Fin 8)), ((57 : Fin 98), (2 : Fin 8)), ((57 : Fin 98), (6 : Fin 8)), ((57 : Fin 98), (7 : Fin 8)), ((57 : Fin 98), (1 : Fin 8)), ((57 : Fin 98), (0 : Fin 8)), ((57 : Fin 98), (4 : Fin 8)), ((57 : Fin 98), (5 : Fin 8)), ((57 : Fin 98), (3 : Fin 8)), ((57 : Fin 98), (2 : Fin 8)), ((57 : Fin 98), (6 : Fin 8)), ((57 : Fin 98), (7 : Fin 8)), ((57 : Fin 98), (1 : Fin 8)), ((57 : Fin 98), (0 : Fin 8)), ((58 : Fin 98), (2 : Fin 8)), ((58 : Fin 98), (3 : Fin 8)), ((58 : Fin 98), (6 : Fin 8)), ((58 : Fin 98), (7 : Fin 8)), ((58 : Fin 98), (2 : Fin 8)), ((58 : Fin 98), (3 : Fin 8)), ((58 : Fin 98), (6 : Fin 8)), ((58 : Fin 98), (7 : Fin 8)), ((58 : Fin 98), (5 : Fin 8)), ((58 : Fin 98), (4 : Fin 8)), ((58 : Fin 98), (1 : Fin 8)), ((58 : Fin 98), (0 : Fin 8)), ((58 : Fin 98), (5 : Fin 8)), ((58 : Fin 98), (4 : Fin 8)), ((58 : Fin 98), (1 : Fin 8)), ((58 : Fin 98), (0 : Fin 8)), ((62 : Fin 98), (2 : Fin 8)), ((62 : Fin 98), (3 : Fin 8)), ((62 : Fin 98), (6 : Fin 8)), ((62 : Fin 98), (7 : Fin 8)), ((67 : Fin 98), (5 : Fin 8)), ((67 : Fin 98), (4 : Fin 8)), ((67 : Fin 98), (1 : Fin 8)), ((67 : Fin 98), (0 : Fin 8)), ((67 : Fin 98), (2 : Fin 8)), ((67 : Fin 98), (3 : Fin 8)), ((67 : Fin 98), (6 : Fin 8)), ((67 : Fin 98), (7 : Fin 8)), ((62 : Fin 98), (5 : Fin 8)), ((62 : Fin 98), (4 : Fin 8)), ((62 : Fin 98), (1 : Fin 8)), ((62 : Fin 98), (0 : Fin 8)), ((59 : Fin 98), (2 : Fin 8)), ((59 : Fin 98), (5 : Fin 8)), ((59 : Fin 98), (2 : Fin 8)), ((59 : Fin 98), (5 : Fin 8)), ((59 : Fin 98), (3 : Fin 8)), ((59 : Fin 98), (4 : Fin 8)), ((59 : Fin 98), (3 : Fin 8)), ((59 : Fin 98), (4 : Fin 8)), ((59 : Fin 98), (6 : Fin 8)), ((59 : Fin 98), (1 : Fin 8)), ((59 : Fin 98), (6 : Fin 8)), ((59 : Fin 98), (1 : Fin 8)), ((59 : Fin 98), (7 : Fin 8)), ((59 : Fin 98), (0 : Fin 8)), ((59 : Fin 98), (7 : Fin 8)), ((59 : Fin 98), (0 : Fin 8)), ((63 : Fin 98), (2 : Fin 8)), ((74 : Fin 98), (5 : Fin 8)), ((74 : Fin 98), (2 : Fin 8)), ((63 : Fin 98), (5 : Fin 8)), ((63 : Fin 98), (3 : Fin 8)), ((74 : Fin 98), (4 : Fin 8)), ((74 : Fin 98), (3 : Fin 8)), ((63 : Fin 98), (4 : Fin 8)), ((63 : Fin 98), (6 : Fin 8)), ((74 : Fin 98), (1 : Fin 8)), ((74 : Fin 98), (6 : Fin 8)), ((63 : Fin 98), (1 : Fin 8)), ((63 : Fin 98), (7 : Fin 8)), ((74 : Fin 98), (0 : Fin 8)), ((74 : Fin 98), (7 : Fin 8)), ((63 : Fin 98), (0 : Fin 8)), ((64 : Fin 98), (1 : Fin 8)), ((70 : Fin 98), (6 : Fin 8)), ((64 : Fin 98), (3 : Fin 8)), ((70 : Fin 98), (4 : Fin 8)), ((70 : Fin 98), (1 : Fin 8)), ((64 : Fin 98), (6 : Fin 8)), ((70 : Fin 98), (3 : Fin 8)), ((64 : Fin 98), (4 : Fin 8)), ((64 : Fin 98), (5 : Fin 8)), ((70 : Fin 98), (2 : Fin 8)), ((64 : Fin 98), (7 : Fin 8)), ((70 : Fin 98), (0 : Fin 8)), ((70 : Fin 98), (5 : Fin 8)), ((64 : Fin 98), (2 : Fin 8)), ((70 : Fin 98), (7 : Fin 8)), ((64 : Fin 98), (0 : Fin 8)), ((60 : Fin 98), (1 : Fin 8)), ((60 : Fin 98), (1 : Fin 8)), ((60 : Fin 98), (3 : Fin 8)), ((60 : Fin 98), (3 : Fin 8)), ((60 : Fin 98), (6 : Fin 8)), ((60 : Fin 98), (6 : Fin 8)), ((60 : Fin 98), (4 : Fin 8)), ((60 : Fin 98), (4 : Fin 8)), ((60 : Fin 98), (5 : Fin 8)), ((60 : Fin 98), (5 : Fin 8)), ((60 : Fin 98), (7 : Fin 8)), ((60 : Fin 98), (7 : Fin 8)), ((60 : Fin 98), (2 : Fin 8)), ((60 : Fin 98), (2 : Fin 8)), ((60 : Fin 98), (0 : Fin 8)), ((60 : Fin 98), (0 : Fin 8))]


def wOneI (p : Fin 6) (g : Fin 4 → ZMod 2) : Fin 98 := (wOne (idx1 p (enc g))).1
def wOneR (p : Fin 6) (g : Fin 4 → ZMod 2) : Fin (foldCodim (wOneI p g)) → Bool :=
  rOf (wOneI p g) (wOne (idx1 p (enc g))).2
def wTwoI (a : Fin 12) (g : Fin 4 → ZMod 2) : Fin 98 := (wTwo (idx2 a (enc g))).1
def wTwoR (a : Fin 12) (g : Fin 4 → ZMod 2) : Fin (foldCodim (wTwoI a g)) → Bool :=
  rOf (wTwoI a g) (wTwo (idx2 a (enc g))).2
def wThreeI (a : Fin 8) (g : Fin 4 → ZMod 2) : Fin 98 := (wThree (idx3 a (enc g))).1
def wThreeR (a : Fin 8) (g : Fin 4 → ZMod 2) : Fin (foldCodim (wThreeI a g)) → Bool :=
  rOf (wThreeI a g) (wThree (idx3 a (enc g))).2

/-- A class with no walls (the codimension zero class), for the empty shape. -/
def wEmptyI : Fin 98 := 0

/-- **The empty shape.**  The codimension zero class has no walls. -/
theorem checkEmpty : ∀ S : Fin 24, ¬ (∃ t : Fin (foldCodim wEmptyI), foldWalls wEmptyI (rOf wEmptyI 0) t = S) := by
  decide

/-- **The single-pair shape.** -/
theorem checkOne (p : Fin 6) (g : Fin 4 → ZMod 2) :
    ∀ S : Fin 24, (∃ t : Fin (foldCodim (wOneI p g)), foldWalls (wOneI p g) (wOneR p g) t = S) ↔
      S = sidePerm g (positiveSide p) := by
  decide +revert

/-- **The two-pair shape.** -/
theorem checkTwo (a : Fin 12) (g : Fin 4 → ZMod 2) :
    ∀ S : Fin 24, (∃ t : Fin (foldCodim (wTwoI a g)), foldWalls (wTwoI a g) (wTwoR a g) t = S) ↔
      (S = sidePerm g (positiveSide (pOf1 a)) ∨ S = sidePerm g (positiveSide (pOf2 a))) := by
  decide +revert

/-- **The three-pair shape.** -/
theorem checkThree (a : Fin 8) (g : Fin 4 → ZMod 2) :
    ∀ S : Fin 24, (∃ t : Fin (foldCodim (wThreeI a g)), foldWalls (wThreeI a g) (wThreeR a g) t = S) ↔
      (S = sidePerm g (positiveSide (triFst a)) ∨ S = sidePerm g (positiveSide (triSnd a)) ∨
        S = sidePerm g (positiveSide (triTrd a))) := by
  decide +revert

/-- **The classification of pairwise intersecting sets of pairs.**  A set of pairs whose supports are
pairwise intersecting is empty, a single pair, a pair of intersecting pairs, or one of the eight
stars/triangles of three pairs. -/
theorem classif (E : Finset (Fin 6)) (h : ∀ p ∈ E, ∀ q ∈ E, interPair p q = true) :
    E = ∅ ∨ (∃ p : Fin 6, E = {p}) ∨ (∃ a : Fin 12, E = {pOf1 a, pOf2 a}) ∨
      (∃ a : Fin 8, E = {triFst a, triSnd a, triTrd a}) := by
  decide +revert

/-! ### The tightness of a side in terms of the sign pattern -/

/-- The two-term form of `sideSlack`. -/
theorem sideSlack_two_term (S : Fin 24) (y : E4) :
    sideSlack S y = 1 - ((sideNormal S (supFst S) : ℝ) * y (supFst S) +
      (sideNormal S (supSnd S) : ℝ) * y (supSnd S)) := by
  have h : (∑ k : Fin 4, (sideNormal S k : ℝ) * y k) =
      (sideNormal S (supFst S) : ℝ) * y (supFst S) +
        (sideNormal S (supSnd S) : ℝ) * y (supSnd S) := by
    have h1 : (∑ k : Fin 4, (sideNormal S k : ℝ) * y k) =
        ∑ k : Fin 4, (((if k = supFst S then (sideNormal S (supFst S) : ℝ) else 0) +
          (if k = supSnd S then (sideNormal S (supSnd S) : ℝ) else 0)) * y k) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [sideNormal_decomp S k]
      push_cast
      ring
    rw [h1, Qbar_sum_two_point (supFst S) (supSnd S) (supFst_ne_supSnd S) _ _ y]
  rw [sideSlack, h]

/-- The two-term form of `sideSlack` at a side of the form `sidePerm g (positiveSide p)`. -/
theorem sideSlack_sidePerm_positiveSide_eq (g : Fin 4 → ZMod 2) (p : Fin 6) (y : E4) :
    sideSlack (sidePerm g (positiveSide p)) y =
      1 - ((signVec g (pairFst p) : ℝ) * y (pairFst p) +
        (signVec g (pairSnd p) : ℝ) * y (pairSnd p)) := by
  have h : (∑ k : Fin 4, (sideNormal (sidePerm g (positiveSide p)) k : ℝ) * y k) =
      (signVec g (pairFst p) : ℝ) * y (pairFst p) +
        (signVec g (pairSnd p) : ℝ) * y (pairSnd p) := by
    have h1 : (∑ k : Fin 4, (sideNormal (sidePerm g (positiveSide p)) k : ℝ) * y k) =
        ∑ k : Fin 4, (((if k = pairFst p then (signVec g (pairFst p) : ℝ) else 0) +
          (if k = pairSnd p then (signVec g (pairSnd p) : ℝ) else 0)) * y k) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [sidePerm_sideNormal_positiveSide g p k]
      by_cases h1 : k = pairFst p <;> by_cases h2 : k = pairSnd p <;>
        simp [h1, h2, pairFst_ne_pairSnd p, Ne.symm (pairFst_ne_pairSnd p)]
    rw [h1, Qbar_sum_two_point (pairFst p) (pairSnd p) (pairFst_ne_pairSnd p) _ _ y]
  rw [sideSlack, h]

/-- **Tightness of the positive side of a pair**: it is tight exactly when `|y|` is maximal on the
pair (`|y i| + |y j| = 1`). -/
theorem sideSlack_sign_positiveSide (y : E4) (p : Fin 6) :
    sideSlack (sidePerm (Qbar_signOfPoint y) (positiveSide p)) y = 0 ↔
      |y (pairFst p)| + |y (pairSnd p)| = 1 := by
  rw [sideSlack_sidePerm_positiveSide_eq]
  rw [signVec_Qbar_signOfPoint y (pairFst p), signVec_Qbar_signOfPoint y (pairSnd p)]
  constructor <;> intro h <;> linarith

/-- The sign of a coordinate, from an equality `a * y i = |y i|`. -/
theorem eq_signVec_of_mul {y : E4} {i : Fin 4} {a : ℤ} (ha : a = 1 ∨ a = -1)
    (h : (a : ℝ) * y i = |y i|) (hne : y i ≠ 0) :
    a = signVec (Qbar_signOfPoint y) i := by
  have hsign : (0 ≤ y i ∧ a = 1) ∨ (y i < 0 ∧ a = -1) := by
    rcases ha with h1 | h1
    · left
      rw [h1] at h
      simp only [Int.cast_one, one_mul] at h
      exact ⟨by rw [h]; exact abs_nonneg _, h1⟩
    · right
      rw [h1] at h
      simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul] at h
      have hlt : y i < 0 := by
        rcases lt_trichotomy (y i) 0 with hlt | heq | hgt
        · exact hlt
        · exact absurd heq hne
        · rw [abs_of_pos hgt] at h; linarith
      exact ⟨hlt, h1⟩
  rcases hsign with ⟨hge, rfl⟩ | ⟨hlt, rfl⟩
  · simp [Qbar_signOfPoint, hge, signVec]
  · simp [Qbar_signOfPoint, not_le.mpr hlt, signVec]


/-- **The converse of tightness**: a side tight at `y` is the sign-change image of the positive side
of a pair on which `|y|` is maximal. -/
theorem sideSlack_zero_imp (y : E4) (hy : y ∈ Qbar) (S : Fin 24) (h : sideSlack S y = 0) :
    ∃ p : Fin 6, |y (pairFst p)| + |y (pairSnd p)| = 1 ∧
      S = sidePerm (Qbar_signOfPoint y) (positiveSide p) := by
  have hkey : (sideNormal S (supFst S) : ℝ) * y (supFst S) +
      (sideNormal S (supSnd S) : ℝ) * y (supSnd S) = 1 := by
    have h2 := sideSlack_two_term S y
    rw [h] at h2
    linarith
  have ha : sideNormal S (supFst S) = 1 ∨ sideNormal S (supFst S) = -1 := sideNormal_supFst_pm S
  have hb : sideNormal S (supSnd S) = 1 ∨ sideNormal S (supSnd S) = -1 := sideNormal_supSnd_pm S
  have hai : (sideNormal S (supFst S) : ℝ) * y (supFst S) ≤ |y (supFst S)| := by
    rcases ha with h1 | h1
    · rw [h1]; simp only [Int.cast_one, one_mul]; exact le_abs_self _
    · rw [h1]; simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul]; exact neg_le_abs _
  have hbj : (sideNormal S (supSnd S) : ℝ) * y (supSnd S) ≤ |y (supSnd S)| := by
    rcases hb with h1 | h1
    · rw [h1]; simp only [Int.cast_one, one_mul]; exact le_abs_self _
    · rw [h1]; simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul]; exact neg_le_abs _
  have hpair := Qbar_pair_le y hy (supFst_ne_supSnd S)
  have heqi : (sideNormal S (supFst S) : ℝ) * y (supFst S) = |y (supFst S)| :=
    le_antisymm hai (by linarith)
  have heqj : (sideNormal S (supSnd S) : ℝ) * y (supSnd S) = |y (supSnd S)| :=
    le_antisymm hbj (by linarith)
  have hsum : |y (supFst S)| + |y (supSnd S)| = 1 := by linarith
  have hine : y (supFst S) ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hsum
    have := Qbar_abs_le y hy (supSnd S)
    linarith
  have hjne : y (supSnd S) ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hsum
    have := Qbar_abs_le y hy (supFst S)
    linarith
  have hsi : sideNormal S (supFst S) = signVec (Qbar_signOfPoint y) (supFst S) :=
    eq_signVec_of_mul ha heqi hine
  have hsj : sideNormal S (supSnd S) = signVec (Qbar_signOfPoint y) (supSnd S) :=
    eq_signVec_of_mul hb heqj hjne
  obtain ⟨p, hp | hp⟩ := pair_exists (supFst S) (supSnd S) (supFst_ne_supSnd S)
  · refine ⟨p, ?_, ?_⟩
    · rw [hp.1, hp.2]; exact hsum
    · apply sideNormal_injective
      funext k
      rw [sidePerm_sideNormal_positiveSide]
      by_cases hk1 : k = pairFst p
      · by_cases hk2 : k = pairSnd p
        · exact absurd (hk1.symm.trans hk2) (pairFst_ne_pairSnd p)
        · rw [if_pos hk1, if_neg hk2, add_zero, hk1, hp.1, hsi]
      · by_cases hk2 : k = pairSnd p
        · rw [if_neg hk1, if_pos hk2, zero_add, hk2, hp.2, hsj]
        · rw [if_neg hk1, if_neg hk2, sideNormal_eq_zero S k
              (fun hh => hk1 (by rw [hp.1]; exact hh))
              (fun hh => hk2 (by rw [hp.2]; exact hh))]
          simp
  · refine ⟨p, ?_, ?_⟩
    · rw [hp.1, hp.2, add_comm]; exact hsum
    · apply sideNormal_injective
      funext k
      rw [sidePerm_sideNormal_positiveSide]
      by_cases hk1 : k = pairFst p
      · by_cases hk2 : k = pairSnd p
        · exact absurd (hk1.symm.trans hk2) (pairFst_ne_pairSnd p)
        · rw [if_pos hk1, if_neg hk2, add_zero, hk1, hp.1, hsj]
      · by_cases hk2 : k = pairSnd p
        · rw [if_neg hk1, if_pos hk2, zero_add, hk2, hp.2, hsi]
        · rw [if_neg hk1, if_neg hk2, sideNormal_eq_zero S k
              (fun hh => hk2 (by rw [hp.2]; exact hh))
              (fun hh => hk1 (by rw [hp.1]; exact hh))]
          simp

/-- A sum over four distinct coordinates is at most the sum over all four. -/
theorem sum_four_le (a b c d : Fin 4) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (f : Fin 4 → ℝ) (hf : ∀ i, 0 ≤ f i) :
    f a + f b + f c + f d ≤ ∑ i, f i := by
  have hsub : ({a, b, c, d} : Finset (Fin 4)) ⊆ Finset.univ := Finset.subset_univ _
  have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => hf k)
  rw [Finset.sum_insert (by simp [hab, hac, had]),
      Finset.sum_insert (by simp [hbc, hbd]),
      Finset.sum_insert (by simp [hcd]),
      Finset.sum_singleton] at h
  linarith

/-- **The pairs on which `|y|` is maximal are pairwise intersecting.**  Two disjoint maximal pairs
would force `∑ |y i| ≥ 2`, contradicting `y ∈ Q̄`. -/
theorem pairwiseInter_pairs (y : E4) (hy : y ∈ Qbar) :
    ∀ p ∈ (Finset.univ.filter fun q : Fin 6 => |y (pairFst q)| + |y (pairSnd q)| = 1),
      ∀ q ∈ (Finset.univ.filter fun r : Fin 6 => |y (pairFst r)| + |y (pairSnd r)| = 1),
        interPair p q = true := by
  intro p hp q hq
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
  by_contra hc
  have hf : interPair p q = false := by
    cases hh : interPair p q <;> simp_all
  obtain ⟨h1, h2, h3, h4⟩ := (interPair_false_iff p q).mp hf
  have hle : |y (pairFst p)| + |y (pairSnd p)| + |y (pairFst q)| + |y (pairSnd q)| ≤
      ∑ i, |y i| :=
    sum_four_le (pairFst p) (pairSnd p) (pairFst q) (pairSnd q)
      (pairFst_ne_pairSnd p) h1 h2 h3 h4 (pairFst_ne_pairSnd q) (fun i => |y i|)
      (fun i => abs_nonneg _)
  have := Qbar_sum_abs_le y hy
  linarith

/-! ### The cover by the fold walls -/

end FoldCover

open FoldCover

/-- **Every point of `Q̄` has the tight sides of a fold wall.**  For `y ∈ Q̄` there is a fold class
`i` and a sign index `r` whose walls `foldWalls i r` are exactly the sides tight at `y`.

Let `σ = Qbar_signOfPoint y` be the sign pattern of `y` and let `E` be the set of coordinate pairs on
which `|y|` is maximal.  A side is tight at `y` exactly when it is the sign-change image of the
positive side of a pair in `E` (`sideSlack_zero_imp`, `sideSlack_sign_positiveSide`), and `E` is
pairwise intersecting (`pairwiseInter_pairs`).  The classification `classif` of such sets and the
finite checks `checkOne`, `checkTwo`, `checkThree` then produce the required class and sign index. -/
theorem fold_cover_sides (y : E4) (hy : y ∈ Qbar) (hT : ∀ w : Fin 24, truncSlack w y ≠ 0) :
    ∃ (i : Fin 98) (r : Fin (foldCodim i) → Bool), ∀ S : Fin 24, sideSlack S y = 0 ↔
      ∃ t : Fin (foldCodim i), foldWalls i r t = S := by
  classical
  set E : Finset (Fin 6) := Finset.univ.filter (fun q : Fin 6 =>
    |y (pairFst q)| + |y (pairSnd q)| = 1) with hE
  have hchar : ∀ S : Fin 24, sideSlack S y = 0 ↔
      ∃ q ∈ E, S = sidePerm (Qbar_signOfPoint y) (positiveSide q) := by
    intro S
    constructor
    · intro h
      obtain ⟨p, hp1, hp2⟩ := sideSlack_zero_imp y hy S h
      exact ⟨p, by rw [hE]; simp [hp1], hp2⟩
    · rintro ⟨q, hq, rfl⟩
      rw [hE] at hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      exact (sideSlack_sign_positiveSide y q).mpr hq
  have hpair : ∀ p ∈ E, ∀ q ∈ E, interPair p q = true := by
    intro p hp q hq
    rw [hE] at hp hq
    exact pairwiseInter_pairs y hy p hp q hq
  rcases classif E hpair with h0 | ⟨p, hp⟩ | ⟨a, ha⟩ | ⟨a, ha⟩
  · refine ⟨wEmptyI, rOf wEmptyI 0, fun S => ?_⟩
    rw [hchar S]
    constructor
    · rintro ⟨q, hq, -⟩
      rw [h0] at hq
      exact absurd hq (Finset.notMem_empty q)
    · intro h
      exact absurd h (checkEmpty S)
  · refine ⟨wOneI p (Qbar_signOfPoint y), wOneR p (Qbar_signOfPoint y), fun S => ?_⟩
    rw [hchar S]
    have hiff : (∃ q ∈ E, S = sidePerm (Qbar_signOfPoint y) (positiveSide q)) ↔
        S = sidePerm (Qbar_signOfPoint y) (positiveSide p) := by
      rw [hp]
      simp
    rw [hiff]
    exact (checkOne p (Qbar_signOfPoint y) S).symm
  · refine ⟨wTwoI a (Qbar_signOfPoint y), wTwoR a (Qbar_signOfPoint y), fun S => ?_⟩
    rw [hchar S]
    have hiff : (∃ q ∈ E, S = sidePerm (Qbar_signOfPoint y) (positiveSide q)) ↔
        (S = sidePerm (Qbar_signOfPoint y) (positiveSide (pOf1 a)) ∨
          S = sidePerm (Qbar_signOfPoint y) (positiveSide (pOf2 a))) := by
      rw [ha]
      simp
    rw [hiff]
    exact (checkTwo a (Qbar_signOfPoint y) S).symm
  · refine ⟨wThreeI a (Qbar_signOfPoint y), wThreeR a (Qbar_signOfPoint y), fun S => ?_⟩
    rw [hchar S]
    have hiff : (∃ q ∈ E, S = sidePerm (Qbar_signOfPoint y) (positiveSide q)) ↔
        (S = sidePerm (Qbar_signOfPoint y) (positiveSide (triFst a)) ∨
          S = sidePerm (Qbar_signOfPoint y) (positiveSide (triSnd a)) ∨
          S = sidePerm (Qbar_signOfPoint y) (positiveSide (triTrd a))) := by
      rw [ha]
      simp
    rw [hiff]
    exact (checkThree a (Qbar_signOfPoint y) S).symm
end Work.FoldInst
