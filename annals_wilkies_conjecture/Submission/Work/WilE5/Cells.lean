/-
  WilE5 — the sign-cell decomposition of a `SemiPf` set, the input to the disjointness clause of
  the frozen `E5_strat`.

  The frozen statement requires the stratification `L` to be *pairwise disjoint*.  The leaves
  produced by the recursion are disjoint inside one recursion tree, but leaves coming from
  different disjuncts of `X` may overlap (e.g. the leaves `{0 < y < 1}` of `[y]` and
  `{1/2 < y < 1}` of `[y - 1/2]`).  The cure is to run the recursion *cell by cell*: for each
  system of signs of the atoms `f_i` of `X` (`= 0`, `> 0`, `< 0`) the cell
  `{f_i = 0 (i ∈ Z), f_i > 0 (i ∈ P), f_i < 0 (i ∈ N)}` is an elementary semi-Pfaffian set; the
  cells are pairwise disjoint, they cover `X ∩ cubeC`, and the leaf of every state of the cell's
  own recursion is contained in that cell.

  Only the cells contained in `X.set` are kept (`goodCells`), and only the *nonempty* ones — the
  latter is what makes the number of cells polynomial in `X.deg` (Khovanskii's bound on the number
  of consistent sign conditions, `Cells/khovCount`), since the crude count `3^(#atoms)` is
  exponential while `#atoms ≤ X.deg`.
-/
import Mathlib
import Submission.Work.WilE5.SysL
import Submission.Work.WilE5.Basic

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE5
open WilkiesDesign WilkiesDesign.E

/-- The three signs used for sign conditions. -/
inductive Sign where
  | zero : Sign
  | pos : Sign
  | neg : Sign
  deriving DecidableEq

instance signFintype : Fintype Sign where
  elems := {Sign.zero, Sign.pos, Sign.neg}
  complete := by intro x; cases x <;> simp

instance signInhabited : Inhabited Sign := ⟨Sign.zero⟩

/-- The list of all atoms of a `SemiPf` set (with repetitions), in the order in which they occur
in `X.basics`.  Its length is at most `X.deg` and the sum of the atom degrees is exactly `X.deg`. -/
def atomsOf {k : ℕ} (X : SemiPf k) : List (EAPoly k X.r) :=
  X.basics.flatMap fun A => A.eqs ++ A.pos

/-- All sign assignments of the atoms of `X`. -/
def allSigns {k : ℕ} (X : SemiPf k) : List (Fin (atomsOf X).length → Sign) :=
  (Finset.univ : Finset (Fin (atomsOf X).length → Sign)).toList

/-- The sign of a real number. -/
def signOf (a : ℝ) : Sign := if a = 0 then Sign.zero else if 0 < a then Sign.pos else Sign.neg

/-- The sign assignment of `X` at a point. -/
def signAssign {k : ℕ} (X : SemiPf k) (z : Fin k → ℝ) : Fin (atomsOf X).length → Sign :=
  fun i => signOf (eaEval X.c ((atomsOf X).get i) z)

/-- The equations of the cell of a sign assignment. -/
def cellEqs {k : ℕ} (X : SemiPf k) (σ : Fin (atomsOf X).length → Sign) : List (EAPoly k X.r) :=
  ((Finset.univ : Finset (Fin (atomsOf X).length)).filter fun i => σ i = Sign.zero).toList.map
    fun i => (atomsOf X).get i

/-- The strict inequalities of the cell of a sign assignment (`-f` for the negative atoms). -/
def cellPos {k : ℕ} (X : SemiPf k) (σ : Fin (atomsOf X).length → Sign) : List (EAPoly k X.r) :=
  ((Finset.univ : Finset (Fin (atomsOf X).length)).filter
      fun i => σ i = Sign.pos ∨ σ i = Sign.neg).toList.map
    fun i => if σ i = Sign.pos then (atomsOf X).get i else -(atomsOf X).get i

/-- The sign cell of a sign assignment, as a basic set. -/
def cell {k : ℕ} (X : SemiPf k) (σ : Fin (atomsOf X).length → Sign) : Basic k X.r :=
  ⟨cellEqs X σ, cellPos X σ⟩

/-- The sign cell of a sign assignment, as a `SemiPf` set (a single disjunct). -/
def cellSemiPf {k : ℕ} (X : SemiPf k) (σ : Fin (atomsOf X).length → Sign) : SemiPf k :=
  ⟨X.r, X.c, [cell X σ]⟩

/-- The `SemiPf` set consisting of a single basic set `C` (over the chain of `X`); this is the
ambient set of one sign cell in the assembly. -/
def cellSemi {k : ℕ} (X : SemiPf k) (C : Basic k X.r) : SemiPf k := ⟨X.r, X.c, [C]⟩

/-- The cells used for the assembly: nonempty and contained in `X.set`. -/
def goodCells {k : ℕ} (X : SemiPf k) : List (Fin (atomsOf X).length → Sign) :=
  (allSigns X).filter fun σ => (cellSemiPf X σ).set.Nonempty ∧ (cellSemiPf X σ).set ⊆ X.set

end Work.WilE5
