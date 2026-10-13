/-
  WilG4c — vocabulary for the final clean-up step `StepClean` (BNZ §5.5, "reduction from
  derivatives bounded only where defined to the smooth case").

  A family member is a function `f : ℝ^p × ℝ^N → ℝ` (parameters first, then the fibre
  coordinates).  Reading it as a single function `famFun f` on `ℝ^{p+N}` lets us speak of its
  `C^m`-locus, of the *bad* loci `badLoc f m` (complements of the interiors of the `C^m`
  loci, which `SharpDeriv` makes `Ω`-bounded), and of the *good* locus `goodLoc f r`
  (the common `C^r`-locus where the `NormLeOneDef` bounds of `PYLipDef` apply).
-/
import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG5.Basic

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- A family member `f : ℝ^p → ℝ^N → ℝ` read as a function `ℝ^{p+N} → ℝ`
(parameters first, then the fibre coordinates). -/
def famFun {p N : ℕ} (f : (Fin p → ℝ) → (Fin N → ℝ) → ℝ) : (Fin (p + N) → ℝ) → ℝ :=
  fun z => f (fun i => z (Fin.castAdd N i)) (fun j => z (Fin.natAdd p j))

/-- The graph of `famFun f` is `famGraph f`. -/
theorem graphOf_famFun {p N : ℕ} (f : (Fin p → ℝ) → (Fin N → ℝ) → ℝ) :
    graphOf (famFun f) = famGraph f := rfl

/-- The interior of the `C^m`-locus of a family member on `ℝ^{p+N}`. -/
def cLoc {p N : ℕ} (f : (Fin p → ℝ) → (Fin N → ℝ) → ℝ) (m : ℕ) : Set (Fin (p + N) → ℝ) :=
  interior {z | ContDiffAt ℝ m (famFun f) z}

/-- The *bad* locus of a family member at order `m`: the complement of the interior of its
`C^m`-locus.  (`SharpDeriv` exhibits this as an `Ω`-set.) -/
def badLoc {p N : ℕ} (f : (Fin p → ℝ) → (Fin N → ℝ) → ℝ) (m : ℕ) : Set (Fin (p + N) → ℝ) :=
  (cLoc f m)ᶜ

/-- The *good* locus of a family member up to order `r`: the set on which it is `C^r`
(as an interior point).  Where `PYLipDef`'s `NormLeOneDef` gives its derivative bounds. -/
def goodLoc {p N : ℕ} (f : (Fin p → ℝ) → (Fin N → ℝ) → ℝ) (r : ℕ) : Set (Fin (p + N) → ℝ) :=
  ⋂ m : Fin (r + 1), cLoc f m

/-- The union of the bad loci of a whole family up to order `r`. -/
def badUnion {p N : ℕ} (k : ℕ) (F : Fin k → (Fin p → ℝ) → (Fin N → ℝ) → ℝ) (r : ℕ) :
    Set (Fin (p + N) → ℝ) :=
  ⋃ i : Fin k, ⋃ m : Fin (r + 1), badLoc (F i) (m : ℕ)

/-- The cube faces of the *fibre* coordinates `j : Fin N` inside `ℝ^{p+N}`: the hyperplanes
`z_{p+j} = 0` and `z_{p+j} = 1`.  Feeding them to `SharpCD` together with the bad loci makes
every cell of the resulting decomposition either entirely inside, or entirely outside, the
open cube `openCube N` in the fibre coordinates. -/
def fibreFace {p N : ℕ} (j : Fin N) (c : ℝ) : Set (Fin (p + N) → ℝ) :=
  {z | z (Fin.natAdd p j) = c}

/-- The set of points of `ℝ^{p+N}` whose fibre part lies in the open cube. -/
def inCubeSet (p N : ℕ) : Set (Fin (p + N) → ℝ) :=
  {z | (fun j : Fin N => z (Fin.natAdd p j)) ∈ openCube N}

/-- The fibre of a set over a parameter, as a set of fibre points. -/
def fibreOf {p N : ℕ} (Z : Set (Fin (p + N) → ℝ)) (l : Fin p → ℝ) : Set (Fin N → ℝ) :=
  {y | Fin.append l y ∈ Z}

end Work.WilG4c
