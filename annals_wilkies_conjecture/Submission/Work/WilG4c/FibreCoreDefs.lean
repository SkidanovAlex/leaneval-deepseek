/-
  WilG4c — the vocabulary of the *fibre* (slice) cores of a family member.

  The F-lemma of BNZ §5 only ever asks for the regularity of the *fibre* functions
  `z ↦ f l z` at a fixed parameter `l` (`ChartsOK` asks for `ContDiffOn` of `t ↦ F i l (φ l t)`).
  The non-`C¹` locus of such a fibre is covered by a finite, `l`-independent, list of sets:

  * `fibBad g i`            — the fibre of `g` in direction `i` is not differentiable;
  * `fibBad (junkP g i) i'` — same for the junk partial;
  * `disc (junkP g i)`      — the junk partial is discontinuous;
  * `disc g`                — `g` itself is discontinuous.

  This file freezes the bookkeeping: the index type `CoreIx N` of these four families and the
  two readings of it, `fibCore h` (in the fibre `ℝ^N`) and `jointCore f` (in `ℝ^{p+N}`, taking
  only *fibre* directions `Fin.natAdd p ·`).

  The crucial point is the *discontinuity* pieces: the joint set `disc (famFun f)` is **not**
  the right joint reading of `disc (f l ·)` — a function can be discontinuous at `(l,z)` while
  its fibre through `l` is continuous at `z` (e.g. `f l t = if l = 0 then 0 else 1`).  The
  correct joint reading is the *fibre-wise* discontinuity `fibDisc H`, in which the parameter
  is held fixed inside the `∃z'` quantifier of the `ε`-`δ` definition of discontinuity.
-/
import Mathlib
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG1.Cell.JunkDefs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilG1.Cell

/-- Index type of the fibre cores: the four families of `fibCore` / `jointCore`. -/
inductive CoreIx (N : ℕ) : Type
  | fbad (i : Fin N) : CoreIx N
  | fbadJ (i i' : Fin N) : CoreIx N
  | discJ (i : Fin N) : CoreIx N
  | disc0 : CoreIx N
  deriving DecidableEq, Fintype

/-- **Fibre-wise discontinuity** of a joint function `H : ℝ^{p+N} → ℝ`: the set of
`w = (l, z)` such that the *fibre* `z' ↦ H (l ⌢ z')` is discontinuous at `z`.  The parameter
part `l` of `w` is held fixed in the quantifier, so this is *not* the same as the restriction of
`disc H` to the fibre. -/
def fibDisc {p N : ℕ} (H : (Fin (p + N) → ℝ) → ℝ) : Set (Fin (p + N) → ℝ) :=
  {w | ¬ ContinuousAt
    (fun z : Fin N → ℝ => H (Fin.append (fun i : Fin p => w (Fin.castAdd N i)) z))
    (fun j : Fin N => w (Fin.natAdd p j))}

/-- The fibre cores of a function `h : ℝ^N → ℝ`. -/
def fibCore {N : ℕ} (h : (Fin N → ℝ) → ℝ) : CoreIx N → Set (Fin N → ℝ)
  | .fbad i => fibBad h i
  | .fbadJ i i' => fibBad (junkP h i) i'
  | .discJ i => disc (junkP h i)
  | .disc0 => disc h

/-- The joint cores of a family member `f`, taken in *fibre* directions only. -/
def jointCore {p N : ℕ} (f : (Fin p → ℝ) → (Fin N → ℝ) → ℝ) :
    CoreIx N → Set (Fin (p + N) → ℝ)
  | .fbad i => fibBad (famFun f) (Fin.natAdd p i)
  | .fbadJ i i' => fibBad (junkP (famFun f) (Fin.natAdd p i)) (Fin.natAdd p i')
  | .discJ i => fibDisc (junkP (famFun f) (Fin.natAdd p i))
  | .disc0 => fibDisc (famFun f)

/-- The **fibre-wise closure** of a subset of `ℝ^{p+N}`: `w = (l, z)` lies in it iff `z` lies in
the closure (in `ℝ^N`) of the fibre `Z_l`.  Written as a first-order formula with an explicit
`∀ε>0 ∃z'`, which is what makes it an `Ω`-set. -/
def fibrewiseClosure {p N : ℕ} (Z : Set (Fin (p + N) → ℝ)) : Set (Fin (p + N) → ℝ) :=
  {w | ∀ ε : ℝ, 0 < ε → ∃ z' : Fin N → ℝ,
    (∑ j : Fin N, (z' j - w (Fin.natAdd p j)) ^ 2) < ε ^ 2 ∧
    Fin.append (fun i : Fin p => w (Fin.castAdd N i)) z' ∈ Z}

end Work.WilG4c
