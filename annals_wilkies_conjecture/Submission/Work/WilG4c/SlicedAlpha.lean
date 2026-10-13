/-
  WilG4c / `SlicedAlpha` — the *sliced* (fibre) version of the `CurveFamAlpha` selection set.

  `StepHigherPlan.md` §8 and §9 explain why the `γ`-choice of BNZ §5.4 must be made with the
  **fibre** `C^{|L|}`-locus (`SliceLocus`, `AlDgListSlice`) rather than the *joint* one
  (`AlLoc`, `AlDgList`): at degenerate parameters the joint locus can have an *empty* fibre,
  while the fibre locus is everything, and it is the fibre locus that carries the
  near-maximality needed for BNZ's transfer (eq. `Gamma-i-alpha-cond`).

  This file fixes the vocabulary only — `AlViolSlice` (the set of `w` beaten on the fibre) and
  `AlZsetPureSlice` (cube membership ∩ fibre locus ∩ not beaten), exactly the fibre analogues of
  `CurveFamAlphaDefs.AlViol` / `CurveFamAlpha_list_pure.AlZsetPure`.  The unfolding
  (`AlZsetPureSliceIff`), the `Ω`-membership (`AlZsetPureSliceMem`, from `AlDgListSliceMem`) and
  the definable choice (`CurveFamAlpha_list_pure_sliced`) are proved in the sibling files.
-/
import Mathlib
import Submission.Work.WilG4c.SlicedDerivDefs
import Submission.Work.WilG4c.CurveFamDefs
import Submission.Work.WilG4c.CurveFamAlphaDefs
import Submission.Work.WilG5.Basic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilG5

/-! ## 1. The violation set of the sliced near-maximality condition -/

/-- The ambient `(w | y' | s | s')` version of the violation set, built exactly like
`AlViol1` but with the *fibre* derivative graph `AlDgListSlice` in place of `AlDgList`.

It says: `(w, s)` is on the fibre derivative graph, `(zPt w y', s')` is on the fibre derivative
graph, `y' ∈ openCube n`, and `4 s² < s'²` (i.e. `2|s| < |s'|`): `w` is *beaten* on the fibre. -/
def AlViolSlice1 (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (n + 1))) : Set (Fin (p + (n + 1) + n + 2) → ℝ) :=
  coordPre (iwIdx p n) (AlDgListSlice p n f L) ∩
    coordPre (izIdx p n) (AlDgListSlice p n f L) ∩
    coordPre (icIdx p n) cmpSet ∩ coordPre (cubeIdx p n) (openCube n)

/-- The set of `w` of `ℝ^{p+(n+1)}` which are *beaten* on the fibre: some `y' ∈ openCube n`
with `zPt w y'` in the fibre `C^{|L|}`-locus has `2|∂^L(w)| < |∂^L(zPt w y')|`, where `∂^L`
is the *fibre* (slice) directional derivative. -/
def AlViolSlice (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (n + 1))) : Set (Fin (p + (n + 1)) → ℝ) :=
  projN (n + 2) (AlViolSlice1 p n f L)

/-! ## 2. The sliced pure selection set -/

/-- `AlZsetPureSlice p n f L`: the selection set of the *fibre* near-maximising curve choice —
the `w = (l,x,y)` with `y ∈ openCube n`, the *slice* `y' ↦ f l y'` being `C^{|L|}` at `w`, and
`w` not beaten on the fibre by any cube point of the same slice.  This is
`CurveFamAlpha_list_pure.AlZsetPure` with `AlLoc` (the joint locus) replaced by `SliceLocus`
(the fibre locus) and `AlViol` replaced by `AlViolSlice`. -/
def AlZsetPureSlice (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (n + 1))) : Set (Fin (p + (n + 1)) → ℝ) :=
  coordPre (yIdx p n) (openCube n) ∩ SliceLocus p n f L.length ∩ (AlViolSlice p n f L)ᶜ

@[simp] theorem mem_AlZsetPureSlice {p n : ℕ}
    {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ} {L : List (Fin (n + 1))}
    {w : Fin (p + (n + 1)) → ℝ} :
    w ∈ AlZsetPureSlice p n f L ↔ (fun j : Fin n => w (yIdx p n j)) ∈ openCube n ∧
      w ∈ SliceLocus p n f L.length ∧ w ∈ (AlViolSlice p n f L)ᶜ := by
  rw [AlZsetPureSlice]
  simp only [Set.mem_inter_iff, coordPre, SliceLocus, Set.mem_ofPred_eq, Function.comp_apply,
    Set.mem_compl_iff]
  tauto

end Work.WilkG4c
