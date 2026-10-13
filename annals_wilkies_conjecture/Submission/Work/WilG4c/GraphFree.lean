/-
  WilG4c / `GraphFree` — the "no bad sheet over a fat set of parameters" crux.

  ## Status, and what has been *established* about possible decompositions

  Target: a continuous graph `w ↦ (w, γ w)` over a nonempty open `O ⊆ W`, with values in the open
  `U` on which all slices `y ↦ g w y` (`w ∈ W`) are `C¹`, cannot lie in the joint non-`C¹` locus
  of `famFun g` (a definable family).

  The statement is TRUE — four independent reviewers of the verbatim duplicate
  `Work.WilkG4c.CruxGraphFree` agreed, and every attempted construction contradicts `hsm` — but it
  is the area's hard crux.  The §5.3/§5.5 dispatch that used to need it has since been reorganised
  to avoid it (`WilkG4c/StepLipHighSession20_Notes.md` §2: use `SliceLipDeformC1` and the
  discontinuity projection instead), so `GraphFree` is currently only wanted for the alternative
  route `smooth_k_cover` + `DefinableSection` (see `WilkG4c/C1AllComplThinSlices.lean`).

  ### Routes that are REFUTED — do not retry

  1. *Fibre-openness*: "`(w₀,y₀) ∈ Z` with `w₀ ∈ W`, `y₀ ∈ U` implies `{w₀} × B(y₀,δ) ⊆ Z`" is
     FALSE.  Counterexample (found in review; also recorded in `WilkG4c/CruxGraphFree.lean`):
     `g w y = w²/(w²+y²)`, `m = N = 1`, `W = U = ℝ`.  Every slice is `C^∞` on `U`; `famFun g` is
     discontinuous at `(0,0)` (along the axis `y = 0` it tends to `1` while `g 0 0 = 0`); yet it is
     smooth, hence `C¹`, at `(0,y)` for every `y ≠ 0`.  So the bad fibre over `0` is `{0}`, not a
     ball, and `AlBadParThin` (fibre-thinness) cannot be fed through fibre-openness.

  2. *"A bad cell meeting `W × U` has a single-point parameter-projection"*: FALSE for `m ≥ 2`.
     For `g w y = |w 0 - w 1| + y`, `W = (0,1) × ℝ`, `U = ℝ`, the cell `{w 0 = w 1 ∈ (0,1)}`
     (with the full `y`-band over it) is entirely bad, meets `W × U`, and projects onto the
     diagonal segment.  Likewise `g w y = |w 1|`, `κ = {z 1 = 0}` (parameter-only badness).

  3. *"A bad cell meeting `W × U` has nowhere-dense parameter-projection"*: correct, but an
     independent reviewer verified it is *equivalent* to `GraphFree` (it is non-vacuous exactly
     when a bad sheet over a fat parameter set exists).  So it is not an independent saving and
     must not be delegated as if it were.

  In short: `GraphFree` is atomic.  Two facts that *are* available and provable in the workspace
  and that a future proof should use: the `Ω`-definability of the joint `C¹`-locus — the `P = 0`
  case of the proved `SliceC1_mem_m` machinery, stated as `JointC1LocMem` in
  `WilkG4c/JointC1LocMem.lean` — which turns the finite cover of `smooth_k_cover` into a cover by
  *cells* of the bad locus; and *slice rigidity*
  (`WilkG4c/CruxGraphFree.lean`, `not_mem_fibBad_fibre_dir`, proved), which excludes the
  fibre-direction pieces of that cover.

  ### Proved here

  * `famFun_append` — reading `famFun` at a glued point (used to relate `hgraph` to `g`).
  * `graphFree_zero_fibre` — the case `N = 0` (proved below): the appended point is the parameter
    itself, so `hgraph` puts all of `O` inside the joint non-`C¹` locus, contradicting
    `FamFunComplContDiffAt`.  Hence the crux has content only for `N ≥ 1`.

  ### The piece decomposition of the crux, and its current state

  Following `WilkG4c/NoSheetFibBad.lean` and `WilkG4c/NoSheetJunkDisc.lean` the crux is decomposed
  along the `smooth_k_cover` pieces of the bad locus, i.e. one must show for each piece that no
  sheet lies in its closure:

  | piece | statement | state |
  |---|---|---|
  | `fibBad (famFun f) j`, `j` a *fibre* direction | `Work.WilkG4c.not_mem_fibBad_fibre_dir`, `closure_fibBad_fibre_dir_avoid` | PROVED (`WilkG4c/CruxGraphFree.lean`, `WilkG4c/NoSheetFibBad.lean`) |
  | `fibBad (famFun f) (castAdd N i)`, *parameter* direction | `Work.WilG4c.NoSheetFibBadParam` | delegated; the hard piece, still open (this file's `GraphFree` is exactly this difficulty) |
  | `disc (junkIt (famFun f) w)`, `w` a list of *fibre* directions, `|w| ≤ 1` | `Work.WilG4c.ProjDiscThinBoxR` + `Work.WilG4c.JunkItSlicesContFibre` | BOTH PROVED (this session) |
  | `disc (junkIt (famFun f) w)`, `w` containing a *parameter* direction | — | **open**: the naive `G2` statement is FALSE (review counterexample: `f w y = w·y/(w²+y²)` has `C¹` slices but the parameter-direction junk partial at `w' = 0` has the slice `y ↦ 1/y`, unbounded on any open `U₀ ∋ 0`), so `WilkG4c/NoSheetJunkDisc.lean`'s `JunkItSlicesCont` needs its parameter-direction case handled by a different argument; do not delete that hypothesis blindly |

  The final assembly (cover of `{¬ C¹}` by the finitely many closures from
  `Work.WilG1.Cell.smooth_k_cover` with `k = 1`, the per-piece no-sheet statements, and the Baire
  step `O ⊆ ⋃_κ proj(κ)` with `Work.WilG4c.PB2Aux.projM_isCell`) is *not* yet written anywhere; it
  needs the two open rows above.
-/
import Mathlib
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.Wilkies.Defs
import Submission.Work.Wilkies.Holes
import Submission.Work.WilG1.Cell.smooth_k_cover
import Submission.Work.WilG4c.BadLocusThin

set_option autoImplicit false

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- Reading `famFun` at a glued point recovers the family member. -/
theorem famFun_append {m N : ℕ} (f : (Fin m → ℝ) → (Fin N → ℝ) → ℝ)
    (w : Fin m → ℝ) (y : Fin N → ℝ) :
    Work.WilG4c.famFun f (Fin.append w y) = f w y := by
  simp only [Work.WilG4c.famFun, Fin.append_left, Fin.append_right]

/-- For the zero-width fibre the appended point is the parameter block itself. -/
theorem append_eq_of_zero {m : ℕ} (w : Fin m → ℝ) (γ : Fin 0 → ℝ) :
    Fin.append w γ = fun i : Fin (m + 0) => w i := by
  funext i
  have hi : (i : ℕ) < m := by simp
  simp only [Fin.append, Fin.addCases, dif_pos hi]
  congr 1

/-- The `N = 0` case of the crux: the appended point is the parameter, so the joint non-`C¹` locus
contains the whole open set `O`, contradicting `FamFunComplContDiffAt`. -/
theorem graphFree_zero_fibre (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (m F0 D : ℕ)
    (g : (Fin m → ℝ) → (Fin 0 → ℝ) → ℝ)
    (hg : WilkiesDesign.CG.famGraph g ∈ S.Ω F0 D (m + 0 + 1))
    (W : Set (Fin m → ℝ)) (hW : IsOpen W)
    (U : Set (Fin 0 → ℝ)) (hU : IsOpen U)
    (hsm : ∀ w ∈ W, ContDiffOn ℝ 1 (g w) U)
    (O : Set (Fin m → ℝ)) (hO : IsOpen O) (hOne : O.Nonempty) (hOW : O ⊆ W)
    (γ : (Fin m → ℝ) → (Fin 0 → ℝ)) (hγcont : ContinuousOn γ O) (hγU : ∀ w ∈ O, γ w ∈ U)
    (hgraph : ∀ w ∈ O, ¬ ContDiffAt ℝ 1 (Work.WilG4c.famFun g) (Fin.append w (γ w))) :
    False := by
  have hsub : O ⊆ {z : Fin (m + 0) → ℝ | ¬ ContDiffAt ℝ 1 (Work.WilG4c.famFun g) z} := by
    intro w hw
    have h := hgraph w hw
    rwa [append_eq_of_zero w (γ w)] at h
  obtain ⟨w, hw⟩ := hOne
  rw [← hO.interior_eq] at hw
  have hmem : w ∈ interior {z : Fin (m + 0) → ℝ | ¬ ContDiffAt ℝ 1 (Work.WilG4c.famFun g) z} :=
    interior_mono hsub hw
  have hempty : interior {z : Fin (m + 0) → ℝ | ¬ ContDiffAt ℝ 1 (Work.WilG4c.famFun g) z} = ∅ :=
    Work.WilkG4c.FamFunComplContDiffAt (S := S) hcd (m := 1) hg
  rw [hempty] at hmem
  exact hmem

/-- No graph of a continuous function `γ : O → U` over a nonempty open `O ⊆ W` can lie
entirely in the joint non-`C¹` locus of `famFun g`, when all slices `y ↦ g w y` are `C¹` on
the open set `U` for `w ∈ W`.  (`ContDiffAt ℝ 1` asks for differentiability on a neighbourhood,
so the joint non-`C¹` locus is the closed `badLoc g 1 = (cLoc g 1)ᶜ`, of empty interior.)  This
is the "no bad sheet over a fat set of parameters" fact behind the parameter-projection
thinness; e.g. `g w y = |w|·w·y/(w²+y²)` has its bad locus a single point and `g w y = |w| * h y`
has a bad locus of shape `{0} × {h ≠ 0}`, but no graph over an open set. -/
theorem GraphFree (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (m N F0 D : ℕ)
    (g : (Fin m → ℝ) → (Fin N → ℝ) → ℝ)
    (hg : WilkiesDesign.CG.famGraph g ∈ S.Ω F0 D (m + N + 1))
    (W : Set (Fin m → ℝ)) (hW : IsOpen W)
    (U : Set (Fin N → ℝ)) (hU : IsOpen U)
    (hsm : ∀ w ∈ W, ContDiffOn ℝ 1 (g w) U)
    (O : Set (Fin m → ℝ)) (hO : IsOpen O) (hOne : O.Nonempty) (hOW : O ⊆ W)
    (γ : (Fin m → ℝ) → (Fin N → ℝ)) (hγcont : ContinuousOn γ O) (hγU : ∀ w ∈ O, γ w ∈ U)
    (hgraph : ∀ w ∈ O, ¬ ContDiffAt ℝ 1 (Work.WilG4c.famFun g) (Fin.append w (γ w))) :
    False := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact graphFree_zero_fibre S hcd m F0 D g hg W hW U hU hsm O hO hOne hOW γ hγcont hγU hgraph
  · sorry

end Work.WilG4c
