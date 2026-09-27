import Mathlib
import Submission.Work.Drive.classTripleRegular
import Submission.Work.Drive.odd_sum_topBdryMeet_clampedSweep

/-!
# The ends clause, in the stable (parity) form: `Odd N`, no collision data

**This file is the statement-only record of the ends clause assigned by the project lead (message of
07:15, correction 2 of the design): the end contribution of the triple count is to be stated as
`Odd N` for every `ClassTripleRegular` triple, *not* as `N = 1` from the collision data
(`hy`/`huniq`, which are unstable — they force the three class images to have a *single* common class,
a non-generic situation).**

## Why the parity is the stable form, and what it needs

For the three radial sweeps `D k = clampedSweep (c k) ψ (P k)` the engine
(`Work.Drive.even_sum_topBdryMeet_add_bottomBdryMeet_clamped_of_planes`) gives
`Σ k (top k + bottom k)` even, so the Lemma 4 identity `Σ k top k` odd is *equivalent* to
`Σ k bottom k` odd.  The ends are therefore a genuine input (the paper's `n_{-λ}` odd, i.e. the cube
`x³ ≠ 0` of `H^*(ℝP³; ℤ/2) = ℤ/2[x]/(x⁴)`), and this is where the "real ends mathematics" sits.

The bottom meets have a concrete description, *in the clamping direction* (this corrects a first draft
of this file: the operative block is the one with the **maximal** clamp level, not the one minimising
`planeLevel`).  At `x k 2 = 0` the `k`-th sweep sits at its **clamp level** `c k`
(`Work.Drive.levelOf_clampedSweep_eq_bottom_iff`), while every other block's level is `≥ c j`.  Since
`c 0` is the strict maximum (`hck`, `hc1`, `hc2`), only the block `k = 0` can occur on its bottom face
(`Work.Drive.bottomBdryMeet_eq_empty_of_lt_level`), and the map

> `y ↦ (y 0, 0 ; y 1, t1 ; y 2, t2)`,  `t j` the unique interior radial parameter of level `c 0`,

is a bijection from `classTripleSet P` onto the bottom triple intersection of block `0` (surjectivity:
the three classes agree at any bottom triple point; injectivity: the level pins the radial parameters).
Hence

> `Σ k bottom k = (classTripleSet P).ncard`

(`hlev` and the strict monotonicity of the cutoff supply the interior parameters, and `hface` is what
keeps the class coordinates interior).  So the ends clause reduces to the parity of the number of
*class triples*, and *that* is the mod-2 degree statement of the paper.

**Note for whoever proves `hodd`.**  Essentiality is *not* implied by `ClassTripleRegular` and cannot be
dropped: if each class image bounds a `3`-chain in `ℝP³` (is inessential) then
`#(Y 0 ∩ Y 1 ∩ Y 2) ≡ 0`, so the parity conclusion is false.  The parity input to be proved elsewhere
is therefore `Odd (classTripleSet P).ncard` *together with* the essentiality of the three class maps
(e.g. in the form "the class map of `P k` is homotopic, through class maps satisfying the seam
condition, to a linear projective plane", which also supplies the bordism for the invariance argument);
for the design's planes this is inherited from the chart (`IsPlaneChart`'s strip clause) and preserved by
`linCapping`.
-/

set_option autoImplicit false
noncomputable section

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

/-- **The class-triple set of a triple of plane presentations**: the triples of *class coordinates*
`y k` at which the three class maps agree.  Its `ncard` is the mod-2 degree input of the ends clause
(`Σ k bottom k ≡ #(classTripleSet P)` under the genericity hypothesis `hmin` below). -/
def classTripleSet (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) :
    Set (Fin 3 → EuclideanSpace ℝ (Fin 2)) :=
  {y | (∀ k, y k ∈ Submission.Drive.unitBox 1) ∧
    (∀ k, planeClassMap (P k) (y k) = planeClassMap (P 0) (y 0))}

/-- The same, restricted to the *open* square (the class coordinates of a triple point of the sweeps
are interior: `Work.Drive.class_coords_mem_Ioo_of_hface`). -/
def classTripleSetIoo (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) :
    Set (Fin 3 → EuclideanSpace ℝ (Fin 2)) :=
  {y | (∀ k, openSquare (y k)) ∧
    (∀ k, planeClassMap (P k) (y k) = planeClassMap (P 0) (y 0))}

/-- The level of the `k`-th plane at a class coordinate. -/
def planeLevel (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (y : Fin 3 → EuclideanSpace ℝ (Fin 2)) (k : Fin 3) : ℝ := levelOf (P k (y k))

lemma mem_classTripleSet {P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace}
    {y : Fin 3 → EuclideanSpace ℝ (Fin 2)} :
    y ∈ classTripleSet P ↔ (∀ k, y k ∈ Submission.Drive.unitBox 1) ∧
      (∀ k, planeClassMap (P k) (y k) = planeClassMap (P 0) (y 0)) := Iff.rfl

lemma mem_classTripleSetIoo {P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace}
    {y : Fin 3 → EuclideanSpace ℝ (Fin 2)} :
    y ∈ classTripleSetIoo P ↔ (∀ k, openSquare (y k)) ∧
      (∀ k, planeClassMap (P k) (y k) = planeClassMap (P 0) (y 0)) := Iff.rfl

end Work.Drive
