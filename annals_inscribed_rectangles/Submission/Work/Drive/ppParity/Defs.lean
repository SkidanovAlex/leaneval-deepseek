import Mathlib
import Submission.Work.Drive.ChartBridge
import Submission.Work.Drive.pairMeetDefs
import Submission.Work.Drive.transportThreeLevel

/-!
# The intrinsic pair map `ppDiff` and its regularity predicate `PPRegAt`

This is the **S1 definition file** of the lead's residency plan
(`Submission/Work/Drive/NOTES_LEAD_residency.md`): the chart-residency-free formulation of the pair
map of the transport, in which the two chart blocks are *self-centred* and only the pointwise
membership `x ∈ (chr p).source` (free at `p` itself) is ever used.

Written by the `chainParity` agent (S3 dependency), so that S2/S3 can be stated on top of it.

* `Work.Drive.ppMeet E E' V W` — the pair-meet set in the `9`-box: `x ∈ unitBox 8`,
  `E (ftS x) (ftU x) = V (ftY x)` and `E' (ftS x) (ftU x) = W (ftZ x)`.  Chart-free.
* `Work.Drive.ppRegion p p' E E' V W` — the chart-residency region of the pair map for the chart pair
  `(p, p')`: all four values lie in the two charts' sources.
* `Work.Drive.ppDiff p p' E E' V W` — the charted pair difference map, the pair analogue of
  `Work.Drive.pairDiff2` with the chart `chr p` on the `(E, V)` block and `chr p'` on the `(E', W)`
  block.
* `Work.Drive.PPRegAt E E' V W x` — **the regularity predicate at a meet** `x`, with the
  *self-centred* charts `chr (E (ftS x) (ftU x))`, `chr (E' (ftS x) (ftU x))`: the `x`-derivative of
  the pair map is onto, and (on the box boundary, where all four values coincide with both chart
  centres) every boundary meet lies on exactly one face coordinate with the tangential derivative
  onto that face.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-- **The pair-meet set in the `9`-box.**  The two equalities are the meets of the two plane chains
with the two sweep chains at the *same* family parameter `ftS x` and the *same* plane parameter
`ftU x` — the shape of the transport's collapse count. -/
def ppMeet (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (V W : EuclideanSpace ℝ (Fin 3) → M) : Set (EuclideanSpace ℝ (Fin 9)) :=
  {x | x ∈ Submission.Drive.unitBox 8 ∧ E (ftS x) (ftU x) = V (ftY x) ∧
    E' (ftS x) (ftU x) = W (ftZ x)}

lemma mem_ppMeet {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    {V W : EuclideanSpace ℝ (Fin 3) → M} {x : EuclideanSpace ℝ (Fin 9)} :
    x ∈ ppMeet E E' V W ↔ x ∈ Submission.Drive.unitBox 8 ∧ E (ftS x) (ftU x) = V (ftY x) ∧
      E' (ftS x) (ftU x) = W (ftZ x) := Iff.rfl

/-- **The chart-residency region of the pair map** for the chart pair `(p, p')`. -/
def ppRegion (p p' : M) (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (V W : EuclideanSpace ℝ (Fin 3) → M) : Set (EuclideanSpace ℝ (Fin 9)) :=
  {x | E (ftS x) (ftU x) ∈ (chr p).source ∧ V (ftY x) ∈ (chr p).source ∧
    E' (ftS x) (ftU x) ∈ (chr p').source ∧ W (ftZ x) ∈ (chr p').source}

/-- **The charted pair difference map** with the chart `chr p` on the `(E, V)` block and `chr p'` on
the `(E', W)` block. -/
def ppDiff (p p' : M) (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (V W : EuclideanSpace ℝ (Fin 3) → M) : EuclideanSpace ℝ (Fin 9) → Tgt 8 :=
  fun x => pair44 (chr p (E (ftS x) (ftU x)) - chr p (V (ftY x)))
    (chr p' (E' (ftS x) (ftU x)) - chr p' (W (ftZ x)))

/-- **The intrinsic regularity of the pair map at a meet `x`**, with the *self-centred* charts at the
two values.  Both chart memberships are `mem_chart_source`, so this is a condition on the family
alone. -/
def PPRegAt (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (V W : EuclideanSpace ℝ (Fin 3) → M) (x : EuclideanSpace ℝ (Fin 9)) : Prop :=
  Function.Surjective
      (fderiv ℝ (ppDiff (E (ftS x) (ftU x)) (E' (ftS x) (ftU x)) E E' V W) x) ∧
    (x ∈ Submission.Drive.unitBoxBdry 8 →
      ∃ i : Fin 9, (x i = 0 ∨ x i = 1) ∧ (∀ j : Fin 9, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
        Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
          fderiv ℝ (ppDiff (E (ftS x) (ftU x)) (E' (ftS x) (ftU x)) E E' V W) x v.1))

/-- The self-centred chart pair of a meet. -/
lemma ppDiff_self (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (V W : EuclideanSpace ℝ (Fin 3) → M) (x : EuclideanSpace ℝ (Fin 9)) :
    ppDiff (E (ftS x) (ftU x)) (E' (ftS x) (ftU x)) E E' V W
      = ppDiff (E (ftS x) (ftU x)) (E' (ftS x) (ftU x)) E E' V W := rfl

/-- At a meet, the second and fourth values of the self-centred chart pair coincide with the first and
third: that is what makes the chart transition of the pair map *block diagonal*. -/
lemma ppMeet_values_eq {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    {V W : EuclideanSpace ℝ (Fin 3) → M} {x : EuclideanSpace ℝ (Fin 9)}
    (hx : x ∈ ppMeet E E' V W) :
    V (ftY x) = E (ftS x) (ftU x) ∧ W (ftZ x) = E' (ftS x) (ftU x) :=
  ⟨hx.2.1.symm, hx.2.2.symm⟩

/-- The two chart centres of a meet are `mem_chart_source` members of their own charts. -/
lemma ppMeet_mem_chart_source {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    {V W : EuclideanSpace ℝ (Fin 3) → M} {x : EuclideanSpace ℝ (Fin 9)}
    (hx : x ∈ ppMeet E E' V W) :
    E (ftS x) (ftU x) ∈ (chr (E (ftS x) (ftU x))).source ∧
      E' (ftS x) (ftU x) ∈ (chr (E' (ftS x) (ftU x))).source :=
  ⟨mem_chart_source _ _, mem_chart_source _ _⟩

end

end Work.Drive
