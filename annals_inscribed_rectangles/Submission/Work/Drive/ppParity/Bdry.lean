import Mathlib
import Submission.Work.Drive.ppParity.Defs

/-!
# S2 of the lead's residency plan: the parity of the pair-meet boundary count

`Submission/Work/Drive/NOTES_LEAD_residency.md` (2026-09-26 04:15) replaces the unprovable chart
residency `hresQ`/`hresV`/`hresW` of the transport by **self-centred** charts: every chart membership
becomes `mem_chart_source` at the value itself.  S1 (`ppParity/Defs.lean`) has the vocabulary
(`ppMeet`, `ppRegion`, `ppDiff`, `PPRegAt`); this file states **S2**, the pair analogue of
`Work.Drive.even_ncard_pairMeetBdry` in which the regularity hypothesis is the *intrinsic* predicate
`PPRegAt`:

> `Work.Drive.even_ncard_ppMeetBdry` — if the four chains are smooth, and at every pair meet the
> self-centred charted pair map has surjective `x`-derivative (and, on the boundary of the `9`-box,
> the face clause), then the meets on the boundary of the `9`-box are **finite and even in number**.

The mathematical content is the standard statement "a compact `1`-manifold with boundary has an even
number of boundary points", applied to the pair-meet set `ppMeet` (a `1`-manifold by the implicit
function theorem from `hreg`, with boundary exactly the meets on the box boundary by the face clause).

The proof is the `TParity/` port the lead prescribes: the pair analogue of
`Work.Drive.TParity.bK3_even` (`Submission/Work/Drive/TParity/Assembly.lean`), with `region3` /
`chartDiff3` replaced by `ppRegion` / `ppDiff`, and the only genuinely new step being the
chart-independence of the surjectivity and of the kernel at a meet (the pair analogue of
`Work.Drive.TParity.chartDiff3_tan3_surjective_iff`), which is what makes `PPRegAt` a condition on the
family and not on the chart pair.

The consumer is S4 (`even_colCount_add2_intrinsic`): the boundary meets split into the two family
faces `s = 0, 1` (the counts `K 0`, `K 1`), the `u`-seam faces, the `y`/`z`-seam faces and the two
level faces; the seams pair up by `hseamU`/`hseamU'`/`hseamV`/`hseamW`, the level faces are empty by
the avoidances, and the parity of the whole gives `Even (K 0 + K 1)`.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {M : Type*}

/-- **The pair meets on the boundary of the `9`-box.**  These are the boundary points of the
`1`-manifold `ppMeet`. -/
def ppMeetBdry (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (V W : EuclideanSpace ℝ (Fin 3) → M) : Set (EuclideanSpace ℝ (Fin 9)) :=
  {x | x ∈ ppMeet E E' V W ∧ x ∈ Submission.Drive.unitBoxBdry 8}

/-- **The pair meets at a fixed family parameter** `s` (the count `K s` of the transport). -/
def ppMeetEnd (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (V W : EuclideanSpace ℝ (Fin 3) → M) (s : ℝ) : Set (EuclideanSpace ℝ (Fin 9)) :=
  {x | x ∈ ppMeet E E' V W ∧ ftS x = s}

lemma mem_ppMeetBdry {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    {V W : EuclideanSpace ℝ (Fin 3) → M} {x : EuclideanSpace ℝ (Fin 9)} :
    x ∈ ppMeetBdry E E' V W ↔ x ∈ ppMeet E E' V W ∧ x ∈ Submission.Drive.unitBoxBdry 8 :=
  Iff.rfl

lemma mem_ppMeetEnd {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    {V W : EuclideanSpace ℝ (Fin 3) → M} {s : ℝ} {x : EuclideanSpace ℝ (Fin 9)} :
    x ∈ ppMeetEnd E E' V W s ↔ x ∈ ppMeet E E' V W ∧ ftS x = s := Iff.rfl

variable [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-! ## S2: the statement, and where it is proved

The theorem itself is stated and proved in
`Submission/Work/Drive/even_ncard_ppMeetBdry.lean` (delegated), so that this file stays `sorry`-free
and can be imported by S3 (`exists_ppReg_shift`) and S4 (`even_colCount_add2_intrinsic`):

> `Work.Drive.even_ncard_ppMeetBdry` — for smooth chains, if the self-centred charted pair map
> `Work.Drive.ppDiff` has onto `x`-derivative at every pair meet (`Work.Drive.PPRegAt`, whose chart
> memberships are `mem_chart_source`), then `(ppMeetBdry E E' V W)` is finite and of even cardinality.

The mathematical content is *the boundary of a compact `1`-manifold with boundary is even*: `ppMeet`
is a `1`-manifold (the implicit function theorem at each of its points, in the chart pair centred
*there*), the box is compact, and by the face clause each boundary meet is a transverse crossing of
the box's boundary — hence the boundary points of `ppMeet` are exactly `ppMeetBdry`. -/

end

end Work.Drive
