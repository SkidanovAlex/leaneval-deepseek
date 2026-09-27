import Mathlib
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.rotSideCount
import Submission.Work.Drive.chartPert_rotCapping_comm

/-!
# The T6 factors of the design's triple *are* the germ counts (the settlement of §7)

`TRIPLE_IDENTITY_STATUS.md` §7 records the structural point that the consumption of the triple
machinery by the *germ* route needs: the multiplicativity T6 computes the factors of the `k`-th block
of the design's triple of `sweepChartFam`-chains — i.e. the counts

> `ε(P_j; chart k) = coreSideCount (Ξ (τ k) ∘ rotCapping (u k) ∘ Q) (cblk j) (Ξ (τ j) ∘ rotPresentation Q (u j))`

(the perturbation applied **after** the rotation) — whereas the germ's own count at the angle
`u j - u k` is

> `CntAt Ξ Q (cblk j) (u j - u k) (τ k, τ j)`

(the perturbation applied to the chart **before** the rotation).

**This file proves that the two agree**, from the single input that the chart perturbation commutes with
the rotations (`Work.Drive.chartPert_rotCapping_comm`, which both reviewers verified for the concrete
`chartPert`: `classMap τ` is *left* quaternion multiplication, `diagRot t` is *right* multiplication by
`circ t`, and left/right multiplications commute).  The proof is

1. the simultaneous rotation invariance of the count (`Work.Drive.coreSideCount_rotCapping`) with the
   rotation `−u k`, which turns the block-`k` chart `Ξ (τ k) ∘ rotCapping (u k) ∘ Q` into
   `Ξ (τ k) ∘ Q` and the block-`j` plane `Ξ (τ j) ∘ rotCapping (u j) ∘ Q` into
   `Ξ (τ j) ∘ rotCapping (u j − u k) ∘ Q`;
2. the commutation, to move `Ξ (τ j)` back to the outside.

The statement is *general* in the family `Ξ` (the commutation is a hypothesis), so the consumer
instantiates it at `Work.Drive.chartPert` with the delegated commutation lemma.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The T6 factor of the block `(k, j)` of the design's triple is the germ count at the angle
difference `u j − u k`.**  This is the identification that makes the multiplicativity T6 directly
consumable by `Work.Drive.hdense_identity_of_design_data` (and by the corresponding `hn2` assembly). -/
theorem coreSideCount_block_eq_CntAt {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (hcomm : ∀ (τ : EuclideanSpace ℝ (Fin m)) (w : UnitAddCircle) (p : CappingSpace),
      Ξ τ (rotCapping w p) = rotCapping w (Ξ τ p))
    (Q : ℂ → CappingSpace) (u : Fin 3 → UnitAddCircle)
    (τ : Fin 3 → EuclideanSpace ℝ (Fin m)) (cblk : Fin 3 → ℝ) (k j : Fin 3) :
    coreSideCount (fun z => Ξ (τ k) (rotCapping (u k) (Q z))) (cblk j)
        (fun y => Ξ (τ j) (rotPresentation Q (u j) y))
      = CntAt Ξ Q (cblk j) (u j - u k) (τ k, τ j) := by
  rw [coreSideCount_rotCapping (fun z => Ξ (τ k) (rotCapping (u k) (Q z))) (cblk j)
    (fun y => Ξ (τ j) (rotPresentation Q (u j) y)) (-u k)]
  simp only [CntAt, pertChart]
  congr 1
  · funext z
    show rotCapping (-u k) (Ξ (τ k) (rotCapping (u k) (Q z))) = Ξ (τ k) (Q z)
    rw [hcomm (τ k) (u k) (Q z)]
    simp only [rotCapping_apply_add, neg_add_cancel, rotCapping_zero, id_eq]
  · funext y
    show rotCapping (-u k) (Ξ (τ j) (rotCapping (u j) (diskPlane Q y)))
      = rotCapping (u j - u k) (Ξ (τ j) (diskPlane Q y))
    rw [hcomm (τ j) (u j) (diskPlane Q y), rotCapping_apply_add,
      show (-u k) + u j = u j - u k from by abel]

/-! ## The form for the concrete chart perturbation -/

/-- **The T6 factor of the block `(k,j)` is the germ count, for the concrete `Work.Drive.chartPert`.**
This is `coreSideCount_block_eq_CntAt` with the commutation discharged by the proved
`Work.Drive.chartPert_rotCapping_comm` (every element of `UnitAddCircle` is the class of a real, so the
real-indexed commutation covers the whole circle).  **This is the form the design consumes**: it turns
the multiplicativity T6 of the design's triple into an identity among the germ's own counts
`CntAt (Ξ := chartPert) Q (cblk j) (u j − u k) (τ k, τ j)`. -/
theorem coreSideCount_block_eq_CntAt_chartPert (Q : ℂ → CappingSpace)
    (u : Fin 3 → UnitAddCircle) (τ : Fin 3 → EuclideanSpace ℝ (Fin 4)) (cblk : Fin 3 → ℝ)
    (k j : Fin 3) :
    coreSideCount (fun z => chartPert (τ k) (rotCapping (u k) (Q z))) (cblk j)
        (fun y => chartPert (τ j) (rotPresentation Q (u j) y))
      = CntAt (fun t p => chartPert t p) Q (cblk j) (u j - u k) (τ k, τ j) := by
  refine coreSideCount_block_eq_CntAt (fun t p => chartPert t p) ?_ Q u τ cblk k j
  intro τ' w p
  obtain ⟨x, hx⟩ : ∃ x : ℝ, ((x : ℝ) : UnitAddCircle) = w := ⟨Quotient.out w, Quotient.out_eq w⟩
  rw [← hx]
  exact chartPert_rotCapping_comm x τ' p

end

end Work.Drive
