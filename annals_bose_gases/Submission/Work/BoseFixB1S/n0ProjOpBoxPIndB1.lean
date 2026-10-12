import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.exclFunOpAux
import Submission.Work.BoseFixB1S.n0ProjOpOrthB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.n0ProjOpBoxPIndB1`

The subset idempotents `n0ProjOp volA A S` (`n0SpectralDefs`) of the FS box projections
`P_{B,i} = UBBInputs8.boxPInd volA A i` commute with the box projections, so the insertion of a
state into the slot `i` *inside* the idempotent can be pulled out:

    n0ProjOp S (P_{B,i} Φ) =ᵐ[·|abox N ℓ] (if i ∈ S then n0ProjOp S Φ else 0).

## Route

`n0ProjOp volA A S = n0Iter volA A (decide (· ∈ S)) (List.ofFn id)` (`n0SpectralDefs`), so the
pointwise identity on the analysis box is the composition of two already proved facts:

* `n0Iter_comm_boxPInd` (`n0ProjOpOrthB1`) — `P_{B,i}` commutes with the whole slot iteration,
  `n0Iter … (P_{B,i}Φ) = P_{B,i}(n0Iter … Φ)`, pointwise on `abox N ℓ`;
* `n0IterEigen` (`n0IterEigen`) — the eigen-property of the iteration,
  `P_{B,i}(n0ProjOp S Φ) = 1_S(i)·n0ProjOp S Φ`, pointwise on `abox N ℓ`.

Pointwise equality on the measurable box `abox N ℓ` gives a.e. equality for the restricted
measure (`MeasureTheory.ae_restrict_iff'`).  (Slot-`i`-inserted states are automatically
admissible: `GoodState` is preserved by `P_{B,i}`, but that is not even needed here — both
ingredients take `GoodState ℓ Φ` directly.)

This is the requested replacement of the development axiom `dev_n0ProjOpBoxPIndB1` of
`interPairFluctIdB1`.
-/

namespace Work.BoseFixB1S

open MeasureTheory
open scoped BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem n0ProjOpBoxPIndB1 {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (S : Finset (Fin N)) (i : Fin N) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦ : Work.BoseFixB1S.GoodState ℓ Φ) :
    (fun x => Work.BoseFixB1S.n0ProjOp volA A S
        (Work.UBBInputs8.boxPInd volA A i Φ) x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)]
      fun x => (if i ∈ S then Work.BoseFixB1S.n0ProjOp volA A S Φ x else 0) := by
  rw [Filter.EventuallyEq,
    MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
  filter_upwards with x hx
  have hcomm : Work.BoseFixB1S.n0Iter volA A (fun j : Fin N => decide (j ∈ S))
      (List.ofFn (fun j : Fin N => j)) (Work.UBBInputs8.boxPInd volA A i Φ) x
      = Work.UBBInputs8.boxPInd volA A i
          (Work.BoseFixB1S.n0Iter volA A (fun j : Fin N => decide (j ∈ S))
            (List.ofFn (fun j : Fin N => j)) Φ) x :=
    n0Iter_comm_boxPInd (Ψ := Φ) hℓ hvol hA hvolA hAc (fun j : Fin N => decide (j ∈ S)) i
      (List.ofFn (fun j : Fin N => j)) hΦ x hx
  have heig : Work.UBBInputs8.boxPInd volA A i
      (Work.BoseFixB1S.n0Iter volA A (fun j : Fin N => decide (j ∈ S))
        (List.ofFn (fun j : Fin N => j)) Φ) x
      = (if i ∈ S then Work.BoseFixB1S.n0Iter volA A (fun j : Fin N => decide (j ∈ S))
          (List.ofFn (fun j : Fin N => j)) Φ x else 0) :=
    n0IterEigen hℓ hvol hA hvolA hAc S hΦ i x hx
  show Work.BoseFixB1S.n0Iter volA A (fun j : Fin N => decide (j ∈ S))
      (List.ofFn (fun j : Fin N => j)) (Work.UBBInputs8.boxPInd volA A i Φ) x
    = (if i ∈ S then Work.BoseFixB1S.n0Iter volA A (fun j : Fin N => decide (j ∈ S))
        (List.ofFn (fun j : Fin N => j)) Φ x else 0)
  rw [hcomm]
  exact heig

end Work.BoseFixB1S
