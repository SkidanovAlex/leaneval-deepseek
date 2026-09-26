import Submission.Work.BoxShrink.PinchOff.ClosedPairing
import Submission.Work.BoxShrink.PinchOff.alternatingPartitionData_of_finite_crossing_of_isPathConnected_slice

/-!
# The pinch when the slice is connected: the residual is one general-position statement

`alternatingPartitionData_of_finite_crossing_of_isPathConnected_slice` (delegated, proved in this
directory) gives the alternating-partition datum of `PairingData.lean` from two hypotheses on the
configuration: the slice `Σ` is path connected, and every loop of the box region that visits both
sides of the cutting plane meets `Σ` in finitely many parameters of a period.

Combined with `dropCase_of_alternatingPartitionData` (`ClosedPairing.lean`) this reduces the whole
remaining content of the area — `DropCase`, equivalently Pardon's `PinchNoJump` under the general
position of the cutting plane, equivalently `KeyTameClosed` — to those two hypotheses:

* **`FiniteCrossing`** — the general position of the *loops*: a loop of the box region that crosses
  the cutting plane does so finitely often.  This is the only place where the loops (rather than
  the surface) are asked to be in general position, and it replaces Pardon's count;
* **path connectedness of the slice** — a purely geometric condition on the configuration.  When
  the slice has several components the connectors of the datum are not automatically available;
  the rank of the box region's span is then bounded by the number of components of the slice, and
  a proof of `DropCase` for several components needs the *pairing* of the crossings within a
  component of the slice (Pardon's finger move), or the two-gate argument of
  `Work.PinchLemma3.ClosedDiscA.two_component_intersection`.

The module records the two named hypotheses and the reduction.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-- **The crossing finiteness of the pinch.**  Every loop of the box region which visits both sides
of the cutting plane meets the slice in finitely many parameters of one period.  This is the
general position of the loops of the box region with respect to the slice; it is the only place in
the reduction where the *loops* are constrained. -/
def FiniteCrossing (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Prop :=
  ∀ γ : Work.CoreTopology.ClosedCurve (surface ψ),
    (∀ t : ℝ, γ t ∈ Omega ψ s c σ) →
    (∃ t₁ : ℝ, γ t₁ ∉ UpperSide ψ s c σ u) →
    (∃ t₂ : ℝ, γ t₂ ∉ LowerSide ψ s c σ u) →
    {t : ℝ | t ∈ Set.Icc 0 (2 * Real.pi) ∧ γ t ∈ Sigma ψ s c σ u}.Finite

/-- **The datum when the slice is path connected and the crossings are finite** (the delegated
`alternatingPartitionData_of_finite_crossing_of_isPathConnected_slice`, in the names of this
module). -/
theorem alternatingPartitionData_of_finiteCrossing_of_isPathConnected_slice
    (hconn : IsPathConnected (Sigma ψ s c σ u))
    (hfin : FiniteCrossing ψ s c σ u) :
    AlternatingPartitionData (surface ψ) (UpperSide ψ s c σ u) (LowerSide ψ s c σ u) :=
  alternatingPartitionData_of_finite_crossing_of_isPathConnected_slice hconn hfin

/-- The same under `TransverseSlice`, in the form the reduction `DropCase` consumes. -/
theorem alternatingPartitionData_of_finiteCrossing_of_isPathConnected_slice_of_transverseSlice
    (_hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (hconn : IsPathConnected (Sigma ψ s c σ u))
    (hfin : FiniteCrossing ψ s c σ u) :
    AlternatingPartitionData (surface ψ) (UpperSide ψ s c σ u) (LowerSide ψ s c σ u) :=
  alternatingPartitionData_of_finiteCrossing_of_isPathConnected_slice hconn hfin

/-! ## The residual, from the crossing data -/

/-- **`DropCase` from the crossing data of the pinch**: if at every configuration of the area the
slice is path connected and the loops cross it finitely often, then the residual holds. -/
theorem dropCase_of_finiteCrossing_of_isPathConnected_slice
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u →
      IsPathConnected (Sigma ψ s c σ u) ∧ FiniteCrossing ψ s c σ u) :
    DropCase :=
  dropCase_of_alternatingPartitionData fun ψ s c σ u hT =>
    alternatingPartitionData_of_finiteCrossing_of_isPathConnected_slice_of_transverseSlice hT
      (h ψ s c σ u hT).1 (h ψ s c σ u hT).2

/-- The same, in the vocabulary of the honest residual `KeyTameClosed`. -/
theorem keyTameClosed_of_finiteCrossing_of_isPathConnected_slice
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u →
      IsPathConnected (Sigma ψ s c σ u) ∧ FiniteCrossing ψ s c σ u) :
    KeyTameClosed :=
  keyTameClosed_of_alternatingPartitionData fun ψ s c σ u hT =>
    alternatingPartitionData_of_finiteCrossing_of_isPathConnected_slice_of_transverseSlice hT
      (h ψ s c σ u hT).1 (h ψ s c σ u hT).2

/-- Pardon's Lemma 3 at the closed-tame configurations from the crossing data. -/
theorem bubbleHalf_of_finiteCrossing_of_isPathConnected_slice
    (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u →
      IsPathConnected (Sigma ψ s c σ u) ∧ FiniteCrossing ψ s c σ u) :
    ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → TameClosedSlice ψ s c σ u →
      ¬ (surface ψ).ContainsEssentialLoop (SphereTrace s c σ) →
      ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
      Work.BoxShrink.Bubble.BubbleHalf (surface ψ) s c σ u :=
  bubbleHalf_of_keyTameClosed hnice
    (keyTameClosed_of_finiteCrossing_of_isPathConnected_slice h)

end

end Work.BoxShrink.PinchOff
