import Submission.Work.BoxShrink.PinchOff.CollarPair
import Submission.Work.BoxShrink.PinchOff.winding_mem_of_split

/-!
# The finger move, as an explicit re-routing of the loops

`CollarPair.lean` reduced the residual of the area to the existence, at every transverse
configuration, of a pair `(A, B)` of inessential sets covering the box region, containing the two
closed halves and meeting in a **path connected** interface `A ∩ B`.  The two-piece bound then
needs the alternating-partition datum of the pair (`PairingData.lean`), whose connectors are paths
inside the interface.

For the *original* loop the datum need not hold — a loop whose consecutive crossings with the
interface lie in different components of it cannot be split with connectors inside the interface.
What Pardon's finger move produces is a *re-routing* of the loop: a homotopy, inside the box, after
which the crossings pair up inside a component of the interface.  This module isolates that
statement as

  `FingerMove P A B` — every loop of `A ∪ B` is carried (by a homotopy, i.e. to a loop of `A ∪ B`
  with the same winding vector) to a loop which *does* admit the alternating partition, with the
  connectors inside `A ∩ B`.

It is the weakest form of the data the pinch needs, and the form in which the two-piece bound is
available without any general position of the loops: the winding of a re-routed loop lies in
`W A ⊔ W B` by the per-curve form of the union lemma (`winding_mem_of_split`, this directory).

* `windingSpan_union_le_sup_of_fingerMove` — the two-piece bound from the finger move;
* `windingSpan_Omega_eq_bot_of_fingerMove` — the sharp conclusion `W(Ω) = ⊥` at a connected
  interface carrying the finger move, with the two span conditions of `SpiderPinchData`;
* `SpiderFingerMove` and `dropCase_of_spiderFingerMove` — the residual of the area in this
  vocabulary (no `FiniteCrossing` is needed: the finger move supplies the splitting);
* `fingerMove_of_alternatingPartitionData`, `fingerMove_of_finiteCrossing_of_isPathConnected_inter`
  — the cases in which the finger move is a theorem (the loop needs no moving).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- **The finger move for a pair of pieces.**  Every loop of `A ∪ B` is re-routed — to a loop of
`A ∪ B` with the same winding vector — so that its image is entirely in `A`, entirely in `B`, or
splits into finitely many monochromatic arcs alternating between `A` and `B`, the endpoints of each
`A`-arc being joined *inside* `A ∩ B` (so that the connectors of the alternating-partition datum
exist inside the interface). -/
def FingerMove (P : Work.CoreTopology.ParamTorus) (A B : Set R3) : Prop :=
  ∀ γ : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ t ∈ A ∪ B) →
    ∃ γ' : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ' t ∈ A ∪ B) ∧
      Work.SurgeryInvariance.windingOf P γ' = Work.SurgeryInvariance.windingOf P γ ∧
      ((∀ t : ℝ, γ' t ∈ A) ∨ (∀ t : ℝ, γ' t ∈ B) ∨
        ∃ (k : ℕ) (_ : 0 < k) (s : ℕ → ℝ),
          s 0 ∈ Set.Ico 0 (2 * Real.pi) ∧ s (2 * k) = s 0 + 2 * Real.pi ∧
          (∀ i j, i ≤ 2 * k → j ≤ 2 * k → i < j → s i < s j) ∧
          (∀ j, j < k → ∀ t : ℝ, s (2 * j) ≤ t → t ≤ s (2 * j + 1) → γ' t ∈ A) ∧
          (∀ j, j < k → ∀ t : ℝ, s (2 * j + 1) ≤ t → t ≤ s (2 * j + 2) → γ' t ∈ B) ∧
          (∀ j, j < k → JoinedIn (A ∩ B) (γ' (s (2 * j))) (γ' (s (2 * j + 1)))))

/-- **The two-piece bound from the finger move.**  A re-routed loop has the same winding vector, and
the per-curve form of the union lemma (`winding_mem_of_split`) puts the winding vector of a loop
which *does* split into `W A ⊔ W B`. -/
theorem windingSpan_union_le_sup_of_fingerMove
    {P : Work.CoreTopology.ParamTorus} {A B : Set R3}
    (hAc : A ⊆ P.carrier) (hBc : B ⊆ P.carrier) (h : FingerMove P A B) :
    Work.SurgeryInvariance.WindingSpan P (A ∪ B) ≤
      Work.SurgeryInvariance.WindingSpan P A ⊔ Work.SurgeryInvariance.WindingSpan P B := by
  rw [Work.SurgeryInvariance.WindingSpan, Submodule.span_le]
  rintro v ⟨γ, hγ, rfl⟩
  obtain ⟨γ', -, hw, hsplit⟩ := h γ hγ
  have hmem := winding_mem_of_split hAc hBc γ' hsplit
  rwa [hw] at hmem

variable {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-- **The sharp conclusion `W(Ω) = ⊥` from the finger move at a connected interface with vanishing
half-spans.**  The pair is `(UpperSide ∪ N, LowerSide ∪ N)`; its intersection is `N`, which is path
connected and carries the connectors. -/
theorem windingSpan_Omega_eq_bot_of_fingerMove {N : Set R3}
    (hslice : Sigma ψ s c σ u ⊆ N) (hN : N ⊆ Omega ψ s c σ) (hconn : IsPathConnected N)
    (hUp : Work.SurgeryInvariance.WindingSpan (surface ψ) (UpperSide ψ s c σ u ∪ N) = ⊥)
    (hLo : Work.SurgeryInvariance.WindingSpan (surface ψ) (LowerSide ψ s c σ u ∪ N) = ⊥)
    (hfm : FingerMove (surface ψ) (UpperSide ψ s c σ u ∪ N) (LowerSide ψ s c σ u ∪ N)) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) = ⊥ := by
  have hpair := collarPair_of_spiderPinchData hslice hN hconn hUp hLo
  have hle := windingSpan_union_le_sup_of_fingerMove hpair.subset_carrier
    hpair.subset_carrier_right hfm
  rw [hpair.span_A, hpair.span_B, sup_bot_eq] at hle
  rw [hpair.cover] at hle
  exact le_bot_iff.mp hle

/-- **The residual of the area in the vocabulary of the finger move**: at every transverse
configuration there is a connected interface inside the box region, containing the slice, whose
addition to either closed half preserves the vanishing of the winding span, and for which the
finger move holds. -/
def SpiderFingerMove (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Prop :=
  ∃ N : Set R3, Sigma ψ s c σ u ⊆ N ∧ N ⊆ Omega ψ s c σ ∧ IsPathConnected N ∧
    Work.SurgeryInvariance.WindingSpan (surface ψ) (UpperSide ψ s c σ u ∪ N) = ⊥ ∧
    Work.SurgeryInvariance.WindingSpan (surface ψ) (LowerSide ψ s c σ u ∪ N) = ⊥ ∧
    FingerMove (surface ψ) (UpperSide ψ s c σ u ∪ N) (LowerSide ψ s c σ u ∪ N)

/-- **`DropCase` from the finger move.**  No general position of the loops is needed here: the
splitting of the loops is exactly what the finger move supplies. -/
theorem dropCase_of_spiderFingerMove
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → SpiderFingerMove ψ s c σ u) :
    DropCase := by
  intro ψ s c σ u hT _hTa _hS _hZ _hbot
  obtain ⟨N, hslice, hN, hconn, hUp, hLo, hfm⟩ := h ψ s c σ u hT
  have h0 := windingSpan_Omega_eq_bot_of_fingerMove hslice hN hconn hUp hLo hfm
  rw [h0, finrank_bot]
  omega

/-! ## The cases in which the finger move is a theorem -/

/-- **The finger move is automatic for a pair carrying the alternating-partition datum**: the loop
needs no moving (`γ' := γ`). -/
theorem fingerMove_of_alternatingPartitionData
    {P : Work.CoreTopology.ParamTorus} {A B : Set R3}
    (h : AlternatingPartitionData P A B) : FingerMove P A B := by
  intro γ hγ
  exact ⟨γ, hγ, rfl, h γ hγ⟩

/-- **The finger move from the crossing finiteness and a path connected interface**: the sign split
(`SignSplit.lean`) gives the datum for the pair, hence the finger move, with no re-routing. -/
theorem fingerMove_of_finiteCrossing_of_isPathConnected_inter
    {A B : Set R3} (hA : UpperSide ψ s c σ u ⊆ A) (hB : LowerSide ψ s c σ u ⊆ B)
    (hO : A ∪ B ⊆ Omega ψ s c σ) (hfin : FiniteCrossing ψ s c σ u)
    (hconn : IsPathConnected (A ∩ B)) :
    FingerMove (surface ψ) A B :=
  fingerMove_of_alternatingPartitionData (P := surface ψ)
    ((alternatingPartitionDataWeak_of_finite_crossing_of_subset hA hB hO hfin)
      |>.toData_of_isPathConnected_inter hconn)

/-- **The residual from the finger move in the case of a path connected slice** (`N := Σ`): this is
the already-delivered theorem `dropCase_of_finiteCrossing_of_isPathConnected_slice`, seen through
the finger-move reduction. -/
theorem spiderFingerMove_of_isPathConnected_sigma
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (hbot : Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) = ⊥)
    (hconn : IsPathConnected (Sigma ψ s c σ u)) (hfin : FiniteCrossing ψ s c σ u) :
    SpiderFingerMove ψ s c σ u := by
  refine ⟨Sigma ψ s c σ u, Subset.rfl, Sigma_subset_Omega, hconn, ?_, ?_, ?_⟩
  · rw [Set.union_eq_left.mpr sigma_subset_upperSide]
    exact windingSpan_upperSide_eq_bot_of_transverseSlice hT hbot
  · rw [Set.union_eq_left.mpr sigma_subset_lowerSide]
    exact windingSpan_lowerSide_eq_bot_of_transverseSlice hT hbot
  · rw [Set.union_eq_left.mpr sigma_subset_upperSide,
      Set.union_eq_left.mpr sigma_subset_lowerSide]
    refine fingerMove_of_finiteCrossing_of_isPathConnected_inter (A := UpperSide ψ s c σ u)
      (B := LowerSide ψ s c σ u) Subset.rfl Subset.rfl ?_ hfin ?_
    · intro x hx
      rw [Omega_eq_upperSide_union_lowerSide]
      exact hx
    · rw [upperSide_inter_lowerSide]; exact hconn

end

end Work.BoxShrink.PinchOff
