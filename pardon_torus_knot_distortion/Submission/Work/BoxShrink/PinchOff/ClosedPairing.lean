import Submission.Work.BoxShrink.PinchOff.PairingData
import Submission.Work.BoxShrink.PinchOff.windingSpan_union_le_sup_of_alternatingPartitionData

/-!
# The pinch from the alternating-partition datum: `DropCase` as one geometric statement

The residual of the area is `DropCase` (`Drop.lean`; equivalently the parent chapter's
`PinchNoJump` with the general position of the cutting plane, equivalently `KeyTameClosed`): at a
transverse, closed-tame configuration whose box sphere and slice carry no essential loop, the box
region is at most one-dimensional as soon as the two half-regions together carry nothing.

This module reduces it to the **alternating-partition datum of the two closed halves**
(`PairingData.lean`), and in fact proves the *sharp* conclusion `W(Ω) = ⊥`:

* `Omega_subset_carrier`, `upperSide_subset_carrier`, `lowerSide_subset_carrier` — the set algebra;
* `windingSpan_Omega_eq_bot_of_alternatingPartitionData` — under `TransverseSlice` the two closed
  halves realise exactly the winding vectors of the corresponding open halves
  (`windingSpan_closedHalfUp_eq_halfUp_holds`, `OneSided.lean`), so they are inessential in the
  pinch situation; the union lemma
  `windingSpan_union_le_sup_of_alternatingPartitionData` (delegated, proved) then gives
  `W(UpperSide ∪ LowerSide) ≤ ⊥`, i.e. `W(Ω) = ⊥` by `Omega_eq_upperSide_union_lowerSide`;
* `dropCase_of_alternatingPartitionData`, `keyTameClosed_of_alternatingPartitionData`,
  `bubbleHalf_of_alternatingPartitionData` — the residual and Pardon's Lemma 3 from the datum at
  every configuration;
* `alternatingPartitionData_of_oneSided` and `alternatingPartitionData_of_sigma_eq_empty` — the
  degenerate cases in which the datum is a theorem (a loop of the region lying on one side of the
  cutting plane, or an empty slice).

## What the datum is, geometrically

The pieces are the two *closed* halves `UpperSide = Ω ∩ {y (σ 2) ≥ c (σ 2) + u}` and
`LowerSide = Ω ∩ {y (σ 2) ≤ c (σ 2) + u}`; they cover `Ω` and meet in the slice `Σ`.  The datum
asks that every loop of `Ω` either stays on one side of the cutting plane, or splits at its
crossings with `Σ` into finitely many monochromatic arcs alternating between the two halves, the
endpoints of each upper arc (which lie in `Σ`) being joined by a path *inside* `Σ`.

This is exactly Pardon's **finger move**: the crossings of a loop with the trace can be cancelled by
an isotopy inside the box.  The datum is *automatic* when the slice is path connected and every
crossing loop meets it finitely often
(`alternatingPartitionData_of_finite_crossing_of_isPathConnected_slice`, delegated in this
directory), so the reduction of `DropCase` there costs only the finiteness of the crossings — the
general position of the *loops* rather than of the surface.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-! ## The set algebra of the two closed halves -/

/-- The box region is contained in the carrier. -/
theorem Omega_subset_carrier : Omega ψ s c σ ⊆ (surface ψ).carrier := fun _ hx => hx.1

/-- The upper side of the box region is contained in the carrier. -/
theorem upperSide_subset_carrier : UpperSide ψ s c σ u ⊆ (surface ψ).carrier :=
  fun _ hx => Omega_subset_carrier hx.1

/-- The lower side of the box region is contained in the carrier. -/
theorem lowerSide_subset_carrier : LowerSide ψ s c σ u ⊆ (surface ψ).carrier :=
  fun _ hx => Omega_subset_carrier hx.1

/-! ## The sharp conclusion from the datum -/

/-- **The box region is inessential from the alternating-partition datum.**

Under `TransverseSlice` the two closed halves carry the same winding vectors as the corresponding
open halves (`windingSpan_closedHalfUp_eq_halfUp_holds`,
`windingSpan_closedHalfDown_eq_halfDown_holds`), hence nothing as soon as the two half-regions
together carry nothing.  The union lemma for the datum then gives `W(Ω) = ⊥` — Pardon's conclusion,
not merely the dimension bound. -/
theorem windingSpan_Omega_eq_bot_of_alternatingPartitionData
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (h : AlternatingPartitionData (surface ψ) (UpperSide ψ s c σ u) (LowerSide ψ s c σ u))
    (hbot : Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) = ⊥) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) = ⊥ := by
  have hUp : Work.SurgeryInvariance.WindingSpan (surface ψ) (UpperSide ψ s c σ u) = ⊥ := by
    rw [upperSide_eq_closedHalfUp, windingSpan_closedHalfUp_eq_halfUp_holds hT]
    exact le_bot_iff.mp (le_trans (Work.SurgeryInvariance.WindingSpan_mono (surface ψ)
      (Set.subset_union_left : HalfUp ψ s c σ u ⊆ Halves ψ s c σ u)) (le_of_eq hbot))
  have hLo : Work.SurgeryInvariance.WindingSpan (surface ψ) (LowerSide ψ s c σ u) = ⊥ := by
    rw [lowerSide_eq_closedHalfDown, windingSpan_closedHalfDown_eq_halfDown_holds hT]
    exact le_bot_iff.mp (le_trans (Work.SurgeryInvariance.WindingSpan_mono (surface ψ)
      (Set.subset_union_right : HalfDown ψ s c σ u ⊆ Halves ψ s c σ u)) (le_of_eq hbot))
  have hle := windingSpan_union_le_sup_of_alternatingPartitionData
    (upperSide_subset_carrier (ψ := ψ) (s := s) (c := c) (σ := σ) (u := u))
    (lowerSide_subset_carrier (ψ := ψ) (s := s) (c := c) (σ := σ) (u := u)) h hUp hLo
  rw [hUp, hLo, sup_bot_eq] at hle
  rw [← Omega_eq_upperSide_union_lowerSide] at hle
  exact le_bot_iff.mp hle

/-- **The sharp conclusion and the dimension bound agree.**  At a configuration whose box-sphere
trace carries no essential loop and whose box level is nice, the box region's winding span is `⊥`
or `⊤` (Pardon's equation (1) at the box region, `pardonDichotomy_boxRegion`); hence
`finrank W(Ω) ≤ 1` — the conclusion of `DropCase` — is *equivalent* to the sharp `W(Ω) = ⊥`.
So the sharp form proved below loses nothing. -/
theorem finrank_Omega_le_one_iff_eq_bot
    (hnice : Work.Smooth.Morse.NiceLevel ψ (Work.BoxShrink.Pinch.boxLevel s c σ) 0)
    (hS : ¬ (surface ψ).ContainsEssentialLoop (SphereTrace s c σ)) :
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ)) ≤ 1 ↔
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) = ⊥ := by
  have hdich := pardonDichotomy_boxRegion (ψ := ψ) (s := s) (c := c) (σ := σ) hnice hS
  constructor
  · intro hfr
    rcases hdich with h | h
    · exact h
    · rw [h] at hfr
      have h2 : Module.finrank ℚ ↥(⊤ : Submodule ℚ (ℚ × ℚ)) = 2 := by
        rw [finrank_top, Module.finrank_prod]
        simp
      rw [h2] at hfr
      omega
  · intro h
    rw [h, finrank_bot]
    omega

/-! ## The residual, and Pardon's Lemma 3, from the datum -/

/-- **`DropCase` from the alternating-partition datum for the two closed halves.**

This is the reduction of the whole remaining content of the area (`Drop.lean`,
`keyTameClosed_iff_dropCase`) to the single geometric statement that the crossings of a loop of the
box region with the slice can be connected inside the slice. -/
theorem dropCase_of_alternatingPartitionData
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u →
      AlternatingPartitionData (surface ψ) (UpperSide ψ s c σ u) (LowerSide ψ s c σ u)) :
    DropCase := by
  intro ψ s c σ u hT _hTa _hS _hZ hbot
  have h0 := windingSpan_Omega_eq_bot_of_alternatingPartitionData hT (h ψ s c σ u hT) hbot
  rw [h0, finrank_bot]
  omega

/-- The same, in the vocabulary of the honest residual `KeyTameClosed` of `KeyTameClosed.lean`. -/
theorem keyTameClosed_of_alternatingPartitionData
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u →
      AlternatingPartitionData (surface ψ) (UpperSide ψ s c σ u) (LowerSide ψ s c σ u)) :
    KeyTameClosed :=
  keyTameClosed_of_dropCase (dropCase_of_alternatingPartitionData h)

/-- **Pardon's Lemma 3 at the closed-tame configurations from the datum** (through the dichotomy at
the box region, `bubbleHalf_of_keyTameClosed`). -/
theorem bubbleHalf_of_alternatingPartitionData (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u →
      AlternatingPartitionData (surface ψ) (UpperSide ψ s c σ u) (LowerSide ψ s c σ u)) :
    ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → TameClosedSlice ψ s c σ u →
      ¬ (surface ψ).ContainsEssentialLoop (SphereTrace s c σ) →
      ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
      Work.BoxShrink.Bubble.BubbleHalf (surface ψ) s c σ u :=
  bubbleHalf_of_keyTameClosed hnice (keyTameClosed_of_alternatingPartitionData h)

/-- **The tamed Pardon Lemma 3 from the datum** (through the tamed dimension bound
`keyTame_of_keyTameClosed` and `smoothHalfSTame_of_keyTame`). -/
theorem smoothHalfSTame_of_alternatingPartitionData (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u →
      AlternatingPartitionData (surface ψ) (UpperSide ψ s c σ u) (LowerSide ψ s c σ u)) :
    SmoothHalfSTame :=
  smoothHalfSTame_of_keyTame hnice
    (keyTame_of_keyTameClosed (keyTameClosed_of_alternatingPartitionData h))

/-! ## The degenerate cases in which the datum is a theorem -/

/-- **The datum when every loop of the region lies on one side of the cutting plane** (the two
degenerate alternatives of the datum). -/
theorem alternatingPartitionData_of_oneSided
    (hone : ∀ γ : Work.CoreTopology.ClosedCurve (surface ψ),
      (∀ t : ℝ, γ t ∈ Omega ψ s c σ) →
      (∀ t : ℝ, γ t ∈ UpperSide ψ s c σ u) ∨ (∀ t : ℝ, γ t ∈ LowerSide ψ s c σ u)) :
    AlternatingPartitionData (surface ψ) (UpperSide ψ s c σ u) (LowerSide ψ s c σ u) := by
  intro γ hγ
  have hΩ : ∀ t : ℝ, γ t ∈ Omega ψ s c σ := by
    intro t
    rw [Omega_eq_upperSide_union_lowerSide]
    exact hγ t
  rcases hone γ hΩ with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- **The datum when the cutting plane misses the box region**: then the two closed halves are the
two *open* half-regions (`UpperSide = HalfUp`, `LowerSide = HalfDown`), and a connected loop of the
region lies in one of them (`Work.SurgeryInvariance.Span.curve_subset_of_union`). -/
theorem alternatingPartitionData_of_sigma_eq_empty (hempty : Sigma ψ s c σ u = ∅) :
    AlternatingPartitionData (surface ψ) (UpperSide ψ s c σ u) (LowerSide ψ s c σ u) := by
  have hmemSigma : ∀ y : R3, y ∈ Omega ψ s c σ → y (σ 2) = c (σ 2) + u → y ∈ Sigma ψ s c σ u := by
    intro y hy h
    rw [Sigma, Work.BoxShrink.Core.mem_sliceRegion]
    exact ⟨hy.1, hy.2, h⟩
  have hUp : UpperSide ψ s c σ u = HalfUp ψ s c σ u := by
    ext x
    rw [UpperSide, Set.mem_inter_iff, Set.mem_ofPred_eq, Omega,
      Work.BoxShrink.Core.mem_boxRegion, HalfUp, Work.BoxShrink.Core.mem_upperRegion]
    constructor
    · rintro ⟨⟨hC, hB⟩, hle⟩
      rcases lt_or_eq_of_le hle with h | h
      · exact ⟨hC, hB, h⟩
      · exact absurd (hmemSigma x ⟨hC, hB⟩ h.symm) (by rw [hempty]; exact fun hc => hc)
    · rintro ⟨hC, hB, hlt⟩
      exact ⟨⟨hC, hB⟩, le_of_lt hlt⟩
  have hLo : LowerSide ψ s c σ u = HalfDown ψ s c σ u := by
    ext x
    rw [LowerSide, Set.mem_inter_iff, Set.mem_ofPred_eq, Omega,
      Work.BoxShrink.Core.mem_boxRegion, HalfDown, Work.BoxShrink.Core.mem_lowerRegion]
    constructor
    · rintro ⟨⟨hC, hB⟩, hle⟩
      rcases lt_or_eq_of_le hle with h | h
      · exact ⟨hC, hB, h⟩
      · exact absurd (hmemSigma x ⟨hC, hB⟩ h) (by rw [hempty]; exact fun hc => hc)
    · rintro ⟨hC, hB, hlt⟩
      exact ⟨⟨hC, hB⟩, le_of_lt hlt⟩
  intro γ hγ
  have hΩ : ∀ t : ℝ, γ t ∈ Omega ψ s c σ := by
    intro t
    rw [Omega_eq_upperSide_union_lowerSide]
    exact hγ t
  have hdisj : Disjoint (UpperSide ψ s c σ u) (LowerSide ψ s c σ u) := by
    rw [hUp, hLo]
    exact Work.BoxShrink.Core.disjoint_upperRegion_lowerRegion (surface ψ) s c σ u
  have hUpOpen : Work.SurgeryInvariance.IsOpenInCarrier (surface ψ) (UpperSide ψ s c σ u) := by
    rw [hUp]
    exact Work.BoxShrink.Core.isOpenInCarrier_upperRegion (surface ψ) s c σ u
  have hLoOpen : Work.SurgeryInvariance.IsOpenInCarrier (surface ψ) (LowerSide ψ s c σ u) := by
    rw [hLo]
    exact Work.BoxShrink.Core.isOpenInCarrier_lowerRegion (surface ψ) s c σ u
  rcases Work.SurgeryInvariance.Span.curve_subset_of_union hUpOpen hLoOpen hdisj γ hγ with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

end

end Work.BoxShrink.PinchOff
