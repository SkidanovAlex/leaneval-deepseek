import Submission.Work.BoxShrink.PinchOff.OneSided
import Submission.Work.BoxShrink.PinchOff.Drop

/-!
# The alternating-partition datum of the pinch

The pinch cuts the box region `Ω = Ω⁺ ∪ Σ ∪ Ω⁻` into the **two closed halves**

  `UpperSide = Ω ∩ {y (σ 2) ≥ c (σ 2) + u}`,  `LowerSide = Ω ∩ {y (σ 2) ≤ c (σ 2) + u}`,

which cover `Ω` and meet in the slice `Σ` (`Omega_eq_upperSide_union_lowerSide`,
`upperSide_inter_lowerSide`).  Under the box-local transversality `TransverseSlice` each closed half
carries the same winding vectors as the corresponding *open* half
(`windingSpan_closedHalfUp_eq_halfUp_holds`, `OneSided.lean`), hence nothing, in the pinch
situation.

This module records the **combinatorial datum** which, for such a pair of closed pieces, produces
the (one-sided) dimension bound — and in fact the sharp `W(Ω) = ⊥` — namely the alternating
partition of every loop of `Ω` at its crossings with the slice, with the connectors supplied by the
slice:

* `AlternatingPartitionData A B` — every closed curve of `A ∪ B` is entirely in `A`, entirely in
  `B`, or splits into finitely many monochromatic arcs alternating between `A` and `B`, the
  endpoints of each `A`-arc lying in `A ∩ B` and being joined *inside* `A ∩ B`.
  The first two alternatives are the degenerate cases `Σ = ∅` (a connected curve cannot cross
  between two disjoint open pieces, `Work.SurgeryInvariance.Span.curve_subset_of_union`);
* the elementary set algebra of the two closed halves.

The union lemma which turns the datum into the winding-span bound is
`Work.BoxShrink.PinchOff.windingSpan_union_le_sup_of_alternatingPartitionData` (delegated in this
directory), and the resulting reduction of the area's residual `DropCase` to the datum is
`Work.BoxShrink.PinchOff.dropCase_of_alternatingPartitionData` (`ClosedPairing.lean`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- **The alternating-partition datum** for two sets `A`, `B` whose union is the region under
consideration: every closed curve of `A ∪ B` lies entirely in `A`, entirely in `B`, or admits a
finite monochromatic alternating partition

* `γ t ∈ A` for `t ∈ [s (2j), s (2j+1)]`,  `γ t ∈ B` for `t ∈ [s (2j+1), s (2j+2)]` (`j < k`),

with `s (2k) = s 0 + 2π` (one period), and with the endpoints of every `A`-arc (which lie in
`A ∩ B`) joined by a path *inside* `A ∩ B`.

For the two closed halves of the pinch the connectors are paths in the slice `Σ`, and the datum is
therefore the statement that the crossings of a loop with the slice can be connected inside the
slice — Pardon's *finger move*. -/
def AlternatingPartitionData (P : Work.CoreTopology.ParamTorus) (A B : Set R3) : Prop :=
  ∀ γ : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ t ∈ A ∪ B) →
    (∀ t : ℝ, γ t ∈ A) ∨ (∀ t : ℝ, γ t ∈ B) ∨
    ∃ (k : ℕ) (_ : 0 < k) (s : ℕ → ℝ),
      s 0 ∈ Set.Ico 0 (2 * Real.pi) ∧ s (2 * k) = s 0 + 2 * Real.pi ∧
      (∀ i j, i ≤ 2 * k → j ≤ 2 * k → i < j → s i < s j) ∧
      (∀ j, j < k → ∀ t, s (2 * j) ≤ t → t ≤ s (2 * j + 1) → γ t ∈ A) ∧
      (∀ j, j < k → ∀ t, s (2 * j + 1) ≤ t → t ≤ s (2 * j + 2) → γ t ∈ B) ∧
      (∀ j, j < k → JoinedIn (A ∩ B) (γ (s (2 * j))) (γ (s (2 * j + 1))))

/-- **The connector-free alternating-partition datum**: every closed curve of `A ∪ B` is
entirely in `A`, entirely in `B`, or splits into finitely many monochromatic arcs alternating
between `A` and `B` (one period, `s (2k) = s 0 + 2π`).  It is the *first half* of the finger move
— the splitting of a loop at its crossings — and, unlike `AlternatingPartitionData`, it asks
nothing of the connectors.  It is therefore available as soon as the crossings of the loops with
the interface are finite, with **no** connectivity hypothesis
(`alternatingPartitionDataWeak_of_finite_crossing`). -/
def AlternatingPartitionDataWeak (P : Work.CoreTopology.ParamTorus) (A B : Set R3) : Prop :=
  ∀ γ : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ t ∈ A ∪ B) →
    (∀ t : ℝ, γ t ∈ A) ∨ (∀ t : ℝ, γ t ∈ B) ∨
    ∃ (k : ℕ) (_ : 0 < k) (s : ℕ → ℝ),
      s 0 ∈ Set.Ico 0 (2 * Real.pi) ∧ s (2 * k) = s 0 + 2 * Real.pi ∧
      (∀ i j, i ≤ 2 * k → j ≤ 2 * k → i < j → s i < s j) ∧
      (∀ j, j < k → ∀ t, s (2 * j) ≤ t → t ≤ s (2 * j + 1) → γ t ∈ A) ∧
      (∀ j, j < k → ∀ t, s (2 * j + 1) ≤ t → t ≤ s (2 * j + 2) → γ t ∈ B)

/-- **The connector-free datum plus a path-connected intersection is the datum with
connectors**: the endpoints of every `A`-arc lie in `A ∩ B` (each is an endpoint of a maximal
`A`-block and of the neighbouring `B`-block), and a path-connected intersection joins them. -/
theorem AlternatingPartitionDataWeak.toData_of_isPathConnected_inter
    {P : Work.CoreTopology.ParamTorus} {A B : Set R3}
    (h : AlternatingPartitionDataWeak P A B) (hconn : IsPathConnected (A ∩ B)) :
    AlternatingPartitionData P A B := by
  intro γ hγ
  rcases h γ hγ with h | h | ⟨k, hk, s, h0, hlast, hmono, hA, hB⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨k, hk, s, h0, hlast, hmono, hA, hB, ?_⟩)
    intro j hj
    have hmemA : γ (s (2 * j)) ∈ A ∩ B := by
      refine ⟨hA j hj (s (2 * j)) le_rfl
        (le_of_lt (hmono (2 * j) (2 * j + 1) (by omega) (by omega) (by omega))), ?_⟩
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · subst hj0
        have hBk : γ (s (2 * k)) ∈ B :=
          hB (k - 1) (by omega) (s (2 * k))
            (le_of_lt (hmono (2 * (k - 1) + 1) (2 * k) (by omega) (by omega) (by omega)))
            (le_of_eq (by congr 1; omega))
        rw [hlast, γ.periodic (s 0)] at hBk
        exact hBk
      · exact hB (j - 1) (by omega) (s (2 * j))
          (le_of_lt (hmono (2 * (j - 1) + 1) (2 * j) (by omega) (by omega) (by omega)))
          (le_of_eq (by congr 1; omega))
    have hmemB : γ (s (2 * j + 1)) ∈ A ∩ B :=
      ⟨hA j hj (s (2 * j + 1))
        (le_of_lt (hmono (2 * j) (2 * j + 1) (by omega) (by omega) (by omega))) le_rfl,
       hB j hj (s (2 * j + 1)) le_rfl
        (le_of_lt (hmono (2 * j + 1) (2 * j + 2) (by omega) (by omega) (by omega)))⟩
    exact hconn.joinedIn _ hmemA _ hmemB

/-- The datum with connectors is the datum without them (the connectors being dropped). -/
theorem AlternatingPartitionData.toWeak {P : Work.CoreTopology.ParamTorus} {A B : Set R3}
    (h : AlternatingPartitionData P A B) : AlternatingPartitionDataWeak P A B := by
  intro γ hγ
  rcases h γ hγ with h | h | ⟨k, hk, s, h0, hlast, hmono, hA, hB, _⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨k, hk, s, h0, hlast, hmono, hA, hB⟩)

variable {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-- The two closed halves meet in the slice. -/
theorem upperSide_inter_lowerSide :
    UpperSide ψ s c σ u ∩ LowerSide ψ s c σ u = Sigma ψ s c σ u := by
  ext x
  simp only [UpperSide, LowerSide, Omega, Sigma, Work.BoxShrink.Core.mem_boxRegion,
    Work.BoxShrink.Core.mem_sliceRegion, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨⟨hC, hB⟩, hp⟩, ⟨⟨-, -⟩, hq⟩⟩
    exact ⟨hC, hB, le_antisymm hq hp⟩
  · rintro ⟨hC, hB, hr⟩
    exact ⟨⟨⟨hC, hB⟩, le_of_eq hr.symm⟩, ⟨⟨hC, hB⟩, le_of_eq hr⟩⟩

/-- The box region is the union of the two closed halves. -/
theorem Omega_eq_upperSide_union_lowerSide :
    Omega ψ s c σ = UpperSide ψ s c σ u ∪ LowerSide ψ s c σ u := by
  ext x
  simp only [UpperSide, LowerSide, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · intro hx
    rcases le_total (x (σ 2)) (c (σ 2) + u) with h | h
    · exact Or.inr ⟨hx, h⟩
    · exact Or.inl ⟨hx, h⟩
  · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx

end

end Work.BoxShrink.PinchOff
