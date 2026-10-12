import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.NominalPerBox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.nomDemand_split` — the slot decomposition of the nominal demand

The nominal per-box demand of FS `thm:smallbox` is read at the *indicator* local density
`boxIndCount ℓ d u x / boxMass ℓ d u` (the count `#{i : xᵢ ∈ B(u)}` over the box volume), so the
weight `ψ(n/|B|) = psiWeight 1 μ (n/|B|)` depends on a configuration only through the cardinality
of its occupant set.  The slot sets `slotSet (dlBox ℓ d u) S` (`Work.PerSector`) partition the
configuration space by that occupant, so the demand splits into the per-sector row

    W·(∫_{abox} Φ²·ψ(n(B)/|B|)) − E·(∫_{abox} Φ²)
      = ∑_{S : Finset (Fin N)} (W·ψ(|S|/|B|) − E)·(∫_{abox} (slotPiece B S Φ)²) ,

i.e. the demand is the sum of its *sector* demands, each at the fixed count `|S|` and against the
`abox`-`L²`-mass of the slot piece `slotPiece B S Φ = 1_{slotSet B S}·Φ`.

This is the exact (indicator-count) localisation step of the per-box chapter: it converts the
`u`-dependent demand of a state into the finite sum, over the `2^N` occupant sets, of the demand
of the corresponding slot piece.  All of its content is the pointwise partition identity
`∑_S (slotPiece B S Φ x)² = (Φ x)²` (`Work.PerSector.sum_indicator_slotSet`) together with
`boxIndCount x = |S|` on `slotSet B S`; the finite sum is exchanged with the integral because each
slot piece is bounded by `Φ` and `abox N ℓ` is compact.
-/

namespace Work.BoseB1Cube

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The nominal count is the occupancy of the slot set**: on the configurations whose box
occupant is exactly `S`, the indicator count `boxIndCount ℓ d u` equals `|S|`. -/
lemma boxIndCount_eq_card_of_mem_slotSet {n : ℕ} {ℓ d : ℝ} (u : E3)
    {S : Finset (Fin n)} {x : Submission.BoseGases.X n}
    (hx : x ∈ Work.PerSector.slotSet (Submission.BoseGases.dlBox ℓ d u) S) :
    boxIndCount ℓ d u x = (S.card : ℝ) := by
  have h1 : boxIndCount ℓ d u x = Work.FockBridge.boxCount (Submission.BoseGases.dlBox ℓ d u) x := by
    rw [Work.FockBridge.boxCount_eq_sum_indicator]
    rfl
  rw [h1, Work.FockBridge.boxCount,
    Work.PerSector.boxOccupancy_eq_card_of_mem_slotSet (Submission.BoseGases.dlBox ℓ d u) hx]

/-- **The pointwise slot decomposition of the nominal demand integrand**: the weight
`Φ²·ψ(n/|B|)` is the sum over the occupant sets `S` of `ψ(|S|/|B|)·(slotPiece B S Φ)²`, the
`ψ`-weight being constant on each slot set and only the occupant's slot piece contributing

(The weight `psiWeight 1 μ` never vanishes, and `boxMass` may be zero; both sides are then read at
`0`, and the identity is the plain partition identity because `boxIndCount x = |S|` on the slot
set, so the two divisions are divisions of the *same* number.) -/
lemma nomDemand_split_pointwise {N : ℕ} {ℓ d μ : ℝ} (u : E3)
    {Φ : Submission.BoseGases.X N → ℝ} (x : Submission.BoseGases.X N) :
    (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ
        (boxIndCount ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u)
      = ∑ S : Finset (Fin N),
          Work.SmallBoxSliding.psiWeight 1 μ
              ((S.card : ℝ) / Work.SmallBoxSliding.boxMass ℓ d u)
            * (Work.PerSector.slotPiece (Submission.BoseGases.dlBox ℓ d u) S Φ x) ^ 2 := by
  classical
  set B := Submission.BoseGases.dlBox ℓ d u with hB
  set m := Work.SmallBoxSliding.boxMass ℓ d u with hm
  set S₀ : Finset (Fin N) := Finset.univ.filter (fun i : Fin N => x i ∈ B) with hS₀
  have hmem₀ : x ∈ Work.PerSector.slotSet B S₀ := by
    intro i
    rw [hS₀, Finset.mem_filter]
    exact ⟨fun h => ⟨Finset.mem_univ i, h⟩, fun h => h.2⟩
  have hcount : boxIndCount ℓ d u x = (S₀.card : ℝ) := by
    have h1 : boxIndCount ℓ d u x = Work.FockBridge.boxCount B x := by
      rw [hB, Work.FockBridge.boxCount_eq_sum_indicator]
      rfl
    rw [h1, Work.FockBridge.boxCount,
      Work.PerSector.boxOccupancy_eq_card_of_mem_slotSet B hmem₀]
  calc (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ (boxIndCount ℓ d u x / m)
      = Work.SmallBoxSliding.psiWeight 1 μ ((S₀.card : ℝ) / m) * (Φ x) ^ 2 := by
        rw [hcount]; ring
    _ = Work.SmallBoxSliding.psiWeight 1 μ ((S₀.card : ℝ) / m)
          * ((Work.PerSector.slotSet B S₀).indicator (fun y => (Φ y) ^ 2) x) := by
        rw [Set.indicator_of_mem hmem₀]
    _ = ∑ S : Finset (Fin N), Work.SmallBoxSliding.psiWeight 1 μ ((S.card : ℝ) / m)
          * ((Work.PerSector.slotSet B S).indicator (fun y => (Φ y) ^ 2) x) := by
        rw [Finset.sum_eq_single S₀]
        · intro S _ hne
          rw [Set.indicator_of_notMem
            (fun hxS => hne (Work.PerSector.slotSet_eq_of_mem hxS hmem₀))]
          ring
        · intro hnot; exact absurd (Finset.mem_univ _) hnot
    _ = ∑ S : Finset (Fin N), Work.SmallBoxSliding.psiWeight 1 μ ((S.card : ℝ) / m)
          * (Work.PerSector.slotPiece B S Φ x) ^ 2 := by
        refine Finset.sum_congr rfl (fun S _ => ?_)
        rw [Work.PerSector.slotPiece_sq]

/-- **FS `thm:smallbox`'s per-`u` demand splits over the occupant sectors.**  The demand
`W·⟨ψ(n(B)/|B|)⟩ − E·⟨1⟩` of a state `Φ` on the box `abox N ℓ` is the sum, over the `2^N` occupant
sets `S : Finset (Fin N)`, of the *sector* demand at the fixed count `|S|` against the `abox`-mass
of the slot piece `slotPiece B S Φ`. -/
theorem nomDemand_split {N : ℕ} {ℓ d μ W E : ℝ} (hℓ : 0 < ℓ)
    (u : EuclideanSpace ℝ (Fin 3)) {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Continuous Φ) :
    W * (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2
          * Work.SmallBoxSliding.psiWeight 1 μ
              (Work.BoseB1Cube.boxIndCount ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u))
      - E * (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2)
    = ∑ S : Finset (Fin N),
        (W * Work.SmallBoxSliding.psiWeight 1 μ ((S.card : ℝ) / Work.SmallBoxSliding.boxMass ℓ d u) - E)
          * (∫ x in Submission.BoseGases.abox N ℓ,
              (Work.PerSector.slotPiece (Submission.BoseGases.dlBox ℓ d u) S Φ x) ^ 2) := by
  classical
  -- ### integrability on the box
  have hΦint : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => (Φ x) ^ 2)
      (Submission.BoseGases.abox N ℓ) :=
    ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact N hℓ)
      (hΦ.pow 2).continuousOn
  have hSint : ∀ S : Finset (Fin N), MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.PerSector.slotPiece (Submission.BoseGases.dlBox ℓ d u) S Φ x) ^ 2)
      (Submission.BoseGases.abox N ℓ) := by
    intro S
    have hfun : (fun x : Submission.BoseGases.X N =>
          (Work.PerSector.slotPiece (Submission.BoseGases.dlBox ℓ d u) S Φ x) ^ 2)
        = (Work.PerSector.slotSet (Submission.BoseGases.dlBox ℓ d u) S).indicator
            (fun y => (Φ y) ^ 2) := by
      funext x; exact Work.PerSector.slotPiece_sq _ S Φ x
    rw [hfun]
    exact hΦint.indicator (Work.PerSector.slotSet_measurable _
      (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u) S)
  -- ### the unweighted mass splits over the slots
  have hU : (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2)
      = ∑ S : Finset (Fin N), ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.PerSector.slotPiece (Submission.BoseGases.dlBox ℓ d u) S Φ x) ^ 2 := by
    rw [← MeasureTheory.integral_finsetSum]
    · refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      exact ((Finset.sum_congr rfl (fun S _ => Work.PerSector.slotPiece_sq _ S Φ x)).trans
        (Work.PerSector.sum_indicator_slotSet (Submission.BoseGases.dlBox ℓ d u)
          (fun y => (Φ y) ^ 2) x)).symm
    · intro S _; exact hSint S
  -- ### the weighted mass splits over the slots
  have hW1 : (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2
        * Work.SmallBoxSliding.psiWeight 1 μ
            (boxIndCount ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u))
      = ∑ S : Finset (Fin N),
          ∫ x in Submission.BoseGases.abox N ℓ, Work.SmallBoxSliding.psiWeight 1 μ
              ((S.card : ℝ) / Work.SmallBoxSliding.boxMass ℓ d u)
            * (Work.PerSector.slotPiece (Submission.BoseGases.dlBox ℓ d u) S Φ x) ^ 2 := by
    rw [← MeasureTheory.integral_finsetSum]
    · refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      exact nomDemand_split_pointwise u x
    · intro S _
      exact (hSint S).const_mul _
  have hW2 : (∑ S : Finset (Fin N),
          ∫ x in Submission.BoseGases.abox N ℓ, Work.SmallBoxSliding.psiWeight 1 μ
              ((S.card : ℝ) / Work.SmallBoxSliding.boxMass ℓ d u)
            * (Work.PerSector.slotPiece (Submission.BoseGases.dlBox ℓ d u) S Φ x) ^ 2)
      = ∑ S : Finset (Fin N), Work.SmallBoxSliding.psiWeight 1 μ
          ((S.card : ℝ) / Work.SmallBoxSliding.boxMass ℓ d u)
          * ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.PerSector.slotPiece (Submission.BoseGases.dlBox ℓ d u) S Φ x) ^ 2 := by
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [MeasureTheory.integral_const_mul]
  have hW := hW1.trans hW2
  -- ### assembly
  rw [hW, hU, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun S _ => by ring)

end Work.BoseB1Cube
