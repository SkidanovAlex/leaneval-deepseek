import Mathlib
import Submission.Work.SurgeryInvariance.All
import Submission.Work.CoreTopology.Winding
import Submission.Work.InnermostDisk.Defs
import Submission.Work.BoxShrink.PinchOff.exists_discRegion_of_not_isEssential
import Submission.Work.BoxShrink.PinchOff.peel_range_eq_of_nhds

namespace Work.BoxShrink.PinchOff

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## Small point-set facts about the regions of the surface -/

/-- **The image of a closed curve of a parametrised torus is compact**: it is the image of the
compact interval `[0, 2π]` under the `2π`-periodic parametrisation. -/
theorem isCompact_range_closedCurve (γ : Work.CoreTopology.ClosedCurve P) :
    IsCompact (Set.range γ.γ) := by
  have hper : Function.Periodic γ.γ (2 * Real.pi) := γ.periodic
  rw [← hper.image_Icc (by positivity) 0]
  exact isCompact_Icc.image γ.cont

/-- **Deleting a closed set from a region open in the carrier leaves it open in the carrier.** -/
theorem isOpenInCarrier_sdiff_of_isClosed {X S : Set R3}
    (hX : Work.SurgeryInvariance.IsOpenInCarrier P X) (hS : IsClosed S) :
    Work.SurgeryInvariance.IsOpenInCarrier P (X \ S) := by
  unfold Work.SurgeryInvariance.IsOpenInCarrier at hX ⊢
  have hc : IsClosed ((Subtype.val : P.carrier → R3) ⁻¹' S) :=
    hS.preimage continuous_subtype_val
  have hset : (Subtype.val : P.carrier → R3) ⁻¹' (X \ S)
      = ((Subtype.val : P.carrier → R3) ⁻¹' X) \ ((Subtype.val : P.carrier → R3) ⁻¹' S) := rfl
  rw [hset]
  exact hX.sdiff hc

/-- **Deleting the image of a closed curve leaves a region open in the carrier.** -/
theorem isOpenInCarrier_sdiff_range {X : Set R3}
    (hX : Work.SurgeryInvariance.IsOpenInCarrier P X) (γ : Work.CoreTopology.ClosedCurve P) :
    Work.SurgeryInvariance.IsOpenInCarrier P (X \ Set.range γ.γ) :=
  isOpenInCarrier_sdiff_of_isClosed hX (isCompact_range_closedCurve γ).isClosed

/-- The finite union of the images of finitely many closed curves is compact. -/
theorem isCompact_iUnion_range_closedCurve {n : ℕ} (γ : Fin n → Work.CoreTopology.ClosedCurve P)
    (S : Finset (Fin n)) : IsCompact (⋃ i ∈ S, Set.range (γ i).γ) := by
  rw [← Set.iUnion_subtype (fun i : Fin n => i ∈ S) (fun i => Set.range (γ i).γ)]
  exact isCompact_iUnion (fun i => isCompact_range_closedCurve (γ i))

/-- **Deleting finitely many closed curves leaves a region open in the carrier.** -/
theorem isOpenInCarrier_sdiff_iUnion_range {X : Set R3}
    (hX : Work.SurgeryInvariance.IsOpenInCarrier P X) {n : ℕ}
    (γ : Fin n → Work.CoreTopology.ClosedCurve P) (S : Finset (Fin n)) :
    Work.SurgeryInvariance.IsOpenInCarrier P (X \ ⋃ i ∈ S, Set.range (γ i).γ) :=
  isOpenInCarrier_sdiff_of_isClosed hX (isCompact_iUnion_range_closedCurve γ S).isClosed

/-! ## The peeling of a finite family -/

/-- **Peeling finitely many pairwise disjoint inessential simple closed curves out of a region**:
for every finite set `S` of indices of the family, the winding span of `X` is unchanged when the
images of the curves with index in `S` are deleted.  This is an induction on `S` in which the
single-curve step `peel_range_eq_of_nhds` is applied to the intermediate region
`X \ ⋃ i ∈ S, range (γ i)`, which is open in the carrier
(`isOpenInCarrier_sdiff_iUnion_range`) and contains the image of the next curve (pairwise
disjointness). -/
theorem windingSpan_sdiff_biUnion_range_eq {n : ℕ} {X : Set R3}
    {γ : Fin n → Work.CoreTopology.ClosedCurve P}
    (hX : Work.SurgeryInvariance.IsOpenInCarrier P X)
    (hsimple : ∀ i, Work.CoreTopology.IsSimple P (γ i))
    (hiness : ∀ i, ¬ Work.CoreTopology.IsEssential P (γ i))
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (γ i).γ) (Set.range (γ j).γ))
    (hsub : ∀ (i : Fin n) (t : ℝ), γ i t ∈ X) (S : Finset (Fin n)) :
    Work.SurgeryInvariance.WindingSpan P X
      = Work.SurgeryInvariance.WindingSpan P (X \ ⋃ i ∈ S, Set.range (γ i).γ) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [ih]
    have hset : (X \ ⋃ i ∈ S, Set.range (γ i).γ) \ Set.range (γ a).γ
        = X \ ⋃ i ∈ insert a S, Set.range (γ i).γ := by
      rw [Finset.set_biUnion_insert, Set.union_comm, ← Set.sdiff_sdiff]
    rw [← hset]
    refine peel_range_eq_of_nhds (P := P) (X := X \ ⋃ i ∈ S, Set.range (γ i).γ)
      (γ := γ a) (hsimple a) (hiness a) ?_
    refine Exists.intro (X \ ⋃ i ∈ S, Set.range (γ i).γ) ?_
    refine And.intro (isOpenInCarrier_sdiff_iUnion_range hX γ S) ?_
    refine And.intro ?_ ?_
    · intro x hx
      obtain ⟨t, rfl⟩ := hx
      refine And.intro (hsub a t) ?_
      intro hcon
      obtain ⟨i, hcon'⟩ := Set.mem_iUnion.mp hcon
      obtain ⟨hiS, hxi⟩ := Set.mem_iUnion.mp hcon'
      obtain ⟨t', ht'⟩ := hxi
      have hne : a ≠ i := by rintro rfl; exact ha hiS
      exact (Set.disjoint_left.mp (hdisj a i hne) ⟨t, rfl⟩) ⟨t', ht'⟩
    · exact subset_rfl

/-! ## The statement -/

/-- **Removing a finite family of pairwise disjoint inessential simple closed curves does not change
the winding span.**  Let `P` be a parametrised torus, `γ : Fin n → ClosedCurve P` a family of
pairwise disjoint simple closed curves, each inessential in `P` (equivalently, by
`Work.InnermostDisk.boundsDiscInSurface_iff_not_isEssential`, each bounds a disc of the surface), and
`X` a region of the surface, open in the carrier, containing the image of every `γ i`.  Then the
winding span of `X` equals the winding span of `X` with the union of the images of the `γ i`
removed.

`≤` is monotonicity (`WindingSpan_mono`); the content is `≥`: every winding vector realised by a
closed curve of `X` is realised by one avoiding the union.  Since each `[γ i] = 0 ∈ H₁(F)` and `X`
is open in the carrier, `X` contains a full neighbourhood of each curve; a curve of `X` meeting one
of the `γ i` can be rerouted along a parallel of that curve, inside that neighbourhood, to a curve
of `X \ ⋃ range (γ i)` with the same winding vector.  Pairwise disjointness gives disjoint collars,
so the modifications do not interfere.

This is the "peeling" statement behind Pardon's pinch when the trace of the cutting plane consists
of circles only: the trace circles are pairwise disjoint simple curves (tameness), each inessential
by the hypothesis `hZ`, and removing them all from the region inside the box does not change its
winding span.

The all-at-once statement is proved here by peeling the curves *one at a time*
(`windingSpan_sdiff_biUnion_range_eq`): the intermediate region `X \ ⋃ i ∈ S, range (γ i)` is again
open in the carrier (it is `X` with finitely many compact — hence closed — curves deleted,
`isOpenInCarrier_sdiff_iUnion_range`) and it contains the image of the curve to be peeled next
(pairwise disjointness), so the single-curve form `peel_range_eq_of_nhds` applies at every step. -/
theorem windingSpan_sdiff_iUnion_range_eq_of_not_isEssential {P : Work.CoreTopology.ParamTorus}
    {X : Set LeanEval.KnotTheory.PardonDistortion.R3} {n : ℕ}
    {γ : Fin n → Work.CoreTopology.ClosedCurve P}
    (hX : Work.SurgeryInvariance.IsOpenInCarrier P X)
    (hsimple : ∀ i, Work.CoreTopology.IsSimple P (γ i))
    (hiness : ∀ i, ¬ Work.CoreTopology.IsEssential P (γ i))
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (γ i).γ) (Set.range (γ j).γ))
    (hsub : ∀ (i : Fin n) (t : ℝ), γ i t ∈ X) :
    Work.SurgeryInvariance.WindingSpan P X =
      Work.SurgeryInvariance.WindingSpan P (X \ ⋃ i, Set.range (γ i).γ) := by
  have h := windingSpan_sdiff_biUnion_range_eq hX hsimple hiness hdisj hsub
    (Finset.univ : Finset (Fin n))
  have huniv : (⋃ i ∈ (Finset.univ : Finset (Fin n)), Set.range (γ i).γ)
      = ⋃ i, Set.range (γ i).γ := by
    ext x
    simp
  rwa [huniv] at h

end

end Work.BoxShrink.PinchOff
