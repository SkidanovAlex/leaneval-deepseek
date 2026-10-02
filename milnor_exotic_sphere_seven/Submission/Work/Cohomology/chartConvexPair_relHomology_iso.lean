import Mathlib
import Submission.Work.Cohomology.relChainsHomeomorphCompat
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.excision

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The chart identifies the relative homology of a convex coordinate pair with the flat model

For a chart `e = chartAt _ cc` of a topological space `M` charted over `ℝ^N`, an open set
`Q ⊆ e.target`, and a compact `K' ⊆ Q`, the chart restricts to a homeomorphism of pairs

`(W, W∖K) ≅ (Q, Q∖K')`,  `W := e ⁻¹' Q ∩ e.source`, `K := e ⁻¹' K' ∩ e.source`,

and excision in `ℝ^N` (with the open cover `Q ∪ (ℝ^N∖K') = ℝ^N`, valid because `K' ⊆ Q`) identifies
the relative homology of `(Q, Q∖K')` with that of the flat model `(ℝ^N, ℝ^N∖K')`.

This is the generalization of `chartBallPair_relHomology_iso` from a ball to an arbitrary open set
`Q` (in particular a convex one), needed for the base case of Poincaré duality on a convex
coordinate set.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- The restriction of an open partial homeomorphism to the preimage of a subset of its target,
as a homeomorphism onto that subset. -/
def partialHomeomorphSetHomeo {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) {Q : Set Y} (hsub : Q ⊆ e.target) :
    ↥(e.source ∩ e ⁻¹' Q) ≃ₜ ↥Q where
  toFun y := ⟨e y.1, y.2.2⟩
  invFun ζ := ⟨e.symm ζ.1,
    ⟨e.map_target (hsub ζ.2),
      by simpa only [Set.mem_preimage, e.right_inv (hsub ζ.2)] using ζ.2⟩⟩
  left_inv y := by
    ext
    exact e.left_inv y.2.1
  right_inv ζ := by
    ext
    exact e.right_inv (hsub ζ.2)
  continuous_toFun := by
    have h1 : Continuous fun y : ↥(e.source ∩ e ⁻¹' Q) => (⟨y.1, y.2.1⟩ : ↥e.source) :=
      Continuous.subtype_mk continuous_subtype_val (fun y => y.2.1)
    have h2 : Continuous fun z : ↥e.source =>
        (⟨e z.1, e.map_source z.2⟩ : ↥e.target) :=
      (e.toHomeomorphSourceTarget).continuous
    have h3 : Continuous fun w : ↥e.target => (w : Y) := continuous_subtype_val
    have h4 : Continuous fun y : ↥(e.source ∩ e ⁻¹' Q) => e y.1 :=
      h3.comp (h2.comp h1)
    exact Continuous.subtype_mk h4 (fun y => y.2.2)
  continuous_invFun := by
    have h1 : Continuous fun ζ : ↥Q =>
        (⟨ζ.1, hsub ζ.2⟩ : ↥e.target) :=
      Continuous.subtype_mk continuous_subtype_val (fun ζ => hsub ζ.2)
    have h2 : Continuous fun w : ↥e.target =>
        (⟨e.symm w.1, e.map_target w.2⟩ : ↥e.source) :=
      (e.symm.toHomeomorphSourceTarget).continuous
    have h3 : Continuous fun z : ↥e.source => (z : X) := continuous_subtype_val
    have h4 : Continuous fun ζ : ↥Q => e.symm ζ.1 := h3.comp (h2.comp h1)
    exact Continuous.subtype_mk h4 (fun ζ =>
      ⟨e.map_target (hsub ζ.2),
        by simpa only [Set.mem_preimage, e.right_inv (hsub ζ.2)] using ζ.2⟩)

/-- **The chart identifies the relative homology of a convex coordinate pair with the flat model.**
For `e = chartAt _ cc`, `Q ⊆ e.target` open, `K' ⊆ Q` compact, the pair
`(W, W∖K)`, `W = e ⁻¹' Q ∩ e.source`, `K = e ⁻¹' K' ∩ e.source`, has the relative homology of
`(ℝ^N, ℝ^N∖K')`. -/
theorem chartConvexPair_relHomology_iso (N : ℕ) (M : TopCat) [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M] (cc : M) :
    let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N)) := chartAt _ cc
    (Q : Set (EuclideanSpace ℝ (Fin N))) → IsOpen Q → Q ⊆ e.target →
    (K' : Set (EuclideanSpace ℝ (Fin N))) → IsCompact K' → K' ⊆ Q →
    let W : Set M := (e ⁻¹' Q) ∩ e.source
    let K : Set M := (e ⁻¹' K') ∩ e.source
    ∀ k, Nonempty (((Work.Cohomology.relChains (TopCat.of W)
        (Work.Cohomology.pdRelSub W K)).homology k) ≅
      ((Work.Cohomology.relChains (TopCat.of (EuclideanSpace ℝ (Fin N)))
        {v : EuclideanSpace ℝ (Fin N) | v ∉ K'}).homology k)) := by
  intro e Q hQ hQsub K' hK'c hK'sub W K k
  have hW : W = e.source ∩ e ⁻¹' Q := by
    show (e ⁻¹' Q) ∩ e.source = e.source ∩ e ⁻¹' Q
    rw [Set.inter_comm]
  let φ : ↥W ≃ₜ ↥Q := (Homeomorph.setCongr hW).trans (partialHomeomorphSetHomeo e hQsub)
  have hφ : ∀ y : ↥W, (φ y : EuclideanSpace ℝ (Fin N)) = e (y : M) := fun y => rfl
  have hcorr : ∀ x : ↥W, x ∈ pdRelSub W K ↔
      φ x ∈ {y : ↥Q | (y : EuclideanSpace ℝ (Fin N)) ∉ K'} := by
    intro x
    show (x : M) ∉ K ↔ (φ x : EuclideanSpace ℝ (Fin N)) ∉ K'
    rw [hφ x]
    constructor
    · intro h hK'
      exact h ⟨hK', x.2.2⟩
    · intro h hK
      exact h hK.1
  obtain ⟨e1⟩ := relChainsHomeomorphCompat ↥W ↥Q (pdRelSub W K)
    {y : ↥Q | (y : EuclideanSpace ℝ (Fin N)) ∉ K'} φ hcorr k
  -- excision on the Euclidean side
  have hcov : Q ∪ {v : EuclideanSpace ℝ (Fin N) | v ∉ K'} = Set.univ := by
    ext v
    by_cases hv : v ∈ K'
    · exact ⟨fun _ => trivial, fun _ => Or.inl (hK'sub hv)⟩
    · exact ⟨fun _ => trivial, fun _ => Or.inr hv⟩
  haveI hiso : IsIso (HomologicalComplex.homologyMap
      (relChainsMap (TopCat.of (EuclideanSpace ℝ (Fin N))) Q
        {v : EuclideanSpace ℝ (Fin N) | v ∉ K'}) k) :=
    excision_relChainsMap_isIso (X := TopCat.of (EuclideanSpace ℝ (Fin N))) (U := Q)
      (A := {v : EuclideanSpace ℝ (Fin N) | v ∉ K'}) hQ hK'c.isClosed.isOpen_compl hcov k
  exact ⟨e1 ≪≫ asIso (HomologicalComplex.homologyMap
    (relChainsMap (TopCat.of (EuclideanSpace ℝ (Fin N))) Q
      {v : EuclideanSpace ℝ (Fin N) | v ∉ K'}) k)⟩

end

end Work.Cohomology
