import Mathlib
import Submission.Work.RatHurewicz.cycleModelDefs
import Submission.Work.RatHurewicz.cellDefs
import Submission.Work.RatHurewicz.cellFacts

/-!
# The vocabulary of the *uniform* push of the `k`-cells of the model

This module fixes the vocabulary used by the uniform (cell-independent) push of the `k`-skeleton of
`Model D` into its `(k-1)`-skeleton, the route to `Work.RatHurewicz.compress_to_skeleton`.

A raw point of weight `k+1` (an interior point of a `k`-cell) is pushed radially away from the
centroid of *its own support*; a raw point of weight `≤ k` is kept fixed.  The push is
discontinuous exactly at the raw points which are the centroid of their own support, and those are
exactly the points whose image in the model is the image of the centroid of a `(k+1)`-face, i.e. a
point `cellOriginOf D i S`.

* `IsCentroidPt x` — `x` is the centroid of its own support;
* `isCentroidModel D k z` — `z` is the image in the model of the centroid of a `(k+1)`-face;
* `pushDomainModel D k z` — the model points of the `k`-skeleton which are not such centroids;
* `pushDomain D k a` — the raw points whose image lies in `pushDomainModel D k`; this set is
  saturated for the gluing relation of the model by construction.
-/

open scoped Topology Simplicial unitInterval

namespace Work.RatHurewicz

namespace SkelPush

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

/-- **A point of the standard simplex is the centroid of its own support.** -/
def IsCentroidPt (x : stdSimplex ℝ (Fin (n + 2))) : Prop :=
  ∃ hS : (ptSupport x).Nonempty, x = centroidPt (ptSupport x) hS

/-- **The images in the model of the centroids of the `(k+1)`-faces**: the points at which the
uniform push of the `k`-cells is discontinuous. -/
def isCentroidModel (D : MData X n x₀) (k : ℕ) (z : Model D) : Prop :=
  ∃ (i : D.Idx) (S : Finset (Fin (n + 2))) (hS : S.Nonempty),
    S.card = k + 1 ∧ z = cellOriginOf D i S hS

/-- **The model-level domain of the uniform push**: the `k`-skeleton with the centroids of the
`(k+1)`-faces removed. -/
def pushDomainModel (D : MData X n x₀) (k : ℕ) (z : Model D) : Prop :=
  z ∈ skel D k ∧ ¬ isCentroidModel D k z

/-- **The raw-level domain of the uniform push**: the raw points whose image in the model lies in
`pushDomainModel`.  Defined as a pullback, this set is automatically saturated for the gluing
relation of the model. -/
def pushDomain (D : MData X n x₀) (k : ℕ) (a : Raw D) : Prop :=
  pushDomainModel D k (Quotient.mk'' a)

/-- Membership in a skeleton, read on a raw representative. -/
theorem mem_skel_mk (D : MData X n x₀) (k : ℕ) (a : Raw D) :
    Quotient.mk'' a ∈ skel D k ↔ rawWeight D a ≤ k + 1 := by
  constructor
  · intro h
    obtain ⟨a', ha', hw'⟩ := (mem_skel_iff (D := D)).mp h
    have hrel : Relation.EqvGen (modelRel D) a' a := Quotient.exact ha'
    have hinv := rawWeight_eqvGen D hrel
    omega
  · intro h
    exact (mem_skel_iff (D := D)).mpr ⟨a, rfl, h⟩

theorem pushDomain_iff (D : MData X n x₀) (k : ℕ) (a : Raw D) :
    pushDomain D k a ↔ rawWeight D a ≤ k + 1 ∧ ¬ isCentroidModel D k (Quotient.mk'' a) :=
  and_congr (mem_skel_mk D k a) Iff.rfl

/-- The raw points which are the centroids of their own support map to `isCentroidModel`. -/
theorem isCentroidModel_of_isCentroidPt {D : MData X n x₀} {k : ℕ}
    {i : D.Idx} {x : stdSimplex ℝ (Fin (n + 2))} (hx : IsCentroidPt (n := n) x)
    (hcard : (ptSupport x).card = k + 1) :
    isCentroidModel D k (Quotient.mk'' (Sum.inl ⟨i, x⟩)) := by
  obtain ⟨hS, hxS⟩ := hx
  refine ⟨i, ptSupport x, hS, hcard, ?_⟩
  have h1 := congrArg
    (fun y : stdSimplex ℝ (Fin (n + 2)) => (Sum.inl ⟨i, y⟩ : Raw D)) hxS
  show Quotient.mk'' (Sum.inl ⟨i, x⟩) = cellOriginOf D i (ptSupport x) hS
  rw [h1]
  rfl

/-- **The `hS`-dependence of `cellOriginOf` is vacuous.** -/
theorem cellOrigin_congr {D : MData X n x₀} (i : D.Idx) (S : Finset (Fin (n + 2)))
    (hS hS' : S.Nonempty) : cellOriginOf D i S hS = cellOriginOf D i S hS' := by
  have hv : centroidPt S hS = centroidPt S hS' := Subtype.ext rfl
  unfold cellOriginOf
  rw [hv]

/-- A copy of `Work.RatHurewicz.rawWeight_eqvGen` under a name that is unique in this workspace (the
original name is declared twice, with different argument conventions, in the workspace). -/
theorem rawWeight_eqvGen' {D : MData X n x₀} {a b : Raw D}
    (h : Relation.EqvGen (modelRel D) a b) : rawWeight D a = rawWeight D b := by
  induction h with
  | rel x y hr => exact rawWeight_rel D hr
  | refl x => rfl
  | symm x y hxy ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

/-- A copy of `Work.RatHurewicz.skel_mono` under a name that is unique in this workspace (the
original name is declared twice, with different argument conventions, in the workspace). -/
theorem skel_mono' {D : MData X n x₀} {a b : ℕ} (h : a ≤ b) : skel D a ⊆ skel D b := by
  intro z hz
  obtain ⟨c, hc, hw⟩ := (mem_skel_iff (D := D)).mp hz
  exact (mem_skel_iff (D := D)).mpr ⟨c, hc, by omega⟩

end

end SkelPush

end Work.RatHurewicz
