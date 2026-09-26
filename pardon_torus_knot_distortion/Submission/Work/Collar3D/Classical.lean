import Submission.Work.Collar3D.Model.Collar
import Submission.Work.Collar3D.Model.DiscCollarModel
import Submission.Work.Collar3D.PushOff.Surface
import Submission.Work.Collar3D.Chart.Ambient

/-!
# The named classical inputs of the collar chapter

Everything in this chapter is proved from two classical theorems of three-dimensional topology,
stated here in `ℝ³` alone — with no mention of a torus, of a box, or of a sphere family, and each
in the sharp form in which the argument uses it:

* `Work.Collar3D.RegularNeighbourhoodCurve` — **the regular-neighbourhood (bicollar) theorem along
  a curve**: a locally flat surface has a collar along any simple closed curve which already has an
  *annular neighbourhood* in the surface.  The annular-neighbourhood hypothesis is the framing of
  the curve and is not removable (the core of a Möbius band has none);
* `Work.Collar3D.RegularNeighbourhoodDisc` — the same for a *disc*: a locally flat embedded disc
  has a bicollar.  From it, `Work.Collar3D.exists_cap_of_discCollar` *proves* the push-off of the
  innermost sub-disc, i.e. the conclusion of the sibling chapter's `SurfacePushOffInput`;
* `Work.Collar3D.IsotopyExtension` — the **isotopy extension theorem** for a compactly supported
  isotopy of a locally flat closed set, with support in a prescribed neighbourhood.  Its
  chart-supported case is *proved* (`Work.Collar3D.ambientIsotopyOfChart`), and it is the general
  form that Pardon's surgery consumes;
* `Work.Topology.Classical.AlexanderSphereTheorem` (already recorded in the workspace) — an
  embedded `2`-sphere in `ℝ³` bounds a ball, from which
  `Work.Collar3D.separates_of_alexanderSphereTheorem` derives Jordan–Brouwer separation.

## Non-vacuity

Each of the two hypotheses of `RegularNeighbourhoodCurve` and the hypothesis of
`RegularNeighbourhoodDisc` is satisfiable by the explicit models of this chapter:

* `Work.Collar3D.hasAnnularNeighbourhood_plane` — the unit circle has an annular neighbourhood in
  the plane, and the plane is locally flat at all of its points
  (`Work.Smooth.PushThrough3D.locallyFlatSet_plane`), so the *conclusion* of
  `RegularNeighbourhoodCurve` holds there (`Work.Collar3D.hasCollar_planeCircle`);
* `Work.Collar3D.hasDiscCollar_modelDisc` — the flat model disc has a collar.
-/

open Set

namespace Work.Collar3D

noncomputable section

open Classical

/-! ## Framings, and the two regular-neighbourhood theorems -/

/-- **`γ` has an annular neighbourhood in `F`**: a piece `A ⊆ F` which is an annulus with core
`γ`, exhibited by a chart onto `S¹ × ℝ` carrying `γ` to the core circle.  This is the *framing*
of the curve, and it is the hypothesis of the regular-neighbourhood theorem which is not
automatic: the core circle of a Möbius band has no such neighbourhood. -/
def HasAnnularNeighbourhood (F : Set R3) (γ : ℝ → R3) : Prop :=
  ∃ (A : Set R3) (hA : A ⊆ F) (hγA : ∀ θ : ℝ, γ θ ∈ A) (Ψ : A ≃ₜ Circle × ℝ),
    ∀ θ : ℝ, Ψ ⟨γ θ, hγA θ⟩ = (circlePoint θ, 0)

/-- **The regular-neighbourhood (bicollar) theorem along a curve** — the classical input of the
collar chapter.  A locally flat (tame) surface `F ⊆ ℝ³` has a collar along any simple closed curve
which has an annular neighbourhood in `F`. -/
def RegularNeighbourhoodCurve : Prop :=
  ∀ (F : Set R3) (γ : ℝ → R3), HasAnnularNeighbourhood F γ →
    (∀ x ∈ F, Work.Smooth.PushThrough3D.LocallyFlatSetAt F x) → HasCollar F γ

/-- **The regular-neighbourhood theorem for a disc**: a locally flat embedded disc in `ℝ³` has a
bicollar.  This is the input from which the push-off of the innermost sub-disc is *proved*
(`Work.Collar3D.exists_cap_of_discCollar`). -/
def RegularNeighbourhoodDisc : Prop :=
  ∀ e : C(Disc, R3), Work.Smooth.SphereJordan.LocallyFlat e → HasDiscCollar e

/-- **The isotopy extension theorem for a locally flat closed set.**  A compactly supported
ambient isotopy of a locally flat closed set `A ⊆ ℝ³` extends to an ambient isotopy of `ℝ³` whose
support is contained in a prescribed open neighbourhood of the support of the given isotopy.

The chart-supported case — an isotopy of a *collar* — is proved in this chapter
(`Work.Collar3D.ambientIsotopyOfChart`); the general case is the classical theorem of Edwards and
Kirby, which the cut-and-paste consumes when the isotopy is of a whole embedded disc. -/
def IsotopyExtension : Prop :=
  ∀ (A : Set R3), IsClosed A → (∀ x ∈ A, Work.Smooth.PushThrough3D.LocallyFlatSetAt A x) →
    ∀ (φ : ℝ → A ≃ₜ A) (_ : Continuous fun p : ℝ × A => φ p.1 p.2)
      (_ : Continuous fun p : ℝ × A => (φ p.1).symm p.2) (K : Set A) (hK : IsCompact K)
      (_ : ∀ (t : ℝ) (x : A), x ∉ K → φ t x = x)
      (V : Set R3) (hV : IsOpen V) (hKV : (Subtype.val '' K) ⊆ V),
      ∃ H : AmbientIsotopy, H.supportedIn V ∧
        ∀ (t : ℝ) (x : A), H t (x : R3) = (φ t x : R3)

/-- **A sphere bounds a ball, with a nonempty inside.**  This is Alexander's sphere result in the
form the cut-and-paste consumes: besides the compact inside `K` with frontier the sphere, it
records that the inside is *thick* (has nonempty interior), which is the clause that makes the
separation `Work.Collar3D.separates_of_boundsBall` usable.  (Deriving that clause from the
homeomorphism-to-the-ball clause of `Work.Topology.Classical.AlexanderSphereTheorem` is
invariance of domain in dimension `3`.) -/
def SphereBoundsBall : Prop :=
  ∀ S : Set R3, Work.InnermostDisk.IsEmbeddedSphere S →
    ∃ K : Set R3, IsCompact K ∧ S = frontier K ∧ (interior K).Nonempty

/-- **Jordan–Brouwer separation for a sphere bounding a ball.**  Let `K ⊆ ℝ³` be compact with
frontier `S` and nonempty interior.  Then `S` separates: a point of the interior of `K` and a point
outside `K` cannot be joined by a preconnected set avoiding `S`. -/
theorem separates_of_boundsBall {S K : Set R3} (hK : IsCompact K) (hfront : S = frontier K)
    (hint : (interior K).Nonempty) :
    ∃ x ∈ interior K, ∃ y : R3, y ∉ K ∧ ∀ Z : Set R3, IsPreconnected Z → x ∈ Z → y ∈ Z →
      (Z ∩ S).Nonempty := by
  obtain ⟨x, hx⟩ := hint
  obtain ⟨y, hy⟩ : ∃ y : R3, y ∉ K := by
    by_contra h
    push_neg at h
    exact hK.ne_univ (Set.eq_univ_iff_forall.mpr h)
  refine ⟨x, hx, y, hy, ?_⟩
  intro Z hZ hxZ hyZ
  by_contra hcon
  have hsub : Z ⊆ interior K ∪ Kᶜ := by
    intro z hz
    by_cases hzK : z ∈ K
    · left
      have hzcl : z ∈ closure K := by rwa [hK.isClosed.closure_eq]
      rw [closure_eq_interior_union_frontier] at hzcl
      rcases hzcl with h | h
      · exact h
      · exfalso
        exact hcon ⟨z, hz, by rw [hfront]; exact h⟩
    · exact Or.inr hzK
  have hdisj : Disjoint (interior K) (Kᶜ) :=
    (disjoint_compl_right : Disjoint K Kᶜ).mono_left interior_subset
  rcases hZ.subset_or_subset isOpen_interior hK.isClosed.isOpen_compl hdisj hsub with hcase | hcase
  · exact hy (interior_subset (hcase hyZ))
  · exact hcase hxZ (interior_subset hx)

/-- **A sphere separates `ℝ³`**, from the ball it bounds. -/
theorem separates_of_sphereBoundsBall {S : Set R3} (h : SphereBoundsBall)
    (hS : Work.InnermostDisk.IsEmbeddedSphere S) :
    ∃ K : Set R3, IsCompact K ∧ S = frontier K ∧ (interior K).Nonempty ∧
      ∃ x ∈ interior K, ∃ y : R3, y ∉ K ∧ ∀ Z : Set R3, IsPreconnected Z → x ∈ Z → y ∈ Z →
        (Z ∩ S).Nonempty := by
  obtain ⟨K, hK, hfront, hint⟩ := h S hS
  exact ⟨K, hK, hfront, hint, separates_of_boundsBall hK hfront hint⟩

end

end Work.Collar3D
