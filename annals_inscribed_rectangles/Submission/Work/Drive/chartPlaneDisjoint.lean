import Mathlib
import Submission.Work.Drive.capSection
import Submission.Work.Drive.classDatum
import Submission.Work.Drive.cappedPlane

/-!
# The whole-plane disjointness of the chart from the cap-cone containment (H4 item (i))

The transport's T6 (`Work.Drive.odd_topBdryMeet_zero_iff_coreSideCounts`) and the whole `hn2`/`hdense`
route need the **whole-plane disjointness**

> `Disjoint (Set.range (diskPlane Q)) (Set.range (rotPresentation Q w))`  for `w ∈ Zc γ`,

i.e. the disjointness of the capped plane `P_0 = diskPlane Q` from its rotation `P_w`.

The workspace proves this for the *paper's* planes: `Work.Drive.cappedPlaneDisjoint` gives
`Disjoint (cappedPlane … 0) (cappedPlane … t)` for `t ∈ Zc γ`, and
`Work.Drive.disjoint_of_subset_cappedPlane` (`classDatum.lean`) transfers it to any `K` with

> `K ⊆ cappedPlane r₀ ρ Ψ Θ μ 0`   (**the containment**).

So the whole-plane disjointness reduces to the *containment of the chart's plane in the paper's capped
plane*, and that splits into two halves:

* the **strip half** — on the annulus `1/2 < ‖z‖ ≤ 1` the chart's value is `stripChart γ hγne 0 (…)`,
  which is a point of the capped plane (`Work.Drive.stripChart_mem_cappedPlane`, proved).  This half is
  a theorem; it is used below without any hypothesis;
* the **cap half** — on the inner disk `‖z‖ ≤ 1/2` the chart's value must lie in the *cap cone*
  `capCone r₀ ρ Ψ Θ 0` of the honest data.  This is a condition on the *construction* of the chart
  (`exists_planeChart` picks the cap freely); it is recorded here as the predicate
  `Work.Drive.CapConeContained`.

## WARNING (session 51, after the child `exists_planeChart_capSection.lean`): the hypothesis is UNSATISFIABLE

`Work.Drive.exists_planeChart_capSection.lean` (module docstring, written by the child H4-L1421)
records a **refutation of the cone route**: the chart's differential at a point of the seam circle
`‖z‖ = 1/2` is forced by the strip values, and the strip's `d`-derivative has a non-zero *tangential*
component, while every point of a cone has `∂_ρ d` parallel to `d/‖d‖`.  Hence **no smooth plane chart
has its cap inside a cone**, i.e. `CapConeContained γ hγne r₀ ρ Ψ Θ Q` is false for every `Q` that
satisfies `IsPlaneChart`.

The declarations below are therefore *correct implications* but a **dead route**: do not build item (i)
on them.  The honest route to the whole-plane disjointness uses the child's chart (whose class map
separates on the cap) plus

* cap–cap: `CapSection` (or the separating property of the class map),
* the two **mixed** cases: the missing ingredient is
  `Work.Drive.isPlaneChart_seam_mem_stripImage` (`Drive/isPlaneChart_seam_mem_stripImage`, delegated),
  i.e. the *image of the inner boundary circle lies in the band* — the corrected form of "the seam is
  ∂M" (compare `Work.Drive.tendsto_stripData_diag`; the chart value on the inner circle is the class of
  the *tangent* chord, not of the degenerate one, so the naive `stripChart … (mk2 a a)` statement is
  false — both reviewers of that statement identified the trap).

The declarations of this file are kept because the *implication* containment ⇒ disjointness is the
correct skeleton, and because a future chart construction may realise the containment in a *different*
capping space (the obstruction is specific to the cone of the honest `cappedPlane`).

## The two consequences proved in this file:

* **`Work.Drive.range_diskPlane_subset_cappedPlane`** — `IsPlaneChart Q` + `CapConeContained` give the
  containment `Set.range (diskPlane Q) ⊆ cappedPlane r₀ ρ Ψ Θ μ 0`;
* **`Work.Drive.disjoint_diskPlane_rotPresentation_of_capCone`** — hence the whole-plane disjointness
  (with the honest polar data of `Work.Drive.exists_strip_cap_disk` as inputs);
* **`Work.Drive.capSection_of_capConeContained`** — `CapConeContained` also *implies* the lead's
  `CapSection` (the cap-cone is rotation-disjoint from itself, `disjoint_capConeImage_rot_capCone`), so
  the cap-cone containment is the strictly stronger construction requirement.
-/

set_option autoImplicit false

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The cap-cone containment of a chart**: the image of its inner disk lies in the cap cone of the
honest data `(r₀, ρ, Ψ, Θ)`.  This is the *cap half* of the containment of the chart's plane in the
paper's capped plane; it is a condition on the construction of the chart (the strip half is a theorem,
`Work.Drive.stripChart_mem_cappedPlane`). -/
def CapConeContained (γ : Circle → ℝ × ℝ) (hγne : ∀ x : Circle, γ x ≠ 0) (r₀ : ℝ)
    (ρ Ψ Θ : ℝ → ℝ) (Q : ℂ → CappingSpace) : Prop :=
  ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → Q z ∈ Quotient.mk'' '' (Sum.inr '' capCone r₀ ρ Ψ Θ 0)

/-- **`CapConeContained` implies `CapSection`.**  The cap cone is disjoint from each of its own
non-trivial rotations (`Work.Drive.disjoint_capConeImage_rot_capCone`), so a chart whose inner disk
lands in the cone meets its own rotations only trivially.  In particular the cap-cone containment is at
least as strong as the lead's `Work.Drive.CapSection` (`capSection.lean`). -/
theorem capSection_of_capConeContained {γ : Circle → ℝ × ℝ} (hγ : Manifold.IsSmoothEmbedding
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
    (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) {Q : ℂ → CappingSpace} {ρ Ψ Θ : ℝ → ℝ}
    (hρc : Continuous ρ) (hΨc : Continuous Ψ) (hΘc : Continuous Θ)
    (hρpos : ∀ t : ℝ, 0 < ρ t) (hpolar : ∀ t : ℝ, polarLift (ρ t, Ψ t) = γ (Circle.exp t))
    (hΨper : ∀ t : ℝ, circleOf (Ψ (t + 2 * Real.pi)) = circleOf (Ψ t))
    (hΘper : ∀ t : ℝ, Θ (t + 2 * Real.pi) = Θ t)
    {r₀ : ℝ} (hr₀pos : 0 < r₀) (hr₀ : ∀ t : ℝ, ρ t ≠ r₀)
    (hcc : CapConeContained γ hγne r₀ ρ Ψ Θ Q) :
    CapSection Q := by
  intro z z' w hz hz' heq
  by_contra hw
  have hdisj := disjoint_capConeImage_rot_capCone hγ hγne hρc hΨc hΘc hρpos hpolar hΨper hΘper
    hr₀pos hr₀ (w := w) hw
  have h1 : Q z ∈ Quotient.mk'' '' (Sum.inr '' capCone r₀ ρ Ψ Θ 0) := hcc z hz
  have h2 : Q z ∈ rotCapping w '' (Quotient.mk'' '' (Sum.inr '' capCone r₀ ρ Ψ Θ 0)) := by
    refine ⟨Q z', hcc z' hz', ?_⟩
    rw [heq]
  exact (Set.disjoint_left.mp hdisj) h1 h2

/-- **The strip values of the chart lie in the capped plane** (`Work.Drive.stripChart_mem_cappedPlane`)
together with the cap-cone containment give the **containment of the chart's plane in the paper's capped
plane**. -/
theorem range_diskPlane_subset_cappedPlane {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ}
    (hμ : ∀ x y : Circle, μ (x, y) = Submission.Configuration.muOrd γ (x, y))
    {r₀ : ℝ} {ρ Ψ Θ : ℝ → ℝ} (hcc : CapConeContained γ hγne r₀ ρ Ψ Θ Q) :
    Set.range (diskPlane Q) ⊆ cappedPlane r₀ ρ Ψ Θ μ 0 := by
  rintro p ⟨y, rfl⟩
  have hy : ‖sqDisk (foldBox y)‖ ≤ 1 :=
    norm_sqDisk_le_one (foldBox y) (foldBox_mem_unitBox y)
  rw [diskPlane_apply]
  by_cases hz : ‖sqDisk (foldBox y)‖ ≤ 1 / 2
  · rw [cappedPlane, rotCapping_zero, Set.image_id]
    exact Set.mem_union_right _ (hcc _ hz)
  · push_neg at hz
    rw [hQ.2.1 _ hz hy]
    exact stripChart_mem_cappedPlane γ hγne hμ 0 _

/-- **The rotation of a presentation is the rotation of the chart's plane.**  `rotPresentation Q w` is
definitionally `diskPlane (fun z => rotCapping w (Q z))`, hence its range is the rotation of the range of
`diskPlane Q` — the form in which the disjointness of `cappedPlaneDisjoint` is stated. -/
lemma range_rotPresentation_eq (Q : ℂ → CappingSpace) (w : UnitAddCircle) :
    Set.range (rotPresentation Q w) = rotCapping w '' Set.range (diskPlane Q) := by
  ext p
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨diskPlane Q y, ⟨y, rfl⟩, rfl⟩
  · rintro ⟨q, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, rfl⟩

/-- **The whole-plane disjointness of the chart, from the cap-cone containment** (H4 item (i)).  With the
honest polar data of the curve and a chart whose inner disk lands in the cap cone, the chart's plane is
disjoint from each of its rotations by a collision-free angle `w ∈ Zc γ`.

This is the hypothesis `hdisj`/the avoidance input of the transport's T6
(`Work.Drive.odd_topBdryMeet_zero_iff_coreSideCounts`) and of `hn2`/`hdense` at the design's planes. -/
theorem disjoint_diskPlane_rotPresentation_of_capCone {γ : Circle → ℝ × ℝ}
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ}
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = Submission.Configuration.muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    {ρ Ψ Θ : ℝ → ℝ} (hρc : Continuous ρ) (hΨc : Continuous Ψ) (hΘc : Continuous Θ)
    (hρpos : ∀ t : ℝ, 0 < ρ t)
    (hpolar : ∀ t : ℝ, polarLift (ρ t, Ψ t) = γ (Circle.exp t))
    (hΨper : ∀ t : ℝ, circleOf (Ψ (t + 2 * Real.pi)) = circleOf (Ψ t))
    (hΘper : ∀ t : ℝ, Θ (t + 2 * Real.pi) = Θ t)
    (hΘclass : ∀ t : ℝ, ((Θ t : ℝ) : UnitAddCircle)
      = tangentDirC γ (Circle.exp t) - 2 • ((Ψ t : ℝ) : UnitAddCircle))
    {r₀ : ℝ} (hr₀pos : 0 < r₀) (hr₀ : ∀ t : ℝ, ρ t ≠ r₀)
    {hγne : ∀ x : Circle, γ x ≠ 0} {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    {hμ : ∀ x y : Circle, μ (x, y) = Submission.Configuration.muOrd γ (x, y)}
    (hcc : CapConeContained γ hγne r₀ ρ Ψ Θ Q)
    {w : UnitAddCircle} (hw : w ∈ Zc γ) :
    Disjoint (Set.range (diskPlane Q)) (Set.range (rotPresentation Q w)) := by
  have hcont := range_diskPlane_subset_cappedPlane (γ := γ) (hγne := hγne) hQ hμ hcc
  have hdisj := disjoint_of_subset_cappedPlane (γ := γ) hγ hμne hμdiag hρc hΨc hΘc hρpos hpolar
    hΨper hΘper hΘclass hr₀pos hr₀ (K := Set.range (diskPlane Q)) hcont hw
  rwa [range_rotPresentation_eq]

/-- **The whole-plane disjointness at two rotations of the chart.**  For `v - u ∈ Zc γ`, the planes
`rotPresentation Q u` and `rotPresentation Q v` are disjoint — the form in which the transport's T6
consumes the disjointness at the two planes of a block of the design's triple
(`Work.Drive.avoidances_of_planeDisjoint`, `transportChartChains.lean`). -/
theorem disjoint_rotPresentation_rotPresentation_of_capCone {γ : Circle → ℝ × ℝ}
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ}
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = Submission.Configuration.muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    {ρ Ψ Θ : ℝ → ℝ} (hρc : Continuous ρ) (hΨc : Continuous Ψ) (hΘc : Continuous Θ)
    (hρpos : ∀ t : ℝ, 0 < ρ t)
    (hpolar : ∀ t : ℝ, polarLift (ρ t, Ψ t) = γ (Circle.exp t))
    (hΨper : ∀ t : ℝ, circleOf (Ψ (t + 2 * Real.pi)) = circleOf (Ψ t))
    (hΘper : ∀ t : ℝ, Θ (t + 2 * Real.pi) = Θ t)
    (hΘclass : ∀ t : ℝ, ((Θ t : ℝ) : UnitAddCircle)
      = tangentDirC γ (Circle.exp t) - 2 • ((Ψ t : ℝ) : UnitAddCircle))
    {r₀ : ℝ} (hr₀pos : 0 < r₀) (hr₀ : ∀ t : ℝ, ρ t ≠ r₀)
    {hγne : ∀ x : Circle, γ x ≠ 0} {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    {hμ : ∀ x y : Circle, μ (x, y) = Submission.Configuration.muOrd γ (x, y)}
    (hcc : CapConeContained γ hγne r₀ ρ Ψ Θ Q)
    {u v : UnitAddCircle} (h : v - u ∈ Zc γ) :
    Disjoint (Set.range (rotPresentation Q u)) (Set.range (rotPresentation Q v)) := by
  have hbase := disjoint_diskPlane_rotPresentation_of_capCone hγ hμne hμdiag hρc hΨc hΘc hρpos
    hpolar hΨper hΘper hΘclass hr₀pos hr₀ hQ (hμ := hμ) hcc h
  rw [range_rotPresentation_eq] at hbase
  rw [Set.disjoint_left] at hbase ⊢
  intro p hp hp'
  rw [range_rotPresentation_eq] at hp
  rw [range_rotPresentation_eq] at hp'
  obtain ⟨a, ha, rfl⟩ := hp
  obtain ⟨b, hb, hbp⟩ := hp'
  have h1 : a = rotCapping (v - u) b := by
    apply rotCapping_injective u
    rw [rotCapping_apply_add, ← hbp]
    congr 1
    abel
  exact hbase ha ⟨b, hb, h1.symm⟩


end

end Work.Drive
