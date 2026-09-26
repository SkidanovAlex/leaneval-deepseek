import Submission.Work.InnermostDisk.Packaging
import Submission.Work.InnermostDisk.not_isEssential_of_range_subset_isSimple
import Submission.Work.InnermostDisk.not_isEssential_of_range_subset_covered

/-!
# The innermost selection, from the PL slicing of a sphere

Pardon's first innermost step (`InnermostDiscInput`) is the conjunction of three classical
topological facts about a PL sphere `S` transverse to the PL surface `F`:

* **transversality**: `S ∩ F` is a finite disjoint union of simple closed curves of `F`
  (`SphereSlicing.c`, with `simple`, `disjoint`, `mem`, `covers`);
* **Jordan–Schoenflies in `S²`**: each of those curves bounds a disc inside `S`
  (`SphereSlicing.disc`);
* **nesting**: the discs are nested, so that a component of `S ∩ F` lying inside the disc of
  another has a smaller rank (`SphereSlicing.rank`, `inside`), and a component meeting the
  interior of a disc is contained in it (`inside_subset`).

Given those, the *innermost selection* is pure combinatorics, and it is **proved** here:

* `Work.InnermostDisk.SphereSlicing.exists_min_essential` — if `S` contains an essential loop then
  some curve of the slicing is essential, and there is an essential one of minimal rank;
* `Work.InnermostDisk.SphereSlicing.innermostDiscOfMinRank` — the disc of such a minimal essential
  curve meets `F` in its interior only along curves of **smaller** rank, which by minimality are
  all inessential: this is the datum `InnermostDisc`;
* `Work.InnermostDisk.SphereSlicing.innermostDiscInput_of_slicing` — hence the slicing implies
  Pardon's first input.

The auxiliary step "a loop whose image lies in the image of an inessential *simple* loop is
inessential" (`not_isEssential_of_range_subset_isSimple`) is what transfers essentiality of the
given loop to one of the curves of the slicing; it is where simplicity of the slicing curves is
used.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology

namespace Work.InnermostDisk

noncomputable section

/-- A **PL slicing of a sphere `S` by the surface `F`**: the components of `S ∩ F` (finitely many
pairwise disjoint simple closed curves of `F`, contained in `S`, covering every loop of `F` inside
`S`), together with the disc that each of them bounds inside `S`, nested by a rank function.

This is exactly the output of the classical description of a PL sphere transverse to a PL surface;
the innermost selection of Pardon's first step is then proved from it. -/
structure SphereSlicing (P : ParamTorus) (S : Set R3) where
  /-- the index type of the components of `S ∩ F` -/
  ι : Type
  /-- finitely many components -/
  fintype : Fintype ι
  /-- the components -/
  c : ι → ClosedCurve P
  /-- each component is an embedded loop -/
  simple : ∀ i : ι, IsSimple P (c i)
  /-- distinct components are disjoint -/
  disjoint : Pairwise fun i j => Disjoint (Set.range (c i).γ) (Set.range (c j).γ)
  /-- they lie in `S` -/
  mem : ∀ i : ι, ∀ t : ℝ, (c i).γ t ∈ S
  /-- every loop of `F` contained in `S` lies in one component -/
  covers : ∀ γ : ClosedCurve P, (∀ t : ℝ, γ.γ t ∈ S) →
    ∃ i : ι, Set.range γ.γ ⊆ Set.range (c i).γ
  /-- the disc inside `S` bounded by a component -/
  disc : ι → C(Disc, R3)
  /-- the disc is embedded -/
  disc_inj : ∀ i : ι, Function.Injective (disc i)
  /-- its boundary is the component -/
  disc_boundary : ∀ i : ι, ∀ θ : ℝ, disc i (circlePoint θ) = (c i).γ θ
  /-- the disc lies in `S` -/
  disc_mem : ∀ i : ι, ∀ z : Disc, disc i z ∈ S
  /-- the nesting rank -/
  rank : ι → ℕ
  /-- a component meeting the interior of the disc of `i` has smaller rank -/
  inside : ∀ i j : ι, (∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ disc i z ∈ Set.range (c j).γ) →
    rank j < rank i
  /-- such a component is contained in the disc -/
  inside_subset : ∀ i j : ι, (∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ disc i z ∈ Set.range (c j).γ) →
    Set.range (c j).γ ⊆ Set.range (disc i)
  /-- the interior of each disc meets `F` only along the components -/
  covers_interior : ∀ i : ι, ∀ z : Disc, ‖(z : ℂ)‖ < 1 → disc i z ∈ P.carrier →
    ∃ j : ι, disc i z ∈ Set.range (c j).γ

attribute [instance] SphereSlicing.fintype

namespace SphereSlicing

variable {P : ParamTorus} {S : Set R3}

/-- **Innermost selection.**  If `S` contains an essential loop of `F`, then one of the components
`c i` of the slicing is essential, and among the essential ones there is one of minimal rank. -/
theorem exists_min_essential (h : SphereSlicing P S)
    (hS : ∃ γ : ClosedCurve P, IsEssential P γ ∧ ∀ t : ℝ, γ.γ t ∈ S) :
    ∃ i : h.ι, IsEssential P (h.c i) ∧ ∀ j : h.ι, IsEssential P (h.c j) → ¬ h.rank j < h.rank i := by
  classical
  obtain ⟨γ, hγess, hγS⟩ := hS
  obtain ⟨i₀, hi₀⟩ := h.covers γ hγS
  have hess₀ : IsEssential P (h.c i₀) := by
    by_contra hne
    exact absurd hγess (not_isEssential_of_range_subset_isSimple (h.simple i₀) hi₀ hne)
  obtain ⟨i, hi_mem, hmin⟩ :=
    Finset.exists_min_image (Finset.univ.filter fun i : h.ι => IsEssential P (h.c i)) h.rank
      ⟨i₀, by simp [hess₀]⟩
  exact ⟨i, by simpa using hi_mem, fun j hj hlt => absurd (hmin j (by simp [hj])) (not_le.mpr hlt)⟩

/-- The `InnermostDisc` obtained from a curve of the slicing which is essential and of minimal rank
among the essential curves: the curves of `F` in the interior of its disc all have smaller rank,
hence are inessential. -/
def innermostDiscOfMinRank (h : SphereSlicing P S) (i : h.ι)
    (hess : IsEssential P (h.c i))
    (hmin : ∀ j : h.ι, IsEssential P (h.c j) → ¬ h.rank j < h.rank i) : InnermostDisc P S where
  α := h.c i
  simple := h.simple i
  essential := hess
  mem := h.mem i
  e := h.disc i
  inj := h.disc_inj i
  boundary := h.disc_boundary i
  e_mem := h.disc_mem i
  ι := {j : h.ι // ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ h.disc i z ∈ Set.range (h.c j).γ}
  fintype := by classical infer_instance
  curves := fun j => h.c j.1
  curves_simple := fun j => h.simple j.1
  curves_inessential := fun j => by
    by_contra hne
    exact hmin j.1 hne (h.inside i j.1 j.2)
  curves_disjoint := fun j j' hne =>
    h.disjoint fun hval => hne (Subtype.ext hval)
  curves_subset := fun j => h.inside_subset i j.1 j.2
  covers := fun z hz hc => by
    obtain ⟨j, hj⟩ := h.covers_interior i z hz hc
    exact ⟨⟨j, z, hz, hj⟩, hj⟩

/-- **Pardon's first innermost step, from a slicing of the sphere.** -/
theorem innermostDiscInput_of_slicing (h : SphereSlicing P S) : InnermostDiscInput P S := by
  intro hS
  obtain ⟨i, hess, hmin⟩ := h.exists_min_essential hS
  exact ⟨h.innermostDiscOfMinRank i hess hmin⟩

end SphereSlicing

/-! ## The packaged PL input -/

/-- **The classical PL input of Pardon's first step**: every embedded sphere admits a slicing of
`F` by its components (transversality), each bounding a disc inside the sphere
(Jordan–Schoenflies), nested (so that an innermost one can be chosen). -/
def SphereSlicingInput (P : ParamTorus) : Prop :=
  ∀ S : Set R3, IsEmbeddedSphere S → Nonempty (SphereSlicing P S)

/-- **The complete classical input of Pardon's Lemma**: the PL slicing of spheres by `F`, and the
cut-and-paste step of the second innermost argument.  Everything else in Pardon's Lemma is proved
in this chapter. -/
def PardonPLInput (P : ParamTorus) : Prop :=
  SphereSlicingInput P ∧ CleansDiscs P

/-- The PL input gives Pardon's first innermost input at every embedded sphere. -/
theorem innermostDiscInput_of_slicingInput {P : ParamTorus} {S : Set R3}
    (h : SphereSlicingInput P) (hS : IsEmbeddedSphere S) : InnermostDiscInput P S :=
  (h S hS).some.innermostDiscInput_of_slicing

/-- The PL input implies the packaged two-factor input `PardonInnermostInput`. -/
theorem pardonInnermostInput_of_PLInput {P : ParamTorus} (h : PardonPLInput P) :
    PardonInnermostInput P :=
  ⟨fun S hS => innermostDiscInput_of_slicingInput h.1 hS, h.2⟩

/-- **Pardon's Lemma 4.2 from the complete PL input.** -/
theorem mustbeinessential_of_PLInput (P : ParamTorus) (β : ClosedCurve P) (S : Set R3)
    (hS : IsEmbeddedSphere S) (h : PardonPLInput P)
    (hSβ : Set.encard (Set.range β.γ ∩ S) < pardonsI P β) :
    ∀ α : ClosedCurve P, (∀ t : ℝ, α.γ t ∈ S) → ¬ IsEssential P α :=
  mustbeinessential_of_pardonInnermostInput P β S hS
    (pardonInnermostInput_of_PLInput h) hSβ

/-- **Pardon's Lemma 4.2 in component form, from the complete PL input.** -/
theorem not_isEssential_components_of_PLInput (P : ParamTorus) (β : ClosedCurve P) (S : Set R3)
    {ι : Type} [Fintype ι] (c : ι → ClosedCurve P) (hS : IsEmbeddedSphere S)
    (h : PardonPLInput P) (hSβ : Set.encard (Set.range β.γ ∩ S) < pardonsI P β)
    (hcS : ∀ i : ι, ∀ t : ℝ, (c i).γ t ∈ S) : ∀ i : ι, ¬ IsEssential P (c i) :=
  fun i => mustbeinessential_of_PLInput P β S hS h hSβ (c i) (hcS i)

end

end Work.InnermostDisk
