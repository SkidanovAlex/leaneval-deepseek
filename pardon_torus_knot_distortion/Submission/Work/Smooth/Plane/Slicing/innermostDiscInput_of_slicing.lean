import Mathlib
import Submission.Work.Smooth.Plane.Slicing
import Submission.Work.Smooth.Plane.Slicing.not_isEssential_of_range_subset_arc
import Submission.Work.InnermostDisk.All

namespace Work.Smooth.Plane.Slicing

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-- **The innermost selection for a planar slicing**, in the form of the auxiliary data: if `D`
contains an essential loop of `F`, then some closed component of the slicing is essential, and
among the essential components there is one of minimal rank. -/
theorem exists_min_essential_of_slicing {P : Work.CoreTopology.ParamTorus} {D : Set R3}
    (h : Work.Smooth.Plane.PlaneSlicing P D)
    (hD : ∃ γ : Work.CoreTopology.ClosedCurve P, Work.CoreTopology.IsEssential P γ ∧
      ∀ t : ℝ, γ.γ t ∈ D) :
    ∃ i : h.ι, Work.CoreTopology.IsEssential P (h.c i) ∧
      ∀ j : h.ι, Work.CoreTopology.IsEssential P (h.c j) → ¬ h.rank j < h.rank i := by
  classical
  obtain ⟨γ, hγess, hγD⟩ := hD
  have hkey : ∃ i : h.ι, Work.CoreTopology.IsEssential P (h.c i) := by
    rcases h.covers γ hγD with ⟨i, hi⟩ | ⟨j, hj⟩
    · exact ⟨i, by
        by_contra hne
        exact absurd hγess
          (Work.InnermostDisk.not_isEssential_of_range_subset_isSimple (h.simple i) hi hne)⟩
    · exact absurd hγess
        (not_isEssential_of_range_subset_arc (h.a_inj j) (h.a_surface j) (fun t => hj ⟨t, rfl⟩))
  obtain ⟨i, hi_mem, hmin⟩ :=
    Finset.exists_min_image (Finset.univ.filter fun i : h.ι => Work.CoreTopology.IsEssential P (h.c i))
      h.rank (by obtain ⟨i, hi⟩ := hkey; exact ⟨i, by simp [hi]⟩)
  exact ⟨i, by simpa using hi_mem,
    fun j hj hlt => absurd (hmin j (by simp [hj])) (not_le.mpr hlt)⟩

/-- **The innermost disc of a planar slicing.**  An essential closed component `h.c i` of minimal
rank among the essential ones bounds a disc inside `D` whose interior meets `F` only along closed
components; by minimality of the rank, all those components are inessential in `F`.  This is
Pardon's datum `Work.InnermostDisk.InnermostDisc P D`. -/
def innermostDiscOfMinRank_of_slicing {P : Work.CoreTopology.ParamTorus} {D : Set R3}
    (h : Work.Smooth.Plane.PlaneSlicing P D) (i : h.ι)
    (hess : Work.CoreTopology.IsEssential P (h.c i))
    (hmin : ∀ j : h.ι, Work.CoreTopology.IsEssential P (h.c j) → ¬ h.rank j < h.rank i) :
    Work.InnermostDisk.InnermostDisc P D where
  α := h.c i
  simple := h.simple i
  essential := hess
  mem := h.mem i
  e := h.disc i
  inj := h.disc_inj i
  boundary := h.disc_boundary i
  e_mem := h.disc_mem i
  ι := {j : h.ι // ∃ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 ∧
    h.disc i z ∈ Set.range (h.c j).γ}
  fintype := by classical infer_instance
  curves := fun j => h.c j.1
  curves_simple := fun j => h.simple j.1
  curves_inessential := fun j => by
    by_contra hne
    exact hmin j.1 hne (h.inside i j.1 j.2)
  curves_disjoint := fun j j' hne => h.disjoint fun hval => hne (Subtype.ext hval)
  curves_subset := fun j => h.inside_subset i j.1 j.2
  covers := fun z hz hc => by
    obtain ⟨j, hj⟩ := h.covers_interior i z hz hc
    exact ⟨⟨j, z, hz, hj⟩, hj⟩

/-- **Pardon's first innermost step for a convex planar slice.**

Let `h : Work.Smooth.Plane.PlaneSlicing P D` be a planar slicing of the convex planar region `D` by
the surface `F = P.carrier`: the components of `F ∩ D` are the finitely many pairwise disjoint
simple closed curves `h.c i` together with the finitely many arcs `h.a j`; each closed component
`h.c i` bounds a disc `h.disc i` inside `D`; the disc family is nested (`h.rank`, `h.inside`,
`h.inside_subset`); the interior of a disc meets `F` only along the closed components
(`h.covers_interior`); and every loop of `F` inside `D` lies on one of the pieces (`h.covers`).

Then, if `D` contains an essential loop of `F`, one of the closed components is an *innermost*
essential loop: Pardon's datum `Work.InnermostDisk.InnermostDisc P D`, i.e. an essential simple loop
`α = h.c i` bounding a disc inside `D` whose interior meets `F` only in inessential closed curves of
`F`.  Equivalently: the statement that `D` satisfies Pardon's first innermost input,
`Work.InnermostDisk.InnermostDiscInput P D`.

Proof sketch (mirroring `Work.InnermostDisk.SphereSlicing.innermostDiscInput_of_slicing` in
`Submission/Work/InnermostDisk/Slicing.lean`, which does the same for a sphere):

* an essential loop `γ` of `F` with image in `D` lies on one of the pieces (`h.covers`); if that
  piece is an arc `h.a j`, then `γ` is inessential by
  `Work.Smooth.Plane.not_isEssential_of_range_subset_arc` (using `h.a_inj` and `h.a_surface`), a
  contradiction; so `γ` lies on a closed component `h.c i`, and that component is essential
  (`Work.InnermostDisk.not_isEssential_of_range_subset_isSimple`, contrapositive);
* by `Finset.exists_min_image` applied to the finite set of essential components, choose an
  essential closed component `h.c i` of minimal rank;
* build the `Work.InnermostDisk.InnermostDisc P D` with `α := h.c i`, `e := h.disc i`, index type
  `{j : h.ι // ∃ z, ‖(z : ℂ)‖ < 1 ∧ h.disc i z ∈ Set.range (h.c j).γ}`, `curves := h.c j`,
  `curves_inessential` from minimality of the rank (an essential `j` inside the disc of `i` would
  have smaller rank by `h.inside`), `curves_subset` from `h.inside_subset`, `covers` from
  `h.covers_interior`, and all remaining fields from the datum (`h.simple`, `h.mem`,
  `h.disc_inj`, `h.disc_boundary`, `h.disc_mem`, `h.disjoint`). -/
theorem innermostDiscInput_of_slicing {P : Work.CoreTopology.ParamTorus} {D : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (h : Work.Smooth.Plane.PlaneSlicing P D) :
    Work.InnermostDisk.InnermostDiscInput P D := by
  intro hD
  obtain ⟨i, hess, hmin⟩ := exists_min_essential_of_slicing h hD
  exact ⟨innermostDiscOfMinRank_of_slicing h i hess hmin⟩

end

end Work.Smooth.Plane.Slicing
