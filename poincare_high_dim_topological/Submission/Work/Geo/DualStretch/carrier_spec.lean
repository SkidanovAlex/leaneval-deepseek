import Mathlib
import Submission.Work.Geo.DualStretch.Defs

/-!
# The carrier face of a point

`Work.Geo.DualStretch.carrier P x` is the (unique) face of `P` that contains `x` and is contained in
every face of `P` containing `x`.  Existence of such a face is the content of `carrier_exists`: among
the faces of `P` whose simplex contains `x` (finitely many, and at least one because `x ∈ P.space`),
pick one of minimal cardinality.  If `ρ` is any other face containing `x` then
`x ∈ simp σ ∩ simp ρ = simp (σ ∩ ρ)` (`SimplicialComplex.convexHull_inter_convexHull`), so `σ ∩ ρ`
is a nonempty subface of `σ`; minimality forces `σ ∩ ρ = σ`, i.e. `σ ⊆ ρ`.
-/

open Set
open scoped Classical

namespace Work.Geo.DualStretch

open PL (E Cx)

variable {n : ℕ}

/-- There is a face of `P` containing `x` in its simplex which is contained in every face of `P`
whose simplex contains `x`. -/
theorem carrier_exists (P : PL.Cx n) (hP : P.faces.Finite) {x : PL.E n} (hx : x ∈ P.space) :
    ∃ σ ∈ P.faces, x ∈ PL.simp σ ∧ ∀ ρ ∈ P.faces, x ∈ PL.simp ρ → σ ⊆ ρ := by
  classical
  obtain ⟨S, hSfaces, hSx⟩ : ∃ s ∈ P.faces, x ∈ PL.simp s := by
    rw [Geometry.SimplicialComplex.mem_space_iff] at hx
    exact hx
  have hne : (hP.toFinset.filter fun σ => x ∈ PL.simp σ).Nonempty := by
    refine ⟨S, ?_⟩
    simp only [Finset.mem_filter]
    exact ⟨(Set.Finite.mem_toFinset hP).mpr hSfaces, hSx⟩
  obtain ⟨σ, hσmem, hσmin⟩ := Finset.exists_min_image _ (fun σ => σ.card) hne
  rw [Finset.mem_filter] at hσmem
  obtain ⟨hσfin, hσx⟩ := hσmem
  have hσfaces : σ ∈ P.faces := (Set.Finite.mem_toFinset hP).mp hσfin
  refine ⟨σ, hσfaces, hσx, ?_⟩
  intro ρ hρ hρx
  -- `x` lies in the simplex of the subface `σ ∩ ρ`
  have hxint : x ∈ PL.simp (σ ∩ ρ) := by
    have h1 : x ∈ PL.simp σ ∩ PL.simp ρ := ⟨hσx, hρx⟩
    have h2 : PL.simp σ ∩ PL.simp ρ = PL.simp (σ ∩ ρ) := by
      simp only [PL.simp, Finset.coe_inter]
      exact Geometry.SimplicialComplex.convexHull_inter_convexHull hσfaces hρ
    rwa [h2] at h1
  have hne_int : (σ ∩ ρ).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    rw [hemp] at hxint
    simp [PL.simp] at hxint
  have hfaces_int : σ ∩ ρ ∈ P.faces :=
    Geometry.SimplicialComplex.down_closed hσfaces Finset.inter_subset_left hne_int
  -- `σ ∩ ρ` is again one of the faces whose simplex contains `x`, so minimality applies
  have hmem_int : σ ∩ ρ ∈ hP.toFinset.filter (fun τ => x ∈ PL.simp τ) := by
    simp only [Finset.mem_filter]
    exact ⟨(Set.Finite.mem_toFinset hP).mpr hfaces_int, hxint⟩
  have hcard : σ.card ≤ (σ ∩ ρ).card := hσmin _ hmem_int
  have heq : σ ∩ ρ = σ := Finset.eq_of_subset_of_card_le Finset.inter_subset_left hcard
  exact Finset.inter_eq_left.mp heq

theorem carrier_spec {n : ℕ} (P : PL.Cx n) (hP : P.faces.Finite) {x : PL.E n} (hx : x ∈ P.space) :
    Work.Geo.DualStretch.carrier P x ∈ P.faces ∧
      x ∈ PL.simp (Work.Geo.DualStretch.carrier P x) ∧
      ∀ ρ ∈ P.faces, x ∈ PL.simp ρ → Work.Geo.DualStretch.carrier P x ⊆ ρ := by
  classical
  have h : ∃ σ ∈ P.faces, x ∈ PL.simp σ ∧ ∀ ρ ∈ P.faces, x ∈ PL.simp ρ → σ ⊆ ρ :=
    carrier_exists P hP hx
  have hcar : Work.Geo.DualStretch.carrier P x = h.choose := by
    rw [Work.Geo.DualStretch.carrier]
    exact dite_eq_left h
  rw [hcar]
  exact h.choose_spec

end Work.Geo.DualStretch
