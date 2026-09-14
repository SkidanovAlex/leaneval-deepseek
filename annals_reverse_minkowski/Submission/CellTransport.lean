import Mathlib
import Submission.GaussianMeasure
import Submission.Transport

open Module Real Submission.Voronoi
open scoped Real InnerProductSpace RealInnerProductSpace Pointwise
set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Voronoi-cell transport under (linear) isometries ([C]-block foundation)

The boundary case of `gamma_stable_of_two_le` must compare Voronoi cells of a lattice and of
its transport across the isometry `realSpanIso`.  This module records the generic facts:

* `latticeMap e ℒ` — the image of a lattice `ℒ ≤ X` under a linear isometry `e : X ≃ₗᵢ Y`
  (a lattice in `Y`);
* `mem_latticeMap` — membership in the transported lattice;
* `voronoi_map` — an isometry carries the Voronoi cell of `ℒ` onto the Voronoi cell of
  `latticeMap e ℒ`:
  `voronoi (latticeMap e ℒ) = e '' voronoi ℒ`
  (from the inner-product and norm preservation of `e`).

Together with `GaussianMeasure.gammaMassGen_transport` this lets Gaussian masses of Voronoi
cells be moved between a real span and the standard space (and later between direct-sum
factors, in the fundamental-product step).
-/

namespace Submission.CellTransport

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- The image of a lattice under a (linear) isometry: a lattice in the codomain. -/
noncomputable def latticeMap (e : X ≃ₗᵢ[ℝ] Y) (ℒ : Submodule ℤ X) : Submodule ℤ Y :=
  Submodule.map ((e.toLinearEquiv.toLinearMap).restrictScalars ℤ) ℒ

/-- Membership in the transported lattice. -/
lemma mem_latticeMap (e : X ≃ₗᵢ[ℝ] Y) (ℒ : Submodule ℤ X) (z : Y) :
    z ∈ latticeMap e ℒ ↔ ∃ y : X, y ∈ ℒ ∧ (e : X → Y) y = z := by
  rw [latticeMap]
  exact Submodule.mem_map

/-- An isometry carries the Voronoi cell of a lattice onto the Voronoi cell of its image:
`voronoi (latticeMap e ℒ) = e '' voronoi ℒ`. -/
lemma voronoi_map (e : X ≃ₗᵢ[ℝ] Y) (ℒ : Submodule ℤ X) :
    voronoi (latticeMap e ℒ) = e '' voronoi ℒ := by
  ext z
  constructor
  · intro hz
    let x : X := (e.symm) z
    have hmem : x ∈ voronoi ℒ := by
      rw [mem_voronoi]
      intro y
      have hw : (e (y : X)) ∈ latticeMap e ℒ := by
        rw [latticeMap]
        exact Submodule.mem_map.mpr ⟨(y : X), y.2, by simp⟩
      have h := hz ⟨(e (y : X)), hw⟩
      have hz' : z = e x := by
        dsimp [x]
        exact (e.apply_symm_apply z).symm
      rw [hz'] at h
      rw [e.inner_map_map] at h
      rw [e.norm_map] at h
      exact h
    refine ⟨x, hmem, ?_⟩
    dsimp [x]
    exact (e.apply_symm_apply z)
  · rintro ⟨x, hx, hzx⟩
    rw [← hzx]
    rw [mem_voronoi]
    intro w
    have hwmem : (w : Y) ∈ latticeMap e ℒ := w.2
    rcases (mem_latticeMap e ℒ (w : Y)).1 hwmem with ⟨y, hy, hwy⟩
    have hxy : ⟪x, y⟫_ℝ ≤ ‖y‖ ^ 2 / 2 := by
      have hx' := hx
      rw [mem_voronoi] at hx'
      exact hx' ⟨y, hy⟩
    calc
      ⟪e x, (w : Y)⟫_ℝ = ⟪e x, e y⟫_ℝ := by rw [hwy]
      _ = ⟪x, y⟫_ℝ := by rw [e.inner_map_map]
      _ ≤ ‖y‖ ^ 2 / 2 := hxy
      _ = ‖e y‖ ^ 2 / 2 := by rw [e.norm_map]
      _ = ‖(w : Y)‖ ^ 2 / 2 := by rw [hwy]

end Submission.CellTransport


/-! ## Ambient-cell cylinder (in-span Voronoi cell)

For a lattice `ℒ` in an ambient `E` with `W := realSpan ℒ`, the ambient Voronoi cell is the
cylinder over the in-span cell:
`voronoi ℒ = (voronoi ℒ ∩ W) +ᵥ W⊥`.
Membership in the cell only tests inner products against lattice vectors (all inside `W`), and
the `W⊥`-component contributes nothing to those inner products.  This is the fact that lets the
boundary case compare the ambient cell of a sublattice with its in-span (transported) cell.
-/

section Cylinder

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

/-- The ambient Voronoi cell of a lattice is the cylinder over its in-span cell:
`voronoi ℒ = (voronoi ℒ ∩ W) +ᵥ W⊥` where `W := realSpan ℒ`. -/
lemma voronoi_cylinder (ℒ : Submodule ℤ E) :
    voronoi ℒ = (voronoi ℒ ∩ (Submission.QuotientLattice.realSpan ℒ : Set E)) +ᵥ
      ((Submission.QuotientLattice.realSpan ℒ)ᗮ : Set E) := by
  ext x
  constructor
  · intro hx
    haveI hW : (Submission.QuotientLattice.realSpan ℒ).HasOrthogonalProjection := by infer_instance
    have hdec : ∃ w ∈ (Submission.QuotientLattice.realSpan ℒ : Set E),
        x - w ∈ (Submission.QuotientLattice.realSpan ℒ)ᗮ := by
      exact (inferInstance :
        (Submission.QuotientLattice.realSpan ℒ).HasOrthogonalProjection).exists_orthogonal x
    rcases hdec with ⟨w, hwW, hwu⟩
    have hwcell : w ∈ voronoi ℒ := by
      rw [mem_voronoi]
      intro y
      have hyW : ((y : ℒ) : E) ∈ (Submission.QuotientLattice.realSpan ℒ : Set E) :=
        Submission.QuotientLattice.mem_realSpan (ℒ := ℒ) (x := (((y : ℒ) : E))) y.2
      have hu0 : ⟪x - w, ((y : ℒ) : E)⟫_ℝ = 0 := by
        exact (Submodule.mem_orthogonal' (Submission.QuotientLattice.realSpan ℒ) (x - w)).1
          hwu ((y : ℒ) : E) hyW
      calc
        ⟪w, ((y : ℒ) : E)⟫_ℝ = ⟪x, ((y : ℒ) : E)⟫_ℝ - ⟪x - w, ((y : ℒ) : E)⟫_ℝ := by
            have hsplit : ⟪x, ((y : ℒ) : E)⟫_ℝ =
                ⟪w, ((y : ℒ) : E)⟫_ℝ + ⟪x - w, ((y : ℒ) : E)⟫_ℝ := by
              calc
                ⟪x, ((y : ℒ) : E)⟫_ℝ = ⟪w + (x - w), ((y : ℒ) : E)⟫_ℝ := by
                      congr 1
                      abel
                _ = ⟪w, ((y : ℒ) : E)⟫_ℝ + ⟪x - w, ((y : ℒ) : E)⟫_ℝ := by
                      rw [inner_add_left]
            rw [hsplit]
            ring
        _ = ⟪x, ((y : ℒ) : E)⟫_ℝ := by rw [hu0]; ring
        _ ≤ ‖((y : ℒ) : E)‖ ^ 2 / 2 := by
            have hx' := hx
            rw [mem_voronoi] at hx'
            exact hx' y
    refine ⟨w, ⟨hwcell, hwW⟩, x - w, hwu, ?_⟩
    abel
  · intro hxmem
    rcases hxmem with ⟨a, ha, b, hb, hxab⟩
    rw [mem_voronoi]
    intro y
    have hb0 : ⟪b, ((y : ℒ) : E)⟫_ℝ = 0 := by
      have hyW : ((y : ℒ) : E) ∈ (Submission.QuotientLattice.realSpan ℒ : Set E) :=
        Submission.QuotientLattice.mem_realSpan (ℒ := ℒ) (x := (((y : ℒ) : E))) y.2
      have hinner : ⟪((y : ℒ) : E), b⟫_ℝ = 0 := by
        exact (Submodule.mem_orthogonal (Submission.QuotientLattice.realSpan ℒ) b).1
          hb ((y : ℒ) : E) hyW
      rw [real_inner_comm]
      exact hinner
    calc
      ⟪x, ((y : ℒ) : E)⟫_ℝ = ⟪a + b, ((y : ℒ) : E)⟫_ℝ := by rw [← hxab]
      _ = ⟪a, ((y : ℒ) : E)⟫_ℝ + ⟪b, ((y : ℒ) : E)⟫_ℝ := by rw [inner_add_left]
      _ = ⟪a, ((y : ℒ) : E)⟫_ℝ := by rw [hb0]; ring
      _ ≤ ‖((y : ℒ) : E)‖ ^ 2 / 2 := by
          have ha' := ha.1
          rw [mem_voronoi] at ha'
          exact ha' y

end Cylinder
