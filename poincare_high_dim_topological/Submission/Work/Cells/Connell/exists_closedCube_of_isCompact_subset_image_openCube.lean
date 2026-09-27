import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Cells.Connell.exists_closedCube_subset_of_isCompact_subset_openCube

/-!
# Shrinking a compact subset of a cube chart into a closed sub-cube

A `PL.CubeChart n M` is an open embedding of the open unit cube `PL.openCube 1 ⊆ ℝⁿ` into `M`.
Consequently it restricts to a homeomorphism from the open cube onto its image `W`, and a
compact subset `K ⊆ W` pulls back to a compact subset of `PL.openCube 1`; shrinking that to a
closed sub-cube `PL.closedCube α` (via
`exists_closedCube_subset_of_isCompact_subset_openCube`) and pushing forward again gives the
statement: a compact `K` inside the image of the open unit cube lies inside the image of some
closed sub-cube `PL.closedCube α`, `0 < α < 1`.

This is the form in which the "chart cubes" of Connell's argument are chosen.
-/

open Set Metric

namespace Work.Cells.Connell

theorem exists_closedCube_of_isCompact_subset_image_openCube {n : ℕ} {M : Type*}
    [TopologicalSpace M] (c : PL.CubeChart n M) {K : Set M} (hK : IsCompact K)
    (hKW : K ⊆ c.toFun '' PL.openCube (n := n) 1) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧ K ⊆ c.toFun '' PL.closedCube α := by
  let U : Set (PL.E n) := PL.openCube (n := n) 1
  let φ : ↥U → M := fun x => c.toFun x.1
  have hemb : Topology.IsEmbedding φ := c.emb.toIsEmbedding
  have hrange : Set.range φ = c.toFun '' PL.openCube (n := n) 1 := by
    ext y; constructor
    · rintro ⟨x, rfl⟩; exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨w, hw, rfl⟩; exact ⟨⟨w, hw⟩, rfl⟩
  have hKW' : K ⊆ Set.range φ := by rw [hrange]; exact hKW
  -- the chart, viewed as a homeomorphism onto its image, and its inverse on `K`
  let e : ↥U ≃ₜ ↥(Set.range φ) := hemb.toHomeomorph
  have he_coe : ∀ x : ↥U, (e x : M) = c.toFun x.1 :=
    fun x => Topology.IsEmbedding.toHomeomorph_apply_coe hemb x
  let Ψ : ↥K → PL.E n := fun y => (e.symm ⟨y.1, hKW' y.2⟩ : ↥U).1
  have hΨcont : Continuous Ψ := by
    have h1 : Continuous (fun y : ↥K => (⟨y.1, hKW' y.2⟩ : ↥(Set.range φ))) :=
      continuous_subtype_val.subtype_mk (fun y => hKW' y.2)
    have h2 : Continuous (fun y : ↥K => (e.symm ⟨y.1, hKW' y.2⟩ : ↥U)) :=
      e.symm.continuous.comp h1
    exact continuous_subtype_val.comp h2
  -- `Ψ '' K` is a compact subset of the open unit cube
  have hKc : IsCompact (univ : Set ↥K) := isCompact_iff_isCompact_univ.mp hK
  have hΨK : IsCompact (Ψ '' univ) := hKc.image hΨcont
  have hΨsub : Ψ '' univ ⊆ PL.openCube (n := n) 1 := by
    rintro x ⟨y, -, rfl⟩
    exact (e.symm ⟨y.1, hKW' y.2⟩ : ↥U).2
  obtain ⟨α, hα0, hα1, hαsub⟩ :=
    exists_closedCube_subset_of_isCompact_subset_openCube hΨK hΨsub
  refine ⟨α, hα0, hα1, ?_⟩
  intro y hyK
  have hmem : Ψ ⟨y, hyK⟩ ∈ PL.closedCube α :=
    hαsub (mem_image_of_mem Ψ (mem_univ _))
  refine ⟨Ψ ⟨y, hyK⟩, hmem, ?_⟩
  have hcoe : (e (e.symm ⟨y, hKW' hyK⟩) : M) = c.toFun (e.symm ⟨y, hKW' hyK⟩).1 :=
    he_coe _
  rw [e.apply_symm_apply] at hcoe
  exact hcoe.symm

end Work.Cells.Connell
