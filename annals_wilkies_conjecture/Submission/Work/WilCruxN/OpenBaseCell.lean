/-
  `Work.WilCruxN` — the Baire step of node N1.

  If a definable set `Z ⊆ ℝ^{m+N}` meets every fibre of the nonempty open `O ⊆ ℝ^m` over the
  open `U`, then some *open* cell `C₀` of the projected decomposition of `ℝ^m` meets `O`.

  The proof is the sharp-o-minimal substitute for Baire: the projection of a `Z`-cell is a cell
  of the projected decomposition, and by `Work.WilG1.Cell.exists_thick_cell` the union of a
  subfamily of the cells of a cylindrical decomposition with nonempty interior contains a cell
  with nonempty interior; that cell is then open (`isOpen_of_isCell_interior_nonempty`).

  This is a clean re-proof of the node `Work.WilCrux.exists_open_base_cell`, stated against the
  same vocabulary (`Work.WilCrux.SheetDefs`, `Work.WilCrux.SheetAux`).
-/
import Mathlib
import Submission.Work.WilCrux.SheetDefs
import Submission.Work.WilCrux.SheetAux
import Submission.Work.WilCrux.isOpen_of_isCell_interior_nonempty
import Submission.Work.WilG1.Cell.thin_union

set_option autoImplicit false
noncomputable section
open Classical
open scoped Topology

namespace Work.WilCruxN

open WilkiesDesign

/-- **The open base cell.**  Let `C` be a cylindrical decomposition of `ℝ^{m+N}` compatible with
`Z`, let `O ⊆ ℝ^m` be open nonempty and suppose that every `w ∈ O` carries a point of `Z` over
the open `U` (only the existence of the parameter point is used).  Then some member `C₀` of the
projected decomposition `projDecomp m N C` is open and meets `O`. -/
theorem OpenBaseCell {m N : ℕ} {C : Finset (Set (Fin (m + N) → ℝ))}
    (hdec : WilkiesDesign.IsCylDecomp (m + N) C) {Z : Set (Fin (m + N) → ℝ)}
    (hcomp : ∀ κ ∈ C, κ ⊆ Z ∨ Disjoint κ Z)
    {O : Set (Fin m → ℝ)} (hO : IsOpen O) (hOne : O.Nonempty)
    (hfib : ∀ w ∈ O, ∃ p ∈ Z, (fun i : Fin m => p (Fin.castAdd N i)) = w) :
    ∃ C₀ ∈ Work.WilCrux.projDecomp m N C, IsOpen C₀ ∧ (C₀ ∩ O).Nonempty := by
  classical
  have hdecD : WilkiesDesign.IsCylDecomp m (Work.WilCrux.projDecomp m N C) :=
    Work.WilCrux.isCylDecomp_projDecomp hdec
  -- the projections of the `Z`-cells that meet `O`
  set T : Finset (Set (Fin m → ℝ)) :=
    ((C.filter (fun κ => κ ⊆ Z)).image (fun κ => Work.WilCrux.projOver m N κ)).filter
      (fun σ => (σ ∩ O).Nonempty) with hT
  have hTsub : T ⊆ Work.WilCrux.projDecomp m N C := by
    intro σ hσ
    rw [hT, Finset.mem_filter] at hσ
    obtain ⟨κ, hκ, rfl⟩ := Finset.mem_image.mp hσ.1
    exact Work.WilCrux.projOver_mem_projDecomp (Finset.mem_filter.mp hκ).1
  -- the union of `T` covers `O`
  have hcover : O ⊆ ⋃₀ (T : Set (Set (Fin m → ℝ))) := by
    intro w hw
    obtain ⟨p, hpZ, hpw⟩ := hfib w hw
    obtain ⟨κ, hκC, hpκ⟩ := Work.WilCrux.cylDecomp_cover hdec p
    have hκZ : κ ⊆ Z := by
      rcases hcomp κ hκC with h | hd
      · exact h
      · exact absurd hpZ (Set.disjoint_left.mp hd hpκ)
    have hmem : Work.WilCrux.projOver m N κ ∈ T := by
      rw [hT, Finset.mem_filter]
      refine ⟨Finset.mem_image.mpr ⟨κ, ?_, rfl⟩, ?_⟩
      · rw [Finset.mem_filter]; exact ⟨hκC, hκZ⟩
      · exact ⟨w, by rw [← hpw]; exact Work.WilCrux.mem_projOver hpκ, hw⟩
    exact Set.mem_sUnion.mpr
      ⟨Work.WilCrux.projOver m N κ, hmem, by rw [← hpw]; exact Work.WilCrux.mem_projOver hpκ⟩
  -- hence the union has nonempty interior
  obtain ⟨w₀, hw₀⟩ := hOne
  have hne : (interior (⋃₀ (T : Set (Set (Fin m → ℝ))))).Nonempty :=
    ⟨w₀, interior_mono hcover (by rw [hO.interior_eq]; exact hw₀)⟩
  -- a cell with nonempty interior
  obtain ⟨C₀, hC₀T, hC₀int⟩ :=
    Work.WilG1.Cell.exists_thick_cell m (Work.WilCrux.projDecomp m N C) hdecD T hTsub hne
  rw [hT, Finset.mem_filter] at hC₀T
  obtain ⟨κ, hκ, hκeq⟩ := Finset.mem_image.mp hC₀T.1
  refine ⟨C₀, hTsub (by rw [hT, Finset.mem_filter]; exact ⟨hC₀T.1, hC₀T.2⟩), ?_, hC₀T.2⟩
  refine Work.WilCrux.isOpen_of_isCell_interior_nonempty ?_ hC₀int
  rw [← hκeq]
  exact Work.WilCrux.projOver_isCell hdec (Finset.mem_filter.mp hκ).1

end Work.WilCruxN
