/-
  WilG1 / Cell / Junk / fibBad_thin_of_last.

  The fibre-bad set of a definable function in an *arbitrary* coordinate direction is thin,
  assuming thinness of the last-direction fibre-bad set `{z | fibBadAt G z}` (which is
  `partialBad_thin`).

  The reduction to the last direction is by a coordinate permutation: for `i : Fin (m+1)` let
  `τ = insPerm m i` move the index `i` to the last position, and reindex the function by
  `G x = h (x ∘ τ)`.  Then the `i`-th fibre of `h` at `y` is the last fibre of `G` at
  `Fin.snoc (Fin.removeNth i y) (y i)`:

    `fibBad h i y ↔ fibBadAt G (Fin.snoc (Fin.removeNth i y) (y i))`
    (`Work.WilG1.Cell.Junk.fibBad_iff_fibBadAt`),

  i.e. `fibBad h i` is the preimage of the fibre-bad set of `G` under the coordinate permutation
  `e = Homeomorph.piCongrLeft τ` (`y ↦ y ∘ τ⁻¹ = Fin.snoc (Fin.removeNth i y) (y i)`, see
  `comp_insPerm_symm_eq_snoc`).  A homeomorphism commutes with `interior`, so thinness transfers.
  Moreover the graph of `G` is the reindexing of the graph of `h` by the lifted permutation
  `insPermLift m i` (`Work.WilG1.Cell.Junk.graphOf_comp_insPerm`), hence is `Ω`-definable by
  `Work.WilG5.reindex_mem`, which is what makes the hypothesis `hlast` applicable to `G`.
-/
import Mathlib
import Submission.Work.WilG1.Cell.JunkDefs
import Submission.Work.WilG1.Plumb.Imports
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG5.Reindex
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.Cell.Junk.fibBad_thin_defs
import Submission.Work.WilG1.Cell.Junk.graphOf_comp_insPerm
import Submission.Work.WilG1.Cell.Junk.fibBad_iff_fibBadAt

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Work.WilG1.Cell.Junk

open WilkiesDesign Work.WilG1

theorem fibBad_thin_of_last {S : WilkiesDesign.SOMin}
    (hlast : ∀ (p F D : ℕ) (G : (Fin (p + 1) → ℝ) → ℝ),
      WilkiesDesign.graphOf G ∈ S.Ω F D (p + 2) →
        interior {z : Fin (p + 1) → ℝ | Work.WilG1.fibBadAt G z} = ∅)
    {n F D : ℕ} (h : (Fin n → ℝ) → ℝ) (hh : WilkiesDesign.graphOf h ∈ S.Ω F D (n + 1))
    (i : Fin n) : interior (fibBad h i) = ∅ := by
  rcases n with _ | m
  · exact Fin.elim0 i
  -- `n = m + 1`: move the direction `i` to the last coordinate
  let τ : Fin (m + 1) ≃ Fin (m + 1) := insPerm m i
  let σ : Fin (m + 2) → Fin (m + 2) := insPermLift m i
  let G : (Fin (m + 1) → ℝ) → ℝ := fun x => h (x ∘ (τ : Fin (m + 1) → Fin (m + 1)))
  -- the graph of `G` is a coordinate reindexing of the graph of `h`, hence `Ω`-definable
  have hgraph : WilkiesDesign.graphOf G =
      {z : Fin (m + 2) → ℝ | (z ∘ σ) ∈ WilkiesDesign.graphOf h} :=
    graphOf_comp_insPerm m i h
  have hGmem : WilkiesDesign.graphOf G ∈
      S.Ω (max (F + (m + 2)) (4 * ((m + 2) + (m + 2)) + 8) + 1 + (m + 2))
        (D + (2 * (m + 2) + 4)) (m + 2) := by
    rw [hgraph]
    exact Work.WilG5.reindex_mem (S := S) σ hh
  have hthinG : interior {z : Fin (m + 1) → ℝ | Work.WilG1.fibBadAt G z} = ∅ :=
    hlast m _ _ G hGmem
  -- the coordinate permutation `y ↦ y ∘ τ⁻¹ = Fin.snoc (Fin.removeNth i y) (y i)`
  let e : (Fin (m + 1) → ℝ) ≃ₜ (Fin (m + 1) → ℝ) :=
    Homeomorph.piCongrLeft (Y := fun _ : Fin (m + 1) => ℝ) τ
  have hey : ∀ y : Fin (m + 1) → ℝ, e y = Fin.snoc (Fin.removeNth i y) (y i) := by
    intro y
    have h1 : e y =
        y ∘ ((τ.symm : Fin (m + 1) ≃ Fin (m + 1)) : Fin (m + 1) → Fin (m + 1)) := by
      funext j
      show (Equiv.piCongrLeft (fun _ : Fin (m + 1) => ℝ) τ) y j = y (τ.symm j)
      simpa using Equiv.piCongrLeft_apply_apply (fun _ : Fin (m + 1) => ℝ) τ y (τ.symm j)
    exact h1.trans (comp_insPerm_symm_eq_snoc m i y)
  -- `fibBad h i` is the preimage of the fibre-bad set of `G` under `e`
  have hpre : fibBad h i = e ⁻¹' {z : Fin (m + 1) → ℝ | Work.WilG1.fibBadAt G z} := by
    ext y
    rw [Set.mem_preimage]
    show fibBad h i y ↔ Work.WilG1.fibBadAt G (e y)
    rw [hey y]
    exact fibBad_iff_fibBadAt m i h y
  calc interior (fibBad h i)
      = interior (e ⁻¹' {z : Fin (m + 1) → ℝ | Work.WilG1.fibBadAt G z}) := by rw [hpre]
    _ = e ⁻¹' interior {z : Fin (m + 1) → ℝ | Work.WilG1.fibBadAt G z} :=
        (e.preimage_interior _).symm
    _ = e ⁻¹' (∅ : Set (Fin (m + 1) → ℝ)) := by rw [hthinG]
    _ = ∅ := by simp

end Work.WilG1.Cell.Junk
