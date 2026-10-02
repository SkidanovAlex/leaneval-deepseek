import Mathlib
import Submission.Work.Tubular.Gauss

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false

/-!
# A strict margin for the box that contains a tube chart

The Pontryagin–Thom collapse of a tube chart `C` is constant on the boundary of the cube of radius
`R` as soon as the whole tube `C.U` lies in the open box `(-R, R)^{8+k}`
(`Work.Tubular.TubeChart.exists_box` produces such an `R`).  For the *homotopies* that compare two
collapses — and for any argument that needs a little room around the tube — one wants the box
inequality to hold with a **uniform strict margin** `δ > 0`, i.e. `|y j| < R - δ` on all of `C.U`.

The tube is compact (`Work.Tubular.TubeChart.isCompact_U`, the image of the compact closed disc
bundle under the continuous tubular map), so the supremum of `|y j|` over `y ∈ C.U` and
`j : Fin (8 + k)` is *attained*; the hypothesis `hbox` makes every attained value strictly smaller
than `R`, and half of the gap is the required margin.
-/

open scoped Manifold ContDiff Topology

namespace Work.ThomBordism

theorem tubeGen_margin {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) {R : ℝ}
    (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R - δ := by
  classical
  have hDisc : CompactSpace (Work.Tubular.NormalDiscSub E ε) :=
    Work.Tubular.compactSpace_normalDiscSub E ε
  have hU : IsCompact C.U := C.isCompact_U
  by_cases hne : C.U.Nonempty
  · -- the set of absolute values of the coordinates of the points of the tube, a compact subset
    -- of `ℝ` because it is a finite union of continuous images of the compact `C.U`
    have hS : IsCompact (⋃ j : Fin (8 + k), (fun y : Work.Tubular.Euc (8 + k) => |y j|) '' C.U) :=
      isCompact_iUnion fun j =>
        hU.image (PiLp.continuous_apply 2 (fun _ : Fin (8 + k) => ℝ) j).abs
    obtain ⟨j₀⟩ : Nonempty (Fin (8 + k)) := ⟨⟨0, by omega⟩⟩
    have hSne : (⋃ j : Fin (8 + k), (fun y : Work.Tubular.Euc (8 + k) => |y j|) '' C.U).Nonempty :=
      ⟨|hne.some j₀|, Set.mem_iUnion_of_mem j₀ ⟨hne.some, hne.some_mem, rfl⟩⟩
    -- a point of `S` at which the identity is maximal, i.e. the largest coordinate modulus
    obtain ⟨M, hMmem, hMmax⟩ := hS.exists_isMaxOn hSne continuous_id.continuousOn
    have hMR : M < R := by
      obtain ⟨j, y, hy, hyM⟩ := Set.mem_iUnion.1 hMmem
      rw [← hyM]
      exact hbox y hy j
    refine ⟨(R - M) / 2, by linarith, fun y hy j => ?_⟩
    have hle : |y j| ≤ M := hMmax (Set.mem_iUnion_of_mem j ⟨y, hy, rfl⟩)
    linarith
  · -- the tube is empty, so the conclusion is vacuous
    exact ⟨1, one_pos, fun y hy => absurd ⟨y, hy⟩ hne⟩

end Work.ThomBordism
