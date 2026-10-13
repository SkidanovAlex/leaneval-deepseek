/-
  WilG1 / Cell / partialBad_thin

  The last-coordinate fibre of a definable function is differentiable off a thin set.

  `fibBadAt G z` says that the fibre `s ↦ G (Fin.snoc (Fin.init z) s)` of `G` fails to be
  differentiable at `z (Fin.last p)`; the theorem says that the set of such `z` has empty
  interior in `ℝ^{p+1}`.

  The proof is a product-topology reduction to a single one-dimensional fibre.  If the bad
  set had non-empty interior, some sup-metric ball inside it would meet the affine curve
  `t ↦ Fin.snoc y t` (for the single parameter `y = Fin.init z₀`) in an interval of positive
  length; that interval is then contained in the non-differentiability set of the
  one-variable function `s ↦ G (Fin.snoc y s)`, contradicting the one-variable thinness
  theorem `Work.WilG1.Thin.oneDim_thin` applied to that fibre -- whose graph is
  `Ω`-definable by `Work.WilG1.Thin.sliceGraph_mem`.
-/
import Mathlib
import Submission.Work.WilG1.Plumb.Imports
import Submission.Work.WilG1.Thin.oneDim_thin
import Submission.Work.WilG1.Thin.sliceGraph_mem

namespace Work.WilG1.Cell

theorem partialBad_thin {S : WilkiesDesign.SOMin} (hcd : S.SharpCD) {p F D : ℕ}
    (G : (Fin (p + 1) → ℝ) → ℝ) (hG : WilkiesDesign.graphOf G ∈ S.Ω F D (p + 2)) :
    interior {z : Fin (p + 1) → ℝ | Work.WilG1.fibBadAt G z} = ∅ := by
  by_contra hne
  obtain ⟨z0, hz0⟩ := Set.nonempty_iff_ne_empty.mpr hne
  -- the parameter of the fibre through `z₀`
  set y : Fin p → ℝ := Fin.init z0 with hy
  -- the affine curve `t ↦ (y, t)` in `ℝ^{p+1}`
  let γ : ℝ → (Fin (p + 1) → ℝ) := fun t => Fin.snoc y t
  have hγcont : Continuous γ := by
    have h := Continuous.finSnoc (A := fun _ : Fin (p + 1) => ℝ)
      (f := fun _ : ℝ => y) (g := fun t : ℝ => t) continuous_const continuous_id
    simpa [γ] using h
  have hγz : γ (z0 (Fin.last p)) = z0 := by
    show Fin.snoc y (z0 (Fin.last p)) = z0
    rw [hy]
    exact Fin.snoc_init_self z0
  -- a neighbourhood of `z₀` inside the (open) interior of the bad set pulls back to a
  -- neighbourhood of `z₀ (Fin.last p)` on the curve
  have hnhds : γ ⁻¹' (interior {z : Fin (p + 1) → ℝ | Work.WilG1.fibBadAt G z}) ∈
      nhds (z0 (Fin.last p)) := by
    refine hγcont.continuousAt.preimage_mem_nhds ?_
    rw [hγz]
    exact isOpen_interior.mem_nhds hz0
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  -- hence the fibre over `y` is nowhere differentiable on an interval of positive length
  have hsubset : Metric.ball (z0 (Fin.last p)) ε ⊆
      {t : ℝ | ¬ DifferentiableAt ℝ (fun s : ℝ => G (Fin.snoc y s)) t} := by
    intro t ht
    have hmem : γ t ∈ ({z : Fin (p + 1) → ℝ | Work.WilG1.fibBadAt G z} : Set _) :=
      interior_subset (hball ht)
    show ¬ DifferentiableAt ℝ (fun s : ℝ => G (Fin.snoc y s)) t
    simpa [γ, Work.WilG1.fibBadAt] using hmem
  have hne2 : interior {t : ℝ | ¬ DifferentiableAt ℝ (fun s : ℝ => G (Fin.snoc y s)) t} ≠ ∅ := by
    refine Set.Nonempty.ne_empty ⟨z0 (Fin.last p), ?_⟩
    exact interior_maximal hsubset Metric.isOpen_ball (Metric.mem_ball_self hε)
  -- the fibre is a one-variable definable function, so its bad set is thin
  obtain ⟨a, b, hb⟩ := Work.WilG1.Thin.sliceGraph_mem (S := S) G hG y
  have hone := Work.WilG1.Thin.oneDim_thin (S := S) (g := fun s : ℝ => G (Fin.snoc y s)) hb
  rw [hone] at hne2
  exact hne2 rfl

end Work.WilG1.Cell
