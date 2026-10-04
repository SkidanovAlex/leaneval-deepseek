import Mathlib
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.EXT.chartMat_ext_symm_posDef

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Set Metric Filter

namespace Work.Diff.EXT

open Work.Diff.EXT.SymPosDef

/-- **Symmetrising and shrinking a smooth extension of the chart matrix, keeping a prescribed
point.**  This is `Work.Diff.EXT.chartMat_ext_symm_posDef` with the extra requirement that the
shrunk open set `U'` still contains a prescribed point `y₀ ∈ U` (in the application `y₀` is the
chart centre `(extChartAt I x₀) x₀`, whose membership in the local chart neighbourhood is exactly
what the gluing theorem `Work.Diff.EXT.glue_seam_T_self` needs: it covers the compact manifold by
closed balls around the chart centres contained in the corresponding `U'`, so that the local forms
can be glued with a partition of unity).

Given a smooth `V` on `(Ioo (T-δ) (T+δ)) ×ˢ U` which agrees with the chart matrix `chartMat G x₀`
on the left slab `(Ico (T-δ) T) ×ˢ U`, and uniform positive definiteness of the chart matrix on
that slab (which passes to the seam `t = T` by continuity), one shrinks `δ` and `U` and replaces
`V` by its symmetric part `W`, which is symmetric and positive definite on the whole two-sided
slab.  The proof is the one already carried out in `Submission/Work/Diff/EXT/
chartMat_ext_symm_posDef.lean` (symmetrise, use `qf_le_at_seam_gen` for the bound at the seam and
`exists_posDef_tube` for the two-sided tube); here the prescribed `y₀` replaces the existential
point, and `exists_posDef_tube` already returns the membership `y₀ ∈ U'`. -/
theorem chartMat_ext_symm_posDef_at_centre
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (T δ : ℝ) (hδ : 0 < δ)
    (V : ℝ × E → Work.Diff.EXT.MatE (E := E))
    (U : Set E) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (y₀ : E) (hy₀ : y₀ ∈ U)
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V ((Set.Ioo (T - δ) (T + δ)) ×ˢ U))
    (hVeq : ∀ t ∈ Set.Ico (T - δ) T, ∀ y ∈ U,
        V (t, y) = Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y)
    (hell : ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Set.Ico (T - δ) T, ∀ y ∈ U,
        ∀ v : Fin (Module.finrank ℝ E) → ℝ,
        ε * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, v i * v j *
          Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y i j) :
    ∃ δ' : ℝ, 0 < δ' ∧ δ' ≤ δ ∧ ∃ U' : Set E, IsOpen U' ∧ U' ⊆ U ∧ y₀ ∈ U' ∧
      ∃ W : ℝ × E → Work.Diff.EXT.MatE (E := E),
        ContDiffOn ℝ (⊤ : ℕ∞) W ((Set.Ioo (T - δ') (T + δ')) ×ˢ U') ∧
        (∀ t ∈ Set.Ico (T - δ') T, ∀ y ∈ U',
          W (t, y) = Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y) ∧
        (∀ t ∈ Set.Ioo (T - δ') (T + δ'), ∀ y ∈ U',
          (∀ i j, W (t, y) i j = W (t, y) j i) ∧
          ∀ v : Fin (Module.finrank ℝ E) → ℝ, v ≠ 0 →
            0 < ∑ i, ∑ j, v i * v j * W (t, y) i j) := by
  obtain ⟨ε, hεpos, hεbnd⟩ := hell
  -- the chart matrix is symmetric, being the matrix of a symmetric bilinear form
  have hsymm : ∀ (t : ℝ) (y : E) (i j : Fin (Module.finrank ℝ E)),
      chartMat (I := I) (M := M) G x₀ t y i j = chartMat (I := I) (M := M) G x₀ t y j i :=
    fun t y i j => (G t).symm _ _ _
  -- the symmetric part of the extension
  set W : ℝ × E → MatE (E := E) := fun p i j => (V p i j + V p j i) / 2 with hWdef
  have hWsm : ContDiffOn ℝ (⊤ : ℕ∞) W (Set.Ioo (T - δ) (T + δ) ×ˢ U) := by
    simp only [hWdef]
    refine contDiffOn_pi.mpr (fun i => contDiffOn_pi.mpr (fun j => ?_))
    exact (((contDiffOn_pi.mp ((contDiffOn_pi.mp hV) i)) j).add
      ((contDiffOn_pi.mp ((contDiffOn_pi.mp hV) j)) i)).div_const 2
  have hWc : ContinuousOn W (Set.Ioo (T - δ) (T + δ) ×ˢ U) := hWsm.continuousOn
  -- `W` agrees with the chart matrix on the left slab
  have hWeq : ∀ t ∈ Set.Ico (T - δ) T, ∀ y ∈ U, W (t, y) = chartMat G x₀ t y := by
    intro t ht y hy
    have h1 : V (t, y) = chartMat G x₀ t y := hVeq t ht y hy
    funext i j
    simp only [hWdef]
    rw [show V (t, y) i j = chartMat G x₀ t y i j by rw [h1],
      show V (t, y) j i = chartMat G x₀ t y j i by rw [h1], hsymm t y j i]
    ring
  -- the uniform lower bound for `W` on the left half
  have hleft : ∀ t ∈ Set.Ioo (T - δ) T, ∀ y ∈ U, ∀ v : Fin (Module.finrank ℝ E) → ℝ,
      ε * ∑ i, (v i) ^ 2 ≤ qf (W (t, y)) v := by
    intro t ht y hy v
    have ht' : t ∈ Set.Ico (T - δ) T := ⟨le_of_lt ht.1, ht.2⟩
    rw [hWeq t ht' y hy]
    exact hεbnd t ht' y hy v
  -- the bound passes to the seam
  have hTb : ∀ y ∈ U, ∀ v : Fin (Module.finrank ℝ E) → ℝ,
      ε * ∑ i, (v i) ^ 2 ≤ qf (W (T, y)) v := qf_le_at_seam_gen hδ hWc hleft
  -- the two-sided positivity tube, around the prescribed point `y₀`
  obtain ⟨δ', hδ'pos, hδ'δ, U', hU'o, hy₀U', hU'sub, htube⟩ :=
    exists_posDef_tube hδ hεpos hU hy₀ hWc hTb
  refine ⟨δ', hδ'pos, hδ'δ, U', hU'o, hU'sub, hy₀U', W, ?_, ?_, ?_⟩
  · -- smoothness on the shrunk slab
    refine hWsm.mono ?_
    exact Set.prod_mono (Set.Ioo_subset_Ioo (by linarith) (by linarith)) hU'sub
  · -- agreement with the chart matrix on the shrunk left slab
    intro t ht y hy
    exact hWeq t ⟨by linarith [ht.1, hδ'δ], ht.2⟩ y (hU'sub hy)
  · -- symmetry and strict positive definiteness
    intro t ht y hy
    refine ⟨fun i j => ?_, fun v hv => ?_⟩
    · simp only [hWdef]
      ring
    · show 0 < qf (W (t, y)) v
      by_cases htT : t < T
      · -- left half: the hypothesis on the chart matrix
        have ht' : t ∈ Set.Ico (T - δ) T := ⟨by linarith [ht.1, hδ'δ], htT⟩
        have hWeqt : W (t, y) = chartMat G x₀ t y := hWeq t ht' y (hU'sub hy)
        rw [hWeqt]
        show 0 < ∑ i, ∑ j, v i * v j * chartMat (I := I) (M := M) G x₀ t y i j
        have h1 : ε * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, v i * v j *
            chartMat (I := I) (M := M) G x₀ t y i j := hεbnd t ht' y (hU'sub hy) v
        have h2 : 0 < ε * ∑ i, (v i) ^ 2 := mul_pos hεpos (sum_sq_pos hv)
        linarith
      · -- right half (including the seam): the tube
        exact htube t ht y hy v hv

end Work.Diff.EXT
