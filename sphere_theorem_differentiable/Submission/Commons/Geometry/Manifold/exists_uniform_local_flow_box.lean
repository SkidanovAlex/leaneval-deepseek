import Mathlib
import Submission.Commons.Geometry.Manifold.exists_isMIntegralCurveOn_nhds

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Bundle Topology
open Bundle Set Metric

namespace Commons.Geometry.Manifold

/-- **Uniform local flow box for a smooth vector field on a compact manifold.**

For a `C^∞` section `v` of the tangent bundle of a compact boundaryless manifold there is a
*uniform* time `ε > 0` such that every point `x` has an open neighbourhood `U` and a jointly
continuous family of integral curves `γ` on `U` which at time `0` are the identity on `U` and
which are integral curves of `v` on `(-ε, ε)`.

This is the compactness upgrade of the pointwise local flow box
`exists_isMIntegralCurveOn_nhds`: apply the pointwise statement to obtain around every point
`x` a time `ε x`, an open neighbourhood `U x` and a flow `γ x`, extract a finite subcover of
`M` by the `U x`, and take `ε` to be the minimum of the finitely many times. -/
theorem exists_uniform_local_flow_box {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [I.Boundaryless] [CompactSpace M] {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ γ : M → ℝ → M,
      (∀ y ∈ U, γ y 0 = y) ∧
      (∀ y ∈ U, IsMIntegralCurveOn (γ y) v (Set.Ioo (-ε) ε)) ∧
      ContinuousOn (fun p : M × ℝ => γ p.1 p.2) (U ×ˢ Set.Ioo (-ε) ε) := by
  classical
  by_cases hM : Nonempty M
  · -- pointwise local flow boxes
    choose εf Uf hεf hUopen hxU γf hγ0 hγcur hγcont using
      fun x : M => exists_isMIntegralCurveOn_nhds hv x
    -- a finite subcover of `M` by the neighbourhoods `Uf`
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover Uf hUopen
      (fun x _ => Set.mem_iUnion.mpr ⟨x, hxU x⟩)
    have htne : t.Nonempty := by
      obtain ⟨m⟩ := hM
      obtain ⟨i, hi'⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ m))
      obtain ⟨hi, _⟩ := Set.mem_iUnion.mp hi'
      exact ⟨i, hi⟩
    -- the uniform time is the minimum of the finitely many times
    set ε : ℝ := (t.image εf).min' (htne.image εf) with hεdef
    have hεεf : ∀ i ∈ t, ε ≤ εf i := by
      intro i hi
      exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    have hεpos : 0 < ε := by
      rw [Finset.lt_min'_iff]
      intro y hy
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
      exact hεf i
    refine ⟨ε, hεpos, ?_⟩
    intro x
    obtain ⟨i, hi'⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ x))
    obtain ⟨hi, hxi⟩ := Set.mem_iUnion.mp hi'
    refine ⟨Uf i, hUopen i, hxi, γf i, hγ0 i, ?_, ?_⟩
    · intro y hy
      exact (hγcur i y hy).mono
        (Ioo_subset_Ioo (neg_le_neg (hεεf i hi)) (hεεf i hi))
    · exact ContinuousOn.mono (hγcont i)
        (Set.prod_mono Subset.rfl
          (Ioo_subset_Ioo (neg_le_neg (hεεf i hi)) (hεεf i hi)))
  · -- `M` is empty: the statement is vacuous
    refine ⟨1, one_pos, fun x => (hM ⟨x⟩).elim⟩

end Commons.Geometry.Manifold
