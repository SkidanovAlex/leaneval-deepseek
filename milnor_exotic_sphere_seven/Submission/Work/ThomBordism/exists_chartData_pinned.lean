import Mathlib
import Submission.Work.PTGeometric.WeakRegion.Setup
import Submission.Work.PTGeometric.regionManifoldTheorem

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter ModelWithCorners

/-- **Pinned region chart data.**

This is `Work.PTGeometric.WeakRegion.RegionSetupWeak.exists_chartData` with the additional
information that, in the case `Φ m.1 < 0` (where the region contains a neighbourhood of `m.1`),
the model chart is the identity and the ambient chart is the restriction of `chartAt` to an open
neighbourhood `U` of `m.1` contained in the region.

In the other case (`¬ Φ m.1 < 0`) the extra conjunct is vacuous, so the statement is the
unpinned one. -/
theorem exists_chartData_pinned (k : ℕ)
    (S : Work.PTGeometric.WeakRegion.RegionSetupWeak k)
    (m : Work.PTGeometric.WeakRegion.RegionSetupWeak.Region S) :
    ∃ (dom : OpenPartialHomeomorph S.A (EuclideanHalfSpace (8 + k + 1)))
      (T : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (8 + k + 1)))
        (EuclideanSpace ℝ (Fin (8 + k + 1)))),
      dom ∈ IsManifold.maximalAtlas (modelWithCornersEuclideanHalfSpace (8 + k + 1))
        ((⊤ : ENat) : WithTop ENat) S.A ∧
      m.1 ∈ dom.source ∧
      (dom.extend (modelWithCornersEuclideanHalfSpace (8 + k + 1))) m.1 ∈ T.source ∧
      T.source = T.target ∧
      ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
        (T : EuclideanSpace ℝ (Fin (8 + k + 1)) → EuclideanSpace ℝ (Fin (8 + k + 1))) T.source ∧
      ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
        (T.symm : EuclideanSpace ℝ (Fin (8 + k + 1)) → EuclideanSpace ℝ (Fin (8 + k + 1)))
        T.target ∧
      IsOpen {u : EuclideanHalfSpace (8 + k + 1) |
        (T.symm : EuclideanSpace ℝ (Fin (8 + k + 1)) → EuclideanSpace ℝ (Fin (8 + k + 1))) u.1
          ∈ (dom.extend (modelWithCornersEuclideanHalfSpace (8 + k + 1))).target ∧
        u.1 ∈ T.target} ∧
      (∀ y ∈ dom.source,
        (dom.extend (modelWithCornersEuclideanHalfSpace (8 + k + 1))) y ∈ T.source →
        (S.Φ y ≤ 0 ↔
          0 ≤ ((T ((dom.extend (modelWithCornersEuclideanHalfSpace (8 + k + 1))) y)).ofLp 0))) ∧
      (((T ((dom.extend (modelWithCornersEuclideanHalfSpace (8 + k + 1))) m.1)).ofLp 0 = 0) ↔
        (m.1 ∈ (modelWithCornersEuclideanHalfSpace (8 + k + 1)).boundary S.A ∨ S.Φ m.1 = 0)) ∧
      (S.Φ m.1 < 0 →
        ∃ U : Set S.A, IsOpen U ∧ m.1 ∈ U ∧
          dom = (chartAt (EuclideanHalfSpace (8 + k + 1)) m.1).restr U ∧
          dom.source ⊆ U ∧
          T = Work.PTGeometric.WeakRegion.RegionSetupWeak.idPH
            (EuclideanSpace ℝ (Fin (8 + k + 1)))) := by
  classical
  by_cases hA : S.Φ m.1 < 0
  · -- ## Case A: the region contains a neighbourhood of `m.1`
    have hreg : {y : S.A | S.Φ y ≤ 0} ∈ 𝓝 m.1 := by
      have h1 : S.Φ ⁻¹' Iio 0 ∈ 𝓝 m.1 :=
        (S.hΦ.continuous.isOpen_preimage _ isOpen_Iio).mem_nhds hA
      exact Filter.mem_of_superset h1 (fun y (hy : S.Φ y < 0) => le_of_lt hy)
    obtain ⟨U, hUsub, hUopen, hUm⟩ := mem_nhds_iff.mp hreg
    set dom : OpenPartialHomeomorph S.A (EuclideanHalfSpace (8 + k + 1)) :=
      (chartAt (EuclideanHalfSpace (8 + k + 1)) m.1).restr U with hdomdef
    have hchimem : (chartAt (EuclideanHalfSpace (8 + k + 1)) m.1) ∈
        IsManifold.maximalAtlas (modelWithCornersEuclideanHalfSpace (8 + k + 1))
          ((⊤ : ENat) : WithTop ENat) S.A :=
      IsManifold.chart_mem_maximalAtlas
        (I := modelWithCornersEuclideanHalfSpace (8 + k + 1)) m.1
    have hdommem : dom ∈ IsManifold.maximalAtlas
        (modelWithCornersEuclideanHalfSpace (8 + k + 1))
        ((⊤ : ENat) : WithTop ENat) S.A :=
      restr_mem_maximalAtlas
        (contDiffGroupoid ((⊤ : ENat) : WithTop ENat)
          (modelWithCornersEuclideanHalfSpace (8 + k + 1))) hchimem hUopen
    have hdomsrc : dom.source = (chartAt (EuclideanHalfSpace (8 + k + 1)) m.1).source ∩ U :=
      OpenPartialHomeomorph.restr_source' _ U hUopen
    have hdomm : m.1 ∈ dom.source := by
      rw [hdomsrc]
      exact ⟨mem_chart_source (EuclideanHalfSpace (8 + k + 1)) m.1, hUm⟩
    have hdomsub : dom.source ⊆ U := by
      rw [hdomsrc]; exact inter_subset_right
    refine ⟨dom, Work.PTGeometric.WeakRegion.RegionSetupWeak.idPH
        (EuclideanSpace ℝ (Fin (8 + k + 1))),
      hdommem, hdomm, mem_univ _, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
        (fun z : EuclideanSpace ℝ (Fin (8 + k + 1)) => z) univ
      exact contDiff_id.contDiffOn
    · show ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
        (fun z : EuclideanSpace ℝ (Fin (8 + k + 1)) => z) univ
      exact contDiff_id.contDiffOn
    · -- ## openness of the target
      obtain ⟨W, hWopen, hW⟩ :=
        Work.ThomBordism.Transversality.Preimage.exists_isOpen_extend_target dom
      have hset : {u : EuclideanHalfSpace (8 + k + 1) |
            (Work.PTGeometric.WeakRegion.RegionSetupWeak.idPH
                (EuclideanSpace ℝ (Fin (8 + k + 1)))).symm u.1
              ∈ (dom.extend (modelWithCornersEuclideanHalfSpace (8 + k + 1))).target ∧
            u.1 ∈ (Work.PTGeometric.WeakRegion.RegionSetupWeak.idPH
                (EuclideanSpace ℝ (Fin (8 + k + 1)))).target}
          = Subtype.val ⁻¹' W := by
        ext u
        constructor
        · rintro ⟨hu, -⟩
          have h2 : u.1 ∈ W ∩ Set.range (modelWithCornersEuclideanHalfSpace (8 + k + 1)) :=
            hW ▸ hu
          exact h2.1
        · intro hu
          refine ⟨?_, mem_univ _⟩
          rw [hW]
          exact ⟨hu, by
            rw [range_modelWithCornersEuclideanHalfSpace]
            exact u.2⟩
      rw [hset]
      exact hWopen.preimage continuous_subtype_val
    · -- ## the sign of `Φ` is the sign of the zeroth coordinate
      intro y hy _
      have hΦy : S.Φ y ≤ 0 := hUsub (hdomsub hy)
      have hcoord : 0 ≤ ((Work.PTGeometric.WeakRegion.RegionSetupWeak.idPH
          (EuclideanSpace ℝ (Fin (8 + k + 1))))
          ((dom.extend (modelWithCornersEuclideanHalfSpace (8 + k + 1))) y)).ofLp 0 := by
        simpa only [Work.PTGeometric.WeakRegion.RegionSetupWeak.idPH_apply] using
          Work.ThomBordism.Transversality.Preimage.zero_le_extend_apply_coord dom hy
      exact ⟨fun _ => hcoord, fun _ => hΦy⟩
    · -- ## the zeroth coordinate of the base point
      have hcoord : ((Work.PTGeometric.WeakRegion.RegionSetupWeak.idPH
          (EuclideanSpace ℝ (Fin (8 + k + 1))))
          ((dom.extend (modelWithCornersEuclideanHalfSpace (8 + k + 1))) m.1)).ofLp 0
          = ((dom.extend (modelWithCornersEuclideanHalfSpace (8 + k + 1))) m.1).ofLp 0 := rfl
      rw [hcoord]
      have hb := Work.ThomBordism.Transversality.Preimage.mem_boundary_iff_extend_apply_coord_eq_zero
        (m := 8 + k + 1) hdommem hdomm
      rw [hb]
      constructor
      · intro h; exact Or.inl h
      · rintro (h | h)
        · exact h
        · exact absurd h (ne_of_lt hA)
    · -- ## the pin
      intro _
      exact ⟨U, hUopen, hUm, rfl, hdomsub, rfl⟩
  · -- ## Not case A: reuse the unpinned chart data (the pin is vacuous)
    obtain ⟨dom, T, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
      Work.PTGeometric.WeakRegion.RegionSetupWeak.exists_chartData S m
    exact ⟨dom, T, h1, h2, h3, h4, h5, h6, h7, h8, h9, fun hlt => absurd hlt hA⟩

end Work.ThomBordism
