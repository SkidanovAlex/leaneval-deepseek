import Mathlib
import Submission.Work.Drive.sideGermDefs

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-! ## Auxiliary: the tube lemma and the disk of a perturbed chart -/

/-- **The tube lemma.**  If `K` is compact and the open set `U ⊆ P × X` contains `{y₀} × K`, then a
whole neighbourhood `V` of `y₀` satisfies `V × K ⊆ U`.  (A local copy of
`Work.Drive.tubeLoop`, so that this file depends only on `sideGermDefs`.) -/
theorem tube_smallChartPert {P X : Type*} [TopologicalSpace P] [TopologicalSpace X] {y₀ : P}
    {K : Set X} (hK : IsCompact K) {U : Set (P × X)} (hU : IsOpen U)
    (h : ∀ x ∈ K, (y₀, x) ∈ U) :
    ∃ V ∈ 𝓝 y₀, ∀ y ∈ V, ∀ x ∈ K, (y, x) ∈ U := by
  classical
  have key : ∀ x ∈ K, ∃ V ∈ 𝓝 y₀, ∃ W ∈ 𝓝 x, V ×ˢ W ⊆ U := by
    intro x hx
    have hmem : U ∈ 𝓝 (y₀, x) := hU.mem_nhds (h x hx)
    rw [nhds_prod_eq] at hmem
    exact Filter.mem_prod_iff.mp hmem
  choose V hV W hW hVW using key
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' W hW
  refine ⟨⋂ i ∈ (t : Set ↥K), V i.1 i.2,
    (Filter.biInter_mem t.finite_toSet).mpr (fun i _ => hV i.1 i.2), ?_⟩
  intro y hy x hx
  obtain ⟨z, hzt, hxz⟩ := Set.mem_iUnion₂.mp (ht hx)
  exact (hVW z.1 z.2) ⟨(Set.mem_iInter₂.mp hy) z hzt, hxz⟩

/-- **The disk of a perturbed chart is the image of the chart's disk under the perturbation.** -/
lemma chartDisk_pertChart {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (t : EuclideanSpace ℝ (Fin m)) :
    chartDisk (pertChart Ξ Q t) = Ξ t '' chartDisk Q := by
  rw [chartDisk, chartDisk, Set.image_image]
  rfl

/-! ## The target -/

/-- §5 P1 of the project lead's `NOTES_LEAD_hdense.md` (the "small-`Ξ` robustness" of the
whole-plane disjointness): if the chart's disk is disjoint from its own rotation by a collision-free
angle, then so are the disks of two *small* chart perturbations.  This is the uniform input that lets
the producer of the `hdense` data transfer the disjointness of the honest chart to all small
parameters, and is used both for the core/diameter avoidances of `T6` and for the level bands.

Proof: `chartDisk (pertChart Ξ Q t) = Ξ t '' chartDisk Q` is the image of a compact set under the
continuous map `(t, p) ↦ Ξ t p`; `chartDisk Q` and `rotCapping a '' chartDisk Q` are compact and
disjoint, and `Ξ 0 = id`. -/
theorem exists_small_chartPert_disjoint {γ : Circle → ℝ × ℝ}
    {Q : ℂ → Work.Drive.CappingSpace} (hQ : Work.Drive.IsSmoothChart Q)
    {Ξ : EuclideanSpace ℝ (Fin 4) → Work.Drive.CappingSpace → Work.Drive.CappingSpace}
    (hΞ : Work.Drive.ChartPert Q 4 Ξ)
    (hdisjZc : ∀ w : UnitAddCircle, w ∈ Work.Drive.Zc γ →
      Disjoint (Work.Drive.chartDisk Q) (Work.Drive.rotCapping w '' Work.Drive.chartDisk Q))
    {a : UnitAddCircle} (ha : a ∈ Work.Drive.Zc γ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ t t' : EuclideanSpace ℝ (Fin 4), ‖t‖ < ρ → ‖t'‖ < ρ →
      Disjoint (Work.Drive.chartDisk (Work.Drive.pertChart Ξ Q t))
        (Work.Drive.rotCapping a '' Work.Drive.chartDisk (Work.Drive.pertChart Ξ Q t')) := by
  have hQc : Continuous Q := hQ.continuous
  have hK : IsCompact (chartDisk Q) := chartDisk_compact hQc
  have hΞc : Continuous fun q : EuclideanSpace ℝ (Fin 4) × CappingSpace => Ξ q.1 q.2 :=
    hΞ.2.1.continuous
  have hmap : Continuous fun z : (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) ×
      (CappingSpace × CappingSpace) =>
      (Ξ z.1.1 z.2.1, rotCapping a (Ξ z.1.2 z.2.2)) :=
    Continuous.prodMk
      (hΞc.comp ((continuous_fst.comp continuous_fst).prodMk
        (continuous_fst.comp continuous_snd)))
      ((continuous_rotCapping a).comp (hΞc.comp ((continuous_snd.comp continuous_fst).prodMk
        (continuous_snd.comp continuous_snd))))
  -- the collision set is an open neighbourhood condition around the parameter `0`
  have hU : IsOpen ((fun z : (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) ×
      (CappingSpace × CappingSpace) =>
      (Ξ z.1.1 z.2.1, rotCapping a (Ξ z.1.2 z.2.2))) ⁻¹'
      {u : CappingSpace × CappingSpace | u.1 ≠ u.2}) :=
    isClosed_diagonal.isOpen_compl.preimage hmap
  have hmem : ∀ x ∈ chartDisk Q ×ˢ chartDisk Q,
      (((0 : EuclideanSpace ℝ (Fin 4)), (0 : EuclideanSpace ℝ (Fin 4))), x) ∈
        ((fun z : (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) ×
          (CappingSpace × CappingSpace) =>
          (Ξ z.1.1 z.2.1, rotCapping a (Ξ z.1.2 z.2.2))) ⁻¹'
          {u : CappingSpace × CappingSpace | u.1 ≠ u.2}) := by
    rintro ⟨p, q⟩ ⟨hp, hq⟩
    change Ξ 0 p ≠ rotCapping a (Ξ 0 q)
    rw [hΞ.1 p, hΞ.1 q]
    intro hpq
    exact Set.disjoint_left.mp (hdisjZc a ha) hp ⟨q, hq, hpq.symm⟩
  obtain ⟨V, hV, hVsub⟩ := tube_smallChartPert
    (y₀ := ((0 : EuclideanSpace ℝ (Fin 4)), (0 : EuclideanSpace ℝ (Fin 4))))
    (hK.prod hK) hU hmem
  obtain ⟨ρ, hρ, hb⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨ρ, hρ, fun t t' ht ht' => ?_⟩
  have hmemV : (t, t') ∈ V := hb (by
    simp only [Metric.mem_ball, dist_eq_norm, Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_zero]
    exact max_lt ht ht')
  have hsep : ∀ p ∈ chartDisk Q, ∀ q ∈ chartDisk Q,
      Ξ t p ≠ rotCapping a (Ξ t' q) := fun p hp q hq =>
    hVsub (t, t') hmemV (p, q) ⟨hp, hq⟩
  rw [chartDisk_pertChart, chartDisk_pertChart, Set.disjoint_left]
  intro x hx hy
  rcases hx with ⟨p, hp, rfl⟩
  rcases hy with ⟨y, hy, hyx⟩
  rcases hy with ⟨q, hq, rfl⟩
  exact hsep p hp q hq hyx.symm

end

end Work.Drive
