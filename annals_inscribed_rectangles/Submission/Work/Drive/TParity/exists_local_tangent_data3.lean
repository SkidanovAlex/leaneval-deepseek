import Mathlib
import Submission.Work.Drive.TParity.Basic
import Submission.Work.Drive.TParity.LocalGraph
import Submission.Work.Drive.TParity.ChartDeriv
import Submission.Work.Drive.ManifoldParity.GraphFDeriv
import Submission.Work.Drive.ManifoldParity.GraphMap

namespace Work.Drive.TParity

open scoped Manifold ContDiff Topology
open Manifold Set Filter
open Work.Drive.ManifoldParity (graphMap graphMap_apply graphMap_apply_i contDiff_graphMap
  differentiableAt_graphMap fderiv_graphMap_apply_i injective_fderiv_graphMap
  eq_fderiv_graphMap_of_fderiv_eq_zero)

noncomputable section

theorem exists_local_tangent_data3 {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (D k))
    (htrans : Work.Drive.TParity.transHyp D) {V : Work.Drive.Amb 8 → Work.Drive.Amb 8}
    (hVtan : Work.Drive.TParity.Vtan D V)
    {q : Work.Drive.Amb 8} (hq : q ∈ Work.Drive.TParity.K3 D) {i : Fin 9}
    (hsurj_i : Function.Surjective (fun v : {v : Work.Drive.Amb 8 // v i = 0} =>
      fderiv ℝ (Work.Drive.TParity.chartDiff3 (D 0 (Work.Drive.TParity.bPartC 0 q)) D) q v.1))
    (hother : ∀ j : Fin 9, j ≠ i → q j ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ (η : ℝ → Work.Drive.Amb 8) (ε : ℝ), 0 < ε ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧
      (∀ u, η u i = 0) ∧
      Work.Drive.ManifoldParity.graphMap i η (q i) = q ∧
      (∀ u, |u - q i| < ε → u ∈ Set.Icc (0 : ℝ) 1 →
        Work.Drive.ManifoldParity.graphMap i η u ∈ Submission.Drive.unitBox 8) ∧
      (∀ u, |u - q i| < ε →
        Work.Drive.TParity.meet3 D (Work.Drive.ManifoldParity.graphMap i η u)) ∧
      (∀ u, |u - q i| < ε → u ∈ Set.Icc (0 : ℝ) 1 →
        V (Work.Drive.ManifoldParity.graphMap i η u) =
          fderiv ℝ (Work.Drive.ManifoldParity.graphMap i η) u
            ((V (Work.Drive.ManifoldParity.graphMap i η u)) i)) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ u, |u - q i| ≤ ε →
        ‖fderiv ℝ (Work.Drive.ManifoldParity.graphMap i η) u‖ ≤ C) := by
  classical
  obtain ⟨hboxq, hmq⟩ := mem_K3.mp hq
  have hregq : q ∈ region3 (D 0 (bPartC 0 q)) D := mem_region3_self D hmq
  obtain ⟨δ, ρ, η, hδ, hρ, hηcd, hηi, hηx, hchar⟩ :=
    exists_local_graph3 (D 0 (bPartC 0 q)) D hD hregq hmq i hsurj_i
  have hηdiff : Differentiable ℝ η := hηcd.differentiable (by simp)
  -- the graph points close to `q` have all other coordinates strictly inside `(0,1)`
  have hgood : ∀ᶠ u in 𝓝 (q i), ∀ j : Fin 9, j ≠ i →
      (graphMap i η u) j ∈ Set.Ioo (0 : ℝ) 1 := by
    refine Filter.eventually_all.mpr (fun j => ?_)
    rcases eq_or_ne j i with rfl | hj
    · exact Filter.Eventually.of_forall (fun u hu => absurd rfl hu)
    · have hqj : η (q i) j = q j := by
        rw [hηx]
        simp [PiLp.sub_apply, PiLp.smul_apply, hj]
      have hmem' : {x : Work.Drive.Amb 8 | x j ∈ Set.Ioo (0 : ℝ) 1} ∈ 𝓝 (η (q i)) :=
        (isOpen_Ioo.preimage (by fun_prop)).mem_nhds
          (show (η (q i)) j ∈ Set.Ioo (0 : ℝ) 1 by rw [hqj]; exact hother j hj)
      filter_upwards [hηcd.continuous.continuousAt.preimage_mem_nhds hmem'] with u hu
      simpa [graphMap_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, hj] using hu
  obtain ⟨ε₁, hε₁, hε₁'⟩ := Metric.eventually_nhds_iff.mp hgood
  -- the local graph characterization at the graph points
  have hchar_at : ∀ t : ℝ, |t - q i| < δ →
      graphMap i η t ∈ region3 (D 0 (bPartC 0 q)) D ∧
        (meet3 D (graphMap i η t) ↔
          graphMap i η t = (graphMap i η t) i • EuclideanSpace.single i (1 : ℝ) +
            η ((graphMap i η t) i)) := by
    intro t ht
    refine hchar (graphMap i η t) ?_ ?_
    · rwa [graphMap_apply_i hηi]
    · rw [graphMap_apply_i hηi, graphMap_apply]
      simp [hρ]
  have hK_at : ∀ t : ℝ, |t - q i| < δ → meet3 D (graphMap i η t) :=
    fun t ht => ((hchar_at t ht).2).mpr (by rw [graphMap_apply_i hηi]; rfl)
  have hbox_at : ∀ u : ℝ, |u - q i| < min δ ε₁ → u ∈ Set.Icc (0 : ℝ) 1 →
      graphMap i η u ∈ Submission.Drive.unitBox 8 := by
    intro u hu huIcc
    rw [Submission.Drive.unitBox]
    intro j
    rcases eq_or_ne j i with rfl | hj
    · rw [graphMap_apply_i hηi]
      exact huIcc
    · exact Set.Ioo_subset_Icc_self
        (hε₁' (by rw [Real.dist_eq]; exact lt_of_lt_of_le hu (min_le_right _ _)) j hj)
  refine ⟨η, min δ ε₁, lt_min hδ hε₁, hηcd, hηi, ?_, ?_, ?_, ?_, ?_⟩
  · -- the graph passes through `q`
    rw [graphMap_apply, hηx]
    abel
  · -- the graph points with coordinate in `[0,1]` are in the box
    exact hbox_at
  · -- the graph points are in `K3`
    intro u hu
    exact hK_at u (lt_of_lt_of_le hu (min_le_left _ _))
  · -- the field is tangent to the graph
    intro u hu huIcc
    have huδ : |u - q i| < δ := lt_of_lt_of_le hu (min_le_left _ _)
    have hreg_gu : graphMap i η u ∈ region3 (D 0 (bPartC 0 q)) D := (hchar_at u huδ).1
    have hmeet_gu : meet3 D (graphMap i η u) := hK_at u huδ
    have hbox_gu : graphMap i η u ∈ Submission.Drive.unitBox 8 := hbox_at u hu huIcc
    have hsurj : Function.Surjective
        (fderiv ℝ (chartDiff3 (D 0 (bPartC 0 q)) D) (graphMap i η u)) :=
      chartDiff3_surj D hD hreg_gu hmeet_gu
        (htrans (graphMap i η u) hbox_gu hmeet_gu)
    have hker : fderiv ℝ (chartDiff3 (D 0 (bPartC 0 q)) D) (graphMap i η u)
        (V (graphMap i η u)) = 0 :=
      hVtan (graphMap i η u) ⟨hbox_gu, hmeet_gu⟩ (D 0 (bPartC 0 q)) hreg_gu
    have hψd : DifferentiableAt ℝ (chartDiff3 (D 0 (bPartC 0 q)) D) (graphMap i η u) :=
      ((contDiffOn_chartDiff3 (D 0 (bPartC 0 q)) D hD).contDiffAt
        ((isOpen_region3 (D 0 (bPartC 0 q)) D (fun k => (hD k).continuous)).mem_nhds
          hreg_gu)).differentiableAt (by simp)
    have hψvan : ∀ᶠ t in 𝓝 u, chartDiff3 (D 0 (bPartC 0 q)) D (graphMap i η t) = 0 := by
      have hset : {t : ℝ | |t - q i| < δ} ∈ 𝓝 u :=
        (isOpen_lt (by fun_prop : Continuous fun t : ℝ => |t - q i|) continuous_const).mem_nhds
          huδ
      filter_upwards [hset] with t ht
      rw [chartDiff3_eq_zero_iff (hchar_at t ht).1]
      exact ((hchar_at t ht).2).mpr (by rw [graphMap_apply_i hηi]; rfl)
    exact eq_fderiv_graphMap_of_fderiv_eq_zero (v := V (graphMap i η u))
      hηdiff.differentiableAt hηi hψd hψvan hsurj hker
  · -- the derivative of the graph map is bounded
    obtain ⟨C, hC⟩ : ∃ C, ∀ u ∈ Set.Icc (q i - min δ ε₁) (q i + min δ ε₁),
        ‖fderiv ℝ (graphMap i η) u‖ ≤ C := by
      refine IsCompact.exists_bound_of_continuousOn isCompact_Icc ?_
      exact ((contDiff_graphMap hηcd).continuous_fderiv (by simp)).continuousOn
    refine ⟨max C 0, le_max_right _ _, fun u hu => ?_⟩
    have hu' : u ∈ Set.Icc (q i - min δ ε₁) (q i + min δ ε₁) := by
      have h := abs_le.mp hu
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    exact (hC u hu').trans (le_max_left _ _)

end

end Work.Drive.TParity
