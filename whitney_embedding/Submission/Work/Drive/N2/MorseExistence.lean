import Mathlib
import Submission.Work.Drive.N2.HeightBasics
import Submission.Work.Drive.N2.ChartSplit
import Submission.Work.Drive.N2.ChartGlue
import Submission.Work.Drive.N2.volume_badSet_eq_zero
import Submission.Work.Drive.N2.exists_depProj_comp_bijective
import Submission.Work.Drive.N2.fderiv_chartHeight_eq_zero_of_isCritical
import Submission.Work.Drive.N2.nondegCrit_iff_chart
import Submission.Work.Drive.N2.isOpen_minorRegion
import Submission.Work.Projection.compact_embedding
import Submission.Work.Projection.exists_countable_chart_cover
import Submission.Work.Embedding.exists_unique_closest_point

/-!
# Existence of a Morse function on a compact surface

For an embedding `e : M → ℝ⁵` with injective derivative, the height functions `h_v = x ↦ ⟪v, e x⟫`
are smooth, and for almost every direction `v` all their critical points are nondegenerate.  The
proof is the classical Sard-type argument carried out in charts:

* in a chart the set of directions `v` for which the chart representation has a degenerate critical
  point is null (`volume_badSet_eq_zero`), provided one of the `(a,b)`-minors is invertible there;
* the chart target is covered by the finitely many minor regions (`exists_depProj_comp_bijective`);
* a countable chart cover turns this into a countable union of null sets.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff RealInnerProductSpace
open MeasureTheory
open Work.Drive.Morse
open Work.Projection

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]

/-- `v` is a *bad direction* for the embedding `e` if the height function `h_v` has a critical point
which is degenerate. -/
def BadDir (e : M → EuclideanSpace ℝ (Fin 5)) (v : EuclideanSpace ℝ (Fin 5)) : Prop :=
  ∃ x : M, IsCritical (heightFun e v) x ∧ ¬ NondegCrit (heightFun e v) x

/-- The chartwise bad set of the pair `(a,b)` vanishes identically for `a = b`, and is the bad set of
the delegated Sard step otherwise. -/
noncomputable def chartBad (e : M → EuclideanSpace ℝ (Fin 5)) (p : M) (ab : Fin 5 × Fin 5) :
    Set (EuclideanSpace ℝ (Fin 5)) :=
  if ab.1 = ab.2 then ∅ else badSet (Work.Projection.chartRep e p) (minorRegion e p ab.1 ab.2)

/-- The bad directions are contained in the union of the chartwise bad sets. -/
theorem badDir_subset (e : M → EuclideanSpace ℝ (Fin 5)) (he : ContMDiff (𝓡 2) (𝓡 5) ∞ e)
    (himm : ∀ x, Function.Injective (mfderiv (𝓡 2) (𝓡 5) e x)) (p : ℕ → M)
    (hp : (Set.univ : Set M) ⊆ ⋃ i, (chartAt (EuclideanSpace ℝ (Fin 2)) (p i)).source) :
    {v : EuclideanSpace ℝ (Fin 5) | BadDir e v} ⊆
      ⋃ i, ⋃ ab : Fin 5 × Fin 5, chartBad e (p i) ab := by
  rintro v ⟨x, hcrit, hnodeg⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hp (Set.mem_univ x))
  set c := chartAt (EuclideanSpace ℝ (Fin 2)) (p i) with hc
  have hxsrc : x ∈ c.source := hi
  have hxtgt : c x ∈ c.target := c.map_source hxsrc
  have hcrit' : fderiv ℝ (chartHeight (Work.Projection.chartRep e (p i)) v) (c x) = 0 :=
    fderiv_chartHeight_eq_zero_of_isCritical e he v (p i) x hi hcrit
  have hnodeg' : ¬ Function.Injective
      (fderiv ℝ (fderiv ℝ (chartHeight (Work.Projection.chartRep e (p i)) v)) (c x)) := by
    intro hinj
    refine hnodeg ?_
    have hiff := nondegCrit_iff_chart (heightFun e v) (contMDiff_heightFun e v he) x (p i) hi hcrit
    exact hiff.mpr hinj
  obtain ⟨a, b, hab, hbij⟩ :=
    exists_depProj_comp_bijective (fderiv ℝ (Work.Projection.chartRep e (p i)) (c x))
      (Work.Embedding.injective_fderiv_chartRep_infty e he himm (p i) hxtgt)
  have hmem : c x ∈ minorRegion e (p i) a b :=
    ⟨hxtgt, (bijective_minor_iff_det_ne_zero e (p i) a b (c x)).mp hbij⟩
  refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨(a, b), ?_⟩⟩
  rw [chartBad, if_neg hab]
  exact ⟨c x, hmem, hcrit', hnodeg'⟩

/-- The chartwise bad sets are all null. -/
theorem volume_chartBad_eq_zero (e : M → EuclideanSpace ℝ (Fin 5))
    (he : ContMDiff (𝓡 2) (𝓡 5) ∞ e) (himm : ∀ x, Function.Injective (mfderiv (𝓡 2) (𝓡 5) e x))
    (p : M) (a b : Fin 5) :
    volume (chartBad e p (a, b)) = 0 := by
  rw [chartBad]
  split_ifs with hab
  · exact measure_empty
  · exact volume_badSet_eq_zero (Work.Projection.chartRep e p) (minorRegion e p a b)
      (isOpen_minorRegion e he p a b) (contDiffOn_minorRegion e he p a b)
      (fun y hy => differentiableAt_minorRegion e he p a b hy)
      (fun y hy => injective_fderiv_minorRegion e he himm p a b hy) a b hab
      (fun y hy => (bijective_minor_iff_det_ne_zero e p a b y).mpr hy.2)

/-- **Existence of a Morse function.**  For an embedding `e : M → ℝ⁵` of a compact surface with
injective derivative, some height function `h_v = x ↦ ⟪v, e x⟫` has only nondegenerate critical
points. -/
theorem exists_isMorse_of_embedding (e : M → EuclideanSpace ℝ (Fin 5))
    (he : ContMDiff (𝓡 2) (𝓡 5) ∞ e) (himm : ∀ x, Function.Injective (mfderiv (𝓡 2) (𝓡 5) e x)) :
    ∃ f : M → ℝ, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f ∧
      ∀ x, IsCritical f x → NondegCrit f x := by
  classical
  rcases isEmpty_or_nonempty M with hM | hM
  · haveI : IsEmpty M := hM
    exact ⟨fun x => isEmptyElim x, fun x => isEmptyElim x, fun x => isEmptyElim x⟩
  · haveI := hM
    obtain ⟨p, hp⟩ := Work.Projection.exists_countable_chart_cover 2 M
    have hnull : volume (⋃ i, ⋃ ab : Fin 5 × Fin 5, chartBad e (p i) ab) = 0 := by
      refine measure_iUnion_null fun i => ?_
      refine measure_iUnion_null fun ab => ?_
      exact volume_chartBad_eq_zero e he himm (p i) ab.1 ab.2
    have hbad : volume {v : EuclideanSpace ℝ (Fin 5) | BadDir e v} = 0 := by
      refine le_antisymm ?_ bot_le
      calc volume {v : EuclideanSpace ℝ (Fin 5) | BadDir e v}
          ≤ volume (⋃ i, ⋃ ab : Fin 5 × Fin 5, chartBad e (p i) ab) :=
            measure_mono (badDir_subset e he himm p hp)
        _ = 0 := hnull
    have : ∃ v : EuclideanSpace ℝ (Fin 5), ¬ BadDir e v := by
      by_contra h
      push_neg at h
      have hsub : (Metric.ball 0 1 : Set (EuclideanSpace ℝ (Fin 5))) ⊆ {v | BadDir e v} :=
        fun v _ => h v
      have hle : volume (Metric.ball 0 1 : Set (EuclideanSpace ℝ (Fin 5))) ≤ 0 := by
        have h2 : volume (Metric.ball 0 1 : Set (EuclideanSpace ℝ (Fin 5)))
            ≤ volume {v : EuclideanSpace ℝ (Fin 5) | BadDir e v} := measure_mono hsub
        rw [hbad] at h2
        exact h2
      have hpos : 0 < volume (Metric.ball 0 1 : Set (EuclideanSpace ℝ (Fin 5))) :=
        Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin 5)) (by norm_num : (0 : ℝ) < 1)
      exact absurd (le_antisymm hle bot_le) (ne_of_gt hpos)
    obtain ⟨v, hv⟩ := this
    exact ⟨heightFun e v, contMDiff_heightFun e v he, fun x hx => by
      by_contra hnd
      exact hv ⟨x, hx, hnd⟩⟩

end Work.Drive.N2
