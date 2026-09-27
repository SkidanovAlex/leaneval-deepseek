import Mathlib
import Submission.Work.Embedding.exists_smooth_retraction
import Submission.Work.Embedding.local_retraction_model
import Submission.Work.Embedding.orthogonal_range_mfderiv
import Submission.Work.Drive.N2.exists_local_chart_data

open scoped Manifold ContDiff
open Topology Metric Set

namespace Work.Drive.N2

theorem exists_smooth_retraction_manifold {n N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [Nonempty M]
    (e : M → EuclideanSpace ℝ (Fin N))
    (he : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N))) ((⊤ : ℕ∞) : WithTop ℕ∞) e)
    (hinj : Function.Injective e)
    (himm : ∀ x, Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N))) e x)) :
    ∃ (U : Set (EuclideanSpace ℝ (Fin N))) (π : EuclideanSpace ℝ (Fin N) → M),
      IsOpen U ∧ Set.range e ⊆ U ∧
      ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) π U ∧
      (∀ x, π (e x) = x) ∧
      (∀ y ∈ U, dist y (e (π y)) = Metric.infDist y (Set.range e)) ∧
      (∀ y ∈ U, y - e (π y) ∈ (fderiv ℝ (fun z => e (π z)) y).rangeᗮ) := by
  obtain ⟨ε, hεpos, huniq⟩ := Work.Embedding.exists_unique_closest_point e he hinj himm
  let np : EuclideanSpace ℝ (Fin N) → M := fun y =>
    if h : Metric.infDist y (Set.range e) < ε then Classical.choose (huniq y h)
    else Classical.arbitrary M
  have hnp_def : ∀ y (h : Metric.infDist y (Set.range e) < ε),
      np y = Classical.choose (huniq y h) := by
    intro y h
    simp only [np]
    exact dif_pos h
  have hnp_dist : ∀ y, Metric.infDist y (Set.range e) < ε →
      dist y (e (np y)) = Metric.infDist y (Set.range e) := by
    intro y h
    rw [hnp_def y h]
    exact (Classical.choose_spec (huniq y h)).1
  have hnp_unique : ∀ y, Metric.infDist y (Set.range e) < ε → ∀ x : M,
      dist y (e x) = Metric.infDist y (Set.range e) → x = np y := by
    intro y h x hx
    rw [hnp_def y h]
    exact (Classical.choose_spec (huniq y h)).2 x hx
  -- The local chart data: for every `p` there is an open neighbourhood `O` of `e p` and a
  -- smooth genuinely-`ℝ^n`-valued map `η` with `η = chartAt p ∘ np` on `O`.
  have hloc : ∀ p : M, ∃ (O : Set (EuclideanSpace ℝ (Fin N)))
      (η : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n)),
      IsOpen O ∧ e p ∈ O ∧ (∀ y ∈ O, Metric.infDist y (Set.range e) < ε) ∧
      ContDiffOn ℝ ∞ η O ∧
      (∀ y ∈ O, np y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source ∧
        η y = (chartAt (EuclideanSpace ℝ (Fin n)) p) (np y)) :=
    fun p => Work.Drive.N2.exists_local_chart_data e he hinj himm hεpos np hnp_dist p
  let Oset : M → Set (EuclideanSpace ℝ (Fin N)) := fun p => Classical.choose (hloc p)
  let ηset : M → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n) :=
    fun p => Classical.choose (Classical.choose_spec (hloc p))
  have hOset : ∀ p, IsOpen (Oset p) ∧ e p ∈ Oset p ∧
      (∀ y ∈ Oset p, Metric.infDist y (Set.range e) < ε) ∧
      ContDiffOn ℝ ∞ (ηset p) (Oset p) ∧
      (∀ y ∈ Oset p, np y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source ∧
        ηset p y = (chartAt (EuclideanSpace ℝ (Fin n)) p) (np y)) :=
    fun p => Classical.choose_spec (Classical.choose_spec (hloc p))
  refine ⟨⋃ p, Oset p, np, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isOpen_iUnion fun p => (hOset p).1
  · intro x hx
    obtain ⟨x', rfl⟩ := hx
    exact mem_iUnion.mpr ⟨x', (hOset x').2.1⟩
  · refine (contMDiffOn_iUnion_iff_of_isOpen (f := np) (s := Oset)
      (fun p => (hOset p).1)).mpr ?_
    intro p
    have hsub : ∀ y ∈ Oset p, ηset p y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target := by
      intro y hy
      have hmem := ((hOset p).2.2.2.2) y hy
      rw [hmem.2]
      exact (chartAt (EuclideanSpace ℝ (Fin n)) p).map_source hmem.1
    have hcomp : ContMDiffOn (𝓡 N) (𝓡 n) ∞
        ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm ∘ ηset p) (Oset p) :=
      ContMDiffOn.comp (contMDiffOn_chart_symm (I := 𝓡 n) (x := p))
        (((hOset p).2.2.2.1).contMDiffOn) (fun y hy => hsub y hy)
    refine hcomp.congr ?_
    intro y hy
    have hmem := ((hOset p).2.2.2.2) y hy
    rw [Function.comp_apply, hmem.2]
    exact ((chartAt (EuclideanSpace ℝ (Fin n)) p).left_inv hmem.1).symm
  · intro x
    have h0 : Metric.infDist (e x) (Set.range e) = 0 := by
      refine le_antisymm ?_ Metric.infDist_nonneg
      calc Metric.infDist (e x) (Set.range e) ≤ dist (e x) (e x) :=
            Metric.infDist_le_dist_of_mem (Set.mem_range_self x)
        _ = 0 := dist_self _
    have hlt : Metric.infDist (e x) (Set.range e) < ε := by rw [h0]; exact hεpos
    have h := hnp_unique (e x) hlt x (by rw [dist_self, h0])
    exact h.symm
  · intro y hy
    obtain ⟨p, hp⟩ := mem_iUnion.mp hy
    exact hnp_dist y ((hOset p).2.2.1 y hp)
  · intro y hy
    obtain ⟨p, hp⟩ := mem_iUnion.mp hy
    have hmem : np y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source :=
      ((hOset p).2.2.2.2 y hp).1
    have hηeq : ηset p y = (chartAt (EuclideanSpace ℝ (Fin n)) p) (np y) :=
      ((hOset p).2.2.2.2 y hp).2
    have hinf : Metric.infDist y (Set.range e) < ε := (hOset p).2.2.1 y hp
    have hmin : ∀ z : M, dist y (e (np y)) ≤ dist y (e z) := by
      intro z
      rw [hnp_dist y hinf]
      exact Metric.infDist_le_dist_of_mem (Set.mem_range_self z)
    have hadj : (fderiv ℝ (Work.Embedding.chartRepN e p)
        (ηset p y)).adjoint (y - e (np y)) = 0 := by
      rw [hηeq]
      exact Work.Embedding.chartRepN_adjoint_min e he hmem hmin
    have hv : y - e (np y) ∈
        (fderiv ℝ (Work.Embedding.chartRepN e p) (ηset p y)).rangeᗮ := by
      rw [ContinuousLinearMap.orthogonal_range, LinearMap.mem_ker]
      simpa using hadj
    have hηdiff : ContDiffAt ℝ ∞ (ηset p) y :=
      ((hOset p).2.2.2.1).contDiffAt ((hOset p).1.mem_nhds hp)
    have hmemη : ηset p y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target := by
      rw [hηeq]
      exact (chartAt (EuclideanSpace ℝ (Fin n)) p).map_source hmem
    have hψdiff : DifferentiableAt ℝ (Work.Embedding.chartRepN e p) (ηset p y) :=
      (Work.Embedding.contDiffAt_chartRepN e he p hmemη).differentiableAt (by simp)
    have hηdiff' : DifferentiableAt ℝ (ηset p) y := hηdiff.differentiableAt (by simp)
    have hev : (fun z => e (np z)) =ᶠ[𝓝 y]
        (Work.Embedding.chartRepN e p ∘ ηset p) := by
      filter_upwards [((hOset p).1).mem_nhds hp] with z hz
      have hzmem := ((hOset p).2.2.2.2 z hz)
      show e (np z) = Work.Embedding.chartRepN e p (ηset p z)
      rw [hzmem.2]
      exact (Work.Embedding.chartRepN_chart e p (np z) hzmem.1).symm
    have hfderiv_eq : fderiv ℝ (fun z => e (np z)) y
        = fderiv ℝ (Work.Embedding.chartRepN e p ∘ ηset p) y :=
      Filter.EventuallyEq.fderiv_eq hev
    have hchain : fderiv ℝ (Work.Embedding.chartRepN e p ∘ ηset p) y
        = (fderiv ℝ (Work.Embedding.chartRepN e p) (ηset p y)).comp
            (fderiv ℝ (ηset p) y) :=
      fderiv_comp (x := y) (f := ηset p)
        (g := Work.Embedding.chartRepN e p) hψdiff hηdiff'
    have hrange : (fderiv ℝ (fun z => e (np z)) y).range
        ≤ (fderiv ℝ (Work.Embedding.chartRepN e p) (ηset p y)).range := by
      rw [hfderiv_eq, hchain]
      rintro u ⟨w, rfl⟩
      exact ⟨fderiv ℝ (ηset p) y w, rfl⟩
    exact Submodule.orthogonal_le hrange hv

end Work.Drive.N2
