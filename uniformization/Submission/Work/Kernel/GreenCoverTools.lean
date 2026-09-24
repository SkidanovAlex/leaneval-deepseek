import Mathlib
import Submission.Work.Kernel.GreenCover
import Submission.Work.SimplyConnected.ABS.manifold_smooth_upgrade

/-!
# Tools for the existence of the chart-ball cover data

Three reusable lemmas on which the proof of `Work.Kernel.exists_greenCover` rests:

* `Work.Kernel.exists_chartBall_subset` — a chart ball around a point, inside a prescribed open set,
  with its model ball inside the chart target;
* `Work.Kernel.exists_contMDiff_eq_one_of_isClosed_subset_isOpen` — a smooth function `≡ 1` on a
  prescribed closed set whose topological support is contained in a prescribed open set (this is how
  the bumps `β` are built; the support bound comes from `SmoothPartitionOfUnity.exists_isSubordinate`,
  so that no closure of chart balls is ever needed);
* `Work.Kernel.chartDiff_of_contMDiff` — the chart representative of a smooth function is
  differentiable, i.e. `Work.Drive.ChartDiff` for smooth `f` in every chart of the atlas.
-/

open Set Metric
open scoped Manifold Topology

noncomputable section

namespace Work.Kernel

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **A chart ball around `y` inside a prescribed open set `O ∋ y`**, with its model ball inside the
chart target.  The chart ball is `source ∩ preimage` (junk values of `chartAt` are never met). -/
lemma exists_chartBall_subset {O : Set X} (hO : IsOpen O) {y : X} (hy : y ∈ O) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball ((chartAt ℂ y) y) ε ⊆ (chartAt ℂ y).target ∧
      Submission.chartBall (chartAt ℂ y) ((chartAt ℂ y) y) ε ⊆ O := by
  set c := chartAt ℂ y with hc
  have hyc : y ∈ c.source := mem_chart_source ℂ y
  have hop : IsOpen (c '' (O ∩ c.source)) :=
    c.isOpen_image_of_subset_source (hO.inter c.open_source) inter_subset_right
  have hmem : c y ∈ c '' (O ∩ c.source) := ⟨y, ⟨hy, hyc⟩, rfl⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hop _ hmem
  have hsub1 : c '' (O ∩ c.source) ⊆ c.target := by
    rintro z ⟨w, hw, rfl⟩
    exact c.map_source hw.2
  refine ⟨ε, hε, hεsub.trans hsub1, ?_⟩
  intro x hx
  obtain ⟨hxs, hxb⟩ := Submission.mem_chartBall.mp hx
  obtain ⟨w, hw, hwx⟩ := hεsub hxb
  have hxw : x = w := by
    rw [← c.left_inv hxs, ← hwx, c.left_inv hw.2]
  rw [hxw]; exact hw.1

/-- **A smooth bump `≡ 1` on a closed set with support in a prescribed open set.** -/
lemma exists_contMDiff_eq_one_of_isClosed_subset_isOpen [T2Space X] [SigmaCompactSpace X]
    [IsManifold (modelWithCornersSelf ℝ ℂ) ⊤ X]
    {C U : Set X} (hC : IsClosed C) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ β : X → ℝ, ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ)
        ((⊤ : ℕ∞) : WithTop ℕ∞) β ∧ (∀ x ∈ C, β x = 1) ∧ tsupport β ⊆ U := by
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate (modelWithCornersSelf ℝ ℂ) hC
    (fun _ : PUnit => U) (fun _ => hU) (by intro x hx; exact Set.mem_iUnion.mpr ⟨(), hCU hx⟩)
  refine ⟨fun x => f () x, ((f ()).contMDiff).of_le le_rfl, ?_, ?_⟩
  · intro x hx
    have h1 := f.sum_finsupport' x hx (Finset.subset_univ (f.finsupport x))
    simpa using h1
  · simpa using hf ()

/-- **The chart representative of a smooth function is differentiable**: `Work.Drive.ChartDiff` for
any chart of the atlas and any open set. -/
lemma chartDiff_of_contMDiff [IsManifold (modelWithCornersSelf ℝ ℂ) ⊤ X]
    {f : X → ℝ}
    (hf : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    {c : OpenPartialHomeomorph X ℂ} (hc : c ∈ atlas ℂ X) (Ω : Set X) :
    Work.Drive.ChartDiff c f Ω := by
  have hI : IsManifold (modelWithCornersSelf ℝ ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) X :=
    IsManifold.of_le (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) le_top
  have : IsManifold (modelWithCornersSelf ℝ ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) X := hI
  intro x hx
  have hG : HasGroupoid X
      (contDiffGroupoid ((⊤ : ℕ∞) : WithTop ℕ∞) (modelWithCornersSelf ℝ ℂ)) := inferInstance
  have hcmax : c ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ ℂ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) X := by
    intro e' he'
    exact ⟨hG.compatible hc he', hG.compatible he' hc⟩
  have hwit := (contMDiffWithinAt_iff_source_of_mem_maximalAtlas (I := modelWithCornersSelf ℝ ℂ)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (s := Set.univ) hcmax hx.2).mp
      ((hf.contMDiffAt (x := x)).contMDiffWithinAt)
  simp only [show ((modelWithCornersSelf ℝ ℂ : ModelWithCorners ℝ ℂ ℂ) : ℂ → ℂ) = id from rfl,
    show (((modelWithCornersSelf ℝ ℂ : ModelWithCorners ℝ ℂ ℂ).symm : ℂ → ℂ)) = id from rfl,
    OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply,
    Function.comp_id, Set.range_id, Set.inter_univ, Set.preimage_univ] at hwit
  rw [contMDiffWithinAt_univ] at hwit
  rw [contMDiffAt_iff_contDiffAt] at hwit
  exact hwit.differentiableAt (by simp)

end Work.Kernel
