import Mathlib
import Submission.Work.Drive.projCharted
import Submission.Work.Drive.ProjectiveChartDefs
import Submission.Work.Drive.ProjectiveTopology
import Submission.Work.Drive.exists_contDiff_extension_box
import Submission.Work.Drive.contMDiffAt_projCharted_iff
import Submission.Work.Drive.exists_chartedSpace_isManifold_projective

/-!
# Local extension of a `C^∞` map into `ℝP³` off a box

`Work.Drive.projCharted 3` is the transparent smooth structure on `ℝP³` whose atlas is the range of
the classical projective charts.  This file proves that a map `h : ℝ² → ℝP³` that is `C^∞` on the
closed box `[a,b] × [c,d]` can be extended, near each point of the box, to a genuinely smooth map
defined on a whole neighbourhood: there is an open `U ∋ x` and a map `H`, smooth on all of `U`,
with `H = h` on `U ∩ [a,b] × [c,d]`.

The proof is the standard one for maps into a manifold: pick a projective chart `projChart i` at
`h x`, so that `h = projChartInv i ∘ (projChartMap i ∘ h)` near `x`; the scalar function
`projChartMap i ∘ h` is `C^∞` (Whitney) on a small sub-box around `x`, so by the box extension
theorem it is the restriction of a globally `C^∞` function `G : ℝ² → ℝ³`, and
`H := projChartInv i ∘ G` is smooth everywhere and agrees with `h` on a neighbourhood of `x`
intersected with the box.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set

noncomputable section

set_option linter.style.haveILetI false

/-! ## Norm estimates on the plane `ℝ²` -/

private lemma eucl_two_norm_le_coords (z : EuclideanSpace ℝ (Fin 2)) :
    ‖z‖ ≤ |z 0| + |z 1| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  nlinarith [sq_abs (z 0), sq_abs (z 1), abs_nonneg (z 0), abs_nonneg (z 1),
    sq_nonneg (|z 0| + |z 1|)]

private lemma eucl_two_coord_le_norm (z : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    |z i| ≤ ‖z‖ := by
  have h := PiLp.norm_apply_le z i
  rwa [Real.norm_eq_abs] at h

private lemma eucl_two_sub_apply (q x : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    (q - x) i = q i - x i := by
  simp

/-! ## The sub-box around a point of `[a,b] × [c,d]` inside a given neighbourhood -/

/-- Given a neighbourhood `V` of a point `x` of the closed box `[a,b] × [c,d]` (certified by a
radius `ε` with `ball x ε ⊆ V`), there is a closed sub-box `[a',b'] × [c' d'] ⊆ [a,b] × [c,d]`
containing `x` and contained in `V`, together with a radius `r > 0` such that every point of
`[a,b] × [c,d]` at distance `< r` from `x` already lies in the sub-box. -/
private lemma exists_local_box {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {x : EuclideanSpace ℝ (Fin 2)} (hx0 : x 0 ∈ Set.Icc a b) (hx1 : x 1 ∈ Set.Icc c d)
    {V : Set (EuclideanSpace ℝ (Fin 2))} {ε : ℝ} (hε : 0 < ε) (hV : Metric.ball x ε ⊆ V) :
    ∃ a' b' c' d' r : ℝ, a' < b' ∧ c' < d' ∧ 0 < r ∧
      {q : EuclideanSpace ℝ (Fin 2) | q 0 ∈ Set.Icc a' b' ∧ q 1 ∈ Set.Icc c' d'} ⊆ V ∧
      {q : EuclideanSpace ℝ (Fin 2) | q 0 ∈ Set.Icc a' b' ∧ q 1 ∈ Set.Icc c' d'} ⊆
        {q : EuclideanSpace ℝ (Fin 2) | q 0 ∈ Set.Icc a b ∧ q 1 ∈ Set.Icc c d} ∧
      {q : EuclideanSpace ℝ (Fin 2) | q 0 ∈ Set.Icc a b ∧ q 1 ∈ Set.Icc c d} ∩
        Metric.ball x r ⊆
        {q : EuclideanSpace ℝ (Fin 2) | q 0 ∈ Set.Icc a' b' ∧ q 1 ∈ Set.Icc c' d'} := by
  have hδ : 0 < ε / 4 := by linarith
  refine ⟨max a (x 0 - ε / 4), min b (x 0 + ε / 4), max c (x 1 - ε / 4), min d (x 1 + ε / 4),
    ε / 4, ?_, ?_, hδ, ?_, ?_, ?_⟩
  · simp only [max_lt_iff, lt_min_iff]
    exact ⟨⟨hab, by linarith [hx0.2]⟩, ⟨by linarith [hx0.1], by linarith⟩⟩
  · simp only [max_lt_iff, lt_min_iff]
    exact ⟨⟨hcd, by linarith [hx1.2]⟩, ⟨by linarith [hx1.1], by linarith⟩⟩
  · -- the sub-box lies in the ball of radius `ε`
    intro q hq
    apply hV
    rw [Metric.mem_ball]
    have hq0 : q 0 ∈ Set.Icc (max a (x 0 - ε / 4)) (min b (x 0 + ε / 4)) := hq.1
    have hq1 : q 1 ∈ Set.Icc (max c (x 1 - ε / 4)) (min d (x 1 + ε / 4)) := hq.2
    rw [Set.mem_Icc] at hq0 hq1
    have h0 : |q 0 - x 0| ≤ ε / 4 := by
      rw [abs_le]
      exact ⟨by linarith [le_max_right a (x 0 - ε / 4), hq0.1],
             by linarith [min_le_right b (x 0 + ε / 4), hq0.2]⟩
    have h1 : |q 1 - x 1| ≤ ε / 4 := by
      rw [abs_le]
      exact ⟨by linarith [le_max_right c (x 1 - ε / 4), hq1.1],
             by linarith [min_le_right d (x 1 + ε / 4), hq1.2]⟩
    calc dist q x = ‖q - x‖ := dist_eq_norm q x
      _ ≤ |(q - x) 0| + |(q - x) 1| := eucl_two_norm_le_coords _
      _ = |q 0 - x 0| + |q 1 - x 1| := by rw [eucl_two_sub_apply, eucl_two_sub_apply]
      _ ≤ ε / 4 + ε / 4 := add_le_add h0 h1
      _ < ε := by linarith
  · -- the sub-box is inside the original box
    intro q hq
    have hq0 : q 0 ∈ Set.Icc (max a (x 0 - ε / 4)) (min b (x 0 + ε / 4)) := hq.1
    have hq1 : q 1 ∈ Set.Icc (max c (x 1 - ε / 4)) (min d (x 1 + ε / 4)) := hq.2
    rw [Set.mem_Icc] at hq0 hq1
    exact ⟨⟨le_trans (le_max_left _ _) hq0.1, le_trans hq0.2 (min_le_left _ _)⟩,
           ⟨le_trans (le_max_left _ _) hq1.1, le_trans hq1.2 (min_le_left _ _)⟩⟩
  · -- points of the box close to `x` lie in the sub-box
    intro q hq
    obtain ⟨hqB, hqb⟩ := hq
    have hd : ‖q - x‖ < ε / 4 := by
      have h := Metric.mem_ball.mp hqb
      rwa [dist_eq_norm] at h
    have h0 : |q 0 - x 0| < ε / 4 := by
      have h := eucl_two_coord_le_norm (q - x) 0
      rw [eucl_two_sub_apply] at h
      exact lt_of_le_of_lt h hd
    have h1 : |q 1 - x 1| < ε / 4 := by
      have h := eucl_two_coord_le_norm (q - x) 1
      rw [eucl_two_sub_apply] at h
      exact lt_of_le_of_lt h hd
    have hqB0 : q 0 ∈ Set.Icc a b := hqB.1
    have hqB1 : q 1 ∈ Set.Icc c d := hqB.2
    rw [Set.mem_Icc] at hqB0 hqB1
    rw [abs_lt] at h0 h1
    refine ⟨?_, ?_⟩
    · rw [Set.mem_Icc]
      exact ⟨max_le_iff.mpr ⟨hqB0.1, by linarith [h0.1]⟩,
             le_min_iff.mpr ⟨hqB0.2, by linarith [h0.2]⟩⟩
    · rw [Set.mem_Icc]
      exact ⟨max_le_iff.mpr ⟨hqB1.1, by linarith [h1.1]⟩,
             le_min_iff.mpr ⟨hqB1.2, by linarith [h1.2]⟩⟩

/-! ## The main theorem -/

theorem exists_localModel_projCharted (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    {h : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (EuclideanSpace ℝ (Fin 4))}
    (hh : letI := Work.Drive.projCharted 3
      ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞) h
        {q : EuclideanSpace ℝ (Fin 2) | q 0 ∈ Set.Icc a b ∧ q 1 ∈ Set.Icc c d}) :
    ∀ x : EuclideanSpace ℝ (Fin 2), x 0 ∈ Set.Icc a b → x 1 ∈ Set.Icc c d →
      ∃ U ∈ nhds x, ∃ H : EuclideanSpace ℝ (Fin 2) →
          Projectivization ℝ (EuclideanSpace ℝ (Fin 4)),
        (letI := Work.Drive.projCharted 3
         ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
           (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞) H U) ∧
        ∀ y ∈ U, y 0 ∈ Set.Icc a b → y 1 ∈ Set.Icc c d → H y = h y := by
  letI := Work.Drive.projCharted 3
  haveI hman : IsManifold (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Projectivization ℝ (EuclideanSpace ℝ (Fin (3 + 1)))) := isManifold_projCharted 3
  intro x hx0 hx1
  have hxB : x ∈ {q : EuclideanSpace ℝ (Fin 2) | q 0 ∈ Set.Icc a b ∧ q 1 ∈ Set.Icc c d} :=
    ⟨hx0, hx1⟩
  -- a projective chart at `h x`
  obtain ⟨i, hi⟩ := Work.Drive.exists_mem_projChartSource (h x)
  have hsrc_open : IsOpen (Work.Drive.projChartSource i) := by
    rw [← Work.Drive.projChart_source]
    exact (Work.Drive.projChart i).open_source
  -- around `x`, `h` stays in the source of that chart
  have hcwa : ContinuousWithinAt h
      {q : EuclideanSpace ℝ (Fin 2) | q 0 ∈ Set.Icc a b ∧ q 1 ∈ Set.Icc c d} x :=
    (hh.continuousOn).continuousWithinAt hxB
  have hpre : h ⁻¹' Work.Drive.projChartSource i ∈
      nhdsWithin x {q : EuclideanSpace ℝ (Fin 2) | q 0 ∈ Set.Icc a b ∧ q 1 ∈ Set.Icc c d} :=
    hcwa.preimage_mem_nhdsWithin (hsrc_open.mem_nhds hi)
  obtain ⟨U₁, hU₁, hU₁sub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hpre
  obtain ⟨ε₁, hε₁, hε₁sub⟩ := Metric.mem_nhds_iff.mp hU₁
  -- a sub-box around `x`, inside `U₁`, inside the box, and with a ball trapping the box
  obtain ⟨a', b', c', d', r, ha'b', hc'd', hr, hboxV, hboxB, hballbox⟩ :=
    exists_local_box hab hcd hx0 hx1 hε₁ hε₁sub
  -- the chart map is smooth on the chart source
  have hchart : ContMDiffOn (𝓡 3) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Drive.projChartMap i)
      (Work.Drive.projChartSource i) := by
    have he' : Work.Drive.projChart i ∈ IsManifold.maximalAtlas (𝓡 3)
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (Projectivization ℝ (EuclideanSpace ℝ (Fin (3 + 1)))) :=
      IsManifold.subset_maximalAtlas (Set.mem_range_self i)
    have hev := (Work.Drive.projChart i).contMDiffOn_extend (I := 𝓡 3) he'
    have hfun : ((Work.Drive.projChart i).extend (𝓡 3)) = Work.Drive.projChartMap i := by
      funext p
      rw [OpenPartialHomeomorph.extend_coe]
      simp [modelWithCornersSelf_coe, Work.Drive.projChart_apply]
    rw [Work.Drive.projChart_source] at hev
    rw [hfun] at hev
    exact hev
  -- the chart coordinates of `h` are `C^∞` on the sub-box
  have hΦ : ContMDiffOn (𝓡 2) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => Work.Drive.projChartMap i (h y))
      {q : EuclideanSpace ℝ (Fin 2) | q 0 ∈ Set.Icc a' b' ∧ q 1 ∈ Set.Icc c' d'} :=
    hchart.comp (hh.mono hboxB) (fun y hy => hU₁sub ⟨hboxV hy, hboxB hy⟩)
  have hΦ' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => Work.Drive.projChartMap i (h y))
      {q : EuclideanSpace ℝ (Fin 2) | q 0 ∈ Set.Icc a' b' ∧ q 1 ∈ Set.Icc c' d'} :=
    hΦ.contDiffOn
  -- extend the chart coordinates off the box
  obtain ⟨G, hG, hGval⟩ :=
    Work.Drive.exists_contDiff_extension_box a' b' c' d' ha'b' hc'd' hΦ'
  -- the inverse chart is smooth, everywhere
  have hInv : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) (𝓡 3)
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Drive.projChartInv i) Set.univ := by
    have he' : Work.Drive.projChart i ∈ IsManifold.maximalAtlas (𝓡 3)
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (Projectivization ℝ (EuclideanSpace ℝ (Fin (3 + 1)))) :=
      IsManifold.subset_maximalAtlas (Set.mem_range_self i)
    have h := contMDiffOn_symm_of_mem_maximalAtlas (I := 𝓡 3)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) he'
    rw [Work.Drive.projChart_target] at h
    exact h
  have hH : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => Work.Drive.projChartInv i (G y)) :=
    (contMDiffOn_univ.mp hInv).comp hG.contMDiff
  refine ⟨U₁ ∩ Metric.ball x r, Filter.inter_mem hU₁ (Metric.ball_mem_nhds x hr),
    fun y => Work.Drive.projChartInv i (G y), hH.contMDiffOn, ?_⟩
  intro y hy hy0 hy1
  have hyB : y ∈ {q : EuclideanSpace ℝ (Fin 2) | q 0 ∈ Set.Icc a b ∧ q 1 ∈ Set.Icc c d} :=
    ⟨hy0, hy1⟩
  have hysrc : h y ∈ Work.Drive.projChartSource i := hU₁sub ⟨hy.1, hyB⟩
  have hyB' : y ∈ {q : EuclideanSpace ℝ (Fin 2) | q 0 ∈ Set.Icc a' b' ∧ q 1 ∈ Set.Icc c' d'} :=
    hballbox ⟨hyB, hy.2⟩
  have hGv : G y = Work.Drive.projChartMap i (h y) := hGval y hyB'.1 hyB'.2
  show Work.Drive.projChartInv i (G y) = h y
  rw [hGv, Work.Drive.projChartInv_projChartMap hysrc]

end

end Work.Drive
