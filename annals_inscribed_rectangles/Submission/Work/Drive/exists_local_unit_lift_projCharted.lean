import Mathlib
import Submission.Work.Drive.projCharted
import Submission.Work.Drive.ProjectiveChartDefs
import Submission.Work.Drive.exists_contDiff_extension_box
import Submission.Work.Drive.exists_localModel_projCharted

namespace Work.Drive

open scoped Manifold ContDiff LinearAlgebra.Projectivization

open Set

/-! ## Elementary norm estimates on the plane `ℝ²` -/

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

/-! ## A sub-box around a point of the box, inside a given neighbourhood -/

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

/-- **A local smooth unit lift of a `C^∞`-on-a-box map into `ℝP³`.**  Near every point `x` of the
box `[a,b] × [c,d]` a map `h` that is `C^∞` (Whitney) on the box admits a *globally defined*
`C^∞` nowhere-vanishing unit vector field `u : ℝ² → S³ ⊆ ℝ⁴` whose projective class reproduces
`h` on the box near `x`: `[u y] = h y` for `y` in the box with `dist y x < r`.  (`u` is the
standard section `projSection i` of the projective chart at `h x`, applied to a global smooth
extension of the chart coordinates of `h`, normalized.) -/
theorem exists_local_unit_lift_projCharted (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    {h : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (EuclideanSpace ℝ (Fin 4))}
    (hh : letI := Work.Drive.projCharted 3
      ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞) h
        {q : EuclideanSpace ℝ (Fin 2) | q 0 ∈ Set.Icc a b ∧ q 1 ∈ Set.Icc c d}) :
    ∀ x : EuclideanSpace ℝ (Fin 2), x 0 ∈ Set.Icc a b → x 1 ∈ Set.Icc c d →
      ∃ r : ℝ, 0 < r ∧ ∃ (u : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
          (hune : ∀ y, u y ≠ 0),
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u ∧ (∀ y, ‖u y‖ = 1) ∧
        ∀ y : EuclideanSpace ℝ (Fin 2), y 0 ∈ Set.Icc a b → y 1 ∈ Set.Icc c d →
          dist y x < r → Projectivization.mk ℝ (u y) (hune y) = h y := by
  letI := Work.Drive.projCharted 3
  haveI hman : IsManifold (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Projectivization ℝ (EuclideanSpace ℝ (Fin (3 + 1)))) := isManifold_projCharted 3
  intro x hx0 hx1
  set B : Set (EuclideanSpace ℝ (Fin 2)) :=
    {q : EuclideanSpace ℝ (Fin 2) | q 0 ∈ Set.Icc a b ∧ q 1 ∈ Set.Icc c d} with hBdef
  have hxB : x ∈ B := ⟨hx0, hx1⟩
  -- a projective chart at `h x`
  obtain ⟨i, hi⟩ := Work.Drive.exists_mem_projChartSource (h x)
  have hsrc_open : IsOpen (Work.Drive.projChartSource i) := by
    rw [← Work.Drive.projChart_source]
    exact (Work.Drive.projChart i).open_source
  -- around `x`, `h` stays in the source of that chart
  have hcwa : ContinuousWithinAt h B x := (hh.continuousOn).continuousWithinAt hxB
  have hpre : h ⁻¹' Work.Drive.projChartSource i ∈ nhdsWithin x B :=
    hcwa.preimage_mem_nhdsWithin (hsrc_open.mem_nhds hi)
  obtain ⟨U₁, hU₁, hU₁sub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hpre
  obtain ⟨ε₁, hε₁, hε₁sub⟩ := Metric.mem_nhds_iff.mp hU₁
  -- a sub-box around `x`, inside `U₁`, inside the box, trapping the box near `x`
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
  -- the vector field `y ↦ projSection i (G y)` and its normalisation
  have hvne : ∀ y, Work.Drive.projSection i (G y) ≠ 0 :=
    fun y => Work.Drive.projSection_ne_zero i (G y)
  have hune : ∀ y, (‖Work.Drive.projSection i (G y)‖)⁻¹ • Work.Drive.projSection i (G y) ≠ 0 :=
    fun y => smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr (hvne y))) (hvne y)
  have hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => Work.Drive.projSection i (G y)) := by
    refine (contDiff_piLp (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 4 => ℝ)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).mpr (fun k => ?_)
    rcases eq_or_ne k i with rfl | hk
    · simpa only [Work.Drive.projSection_apply_same] using
        (contDiff_const (c := (1 : ℝ)) :
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun _ : EuclideanSpace ℝ (Fin 2) => (1 : ℝ)))
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
      have hcoord : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : EuclideanSpace ℝ (Fin 2) => (G y).ofLp j) :=
        (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 => ℝ)
          (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (i := j)).comp hG
      simpa only [Work.Drive.projSection_apply_succAbove] using hcoord
  have hgunit : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => (‖Work.Drive.projSection i (G y)‖)⁻¹ • Work.Drive.projSection i (G y)) := by
    have hnorm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y => ‖Work.Drive.projSection i (G y)‖) := ContDiff.norm ℝ hv hvne
    exact (hnorm.inv (fun y => norm_ne_zero_iff.mpr (hvne y))).smul hv
  refine ⟨r, hr, (fun y => (‖Work.Drive.projSection i (G y)‖)⁻¹ •
    Work.Drive.projSection i (G y)), hune, hgunit, ?_, ?_⟩
  · intro y
    exact norm_smul_inv_norm (hvne y)
  · intro y hy0 hy1 hyd
    have hyB : y ∈ B := ⟨hy0, hy1⟩
    have hyball : y ∈ Metric.ball x r := Metric.mem_ball.mpr hyd
    have hsub : y ∈ {q : EuclideanSpace ℝ (Fin 2) | q 0 ∈ Set.Icc a' b' ∧ q 1 ∈ Set.Icc c' d'} :=
      hballbox ⟨hyB, hyball⟩
    have hGy : G y = Work.Drive.projChartMap i (h y) := hGval y hsub.1 hsub.2
    have hysrc : h y ∈ Work.Drive.projChartSource i := hU₁sub ⟨hboxV hsub, hboxB hsub⟩
    have h1 : Projectivization.mk ℝ ((‖Work.Drive.projSection i (G y)‖)⁻¹ •
        Work.Drive.projSection i (G y)) (hune y)
        = Projectivization.mk ℝ (Work.Drive.projSection i (G y)) (hvne y) := by
      refine (Projectivization.mk_eq_mk_iff' ℝ _ _ (hune y) (hvne y)).mpr
        ⟨(‖Work.Drive.projSection i (G y)‖)⁻¹, rfl⟩
    have h2 : Projectivization.mk ℝ (Work.Drive.projSection i (G y)) (hvne y) = h y := by
      change Work.Drive.projChartInv i (G y) = h y
      rw [hGy, Work.Drive.projChartInv_projChartMap hysrc]
    exact h1.trans h2

end Work.Drive
