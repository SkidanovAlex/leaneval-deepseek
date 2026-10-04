import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.EXT.Basic
import Submission.Work.Diff.STE.B3.goodSet_smooth_noT2
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData
import Submission.Work.Diff.STE.B3.MatGlob.isCompact_uniform_bound
import Submission.Work.Diff.STE.B3.MatGlob.abs_clm_apply_le
import Submission.Work.Diff.STE.B3.MatGlob.abs_bilin_le_of_sandwich

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- The class of sections `h` admitted by the global jet bound: symmetric, smooth chart matrix,
sandwiched between `lam · g₀` and `K · g₀`, with the chart-`e i` jet bound `K` on the `2σ i`-balls.
This packages the five hypotheses of the target so that the compactness argument can quantify over
them as a single family. -/
def Pack (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (lam K : ℝ)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) : Prop :=
  (∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u) ∧
  Work.Diff.STE.D.ChartData (I := I) (M := M) h ∧
  (∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v) ∧
  (∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v) ∧
  (∀ (i : ι₀) (c d r : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
    ‖z‖ ≤ 2 * D.σ i → |Work.Diff.STE.pdR r (D.mat i h c d) z| ≤ K)

/-- **Smoothness of the chart matrix in the orthonormal frame from `ChartData`.**  For a section `h`
whose chart matrix in the *coordinate* frame is smooth (`ChartData`), the chart matrix
`D.mat i h a b` in the orthonormal frame `e i` is smooth at every flat coordinate `y` whose
`flatToE`-image lies in the chart target.  (The proof is the `hsm` step of
`Work.Diff.STE.B3.R_contDiff_of_chartData`, extracted here because that file does not export it and
`Work.Diff.STE.Lead.Gal.gardJet_holds` — which has a copy — does not compile.) -/
lemma mat_contDiffAt_of_chartData
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (y : Fin (Module.finrank ℝ E) → ℝ)
    (hy : Work.Diff.STE.flatToE (I := I) (D.x₀ i) y ∈ (extChartAt I (D.x₀ i)).target) :
    ContDiffAt ℝ (⊤ : ℕ∞) (D.mat i h a b) y := by
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) (D.matChart i h a b) (extChartAt I (D.x₀ i)).target := by
    have hsec : ∀ x : M, ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
        (fun x : M => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x (h x)) x :=
      fun x => section_contMDiffAt_of_chartData (I := I) (M := M) hh x
    have hmat : ContMDiffOn I 𝓘(ℝ, ℝ) (⊤ : ℕ∞)
        (fun x : M => h x (D.e i a x) (D.e i b x)) Set.univ := by
      intro x _
      have hψ := (hsec x).contMDiffWithinAt (s := Set.univ)
      have hv : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) (⊤ : ℕ∞) (T% (D.e i a)) Set.univ x :=
        (D.hesm i a).contMDiffAt.contMDiffWithinAt
      have hw : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) (⊤ : ℕ∞) (T% (D.e i b)) Set.univ x :=
        (D.hesm i b).contMDiffAt.contMDiffWithinAt
      have hres := hψ.clm_bundle_apply₂ (F₁ := E) (F₂ := E) hv hw
      simp only [contMDiffWithinAt_totalSpace] at hres
      exact hres.2
    have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (⊤ : ℕ∞)
        (fun y : E => h ((extChartAt I (D.x₀ i)).symm y)
          (D.e i a ((extChartAt I (D.x₀ i)).symm y))
          (D.e i b ((extChartAt I (D.x₀ i)).symm y))) (extChartAt I (D.x₀ i)).target :=
      hmat.comp (contMDiffOn_extChartAt_symm (I := I) (x := D.x₀ i) (n := (⊤ : ℕ∞)))
        (fun y _ => Set.mem_univ _)
    exact hcomp.contDiffOn
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z => D.matChart i h a b (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z)) y :=
    (hsm.contDiffAt ((isOpen_extChartAt_target (I := I) (D.x₀ i)).mem_nhds hy)).comp y
      ((Work.Diff.STE.contDiff_flatToE (I := I) (x₀ := D.x₀ i)).contDiffAt)
  simpa only [Work.Diff.STE.B3Data.mat_eq] using h1

/-- **The enlargement margin and the uniform frame bound.**  There is a `δ > 0` such that the
enlarged flat ball `‖z‖ ≤ 2 σ j + δ` of every chart `j` still lies inside the chart target (so that
`D.pt j ·` is genuine there), and a constant `B` bounding the `g₀`-square of every frame vector
`D.e j a` on that enlarged ball.  (Own copy of
`Work.Diff.STE.B3.MatGlob.exists_delta_target_frame`, kept private because that module is in
flight.) -/
private lemma delta_target_frame_priv (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 ≤ B ∧
      (∀ (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j + δ →
        Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target) ∧
      (∀ (j : ι₀) (a : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
        ‖z‖ ≤ 2 * D.σ j + δ →
        g₀.inner (D.pt j z) (D.e j a (D.pt j z)) (D.e j a (D.pt j z)) ≤ B) := by
  classical
  have hmargin : ∀ j : ι₀, ∃ δj : ℝ, 0 < δj ∧ ∀ z : Fin (Module.finrank ℝ E) → ℝ,
      ‖z‖ ≤ 2 * D.σ j + δj →
        Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target := by
    intro j
    have hA : IsCompact {z : Fin (Module.finrank ℝ E) → ℝ | ‖z‖ ≤ 2 * D.σ j} := by
      rw [show {z : Fin (Module.finrank ℝ E) → ℝ | ‖z‖ ≤ 2 * D.σ j}
          = Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j) from by
        ext z; simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_eq_norm, sub_zero]]
      exact isCompact_closedBall _ _
    have hTopen : IsOpen (Work.Diff.STE.flatToE (I := I) (D.x₀ j) ⁻¹'
        (extChartAt I (D.x₀ j)).target) :=
      (isOpen_extChartAt_target (I := I) (D.x₀ j)).preimage
        (Work.Diff.STE.contDiff_flatToE (I := I) (D.x₀ j)).continuous
    obtain ⟨δj, hδjpos, hδjsub⟩ :=
      hA.exists_cthickening_subset_open hTopen (fun z hz => D.htarget j z hz)
    refine ⟨δj, hδjpos, fun z hz => hδjsub ?_⟩
    by_cases hle : ‖z‖ ≤ 2 * D.σ j
    · exact Metric.mem_cthickening_of_dist_le z z δj _ hle (by rw [dist_self]; exact hδjpos.le)
    · push_neg at hle
      have hσpos : 0 < 2 * D.σ j := by have := D.hσ j; linarith
      have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hσpos hle.le
      have hmem : ((2 * D.σ j / ‖z‖) • z) ∈ {z : Fin (Module.finrank ℝ E) → ℝ |
          ‖z‖ ≤ 2 * D.σ j} := by
        simp only [Set.mem_setOf_eq]
        rw [norm_smul, Real.norm_of_nonneg (by positivity),
          div_mul_cancel₀ (2 * D.σ j) hzpos.ne']
      refine Metric.mem_cthickening_of_dist_le z ((2 * D.σ j / ‖z‖) • z) δj _ hmem ?_
      have hvec : (1 - 2 * D.σ j / ‖z‖) • z = z - (2 * D.σ j / ‖z‖) • z := by
        rw [sub_smul, one_smul]
      have hnorm : ‖z - (2 * D.σ j / ‖z‖) • z‖ = ‖z‖ - 2 * D.σ j := by
        rw [← hvec, norm_smul,
          Real.norm_of_nonneg (by rw [sub_nonneg, div_le_one hzpos]; exact hle.le),
          sub_mul, one_mul, div_mul_cancel₀ (2 * D.σ j) hzpos.ne']
      rw [dist_eq_norm, hnorm]
      linarith
  by_cases hne : Nonempty ι₀
  · haveI : Nonempty ι₀ := hne
    choose δj hδjpos hδjmarg using hmargin
    set δ : ℝ := Finset.univ.inf' Finset.univ_nonempty δj with hδdef
    have hδpos : 0 < δ :=
      (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun i _ => hδjpos i)
    have hδle : ∀ j : ι₀, δ ≤ δj j := fun j => Finset.inf'_le δj (Finset.mem_univ j)
    have hmarg : ∀ (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j + δ →
        Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target :=
      fun j z hz => hδjmarg j z (le_trans hz (by linarith [hδle j]))
    by_cases hne2 : Nonempty (Fin (Module.finrank ℝ E))
    · haveI : Nonempty (Fin (Module.finrank ℝ E)) := hne2
      have hframe : ∀ ja : ι₀ × Fin (Module.finrank ℝ E), ∃ B : ℝ,
          ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ ja.1 + δ →
            g₀.inner (D.pt ja.1 z) (D.e ja.1 ja.2 (D.pt ja.1 z))
              (D.e ja.1 ja.2 (D.pt ja.1 z)) ≤ B := by
        intro ja
        obtain ⟨j, a⟩ := ja
        have hcomp : IsCompact {z : Fin (Module.finrank ℝ E) → ℝ | ‖z‖ ≤ 2 * D.σ j + δ} := by
          rw [show {z : Fin (Module.finrank ℝ E) → ℝ | ‖z‖ ≤ 2 * D.σ j + δ}
              = Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ) from by
            ext z; simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_eq_norm, sub_zero]]
          exact isCompact_closedBall _ _
        have hcont : ContinuousOn (fun z => g₀.inner (D.pt j z) (D.e j a (D.pt j z))
            (D.e j a (D.pt j z))) {z : Fin (Module.finrank ℝ E) → ℝ | ‖z‖ ≤ 2 * D.σ j + δ} := by
          intro z hz
          have hzt : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z
              ∈ interior (extChartAt I (D.x₀ j)).target := by
            rw [IsOpen.interior_eq (isOpen_extChartAt_target (I := I) (D.x₀ j))]
            exact hmarg j z (by simpa only [Set.mem_setOf_eq] using hz)
          have hpt := Work.Diff.STE.D.pt_contMDiffAt_of_mem_interior (I := I) D j z hzt
          have hpair := Work.EXT.ONF.pairing g₀ (D.pt j z)
            ((D.hesm j a).contMDiffAt) ((D.hesm j a).contMDiffAt)
          exact ((contMDiffAt_iff_contDiffAt.mp (hpair.comp z hpt)).continuousAt).continuousWithinAt
        obtain ⟨B, hB⟩ := hcomp.exists_bound_of_continuousOn hcont
        refine ⟨B, fun z hz => ?_⟩
        have h1 := hB z (by simpa only [Set.mem_setOf_eq] using hz)
        rw [Real.norm_eq_abs] at h1
        exact le_trans (le_abs_self _) h1
      choose Bf hBf using hframe
      refine ⟨δ, max 0 (Finset.univ.sup' Finset.univ_nonempty Bf), hδpos, le_max_left _ _, hmarg,
        fun j a z hz => ?_⟩
      exact le_trans (hBf (j, a) z hz)
        (le_trans (Finset.le_sup' Bf (Finset.mem_univ (j, a))) (le_max_right _ _))
    · refine ⟨δ, 0, hδpos, le_refl 0, hmarg, fun j a => (hne2 ⟨a⟩).elim⟩
  · exact ⟨1, 0, one_pos, le_refl 0, (fun j => (hne ⟨j⟩).elim), (fun j => (hne ⟨j⟩).elim)⟩

/-- **The cross-chart expansion of the chart matrix.**  If `e i` is `g₀`-orthonormal at the
point of flat coordinate `z` of chart `j` (which `hτ` and `hsrc` guarantee), then the chart matrix of
`h` in the frame `e j` equals its chart matrix in the frame `e i` at the chart-`i` coordinate of
`D.pt j z`, contracted with the frame-change coefficients.  (Own copy of
`Work.Diff.STE.B3.MatGlob.mat_expansion`, kept private because that module is in flight.) -/
private lemma mat_expansion_priv
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E))
    (z : Fin (Module.finrank ℝ E) → ℝ)
    (hsrc : D.pt j z ∈ (extChartAt I (D.x₀ i)).source)
    (hτ : ‖Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)‖ ≤ 2 * D.σ i) :
    D.mat j h a b z
      = ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
        (g₀.inner (D.pt j z) (D.e j a (D.pt j z)) (D.e i c (D.pt j z)))
          * (g₀.inner (D.pt j z) (D.e j b (D.pt j z)) (D.e i d (D.pt j z)))
          * D.mat i h c d (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)) := by
  classical
  have hpt : D.pt i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)) = D.pt j z :=
    D.pt_coord i hsrc
  have hON : Submission.Diff.IsONFrame g₀ (D.pt j z) (fun c => D.e i c (D.pt j z)) := by
    have hh := D.heON i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)) hτ
    have h2 : (extChartAt I (D.x₀ i)).symm
          (Work.Diff.STE.flatToE (I := I) (D.x₀ i)
            (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)))
        = (extChartAt I (D.x₀ j)).symm (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) := hpt
    rw [h2] at hh
    exact hh
  have hmat : ∀ c d : Fin (Module.finrank ℝ E),
      D.mat i h c d (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z))
        = h (D.pt j z) (D.e i c (D.pt j z)) (D.e i d (D.pt j z)) := by
    intro c d
    show h (D.pt i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)))
        (D.e i c (D.pt i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z))))
        (D.e i d (D.pt i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z))))
      = h (D.pt j z) (D.e i c (D.pt j z)) (D.e i d (D.pt j z))
    rw [hpt]
  have hX := Work.EXT.sum_inner_smul_eq_self_of_isONFrame g₀ (D.pt j z)
    (fun c => D.e i c (D.pt j z)) hON (D.e j a (D.pt j z))
  have hY := Work.EXT.sum_inner_smul_eq_self_of_isONFrame g₀ (D.pt j z)
    (fun c => D.e i c (D.pt j z)) hON (D.e j b (D.pt j z))
  have hmain : h (D.pt j z)
        (∑ c : Fin (Module.finrank ℝ E),
          g₀.inner (D.pt j z) (D.e j a (D.pt j z)) (D.e i c (D.pt j z)) • D.e i c (D.pt j z))
        (∑ d : Fin (Module.finrank ℝ E),
          g₀.inner (D.pt j z) (D.e j b (D.pt j z)) (D.e i d (D.pt j z)) • D.e i d (D.pt j z))
      = ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          (g₀.inner (D.pt j z) (D.e j a (D.pt j z)) (D.e i c (D.pt j z)))
            * (g₀.inner (D.pt j z) (D.e j b (D.pt j z)) (D.e i d (D.pt j z)))
            * h (D.pt j z) (D.e i c (D.pt j z)) (D.e i d (D.pt j z)) := by
    have step1 : h (D.pt j z)
          (∑ c : Fin (Module.finrank ℝ E),
            g₀.inner (D.pt j z) (D.e j a (D.pt j z)) (D.e i c (D.pt j z)) • D.e i c (D.pt j z))
        = ∑ c : Fin (Module.finrank ℝ E),
            g₀.inner (D.pt j z) (D.e j a (D.pt j z)) (D.e i c (D.pt j z))
              • h (D.pt j z) (D.e i c (D.pt j z)) := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun c _ => map_smul (h (D.pt j z)) _ _)
    rw [step1]
    rw [sum_apply]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [smul_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [map_smul, smul_smul, smul_eq_mul]
  calc D.mat j h a b z
      = h (D.pt j z) (D.e j a (D.pt j z)) (D.e j b (D.pt j z)) := rfl
    _ = h (D.pt j z)
          (∑ c : Fin (Module.finrank ℝ E),
            g₀.inner (D.pt j z) (D.e j a (D.pt j z)) (D.e i c (D.pt j z))
              • D.e i c (D.pt j z))
          (∑ d : Fin (Module.finrank ℝ E),
            g₀.inner (D.pt j z) (D.e j b (D.pt j z)) (D.e i d (D.pt j z))
              • D.e i d (D.pt j z)) := by
        conv_lhs => rw [← hX, ← hY]
    _ = ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          (g₀.inner (D.pt j z) (D.e j a (D.pt j z)) (D.e i c (D.pt j z)))
            * (g₀.inner (D.pt j z) (D.e j b (D.pt j z)) (D.e i d (D.pt j z)))
            * h (D.pt j z) (D.e i c (D.pt j z)) (D.e i d (D.pt j z)) := hmain
    _ = ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          (g₀.inner (D.pt j z) (D.e j a (D.pt j z)) (D.e i c (D.pt j z)))
            * (g₀.inner (D.pt j z) (D.e j b (D.pt j z)) (D.e i d (D.pt j z)))
            * D.mat i h c d (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)) := by
        refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
        rw [hmat c d]

/-- **The local derivative bound, at a fixed chart and a fixed triple of indices.**

For `z` in the enlarged flat ball of chart `j`, the first flat derivative of the chart matrix
`D.mat j h a b` is bounded *uniformly over the whole class `Pack D lam K`* on a neighbourhood of
`z`, with a constant depending only on `D`, `lam`, `K`, the point `z` and the triple `(a,b,r)`.

The point `D.pt j z` is covered by the `σ i`-ball of some chart `i` (`B3Data.hcover`); expanding
`h` in the orthonormal frame `e i` turns `D.mat j h a b` near `z` into the sum
`Σ_{cd} A_c B_d · (D.mat i h c d ∘ T)` with `A_c`, `B_d` the frame pairings and `T` the transition
map `coord i ∘ pt j`, all of which are `C^∞` on the (`D`-dependent, `h`-independent) region
`goodSet i j`; the chain rule then bounds the derivative by the data-dependent factorials of
`A_c`, `B_d`, `T` at `z`, the bound `X` of the hypothesis for the partials of `D.mat i h c d`, and
the sandwich bound `|D.mat i h c d| ≤ 2K`.  Since every constant is independent of `h`, so is the
final bound. -/
private lemma local_bound_triple
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (lam K : ℝ) (hlam : 0 ≤ lam)
    (hK : 0 ≤ K) (δ : ℝ)
    (hδtarget : ∀ (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ),
      ‖z‖ ≤ 2 * D.σ j + δ →
        Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target)
    (j : ι₀) (a b r : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ)
    (hz : ‖z‖ ≤ 2 * D.σ j + δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ u ∈ 𝓝 z,
      ∀ y ∈ u, ∀ q : {h : Work.Diff.STE.Bil (I := I) (M := M) // Pack D lam K h},
        |Work.Diff.STE.pdR r (D.mat j q.1 a b) y| ≤ C := by
  classical
  -- the chart covering the point `D.pt j z`
  obtain ⟨i, hsrc, hcoord⟩ := D.hcover (D.pt j z)
  have hσi : 0 < D.σ i := D.hσ i
  have hτz : ‖Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)‖ ≤ 2 * D.σ i := by
    refine le_trans hcoord ?_; linarith
  have hzgood : z ∈ Work.Diff.STE.D.goodSet (I := I) (M := M) D i j := by
    refine ⟨?_, hsrc, ?_⟩
    · rw [IsOpen.interior_eq (isOpen_extChartAt_target (I := I) (D.x₀ j))]
      exact hδtarget j z hz
    · rw [IsOpen.interior_eq (isOpen_extChartAt_target (I := I) (D.x₀ i)),
        ← noT2_flatToE_coord (I := I) (M := M) D i hsrc]
      exact D.htarget i _ hτz
  -- the fixed, `h`-independent functions
  set A : Fin (Module.finrank ℝ E) → (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
    fun c w => g₀.inner (D.pt j w) (D.e j a (D.pt j w)) (D.e i c (D.pt j w)) with hA
  set B : Fin (Module.finrank ℝ E) → (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
    fun d w => g₀.inner (D.pt j w) (D.e j b (D.pt j w)) (D.e i d (D.pt j w)) with hB
  set T : (Fin (Module.finrank ℝ E) → ℝ) → (Fin (Module.finrank ℝ E) → ℝ) :=
    Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j with hT
  have hTapply : ∀ w : Fin (Module.finrank ℝ E) → ℝ,
      T w = Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j w) := by
    intro w
    simp only [hT, Work.Diff.STE.D.tMapFun_apply]
  have hAsm : ∀ {w : Fin (Module.finrank ℝ E) → ℝ}, w ∈ Work.Diff.STE.D.goodSet D i j →
      ∀ c : Fin (Module.finrank ℝ E), ContDiffAt ℝ (⊤ : ℕ∞) (A c) w := by
    intro w hw c
    simpa only [hA] using noT2_contDiffAt_pairing_pt (I := I) (M := M) D i j j a c hw
  have hBsm : ∀ {w : Fin (Module.finrank ℝ E) → ℝ}, w ∈ Work.Diff.STE.D.goodSet D i j →
      ∀ d : Fin (Module.finrank ℝ E), ContDiffAt ℝ (⊤ : ℕ∞) (B d) w := by
    intro w hw d
    simpa only [hB] using noT2_contDiffAt_pairing_pt (I := I) (M := M) D i j j b d hw
  have hTsm : ∀ {w : Fin (Module.finrank ℝ E) → ℝ}, w ∈ Work.Diff.STE.D.goodSet D i j →
      ContDiffAt ℝ (⊤ : ℕ∞) T w := by
    intro w hw
    simpa only [hT] using noT2_tMapFun_contDiffAt (I := I) (M := M) D i j hw
  -- the constant
  set Cst : ℝ := ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
      ((|A c z| + 1) * (|B d z| + 1)
          * ((Module.finrank ℝ E : ℝ) * K * (‖fderiv ℝ T z‖ + 1))
        + 2 * K * ((|A c z| + 1) * (‖fderiv ℝ (B d) z‖ + 1)
          + (|B d z| + 1) * (‖fderiv ℝ (A c) z‖ + 1))) with hCst
  refine ⟨Cst, ?_, ?_⟩
  · rw [hCst]
    refine Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun d _ => add_nonneg ?_ ?_
    · exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
        (mul_nonneg (mul_nonneg (by positivity) hK) (by positivity))
    · exact mul_nonneg (by positivity)
        (add_nonneg (mul_nonneg (by positivity) (by positivity))
          (mul_nonneg (by positivity) (by positivity)))
  · -- the neighbourhood on which all the `h`-independent constants hold
    have hTlt : ‖T z‖ < 2 * D.σ i := by
      rw [hTapply z]; exact lt_of_le_of_lt hcoord (by linarith)
    have hAnhds : ∀ c, {y | |A c y| < |A c z| + 1} ∈ 𝓝 z := fun c =>
      ((hAsm hzgood c).continuousAt.abs).eventually_lt continuousAt_const (by linarith)
    have hAdnhds : ∀ c, {y | ‖fderiv ℝ (A c) y‖ < ‖fderiv ℝ (A c) z‖ + 1} ∈ 𝓝 z := fun c =>
      (((hAsm hzgood c).fderiv_right (m := (1 : WithTop ℕ∞)) (by simp)).continuousAt.norm)
        |>.eventually_lt continuousAt_const (by linarith)
    have hBnhds : ∀ d, {y | |B d y| < |B d z| + 1} ∈ 𝓝 z := fun d =>
      ((hBsm hzgood d).continuousAt.abs).eventually_lt continuousAt_const (by linarith)
    have hBdnhds : ∀ d, {y | ‖fderiv ℝ (B d) y‖ < ‖fderiv ℝ (B d) z‖ + 1} ∈ 𝓝 z := fun d =>
      (((hBsm hzgood d).fderiv_right (m := (1 : WithTop ℕ∞)) (by simp)).continuousAt.norm)
        |>.eventually_lt continuousAt_const (by linarith)
    have hTnhds : {y | ‖T y‖ < 2 * D.σ i} ∈ 𝓝 z :=
      (((hTsm hzgood).continuousAt).norm).eventually_lt continuousAt_const hTlt
    have hTdnhds : {y | ‖fderiv ℝ T y‖ < ‖fderiv ℝ T z‖ + 1} ∈ 𝓝 z :=
      (((hTsm hzgood).fderiv_right (m := (1 : WithTop ℕ∞)) (by simp)).continuousAt.norm)
        |>.eventually_lt continuousAt_const (by linarith)
    have hUnhds : (Work.Diff.STE.D.goodSet (I := I) (M := M) D i j
        ∩ {y | ‖T y‖ < 2 * D.σ i}
        ∩ (⋂ c, {y | |A c y| < |A c z| + 1})
        ∩ (⋂ c, {y | ‖fderiv ℝ (A c) y‖ < ‖fderiv ℝ (A c) z‖ + 1})
        ∩ (⋂ d, {y | |B d y| < |B d z| + 1})
        ∩ (⋂ d, {y | ‖fderiv ℝ (B d) y‖ < ‖fderiv ℝ (B d) z‖ + 1})
        ∩ {y | ‖fderiv ℝ T y‖ < ‖fderiv ℝ T z‖ + 1}) ∈ 𝓝 z := by
      refine Filter.inter_mem (Filter.inter_mem (Filter.inter_mem
        (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem ?_ hTnhds)
          (Filter.iInter_mem.mpr hAnhds)) (Filter.iInter_mem.mpr hAdnhds))
          (Filter.iInter_mem.mpr hBnhds)) (Filter.iInter_mem.mpr hBdnhds)) hTdnhds
      exact (noT2_isOpen_goodSet (I := I) (M := M) D i j).mem_nhds hzgood
    refine ⟨_, hUnhds, ?_⟩
    intro y hy
    obtain ⟨⟨⟨⟨⟨⟨hy1, hy2⟩, hy3⟩, hy4⟩, hy5⟩, hy6⟩, hy7⟩ := hy
    intro q
    obtain ⟨h, hsym, hchart, hell, hub, hjet⟩ := q
    -- the cross-chart expansion holds eventually at `y`
    have hident : (fun w => D.mat j h a b w) =ᶠ[𝓝 y]
        (fun w => ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          (A c w * B d w) * D.mat i h c d (T w)) := by
      have h1 : Work.Diff.STE.D.goodSet (I := I) (M := M) D i j ∈ 𝓝 y :=
        (noT2_isOpen_goodSet (I := I) (M := M) D i j).mem_nhds hy1
      have h2 : {w | ‖T w‖ < 2 * D.σ i} ∈ 𝓝 y :=
        (((hTsm hy1).continuousAt).norm).eventually_lt continuousAt_const hy2
      filter_upwards [h1, h2] with w hw1 hw2
      have hme := mat_expansion_priv (I := I) (M := M) D i j h a b w hw1.2.1 (le_of_lt hw2)
      simpa only [hA, hB, hT, Work.Diff.STE.D.tMapFun_apply] using hme
    -- the point `D.pt i (T y)` is `D.pt j y`
    have hpt : D.pt i (T y) = D.pt j y := by
      have h := D.pt_coord i hy1.2.1
      rwa [← hTapply y] at h
    have hty : Work.Diff.STE.flatToE (I := I) (D.x₀ i) (T y)
        ∈ (extChartAt I (D.x₀ i)).target := by
      rw [hTapply y, noT2_flatToE_coord (I := I) (M := M) D i hy1.2.1]
      exact interior_subset hy1.2.2
    have hmat_sm : ∀ c d, ContDiffAt ℝ (⊤ : ℕ∞) (D.mat i h c d) (T y) := fun c d =>
      mat_contDiffAt_of_chartData (I := I) (M := M) D h hchart i c d (T y) hty
    -- the derivative of the expansion, term by term
    have hterm : ∀ c d, HasFDerivAt (fun w => (A c w * B d w) * D.mat i h c d (T w))
        ((A c y * B d y) • ((fderiv ℝ (D.mat i h c d) (T y)).comp (fderiv ℝ T y))
          + (D.mat i h c d (T y)) •
            ((A c y) • fderiv ℝ (B d) y + (B d y) • fderiv ℝ (A c) y)) y := by
      intro c d
      have hAy : HasFDerivAt (A c) (fderiv ℝ (A c) y) y :=
        ((hAsm hy1 c).differentiableAt (by simp)).hasFDerivAt
      have hBy : HasFDerivAt (B d) (fderiv ℝ (B d) y) y :=
        ((hBsm hy1 d).differentiableAt (by simp)).hasFDerivAt
      have hTy : HasFDerivAt T (fderiv ℝ T y) y :=
        ((hTsm hy1).differentiableAt (by simp)).hasFDerivAt
      have hFy : HasFDerivAt (D.mat i h c d) (fderiv ℝ (D.mat i h c d) (T y)) (T y) :=
        ((hmat_sm c d).differentiableAt (by simp)).hasFDerivAt
      have hcomp : HasFDerivAt (fun w => D.mat i h c d (T w))
          ((fderiv ℝ (D.mat i h c d) (T y)).comp (fderiv ℝ T y)) y := hFy.comp y hTy
      exact (hAy.mul hBy).mul hcomp
    have hsum_fun : HasFDerivAt
        (∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          fun w => (A c w * B d w) * D.mat i h c d (T w))
        (∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          ((A c y * B d y) • ((fderiv ℝ (D.mat i h c d) (T y)).comp (fderiv ℝ T y))
            + (D.mat i h c d (T y)) •
              ((A c y) • fderiv ℝ (B d) y + (B d y) • fderiv ℝ (A c) y))) y :=
      HasFDerivAt.sum (u := Finset.univ) fun c _ =>
        HasFDerivAt.sum (u := Finset.univ) fun d _ => hterm c d
    have hsum : HasFDerivAt
        (fun w => ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          (A c w * B d w) * D.mat i h c d (T w))
        (∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          ((A c y * B d y) • ((fderiv ℝ (D.mat i h c d) (T y)).comp (fderiv ℝ T y))
            + (D.mat i h c d (T y)) •
              ((A c y) • fderiv ℝ (B d) y + (B d y) • fderiv ℝ (A c) y))) y := by
      rw [show (∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
            fun w => (A c w * B d w) * D.mat i h c d (T w))
          = (fun w => ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
            (A c w * B d w) * D.mat i h c d (T w)) from by
        funext w; simp only [Finset.sum_apply]] at hsum_fun
      exact hsum_fun
    rw [show Work.Diff.STE.pdR r (D.mat j h a b) y
        = fderiv ℝ (fun w => D.mat j h a b w) y (Pi.single r 1) from rfl,
      hident.fderiv_eq, hsum.fderiv, hCst]
    -- the estimate
    have hbnd : |(∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          ((A c y * B d y) • ((fderiv ℝ (D.mat i h c d) (T y)).comp (fderiv ℝ T y))
            + (D.mat i h c d (T y)) •
              ((A c y) • fderiv ℝ (B d) y + (B d y) • fderiv ℝ (A c) y)))
        (Pi.single r (1 : ℝ))|
        ≤ ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
            ((|A c z| + 1) * (|B d z| + 1)
                * ((Module.finrank ℝ E : ℝ) * K * (‖fderiv ℝ T z‖ + 1))
              + 2 * K * ((|A c z| + 1) * (‖fderiv ℝ (B d) z‖ + 1)
                + (|B d z| + 1) * (‖fderiv ℝ (A c) z‖ + 1))) := by
      -- factor the sandwich bound and the hypothesis bound
      have hF1 : ∀ c d, |D.mat i h c d (T y)| ≤ 2 * K := by
        intro c d
        have hON : Submission.Diff.IsONFrame g₀ (D.pt j y) (fun c => D.e i c (D.pt j y)) := by
          have hh := D.heON i (T y) (le_of_lt hy2)
          have h2 : (extChartAt I (D.x₀ i)).symm (Work.Diff.STE.flatToE (I := I) (D.x₀ i) (T y))
              = (extChartAt I (D.x₀ j)).symm
                  (Work.Diff.STE.flatToE (I := I) (D.x₀ j) y) := hpt
          rw [h2] at hh
          exact hh
        have h1 := MatGlob.abs_bilin_le_of_sandwich (I := I) (M := M) (g₀ := g₀) (h := h)
          (lam := lam) (K := K) hlam hK hsym hell hub (D.pt j y)
          (D.e i c (D.pt j y)) (D.e i d (D.pt j y))
        have h2 : g₀.inner (D.pt j y) (D.e i c (D.pt j y)) (D.e i c (D.pt j y)) = 1 := by
          simpa using hON c c
        have h3 : g₀.inner (D.pt j y) (D.e i d (D.pt j y)) (D.e i d (D.pt j y)) = 1 := by
          simpa using hON d d
        rw [h2, h3] at h1
        have h4 : D.mat i h c d (T y)
            = h (D.pt i (T y)) (D.e i c (D.pt i (T y))) (D.e i d (D.pt i (T y))) := rfl
        rw [h4, hpt]
        linarith [h1]
      have hF2 : ∀ c d, (∑ s : Fin (Module.finrank ℝ E),
          |Work.Diff.STE.pdR s (D.mat i h c d) (T y)|) ≤ (Module.finrank ℝ E : ℝ) * K := by
        intro c d
        calc (∑ s : Fin (Module.finrank ℝ E), |Work.Diff.STE.pdR s (D.mat i h c d) (T y)|)
            ≤ ∑ _s : Fin (Module.finrank ℝ E), K :=
              Finset.sum_le_sum fun s _ => hjet i c d s (T y) (le_of_lt hy2)
          _ = (Module.finrank ℝ E : ℝ) * K := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hw1 : ‖(fderiv ℝ T y) (Pi.single r (1 : ℝ))‖ ≤ ‖fderiv ℝ T y‖ := by
        refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
        rw [Pi.norm_single, norm_one, mul_one]
      have hL1 : ∀ c d, |(fderiv ℝ (D.mat i h c d) (T y))
            ((fderiv ℝ T y) (Pi.single r (1 : ℝ)))|
          ≤ ((Module.finrank ℝ E : ℝ) * K) * (‖fderiv ℝ T z‖ + 1) := by
        intro c d
        refine le_trans (MatGlob.abs_clm_apply_le _ _) ?_
        refine le_trans (mul_le_mul (hF2 c d) hw1 (norm_nonneg _) (by positivity)) ?_
        exact mul_le_mul_of_nonneg_left (le_of_lt hy7) (by positivity)
      have hL2 : ∀ d, |(fderiv ℝ (B d) y) (Pi.single r (1 : ℝ))| ≤ ‖fderiv ℝ (B d) z‖ + 1 := by
        intro d
        rw [← Real.norm_eq_abs]
        refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
        rw [Pi.norm_single, norm_one, mul_one]
        exact le_of_lt ((Set.mem_iInter.mp hy6) d)
      have hL3 : ∀ c, |(fderiv ℝ (A c) y) (Pi.single r (1 : ℝ))| ≤ ‖fderiv ℝ (A c) z‖ + 1 := by
        intro c
        rw [← Real.norm_eq_abs]
        refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
        rw [Pi.norm_single, norm_one, mul_one]
        exact le_of_lt ((Set.mem_iInter.mp hy4) c)
      have htermbound : ∀ c d, |((A c y * B d y) •
              ((fderiv ℝ (D.mat i h c d) (T y)).comp (fderiv ℝ T y))
            + (D.mat i h c d (T y)) •
              ((A c y) • fderiv ℝ (B d) y + (B d y) • fderiv ℝ (A c) y)) (Pi.single r (1 : ℝ))|
          ≤ (|A c z| + 1) * (|B d z| + 1)
              * ((Module.finrank ℝ E : ℝ) * K * (‖fderiv ℝ T z‖ + 1))
            + 2 * K * ((|A c z| + 1) * (‖fderiv ℝ (B d) z‖ + 1)
              + (|B d z| + 1) * (‖fderiv ℝ (A c) z‖ + 1)) := by
        intro c d
        have hev : ((A c y * B d y) •
              ((fderiv ℝ (D.mat i h c d) (T y)).comp (fderiv ℝ T y))
            + (D.mat i h c d (T y)) •
              ((A c y) • fderiv ℝ (B d) y + (B d y) • fderiv ℝ (A c) y)) (Pi.single r (1 : ℝ))
            = (A c y * B d y) * ((fderiv ℝ (D.mat i h c d) (T y))
                ((fderiv ℝ T y) (Pi.single r (1 : ℝ))))
              + (D.mat i h c d (T y)) * ((A c y) * ((fderiv ℝ (B d) y) (Pi.single r (1 : ℝ)))
                + (B d y) * ((fderiv ℝ (A c) y) (Pi.single r (1 : ℝ)))) := by
          simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
        rw [hev]
        have h1 : |(A c y * B d y) * ((fderiv ℝ (D.mat i h c d) (T y))
              ((fderiv ℝ T y) (Pi.single r (1 : ℝ))))|
            ≤ (|A c z| + 1) * (|B d z| + 1)
              * ((Module.finrank ℝ E : ℝ) * K * (‖fderiv ℝ T z‖ + 1)) := by
          rw [abs_mul, abs_mul]
          exact mul_le_mul
            (mul_le_mul (le_of_lt ((Set.mem_iInter.mp hy3) c)) (le_of_lt ((Set.mem_iInter.mp hy5) d)) (abs_nonneg _) (by positivity))
            (hL1 c d) (abs_nonneg _) (by positivity)
        have h2 : |(D.mat i h c d (T y)) * ((A c y) * ((fderiv ℝ (B d) y) (Pi.single r (1 : ℝ)))
              + (B d y) * ((fderiv ℝ (A c) y) (Pi.single r (1 : ℝ))))|
            ≤ 2 * K * ((|A c z| + 1) * (‖fderiv ℝ (B d) z‖ + 1)
              + (|B d z| + 1) * (‖fderiv ℝ (A c) z‖ + 1)) := by
          rw [abs_mul]
          refine mul_le_mul (hF1 c d) ?_ (by positivity) (by positivity)
          calc |(A c y) * ((fderiv ℝ (B d) y) (Pi.single r (1 : ℝ)))
                + (B d y) * ((fderiv ℝ (A c) y) (Pi.single r (1 : ℝ)))|
              ≤ |(A c y) * ((fderiv ℝ (B d) y) (Pi.single r (1 : ℝ)))|
                + |(B d y) * ((fderiv ℝ (A c) y) (Pi.single r (1 : ℝ)))| := abs_add_le _ _
            _ = |A c y| * |(fderiv ℝ (B d) y) (Pi.single r (1 : ℝ))|
                + |B d y| * |(fderiv ℝ (A c) y) (Pi.single r (1 : ℝ))| := by rw [abs_mul, abs_mul]
            _ ≤ (|A c z| + 1) * (‖fderiv ℝ (B d) z‖ + 1)
                + (|B d z| + 1) * (‖fderiv ℝ (A c) z‖ + 1) :=
                add_le_add
                  (mul_le_mul (le_of_lt ((Set.mem_iInter.mp hy3) c)) (hL2 d) (abs_nonneg _) (by positivity))
                  (mul_le_mul (le_of_lt ((Set.mem_iInter.mp hy5) d)) (hL3 c) (abs_nonneg _) (by positivity))
        calc |(A c y * B d y) * ((fderiv ℝ (D.mat i h c d) (T y))
                ((fderiv ℝ T y) (Pi.single r (1 : ℝ))))
              + (D.mat i h c d (T y)) * ((A c y) * ((fderiv ℝ (B d) y) (Pi.single r (1 : ℝ)))
                + (B d y) * ((fderiv ℝ (A c) y) (Pi.single r (1 : ℝ))))|
            ≤ |(A c y * B d y) * ((fderiv ℝ (D.mat i h c d) (T y))
                ((fderiv ℝ T y) (Pi.single r (1 : ℝ))))|
              + |(D.mat i h c d (T y)) * ((A c y) * ((fderiv ℝ (B d) y) (Pi.single r (1 : ℝ)))
                + (B d y) * ((fderiv ℝ (A c) y) (Pi.single r (1 : ℝ))))| := abs_add_le _ _
          _ ≤ (|A c z| + 1) * (|B d z| + 1)
                * ((Module.finrank ℝ E : ℝ) * K * (‖fderiv ℝ T z‖ + 1))
              + 2 * K * ((|A c z| + 1) * (‖fderiv ℝ (B d) z‖ + 1)
                + (|B d z| + 1) * (‖fderiv ℝ (A c) z‖ + 1)) := add_le_add h1 h2
      rw [show (∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
            ((A c y * B d y) • ((fderiv ℝ (D.mat i h c d) (T y)).comp (fderiv ℝ T y))
              + (D.mat i h c d (T y)) •
                ((A c y) • fderiv ℝ (B d) y + (B d y) • fderiv ℝ (A c) y)))
          (Pi.single r (1 : ℝ))
          = ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
            ((A c y * B d y) • ((fderiv ℝ (D.mat i h c d) (T y)).comp (fderiv ℝ T y))
              + (D.mat i h c d (T y)) •
                ((A c y) • fderiv ℝ (B d) y + (B d y) • fderiv ℝ (A c) y))
              (Pi.single r (1 : ℝ)) from by simp only [sum_apply]]
      calc |∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              ((A c y * B d y) • ((fderiv ℝ (D.mat i h c d) (T y)).comp (fderiv ℝ T y))
                + (D.mat i h c d (T y)) •
                  ((A c y) • fderiv ℝ (B d) y + (B d y) • fderiv ℝ (A c) y))
                (Pi.single r (1 : ℝ))|
          ≤ ∑ c : Fin (Module.finrank ℝ E), |∑ d : Fin (Module.finrank ℝ E),
              ((A c y * B d y) • ((fderiv ℝ (D.mat i h c d) (T y)).comp (fderiv ℝ T y))
                + (D.mat i h c d (T y)) •
                  ((A c y) • fderiv ℝ (B d) y + (B d y) • fderiv ℝ (A c) y))
                (Pi.single r (1 : ℝ))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              |((A c y * B d y) • ((fderiv ℝ (D.mat i h c d) (T y)).comp (fderiv ℝ T y))
                + (D.mat i h c d (T y)) •
                  ((A c y) • fderiv ℝ (B d) y + (B d y) • fderiv ℝ (A c) y))
                (Pi.single r (1 : ℝ))| :=
            Finset.sum_le_sum fun c _ => Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
            ((|A c z| + 1) * (|B d z| + 1)
                * ((Module.finrank ℝ E : ℝ) * K * (‖fderiv ℝ T z‖ + 1))
              + 2 * K * ((|A c z| + 1) * (‖fderiv ℝ (B d) z‖ + 1)
                + (|B d z| + 1) * (‖fderiv ℝ (A c) z‖ + 1))) :=
            Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun d _ => htermbound c d
    exact hbnd

end Helpers

theorem mat_jet_bound_global
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (lam K : ℝ) (hlam : 0 < lam) :
    ∃ (δ C : ℝ), 0 < δ ∧ 0 ≤ C ∧
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
        (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
        (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
        (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
        (hjet : ∀ (i : ι₀) (c d r : Fin (Module.finrank ℝ E))
          (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ i →
          |Work.Diff.STE.pdR r (D.mat i h c d) z| ≤ K),
        ∀ (j : ι₀) (a b r : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
          ‖z‖ ≤ 2 * D.σ j + δ →
          |D.mat j h a b z| ≤ C ∧ |Work.Diff.STE.pdR r (D.mat j h a b) z| ≤ C := by
  classical
  by_cases hι : Nonempty ι₀
  · by_cases hfin : Module.finrank ℝ E = 0
    · refine ⟨1, 0, one_pos, le_refl 0, ?_⟩
      intro h hsym hsmooth hell hub hjet j a b r z hz
      exact absurd a.isLt (by omega)
    · -- the main case
      obtain ⟨i₀⟩ := hι
      haveI : Nonempty ι₀ := ⟨i₀⟩
      have hn : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero hfin
      obtain ⟨c₀⟩ : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, hn⟩⟩
      by_cases hex : ∃ h : Work.Diff.STE.Bil (I := I) (M := M), Pack D lam K h
      · obtain ⟨h₀, hsym₀, hchart₀, hell₀, hub₀, hjet₀⟩ := hex
        -- `K` is nonnegative as soon as the class is nonempty
        have hK : 0 ≤ K := by
          have h0 := hjet₀ i₀ c₀ c₀ c₀ 0 (by simp only [norm_zero]; have := D.hσ i₀; linarith)
          exact le_trans (abs_nonneg _) h0
        obtain ⟨δ, B, hδpos, hBnn, hδtarget, hδframe⟩ :=
          delta_target_frame_priv (I := I) (M := M) D
        -- the uniform bound on the first flat derivative
        have hder : ∀ j : ι₀, ∃ C : ℝ, 0 ≤ C ∧
            ∀ (q : {h : Work.Diff.STE.Bil (I := I) (M := M) // Pack D lam K h})
              (a b r : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
              ‖z‖ ≤ 2 * D.σ j + δ → |Work.Diff.STE.pdR r (D.mat j q.1 a b) z| ≤ C := by
          intro j
          have hcomp : IsCompact {z : Fin (Module.finrank ℝ E) → ℝ | ‖z‖ ≤ 2 * D.σ j + δ} := by
            rw [show {z : Fin (Module.finrank ℝ E) → ℝ | ‖z‖ ≤ 2 * D.σ j + δ}
                = Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ) from by
              ext z; simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_eq_norm, sub_zero]]
            exact isCompact_closedBall _ _
          haveI : Nonempty (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
              × Fin (Module.finrank ℝ E)) := ⟨(c₀, c₀, c₀)⟩
          have htriple : ∀ t : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
              × Fin (Module.finrank ℝ E),
              ∃ C : ℝ, 0 ≤ C ∧
                ∀ (q : {h : Work.Diff.STE.Bil (I := I) (M := M) // Pack D lam K h})
                  (z : Fin (Module.finrank ℝ E) → ℝ),
                  ‖z‖ ≤ 2 * D.σ j + δ →
                    |Work.Diff.STE.pdR t.2.2 (D.mat j q.1 t.1 t.2.1) z| ≤ C := by
            intro t
            refine MatGlob.isCompact_uniform_bound
              (X := Fin (Module.finrank ℝ E) → ℝ)
              (ι := {h : Work.Diff.STE.Bil (I := I) (M := M) // Pack D lam K h})
              (Kc := {z : Fin (Module.finrank ℝ E) → ℝ | ‖z‖ ≤ 2 * D.σ j + δ})
              (f := fun q z => Work.Diff.STE.pdR t.2.2 (D.mat j q.1 t.1 t.2.1) z)
              hcomp ?_
            intro z hz
            obtain ⟨C, hCnn, u, hu, hb⟩ := local_bound_triple (I := I) (M := M) D lam K hlam.le
              hK δ hδtarget j t.1 t.2.1 t.2.2 z (by simpa only [Set.mem_setOf_eq] using hz)
            exact ⟨C, u, hu, fun y hy q => hb y hy q⟩
          choose Ct hCt using htriple
          refine ⟨Finset.univ.sup' Finset.univ_nonempty Ct, ?_, ?_⟩
          · exact le_trans (hCt (c₀, c₀, c₀)).1 (Finset.le_sup' Ct (Finset.mem_univ _))
          · intro q a b r z hz
            have hzk := (hCt (a, b, r)).2 q z hz
            exact le_trans hzk (Finset.le_sup' Ct (Finset.mem_univ (a, b, r)))
        choose Cj hCj using hder
        refine ⟨δ, max (max (2 * K * B) 0) (Finset.univ.sup' Finset.univ_nonempty Cj), hδpos,
          ?_, ?_⟩
        · exact le_trans (le_max_right (2 * K * B) 0) (le_max_left _ _)
        · intro h hsym hsmooth hell hub hjet j a b r z hz
          constructor
          · -- the value bound
            have h1 := MatGlob.abs_bilin_le_of_sandwich (I := I) (M := M) (g₀ := g₀) (h := h)
              (lam := lam) (K := K) hlam.le hK hsym hell hub (D.pt j z)
              (D.e j a (D.pt j z)) (D.e j b (D.pt j z))
            have h2 := hδframe j a z hz
            have h3 := hδframe j b z hz
            rw [show D.mat j h a b z
              = h (D.pt j z) (D.e j a (D.pt j z)) (D.e j b (D.pt j z)) from rfl]
            calc |h (D.pt j z) (D.e j a (D.pt j z)) (D.e j b (D.pt j z))|
                ≤ K * (g₀.inner (D.pt j z) (D.e j a (D.pt j z)) (D.e j a (D.pt j z))
                  + g₀.inner (D.pt j z) (D.e j b (D.pt j z)) (D.e j b (D.pt j z))) := h1
              _ ≤ K * (B + B) := by gcongr
              _ = 2 * K * B := by ring
              _ ≤ max (2 * K * B) 0 := le_max_left _ _
              _ ≤ max (max (2 * K * B) 0) (Finset.univ.sup' Finset.univ_nonempty Cj) :=
                  le_max_left _ _
          · -- the derivative bound
            have hderj := (hCj j).2 ⟨h, hsym, hsmooth, hell, hub, hjet⟩ a b r z hz
            exact le_trans hderj
              (le_trans (Finset.le_sup' Cj (Finset.mem_univ j)) (le_max_right _ _))
      · -- the class is empty: the statement is vacuous
        refine ⟨1, 0, one_pos, le_refl 0, ?_⟩
        intro h hsym hsmooth hell hub hjet j a b r z hz
        exact (hex ⟨h, hsym, hsmooth, hell, hub, hjet⟩).elim
  · refine ⟨1, 0, one_pos, le_refl 0, ?_⟩
    intro h hsym hsmooth hell hub hjet j a b r z hz
    exact (hι ⟨j⟩).elim

end Work.Diff.STE.B3
