import Mathlib
import Submission.Work.Diff.STE.Lead.contDiffOn_of_solves_jet
import Submission.Work.Diff.STE.Lead.jetTower_jointContinuous
import Submission.Work.Diff.STE.Lead.JointSmoothKit
import Submission.Work.Diff.STE.Man.chartNonlin_eq_pPhiJet
import Submission.Work.Diff.STE.B3.transport_Rres_contDiffOn
import Submission.Work.Diff.STE.C2.formFamJoint_pullMetBilin
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.Lead.Gf_tower_jointContinuous
import Submission.Work.Diff.STE.Lead.chartMat_solves_chartNonlin_gen
import Submission.Work.Diff.STE.Lead.exists_smooth_surrogate_chartNonlin
import Submission.Work.Diff.STE.Lead.section_contMDiffWithinAt_of_frameMat_at
import Submission.Work.Diff.STE.Lead.frameMatWithinAt_of_matrixWithinAt
import Submission.Work.Diff.STE.Lead.exists_localised_chartDatum
import Submission.Work.Diff.EXT.FrameKit.formInFrame_frameMat

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set Filter

namespace Work.Diff.STE.Lead

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]

/-! ## Elementary chart-coordinate algebra -/

/-- The **flat coordinate map** of the chart at `x₀`: the `finBasis`-coordinates of `y`, translated
so that the chart centre has coordinate `0`.  It is the inverse of `Work.Diff.STE.flatToE`. -/
noncomputable def flatCoordMap (x₀ : M) : E → (Fin (Module.finrank ℝ E) → ℝ) :=
  fun y => (Module.finBasis ℝ E).equivFun (y - (extChartAt I x₀) x₀)

/-- Unfolding lemma for `flatCoordMap`. -/
lemma flatCoordMap_def (x₀ : M) :
    flatCoordMap (I := I) x₀
      = fun y : E => (Module.finBasis ℝ E).equivFun (y - (extChartAt I x₀) x₀) := rfl

/-- Unfolding lemma for `Work.Diff.STE.flatToE`. -/
lemma flatToE_def (x₀ : M) :
    Work.Diff.STE.flatToE (I := I) x₀
      = fun z : Fin (Module.finrank ℝ E) → ℝ => (Module.finBasis ℝ E).equivFun.symm
          ((Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀) + z) := rfl

/-- **The chart coordinate is inverted by `flatToE`.**  (Private: `Work.Diff.STE.Lead.coordBound`
declares a public lemma of the same name with a `B3Data`-flavoured signature.) -/
private lemma flatToE_coord {x₀ p : M} (hp : p ∈ (extChartAt I x₀).source) :
    Work.Diff.STE.flatToE (I := I) x₀ (Work.Diff.STE.coord (I := I) x₀ p)
      = (extChartAt I x₀) p := by
  show (Module.finBasis ℝ E).equivFun.symm
      ((Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀)
        + Work.Diff.STE.coord (I := I) x₀ p) = (extChartAt I x₀) p
  have h : (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀)
      + Work.Diff.STE.coord (I := I) x₀ p
      = (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) p) := by
    rw [Work.Diff.STE.coord_apply]; abel
  rw [h, LinearEquiv.symm_apply_apply]

/-- **The flat coordinate map inverts `flatToE`.** -/
lemma flatToE_flatCoordMap (x₀ : M) (y : E) :
    Work.Diff.STE.flatToE (I := I) x₀ (flatCoordMap (I := I) x₀ y) = y := by
  show (Module.finBasis ℝ E).equivFun.symm
      ((Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀)
        + (Module.finBasis ℝ E).equivFun (y - (extChartAt I x₀) x₀)) = y
  have h : (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀)
      + (Module.finBasis ℝ E).equivFun (y - (extChartAt I x₀) x₀)
      = (Module.finBasis ℝ E).equivFun y := by
    rw [map_sub]; abel
  rw [h, LinearEquiv.symm_apply_apply]

/-- **The flat coordinate map inverts `flatToE`** (unfolded form). -/
lemma flatToE_flatOf (x₀ : M) (y : E) :
    Work.Diff.STE.flatToE (I := I) x₀
      ((Module.finBasis ℝ E).equivFun (y - (extChartAt I x₀) x₀)) = y := by
  show (Module.finBasis ℝ E).equivFun.symm
      ((Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀)
        + (Module.finBasis ℝ E).equivFun (y - (extChartAt I x₀) x₀)) = y
  have h : (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀)
      + (Module.finBasis ℝ E).equivFun (y - (extChartAt I x₀) x₀)
      = (Module.finBasis ℝ E).equivFun y := by
    rw [map_sub]; abel
  rw [h, LinearEquiv.symm_apply_apply]

/-- **`flatToE` inverts the flat coordinate map.** -/
lemma flatCoordMap_flatToE (x₀ : M) (z : Fin (Module.finrank ℝ E) → ℝ) :
    flatCoordMap (I := I) x₀ (Work.Diff.STE.flatToE (I := I) x₀ z) = z := by
  show (Module.finBasis ℝ E).equivFun
      ((Module.finBasis ℝ E).equivFun.symm
        ((Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀) + z)
        - (extChartAt I x₀) x₀) = z
  rw [map_sub, LinearEquiv.apply_symm_apply, add_sub_cancel_left]

/-- The map `flatToE x₀` is smooth. -/
lemma contDiff_flatToE (x₀ : M) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.flatToE (I := I) x₀) := by
  rw [flatToE_def]
  exact (LinearMap.toContinuousLinearMap
    ((Module.finBasis ℝ E).equivFun.symm
      : (Fin (Module.finrank ℝ E) → ℝ) →ₗ[ℝ] E)).contDiff.comp
    (contDiff_const.add contDiff_id)

/-- The flat coordinate map is smooth. -/
lemma contDiff_flatCoordMap (x₀ : M) : ContDiff ℝ (⊤ : ℕ∞) (flatCoordMap (I := I) x₀) := by
  rw [flatCoordMap_def]
  exact (LinearMap.toContinuousLinearMap
    ((Module.finBasis ℝ E).equivFun
      : E →ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ))).contDiff.comp
    (contDiff_id.sub contDiff_const)

/-- The flat coordinate map is continuous. -/
lemma continuous_flatCoordMap (x₀ : M) : Continuous (flatCoordMap (I := I) x₀) :=
  (contDiff_flatCoordMap (I := I) x₀).continuous

/-- Complexification of matrices is smooth. -/
lemma contDiff_ofRealMat_aux :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.Man.ofRealMat (E := E)) := by
  rw [contDiff_pi]
  intro i
  rw [contDiff_pi]
  intro j
  exact Complex.ofRealCLM.contDiff.comp (by fun_prop)

/-! ## Two reconstruction lemmas -/

/-- **The chart matrix at the chart coordinate of a point reconstructs the section's form.** -/
lemma formInFrame_chartMatOf (h : Work.Diff.STE.Bil (I := I) (M := M)) {x₀ x : M}
    (hx : x ∈ (chartAt H x₀).source) :
    Work.Diff.EXT.formInFrame (I := I) x₀ x
      (fun i j => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀ ((extChartAt I x₀) x) i j)
      = h x := by
  have hx' : x ∈ (extChartAt I x₀).source := by rwa [extChartAt_source]
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hx
  rw [← Work.Diff.EXT.FrameKit.formInFrame_frameMat (I := I) hbase (h x)]
  congr 1
  funext i j
  simp only [Work.Diff.EXT.frameMat, Work.Diff.STE.D.chartMatOf_apply]
  rw [(extChartAt I x₀).left_inv hx']

/-- **The chart matrix in the chart coordinates is smooth when the flat chart matrix is.** -/
lemma chartMatOf_contMDiffWithinAt_of_flat {ι₀ : Type*} [Fintype ι₀]
    {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (U : ℝ → Work.Diff.STE.Bil (I := I) (M := M)) (i : ι₀)
    {b t₀ : ℝ} {c : Fin (Module.finrank ℝ E) → ℝ} {ρ : ℝ} {x₀ : M}
    (hc_def : c = Work.Diff.STE.coord (I := I) (D.x₀ i) x₀)
    (hx₀src : x₀ ∈ (extChartAt I (D.x₀ i)).source)
    (ht₀ : t₀ ∈ Set.Ico (0 : ℝ) b) (hρpos : 0 < ρ)
    (hflat : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin (Module.finrank ℝ E) → ℝ) =>
        chartMatC (I := I) (M := M) D (U p.1) i p.2)
      (Set.Ico (0 : ℝ) b ×ˢ Metric.ball c ρ)) :
    ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ E))
      (modelWithCornersSelf ℝ (Work.Diff.EXT.MatE (E := E))) (⊤ : ℕ∞)
      (fun p : ℝ × E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) (U p.1) (D.x₀ i) p.2)
      (Set.Ico (0 : ℝ) b ×ˢ (Work.Diff.STE.flatToE (I := I) (D.x₀ i) '' Metric.ball c ρ))
      (t₀, (extChartAt I (D.x₀ i)) x₀) := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin (Module.finrank ℝ E) → ℝ) =>
        Work.Diff.STE.Man.reMatE (E := E)
          (chartMatC (I := I) (M := M) D (U p.1) i p.2))
      (Set.Ico (0 : ℝ) b ×ˢ Metric.ball c ρ) :=
    (Work.Diff.STE.Man.reMatECLM (E := E)).contDiff.comp_contDiffOn hflat
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin (Module.finrank ℝ E) → ℝ) =>
        Work.Diff.STE.D.chartMatOf (I := I) (M := M) (U p.1) (D.x₀ i)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ i) p.2))
      (Set.Ico (0 : ℝ) b ×ˢ Metric.ball c ρ) := by
    refine h1.congr fun p hp => ?_
    funext a bb
    simp only [Work.Diff.STE.Man.reMatE, Work.Diff.STE.Man.ofRealMat, chartMatC,
      Work.Diff.STE.B3.Gf, Work.Diff.STE.B3.yf]
    rfl
  have hmap : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × E => (p.1, flatCoordMap (I := I) (D.x₀ i) p.2))
      (Set.Ico (0 : ℝ) b ×ˢ
        (Work.Diff.STE.flatToE (I := I) (D.x₀ i) '' Metric.ball c ρ)) :=
    contDiffOn_fst.prodMk
      ((contDiff_flatCoordMap (I := I) (D.x₀ i)).comp_contDiffOn contDiffOn_snd)
  have hmaps : Set.MapsTo (fun p : ℝ × E => (p.1, flatCoordMap (I := I) (D.x₀ i) p.2))
      (Set.Ico (0 : ℝ) b ×ˢ (Work.Diff.STE.flatToE (I := I) (D.x₀ i) '' Metric.ball c ρ))
      (Set.Ico (0 : ℝ) b ×ˢ Metric.ball c ρ) := by
    rintro ⟨t, y⟩ ⟨ht, z, hz, rfl⟩
    refine ⟨ht, ?_⟩
    show flatCoordMap (I := I) (D.x₀ i)
      (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) ∈ Metric.ball c ρ
    rw [flatCoordMap_flatToE]
    exact hz
  have h4 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) (U p.1) (D.x₀ i) p.2)
      (Set.Ico (0 : ℝ) b ×ˢ
        (Work.Diff.STE.flatToE (I := I) (D.x₀ i) '' Metric.ball c ρ)) := by
    refine (ContDiffOn.comp
      (s := Set.Ico (0 : ℝ) b ×ˢ
        (Work.Diff.STE.flatToE (I := I) (D.x₀ i) '' Metric.ball c ρ))
      (t := Set.Ico (0 : ℝ) b ×ˢ Metric.ball c ρ)
      (g := fun p : ℝ × (Fin (Module.finrank ℝ E) → ℝ) =>
        Work.Diff.STE.D.chartMatOf (I := I) (M := M) (U p.1) (D.x₀ i)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ i) p.2))
      (f := fun p : ℝ × E => (p.1, flatCoordMap (I := I) (D.x₀ i) p.2)) h2 hmap hmaps).congr ?_
    rintro ⟨t, y⟩ hp
    simp only [Function.comp_apply]
    show Work.Diff.STE.D.chartMatOf (I := I) (M := M) (U t) (D.x₀ i) y
      = Work.Diff.STE.D.chartMatOf (I := I) (M := M) (U t) (D.x₀ i)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ i) (flatCoordMap (I := I) (D.x₀ i) y))
    rw [flatToE_flatCoordMap]
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  refine ContDiffWithinAt.contMDiffWithinAt (h4.contDiffWithinAt ?_)
  refine ⟨ht₀, c, Metric.mem_ball_self hρpos, ?_⟩
  rw [hc_def]
  exact flatToE_coord (I := I) (x₀ := D.x₀ i) hx₀src

/-! ## The pointwise joint smoothness -/

/-- **Pointwise joint smoothness of the metric family.** -/
private theorem jointSmoothWithinAt
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M)
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (τ₀ : ℝ) (hτ₀ : 0 < τ₀) (U : ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (B : ℕ → ℝ) (hB : ∀ k : ℕ, 0 ≤ B k)
    (hsym : ∀ (t : ℝ) (x : M) (u v : TangentSpace I x), (U t) x u v = (U t) x v u)
    (hpos : ∀ (t : ℝ) (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < (U t) x v v)
    (hsm : ∀ t : ℝ, Work.Diff.STE.D.ChartData (I := I) (M := M) (U t))
    (hUB : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ k : ℕ, D.BNorm k (U t) ≤ B k)
    (hcont : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ k : ℕ,
      Filter.Tendsto (fun σ : ℝ => D.BNorm k (U σ - U t))
        (nhdsWithin t (Set.Ico (0 : ℝ) τ₀)) (nhds 0))
    (heq : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ (x : M) (u v : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => (U s) x u v)
        ((Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (U t) (hsym t) (hpos t) (hsm t)) x u v)
        (Set.Ico (0 : ℝ) τ₀) t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ico (0 : ℝ) τ₀) (x₀ : M) :
    ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod I)
      (I.prod (modelWithCornersSelf ℝ (E →L[ℝ] E →L[ℝ] ℝ))) (⊤ : ℕ∞)
      (fun p : ℝ × M => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2 ((U p.1) p.2))
      (Set.Ico (0 : ℝ) τ₀ ×ˢ Set.univ) (t₀, x₀) := by
  classical
  -- ## Step 1: the chart, the flat point and the radii
  obtain ⟨i, hsrc, hcoord⟩ := D.hcover x₀
  have hxsrc : x₀ ∈ (chartAt H (D.x₀ i)).source := by rwa [extChartAt_source] at hsrc
  set c : Fin (Module.finrank ℝ E) → ℝ := Work.Diff.STE.coord (I := I) (D.x₀ i) x₀ with hcdef
  have hcle : ‖c‖ ≤ D.σ i := hcoord
  have hσpos : 0 < D.σ i := D.hσ i
  set ρ' : ℝ := (2 * D.σ i - ‖c‖) / 2 with hρ'eq
  have hρ'pos : 0 < ρ' := by rw [hρ'eq]; linarith
  have hρ'ball : ‖c‖ + ρ' < 2 * D.σ i := by rw [hρ'eq]; linarith
  set ρ : ℝ := ρ' / 2 with hρeq
  have hρpos : 0 < ρ := by rw [hρeq]; linarith
  have hρlt : ρ < ρ' := by rw [hρeq]; linarith
  set b : ℝ := (t₀ + τ₀) / 2 with hbeq
  have ht₀τ : t₀ < τ₀ := ht₀.2
  have ht₀ge : (0 : ℝ) ≤ t₀ := ht₀.1
  have ht₀b : t₀ < b := by rw [hbeq]; linarith
  have hbτ₀ : b ≤ τ₀ := by rw [hbeq]; linarith
  have hbτ₀lt : b < τ₀ := by rw [hbeq]; linarith
  have hbpos : 0 < b := by rw [hbeq]; linarith [ht₀ge]
  have htarget_ball : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z - c‖ < ρ' →
      Work.Diff.STE.flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target := by
    intro z hz
    refine D.htarget i z (le_of_lt ?_)
    have h1 : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by
      simpa only [sub_add_cancel] using norm_add_le (z - c) c
    linarith
  -- ## Step 2: the localised background datum and the surrogate nonlinearity
  obtain ⟨bg, hbg_sm, hbg_agr, hbg_det, hbg_nl⟩ :=
    exists_localised_chartDatum (I := I) (M := M) D hg i c ρ ρ' hρpos hρlt hρ'ball
  have hK : IsCompact (Set.Icc (0 : ℝ) b ×ˢ Metric.closedBall c ρ) :=
    isCompact_Icc.prod (isCompact_closedBall c ρ)
  have hfcont : ContinuousOn (fun p : ℝ × (Fin (Module.finrank ℝ E) → ℝ) =>
      Work.Diff.STE.B3.Gf (I := I) (M := M) D (U p.1) i p.2)
      (Set.Icc (0 : ℝ) b ×ˢ Metric.closedBall c ρ) := by
    refine continuousOn_pi.mpr fun a => continuousOn_pi.mpr fun bb => ?_
    have h1 := Gf_tower_jointContinuous (I := I) (M := M) D τ₀ hτ₀ U hsm B hB hUB hcont
      i c ρ' hρ'pos hρ'ball 0 (fun j : Fin 0 => j.elim0) a bb
    have h1' : ContinuousOn (fun p : ℝ × (Fin (Module.finrank ℝ E) → ℝ) =>
        ((Work.Diff.STE.pdVec 0 (fun j : Fin 0 => j.elim0)
          (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((Work.Diff.STE.B3.Gf (I := I) (M := M) D (U p.1) i y a bb : ℝ) : ℂ)) p.2)).re)
        (Set.Icc (0 : ℝ) b ×ˢ Metric.closedBall c ρ) :=
      Complex.continuous_re.comp_continuousOn
        (h1.mono (fun p hp => ⟨⟨hp.1.1, lt_of_le_of_lt hp.1.2 hbτ₀lt⟩,
          Metric.closedBall_subset_ball hρlt hp.2⟩))
    exact h1'.congr (fun p hp => rfl)
  have hfdet : ∀ p ∈ Set.Icc (0 : ℝ) b ×ˢ Metric.closedBall c ρ,
      (Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D (U p.1) i p.2)).det ≠ 0 := by
    intro p hp
    refine det_Gf_ne_zero (I := I) (M := M) D (U p.1) (hsym p.1) (hpos p.1) i ?_
    have h1 : ‖p.2‖ ≤ ‖p.2 - c‖ + ‖c‖ := by
      simpa only [sub_add_cancel] using norm_add_le (p.2 - c) c
    have h2 : ‖p.2 - c‖ ≤ ρ := by
      have h3 := Metric.mem_closedBall.mp hp.2
      rwa [dist_eq_norm] at h3
    linarith
  obtain ⟨Φ, hΦsm, hΦeq⟩ := exists_smooth_surrogate_chartNonlin (E := E) bg hbg_nl
    (fun p : ℝ × (Fin (Module.finrank ℝ E) → ℝ) =>
      Work.Diff.STE.B3.Gf (I := I) (M := M) D (U p.1) i p.2)
    (Set.Icc (0 : ℝ) b ×ˢ Metric.closedBall c ρ) hK hfcont hfdet
  -- ## Step 3: the flat chart matrices satisfy the chart equation with the datum `bg`
  have hode : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z - c‖ < ρ →
      HasDerivWithinAt (fun s : ℝ => chartMatC (I := I) (M := M) D (U s) i z)
        (Work.Diff.STE.Man.chartNonlin (E := E) bg
          (z, Work.Diff.STE.Flat.jetM (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            chartMatC (I := I) (M := M) D (U t) i y) z)) (Set.Ico (0 : ℝ) τ₀) t := by
    intro t ht z hz
    exact chartMat_solves_chartNonlin_gen (I := I) (M := M) D hLC hg τ₀ hτ₀ U hsym hpos
      hsm heq i c ρ ρ' hρpos hρlt hρ'ball bg hbg_sm hbg_agr t ht z hz
  -- ## Step 4: the jet tower is jointly continuous on the slab
  have hjet : ∀ (l : List (Fin (Module.finrank ℝ E))) (a bb : Fin (Module.finrank ℝ E)),
      ContinuousOn (fun p : ℝ × (Fin (Module.finrank ℝ E) → ℝ) =>
        Work.Diff.STE.pdList l (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          chartMatC (I := I) (M := M) D (U p.1) i y a bb) p.2)
        (Set.Ico (0 : ℝ) b ×ˢ Metric.ball c ρ) := by
    intro l a bb
    have h1 := Gf_tower_jointContinuous (I := I) (M := M) D τ₀ hτ₀ U hsm B hB hUB hcont
      i c ρ' hρ'pos hρ'ball l.length (fun j => l.get j) a bb
    have h2 : (fun p : ℝ × (Fin (Module.finrank ℝ E) → ℝ) =>
        Work.Diff.STE.pdList l (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          chartMatC (I := I) (M := M) D (U p.1) i y a bb) p.2)
        = fun p : ℝ × (Fin (Module.finrank ℝ E) → ℝ) =>
          Work.Diff.STE.pdVec l.length (fun j => l.get j)
            (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              ((Work.Diff.STE.B3.Gf (I := I) (M := M) D (U p.1) i y a bb : ℝ) : ℂ)) p.2 := by
      funext p
      simp only [Work.Diff.STE.Lead.pdList_eq_pdVec_get, chartMatC_apply]
    rw [h2]
    refine h1.mono ?_
    intro p hp
    exact ⟨⟨hp.1.1, lt_of_lt_of_le hp.1.2 hbτ₀⟩,
      Metric.ball_subset_ball (le_of_lt hρlt) hp.2⟩
  -- ## Step 5: the slices are smooth
  have hslice : ∀ t ∈ Set.Ico (0 : ℝ) b, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : Fin (Module.finrank ℝ E) → ℝ => chartMatC (I := I) (M := M) D (U t) i z)
      (Metric.ball c ρ) := by
    intro t ht
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) (U t) (D.x₀ i) y)
        (extChartAt I (D.x₀ i)).target := hsm t (D.x₀ i)
    have h2 : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : Fin (Module.finrank ℝ E) → ℝ =>
          Work.Diff.STE.D.chartMatOf (I := I) (M := M) (U t) (D.x₀ i)
            (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z)) (Metric.ball c ρ) :=
      h1.comp ((contDiff_flatToE (I := I) (D.x₀ i)).contDiffOn)
        (fun z hz => htarget_ball z (lt_of_lt_of_le hz (le_of_lt hρlt)))
    have h3 : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : Fin (Module.finrank ℝ E) → ℝ =>
          Work.Diff.STE.Man.ofRealMat (E := E)
            (Work.Diff.STE.D.chartMatOf (I := I) (M := M) (U t) (D.x₀ i)
              (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))) (Metric.ball c ρ) :=
      (contDiff_ofRealMat_aux (E := E)).comp_contDiffOn h2
    refine h3.congr fun z hz => ?_
    simp only [chartMatC, Work.Diff.STE.B3.Gf, Work.Diff.STE.B3.yf]
  -- ## Step 6: the bootstrap
  have hflat : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin (Module.finrank ℝ E) → ℝ) =>
        chartMatC (I := I) (M := M) D (U p.1) i p.2)
      (Set.Ico (0 : ℝ) b ×ˢ Metric.ball c ρ) := by
    refine contDiffOn_of_solves_jet (Φ := Φ) (hΦ := hΦsm) (hΩ := Metric.isOpen_ball)
      (hτ := hbpos) (V := fun t z => chartMatC (I := I) (M := M) D (U t) i z)
      (hslice := hslice) (hjet := hjet) (heq := ?_)
    intro t ht y hy
    have hmem : (t, y) ∈ Set.Icc (0 : ℝ) b ×ˢ Metric.closedBall c ρ :=
      ⟨⟨ht.1, le_of_lt ht.2⟩, Metric.ball_subset_closedBall hy⟩
    have hkey := hΦeq (t, y) hmem
    have hVeq : (fun y' : Fin (Module.finrank ℝ E) → ℝ =>
        Work.Diff.STE.Man.ofRealMat (E := E)
          (Work.Diff.STE.B3.Gf (I := I) (M := M) D (U t) i y'))
        = fun y' : Fin (Module.finrank ℝ E) → ℝ => chartMatC (I := I) (M := M) D (U t) i y' := by
      funext y'
      rfl
    rw [hVeq] at hkey
    rw [hkey]
    exact (hode t ⟨ht.1, lt_of_lt_of_le ht.2 hbτ₀⟩ y hy).mono
      (fun s hs => ⟨hs.1, lt_of_lt_of_le hs.2 hbτ₀⟩)
  -- ## Step 7: from the flat chart matrix to the section
  set Ω : Set E := Work.Diff.STE.flatToE (I := I) (D.x₀ i) '' Metric.ball c ρ with hΩeq
  have hΩtgt : Ω ⊆ (extChartAt I (D.x₀ i)).target := by
    rintro y ⟨z, hz, rfl⟩
    exact htarget_ball z (lt_of_lt_of_le hz (le_of_lt hρlt))
  have hxΩ : (extChartAt I (D.x₀ i)) x₀ ∈ Ω :=
    ⟨c, Metric.mem_ball_self hρpos,
      by rw [hcdef]; exact flatToE_coord (I := I) (x₀ := D.x₀ i) hsrc⟩
  have hW := chartMatOf_contMDiffWithinAt_of_flat (I := I) (M := M) D U i
    (hc_def := hcdef) hsrc ⟨ht₀.1, ht₀b⟩ hρpos hflat
  have hframe0 := frameMatWithinAt_of_matrixWithinAt (I := I) (x₀ := D.x₀ i) (x := x₀)
    (A := fun t (y : E) => Work.Diff.STE.D.chartMatOf (I := I) (M := M) (U t) (D.x₀ i) y)
    (J := Set.Ico (0 : ℝ) b) (Ω := Ω) (τ := t₀) hxsrc hxΩ hΩtgt hW
  have hsub : (Set.Ico (0 : ℝ) b ×ˢ (((extChartAt I (D.x₀ i)) ⁻¹' Ω) ∩
        ((chartAt H x₀).source ∩ (chartAt H (D.x₀ i)).source)))
      ⊆ (Set.Ico (0 : ℝ) b ×ˢ (((extChartAt I (D.x₀ i)) ⁻¹' Ω) ∩
        (chartAt H x₀).source)) := by
    rintro ⟨t, x⟩ ⟨ht, hxA, hx₁, hx₂⟩
    exact ⟨ht, hxA, hx₁⟩
  have hframe : ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ (Work.Diff.EXT.MatE (E := E))) (⊤ : ℕ∞)
      (fun p : ℝ × M => Work.Diff.EXT.frameMat (I := I) x₀ p.2 ((U p.1) p.2))
      (Set.Ico (0 : ℝ) b ×ˢ (((extChartAt I (D.x₀ i)) ⁻¹' Ω) ∩
        ((chartAt H x₀).source ∩ (chartAt H (D.x₀ i)).source)))
      (t₀, x₀) := by
    refine (hframe0.mono hsub).congr ?_ ?_
    · rintro ⟨t, x⟩ ⟨-, hxA, hx₁, hx₂⟩
      show Work.Diff.EXT.frameMat (I := I) x₀ x ((U t) x)
        = Work.Diff.EXT.frameMat (I := I) x₀ x
            (Work.Diff.EXT.formInFrame (I := I) (D.x₀ i) x
              (fun a b => Work.Diff.STE.D.chartMatOf (I := I) (M := M) (U t) (D.x₀ i)
                ((extChartAt I (D.x₀ i)) x) a b))
      rw [formInFrame_chartMatOf (I := I) (M := M) (h := U t) (x₀ := D.x₀ i) (x := x) hx₂]
    · show Work.Diff.EXT.frameMat (I := I) x₀ x₀ ((U t₀) x₀)
        = Work.Diff.EXT.frameMat (I := I) x₀ x₀
            (Work.Diff.EXT.formInFrame (I := I) (D.x₀ i) x₀
              (fun a b => Work.Diff.STE.D.chartMatOf (I := I) (M := M) (U t₀) (D.x₀ i)
                ((extChartAt I (D.x₀ i)) x₀) a b))
      rw [formInFrame_chartMatOf (I := I) (M := M) (h := U t₀) (x₀ := D.x₀ i) (x := x₀) hxsrc]
  have hpt : (t₀, x₀) ∈ Set.Ico (0 : ℝ) b ×ˢ
      (((extChartAt I (D.x₀ i)) ⁻¹' Ω) ∩
        ((chartAt H x₀).source ∩ (chartAt H (D.x₀ i)).source)) :=
    ⟨⟨ht₀.1, ht₀b⟩, hxΩ, mem_chart_source H x₀, hxsrc⟩
  have hsec := section_contMDiffWithinAt_of_frameMat_at (I := I)
    (γ := fun t x => (U t) x) (y := x₀) hpt (mem_chart_source H x₀) hframe
  -- ## Step 8: enlarge the set
  have hΩmem : Ω ∈ 𝓝 ((extChartAt I (D.x₀ i)) x₀) := by
    have hΨy : flatCoordMap (I := I) (D.x₀ i) ((extChartAt I (D.x₀ i)) x₀) = c := by
      show (Module.finBasis ℝ E).equivFun
          ((extChartAt I (D.x₀ i)) x₀ - (extChartAt I (D.x₀ i)) (D.x₀ i)) = c
      rw [hcdef, Work.Diff.STE.coord_apply, map_sub]
    have hpre : flatCoordMap (I := I) (D.x₀ i) ⁻¹' Metric.ball c ρ
        ∈ 𝓝 ((extChartAt I (D.x₀ i)) x₀) := by
      refine (continuous_flatCoordMap (I := I) (D.x₀ i)).continuousAt.preimage_mem_nhds ?_
      rw [hΨy]
      exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρpos)
    refine Filter.mem_of_superset hpre ?_
    intro w hw
    exact ⟨flatCoordMap (I := I) (D.x₀ i) w, hw, flatToE_flatCoordMap (I := I) (D.x₀ i) w⟩
  have hA : (extChartAt I (D.x₀ i)) ⁻¹' Ω ∈ 𝓝 x₀ :=
    (continuousAt_extChartAt' (I := I) (x := D.x₀ i) (x' := x₀) hsrc).preimage_mem_nhds hΩmem
  have hB : (chartAt H x₀).source ∈ 𝓝 x₀ :=
    IsOpen.mem_nhds (chartAt H x₀).open_source (mem_chart_source H x₀)
  have hB2 : (chartAt H (D.x₀ i)).source ∈ 𝓝 x₀ :=
    IsOpen.mem_nhds (chartAt H (D.x₀ i)).open_source hxsrc
  have hM : (((extChartAt I (D.x₀ i)) ⁻¹' Ω) ∩
      ((chartAt H x₀).source ∩ (chartAt H (D.x₀ i)).source)) ∈ 𝓝 x₀ :=
    Filter.inter_mem hA (Filter.inter_mem hB hB2)
  have hcongr : (Set.Ico (0 : ℝ) b ×ˢ
        (((extChartAt I (D.x₀ i)) ⁻¹' Ω) ∩
          ((chartAt H x₀).source ∩ (chartAt H (D.x₀ i)).source)))
      =ᶠ[𝓝 (t₀, x₀)] (Set.Ico (0 : ℝ) τ₀ ×ˢ (Set.univ : Set M)) := by
    have hWn : Set.Iio b ×ˢ (((extChartAt I (D.x₀ i)) ⁻¹' Ω) ∩
        ((chartAt H x₀).source ∩ (chartAt H (D.x₀ i)).source))
        ∈ 𝓝 (t₀, x₀) := by
      rw [nhds_prod_eq]
      exact Filter.prod_mem_prod (Iio_mem_nhds ht₀b) hM
    refine Filter.mem_of_superset hWn ?_
    rintro ⟨a, y⟩ ⟨ha, hy⟩
    simp only [Set.mem_prod, Set.mem_Iio, Set.mem_Ico, Set.mem_univ] at ha ⊢
    refine propext ⟨fun h => ?_, fun h => ?_⟩
    · exact ⟨⟨h.1.1, lt_of_lt_of_le h.1.2 hbτ₀⟩, trivial⟩
    · exact ⟨⟨h.1.1, ha⟩, hy⟩
  exact (contMDiffWithinAt_congr_set hcongr).mp hsec

/-! ## The target -/

theorem jointSmooth_of_solves_deTurck
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless] [CompactSpace M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M)
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (τ₀ : ℝ) (hτ₀ : 0 < τ₀)
    (U : ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (B : ℕ → ℝ) (hB : ∀ k : ℕ, 0 ≤ B k)
    (hsym : ∀ (t : ℝ) (x : M) (u v : TangentSpace I x), (U t) x u v = (U t) x v u)
    (hpos : ∀ (t : ℝ) (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < (U t) x v v)
    (hsm : ∀ t : ℝ, Work.Diff.STE.D.ChartData (I := I) (M := M) (U t))
    (hUB : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ k : ℕ, D.BNorm k (U t) ≤ B k)
    (hcont : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ k : ℕ,
      Filter.Tendsto (fun σ : ℝ => D.BNorm k (U σ - U t))
        (nhdsWithin t (Set.Ico (0 : ℝ) τ₀)) (nhds 0))
    (heq : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ (x : M) (u v : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => (U s) x u v)
        ((Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (U t) (hsym t) (hpos t) (hsm t)) x u v)
        (Set.Ico (0 : ℝ) τ₀) t) :
    Submission.Diff.JointSmooth
      (fun t : ℝ => Work.Diff.STE.D.smetOf (I := I) (U t) (hsym t) (hpos t) (hsm t))
      (Set.Ico (0 : ℝ) τ₀) := by
  rw [Submission.Diff.JointSmooth]
  intro p hp
  exact jointSmoothWithinAt (I := I) (M := M) D hLC hg τ₀ hτ₀ U B hB hsym hpos hsm hUB hcont
    heq hp.1 p.2

end Work.Diff.STE.Lead
