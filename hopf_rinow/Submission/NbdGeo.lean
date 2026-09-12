import ChallengeDeps
import Submission.MChartGlobal
import Submission.MChartMetric2
import Submission.MChartSpeed
import Submission.MChartGeodesicUB
import Submission.ModelNormalBall
import Submission.ModelPkg
import Submission.ChartNormal
import Mathlib

/-! # Extended normal-coordinate package with geodesic curves (renamed copy of ChartNormal) -/

open scoped Manifold ENNReal ContDiff Topology
open Set Metric
open Bundle
open MeasureTheory

namespace Submission

open Filter

set_option linter.unusedSectionVars false

open ContinuousLinearMap

theorem chart_normal_geo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] (p : M) :
    ∃ ρ₀ > 0, ∃ ge : E → E →L[ℝ] E →L[ℝ] ℝ,
      ContDiff ℝ 3 ge ∧
      (∀ y u v : E, (ge y) u v = (ge y) v u) ∧
      (∀ y : E, ∀ v : E, v ≠ 0 → 0 < (ge y) v v) ∧
      (∀ y ∈ ball (extChartAt I p p) ρ₀, ∀ u v : E,
         (ge y) u v = (Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner
                       ((extChartAt I p).symm y)
                       ((mfderiv[range I] (extChartAt I p).symm y) u)
                       ((mfderiv[range I] (extChartAt I p).symm y) v)) ∧
      ∃ r > 0, ∃ ExpM : E → M, ∃ S : Set M, ∃ invM : M → E,
        ExpM 0 = p ∧ S ∈ 𝓝 p ∧
        (∀ v ∈ ball (0 : E) r, ExpM v ∈ S) ∧
        ContinuousOn ExpM (ball (0 : E) r) ∧
        Function.Injective (fun v : {v : E // v ∈ ball (0 : E) r} => ExpM v.1) ∧
        Set.SurjOn ExpM (ball (0 : E) r) S ∧
        (∀ y ∈ S, invM y ∈ ball (0 : E) r ∧ ExpM (invM y) = y) ∧
        (∀ v ∈ ball (0 : E) r, invM (ExpM v) = v) ∧
        (∀ v ∈ ball (0 : E) r,
           edist p (ExpM v) = ENNReal.ofReal (Real.sqrt ((ge (extChartAt I p p)) v v))) ∧
      ∃ ρe > 0, ∃ τe : ℝ, 0 < τe ∧ ρe ≤ r ∧ ρe ≤ τe / 4 ∧
        ∃ Φ : E × E → ℝ → E × E, ∃ exp : E → E,
        (∀ v ∈ ball (0 : E) ρe, ExpM v = (extChartAt I p).symm (exp v)) ∧
        exp 0 = extChartAt I p p ∧
        ContDiffOn ℝ 1 exp (ball (0 : E) ρe) ∧
        (∀ z ∈ closedBall (extChartAt I p p, 0) 2, Φ z 0 = z ∧
           ∀ t ∈ Ioo (-((3 / 2) * τe)) ((3 / 2) * τe),
             HasDerivAt (Φ z) (Submission.Model.odeField ge (Φ z t)) t) ∧
        (∀ v ∈ ball (0 : E) ρe,
           exp v = (Φ (extChartAt I p p, (1 / τe) • v) τe).1) ∧
        (∀ u : E, ‖u‖ ≤ 1 → Real.sqrt ((ge (extChartAt I p p)) u u) = 1 →
           ∀ t ∈ Ioo (-(τe / 4)) (τe / 4), exp (t • u) = (Φ (extChartAt I p p, u) t).1) ∧
        (∃ ρT > 0, ρT ≤ ρ₀ ∧
           ball (extChartAt I p p) ρT ⊆ (extChartAt I p).target ∧
           (∀ v ∈ ball (0 : E) ρe, ∃ cv velv : ℝ → E,
             cv 0 = extChartAt I p p ∧ cv 1 = exp v ∧
             (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt cv (velv t) t) ∧
             (∀ t ∈ Icc (0 : ℝ) 1,
                Real.sqrt ((ge (cv t)) (velv t) (velv t)) =
                  Real.sqrt ((ge (extChartAt I p p)) v v)) ∧
             (∀ t ∈ Icc (0 : ℝ) 1, cv t ∈ ball (extChartAt I p p) ρT) ∧
             (∀ t ∈ Icc (0 : ℝ) 1,
                cv t = (Φ (extChartAt I p p, (1 / τe) • v) (τe * t)).1) ∧
             (∃ O : Set ℝ, IsOpen O ∧ Icc (0 : ℝ) 1 ⊆ O ∧ ContDiffOn ℝ 1 cv O))) := by
  classical
  let x₀ : E := extChartAt I p p
  let φ := extChartAt I p
  rcases chart_speed (I := I) (M := M) p with
    ⟨ρs, hρs0, ge, hgeC, hgeSymm, hgePos, hgeAgree, hSpeedClause⟩
  let hinv : ∀ y : E, (ge y).IsInvertible := fun y => bilin_isInvertible_of_pos (ge y) (hgePos y)
  -- chart target contains a ball around x₀
  rcases Metric.nhds_basis_ball.mem_iff.mp ((isOpen_extChartAt_target (I := I) p).mem_nhds (mem_extChartAt_target p))
    with ⟨δT, hδT0, hδTsub⟩
  -- model data
  let δa : ℝ := min ρs δT / 2
  have hδa0 : 0 < δa := by dsimp [δa]; positivity
  rcases (Submission.Model.model_geodesic_pkg ge hgeC hinv hgeSymm hgePos x₀ δa hδa0) with
    ⟨ρm, hρm0, hrest1⟩
  rcases hrest1 with ⟨Φm, hrest2⟩
  rcases hrest2 with ⟨hΦm, hrest3⟩
  rcases hrest3 with ⟨τe, hrest4⟩
  rcases hrest4 with ⟨hτe0, hrest5⟩
  rcases hrest5 with ⟨hτele, hrest6⟩
  rcases hrest6 with ⟨expm, hrest7⟩
  rcases hrest7 with ⟨hExp0, hrest8⟩
  rcases hrest8 with ⟨hExpC1, hrest9⟩
  rcases hrest9 with ⟨hExpFd, hrest10⟩
  rcases hrest10 with ⟨hExpFlow, hrest11⟩
  -- hrest11 : the homeo block (∃ U ∈ 𝓝 0, ...) possibly followed by ∧ curves
  rcases hrest11 with ⟨hHomeoAndGeo, hGeoCurves, hODEbig, hRayProp⟩
  rcases hHomeoAndGeo with ⟨U, hUnhds, hHomeo1⟩
  rcases hHomeo1 with ⟨V, hVnhds, hHomeo2⟩
  rcases hHomeo2 with ⟨hUopen, hHomeo2b⟩
  rcases hHomeo2b with ⟨hVopen, hHomeo3⟩
  rcases hHomeo3 with ⟨hMapsTo, hHomeo4⟩
  rcases hHomeo4 with ⟨hInj, hHomeo5⟩
  rcases hHomeo5 with ⟨hSurj, hHomeo6⟩
  rcases hHomeo6 with ⟨hContU, hHomeo7⟩
  rcases hHomeo7 with ⟨modelInv, hHomeo8⟩
  rcases hHomeo8 with ⟨hInv1, hHomeo9⟩
  rcases hHomeo9 with ⟨hInv2, hHomeo10⟩
  rcases hHomeo10 with ⟨hContInv, hMin, hRad⟩
  -- hGeoCurves (top-level) is already available from hrest11
  rcases Metric.nhds_basis_ball.mem_iff.mp hUnhds with ⟨δU, hδU0, hδUsub⟩
  rcases Metric.nhds_basis_ball.mem_iff.mp hVnhds with ⟨δV, hδV0, hδVsub⟩
  -- exp continuous at 0; radius δε with exp(ball 0 δε) ⊆ ball x₀ δV
  have hExpContAt0 : ContinuousAt expm (0 : E) := by
    have h0mem : (0 : E) ∈ ball (0 : E) ρm := by simpa using hρm0
    exact (hExpC1.contDiffAt (isOpen_ball.mem_nhds h0mem)).continuousAt
  have hεV : ∃ εV > 0, expm '' ball (0 : E) εV ⊆ ball x₀ δV := by
    have hpre : expm ⁻¹' ball x₀ δV ∈ 𝓝 (0 : E) := by
      exact hExpContAt0.preimage_mem_nhds (by simpa [hExp0] using (ball_mem_nhds x₀ hδV0))
    rcases Metric.mem_nhds_iff.mp hpre with ⟨εV, hεV0, hεVball⟩
    refine ⟨εV, hεV0, ?_⟩
    intro y hy
    rcases hy with ⟨v, hv, rfl⟩
    exact hεVball (by simpa [mem_preimage, dist_eq_norm] using hv)
  rcases hεV with ⟨εV, hεV0, hεVsub⟩
  -- big normal radius rS (model radius for S_big := ExpM '' ball 0 rS)
  let rS : ℝ := min (min ρm δU) (min εV (min δV δT)) / 2
  have hrS0 : 0 < rS := by dsimp [rS]; positivity
  have hminx : 0 ≤ min (min ρm δU) (min εV (min δV δT)) := by positivity
  have hrSρm : rS ≤ ρm := by
    dsimp [rS]
    calc
      min (min ρm δU) (min εV (min δV δT)) / 2
          ≤ min (min ρm δU) (min εV (min δV δT)) := by linarith
      _ ≤ ρm := le_trans (min_le_left _ _) (min_le_left ρm δU)
  have hrSδU : rS ≤ δU := by
    dsimp [rS]
    calc
      min (min ρm δU) (min εV (min δV δT)) / 2
          ≤ min (min ρm δU) (min εV (min δV δT)) := by linarith
      _ ≤ δU := le_trans (min_le_left _ _) (min_le_right ρm δU)
  have hrSεV : rS ≤ εV := by
    dsimp [rS]
    calc
      min (min ρm δU) (min εV (min δV δT)) / 2
          ≤ min (min ρm δU) (min εV (min δV δT)) := by linarith
      _ ≤ εV := le_trans (min_le_right _ _) (min_le_left εV (min δV δT))
  have hrSδV : rS ≤ δV := by
    dsimp [rS]
    calc
      min (min ρm δU) (min εV (min δV δT)) / 2
          ≤ min (min ρm δU) (min εV (min δV δT)) := by linarith
      _ ≤ δV := le_trans (min_le_right _ _) (le_trans (min_le_right εV (min δV δT)) (min_le_left δV δT))
  have hrSδT : rS ≤ δT := by
    dsimp [rS]
    calc
      min (min ρm δU) (min εV (min δV δT)) / 2
          ≤ min (min ρm δU) (min εV (min δV δT)) := by linarith
      _ ≤ δT := le_trans (min_le_right _ _) (le_trans (min_le_right εV (min δV δT)) (min_le_right δV δT))
  let ExpM : E → M := fun v => φ.symm (expm v)
  -- expm maps the small ball into the agreement ball, V and the chart target
  have hδa_le_ρs : δa ≤ ρs := by
    dsimp [δa]
    have hmin : min ρs δT ≤ ρs := min_le_left ρs δT
    nlinarith [hρs0, hmin]
  have hδa_le_δT : δa ≤ δT := by
    dsimp [δa]
    have hmin : min ρs δT ≤ δT := min_le_right ρs δT
    nlinarith [hδT0, hmin]
  have hExpSmall : ∀ v ∈ ball (0 : E) rS,
      expm v ∈ ball x₀ δa ∧ expm v ∈ V ∧ expm v ∈ φ.target := by
    intro v hv
    have hvρm : v ∈ ball (0 : E) ρm := ball_subset_ball hrSρm hv
    rcases hGeoCurves v hvρm with ⟨cv, velv, hcv0, hcv1, hcvd, hcvsp, hcvstay, hcvformula, hcvO⟩
    have hd : expm v ∈ ball x₀ δa := by
      rw [← hcv1]
      exact hcvstay 1 ⟨by norm_num, by norm_num⟩
    have hV : expm v ∈ V := by
      have hvεV : v ∈ ball (0 : E) εV := ball_subset_ball hrSεV hv
      exact hδVsub (hεVsub ⟨v, hvεV, rfl⟩)
    have hT : expm v ∈ φ.target := hδTsub (ball_subset_ball hδa_le_δT hd)
    exact ⟨hd, hV, hT⟩
  have hExpImgV : expm '' ball (0 : E) rS ⊆ V := by
    intro y hy
    rcases hy with ⟨v, hv, rfl⟩
    exact (hExpSmall v hv).2.1
  have hExpImgT : expm '' ball (0 : E) rS ⊆ φ.target := by
    intro y hy
    rcases hy with ⟨v, hv, rfl⟩
    exact (hExpSmall v hv).2.2
  -- generic claims about images of balls of radius ≤ rS
  have hContφsource : ContinuousOn (fun x : M => (extChartAt I p) x) (extChartAt I p).source :=
    continuousOn_extChartAt (I := I) p
  have hExpBall_open (ρ : ℝ) (hρ0 : 0 < ρ) (hρle : ρ ≤ rS) :
      IsOpen (expm '' ball (0 : E) ρ) := by
    have hA_sub_V : expm '' ball (0 : E) ρ ⊆ V := by
      intro y hy
      rcases hy with ⟨v, hv, rfl⟩
      exact (hExpSmall v (ball_subset_ball hρle hv)).2.1
    have hContInvOnV : ContinuousOn modelInv V := hContInv.continuousOn
    have hopenVball : IsOpen (V ∩ modelInv ⁻¹' ball (0 : E) ρ) := by
      refine isOpen_iff_mem_nhds.mpr ?_
      intro y hy
      have hyV : y ∈ V := hy.1
      have hmb : modelInv y ∈ ball (0 : E) ρ := hy.2
      have hc : ContinuousAt modelInv y :=
        hContInvOnV.continuousAt (hVopen.mem_nhds hyV)
      have hpre : modelInv ⁻¹' ball (0 : E) ρ ∈ 𝓝 y :=
        hc.preimage_mem_nhds (isOpen_ball.mem_nhds hmb)
      exact Filter.inter_mem (hVopen.mem_nhds hyV) hpre
    have hA_eq : expm '' ball (0 : E) ρ = V ∩ modelInv ⁻¹' ball (0 : E) ρ := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨v, hv, rfl⟩
        have hyV : expm v ∈ V := hA_sub_V ⟨v, hv, rfl⟩
        have hvU : v ∈ U := hδUsub (ball_subset_ball (le_trans hρle hrSδU) hv)
        have hiv : modelInv (expm v) = v := hInv2 v hvU
        exact ⟨hyV, by simpa [hiv] using hv⟩
      · intro hy
        rcases hy with ⟨hyV, hyb⟩
        have h1 := hInv1 y hyV
        refine ⟨modelInv y, hyb, ?_⟩
        exact h1.2
    simpa [hA_eq] using hopenVball
  have hExpM0 : ExpM 0 = p := by
    dsimp [ExpM]
    rw [hExp0]
    exact PartialEquiv.left_inv (extChartAt I p) (mem_extChartAt_source p)
  -- the image of a ball (of radius ≤ rS) is a neighbourhood of p
  have hExpBall_nhds (ρ : ℝ) (hρ0 : 0 < ρ) (hρle : ρ ≤ rS) :
      ExpM '' ball (0 : E) ρ ∈ 𝓝 p := by
    let A : Set E := expm '' ball (0 : E) ρ
    have hA_sub_V : A ⊆ V := by
      intro y hy
      rcases hy with ⟨v, hv, rfl⟩
      exact (hExpSmall v (ball_subset_ball hρle hv)).2.1
    have hAopen : IsOpen A := hExpBall_open ρ hρ0 hρle
    have hx₀A : x₀ ∈ A := by
      refine ⟨0, (mem_ball.mpr (by simpa [dist_eq_norm] using hρ0)), ?_⟩
      exact hExp0
    have hA_nhds : A ∈ 𝓝 x₀ := hAopen.mem_nhds hx₀A
    have hpsrc : p ∈ (extChartAt I p).source := mem_extChartAt_source p
    have hφcontAt_p : ContinuousAt (fun x : M => (extChartAt I p) x) p :=
      hContφsource.continuousAt ((isOpen_extChartAt_source (I := I) p).mem_nhds hpsrc)
    have hpre_nhds : (fun x : M => (extChartAt I p) x) ⁻¹' A ∈ 𝓝 p :=
      hφcontAt_p.preimage_mem_nhds (by simpa [x₀] using hA_nhds)
    have hsrc_nhds : (extChartAt I p).source ∈ 𝓝 p :=
      (isOpen_extChartAt_source (I := I) p).mem_nhds hpsrc
    have hboth : ((fun x : M => (extChartAt I p) x) ⁻¹' A ∩ (extChartAt I p).source) ∈ 𝓝 p :=
      Filter.inter_mem hpre_nhds hsrc_nhds
    have hsub : ((fun x : M => (extChartAt I p) x) ⁻¹' A ∩ (extChartAt I p).source)
        ⊆ ExpM '' ball (0 : E) ρ := by
      intro z hz
      have hφzA : (extChartAt I p) z ∈ A := hz.1
      rcases hφzA with ⟨v, hv, hφzv⟩
      refine ⟨v, hv, ?_⟩
      -- z = φ.symm (φ z) = φ.symm (expm v) = ExpM v
      have hzsrc : z ∈ (extChartAt I p).source := hz.2
      have hleft : (extChartAt I p).symm ((extChartAt I p) z) = z :=
        PartialEquiv.left_inv (extChartAt I p) hzsrc
      have hmain : (extChartAt I p).symm (expm v) = z := by
        exact (congrArg (extChartAt I p).symm hφzv).trans hleft
      exact hmain
    exact mem_of_superset hboth hsub
  have hSbig_nhds : ExpM '' ball (0 : E) rS ∈ 𝓝 p := hExpBall_nhds rS hrS0 (le_rfl)
  -- finite metric ball constant: eball p c ⊆ Sbig  (c : ℝ, 0 < c)
  have hc : ∃ c : ℝ, 0 < c ∧ ∀ y : M, edist p y < ENNReal.ofReal c → y ∈ ExpM '' ball (0 : E) rS := by
    rcases Metric.nhds_basis_eball.mem_iff.mp hSbig_nhds with ⟨η, hη0, hη⟩
    let η' : ℝ≥0∞ := min η 1
    have hη'0 : 0 < η' := lt_min hη0 (by norm_num)
    have hη'le1 : η' ≤ 1 := min_le_right _ _
    have hη'ne_top : η' ≠ (⊤ : ℝ≥0∞) :=
      ne_top_of_le_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hη'le1
    have hball : {y : M | edist p y < η'} ⊆ ExpM '' ball (0 : E) rS := by
      intro y hy
      exact hη (by simpa [Metric.mem_eball, edist_comm] using (lt_of_lt_of_le hy (min_le_left η 1)))
    let c : ℝ := η'.toReal
    refine ⟨c, ?_, ?_⟩
    · dsimp [c]
      exact ENNReal.toReal_pos (ne_of_gt hη'0) hη'ne_top
    · intro y hy
      apply hball
      have hc_eq : ENNReal.ofReal c = η' := by
        dsimp [c]
        exact ENNReal.ofReal_toReal hη'ne_top
      simpa [hc_eq] using hy
  rcases hc with ⟨c, hc0, hcball⟩
  -- small final radius r: r ≤ rS and √‖ge x₀‖ * r < c
  let B0 : E →L[ℝ] E →L[ℝ] ℝ := ge x₀
  let r : ℝ := min rS (c / (2 * (Real.sqrt ‖B0‖ + 1)))
  have hcpos : 0 < c / (2 * (Real.sqrt ‖B0‖ + 1)) := by positivity
  have hr0 : 0 < r := lt_min hrS0 hcpos
  have hrrS : r ≤ rS := min_le_left _ _
  have hrc : r ≤ c / (2 * (Real.sqrt ‖B0‖ + 1)) := min_le_right _ _
  have hb0_nonneg : ∀ v : E, 0 ≤ B0 v v := by
    intro v
    by_cases hv : v = 0
    · subst v; simp [B0]
    · exact le_of_lt (hgePos x₀ v hv)
  have hsmall : ∀ v : E, v ∈ ball (0 : E) r → Real.sqrt (B0 v v) < c := by
    intro v hv
    have hnorm : ‖v‖ < r := by simpa [dist_eq_norm] using (mem_ball.mp hv)
    have hsqrt_nonneg : 0 ≤ Real.sqrt ‖B0‖ := Real.sqrt_nonneg ‖B0‖
    have hbv : Real.sqrt (B0 v v) ≤ Real.sqrt ‖B0‖ * ‖v‖ := sqrt_bilin_le B0 v (hb0_nonneg v)
    have hle2 : Real.sqrt ‖B0‖ * r < c := by
      have hden : 0 < 2 * (Real.sqrt ‖B0‖ + 1) := by positivity
      have hfrac : Real.sqrt ‖B0‖ < 2 * (Real.sqrt ‖B0‖ + 1) := by
        nlinarith [hsqrt_nonneg]
      have h1 : Real.sqrt ‖B0‖ * r ≤ Real.sqrt ‖B0‖ * (c / (2 * (Real.sqrt ‖B0‖ + 1))) :=
        mul_le_mul_of_nonneg_left hrc hsqrt_nonneg
      have h2 : Real.sqrt ‖B0‖ * (c / (2 * (Real.sqrt ‖B0‖ + 1))) < c := by
        have hmul : Real.sqrt ‖B0‖ * c < (2 * (Real.sqrt ‖B0‖ + 1)) * c :=
          mul_lt_mul_of_pos_right hfrac hc0
        have hdiv : Real.sqrt ‖B0‖ * c / (2 * (Real.sqrt ‖B0‖ + 1)) < c := by
          rw [div_lt_iff₀ hden]
          simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
        rw [← mul_div_assoc]
        exact hdiv
      exact lt_of_le_of_lt h1 h2
    exact lt_of_le_of_lt hbv (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_of_lt hnorm) hsqrt_nonneg) hle2)
  let S : Set M := ExpM '' ball (0 : E) r
  let invM : M → E := fun y => modelInv (φ y)
  have hBallU : ball (0 : E) r ⊆ U := fun v hv => hδUsub (ball_subset_ball (le_trans hrrS hrSδU) hv)
  have hExpTgt (v : E) (hv : v ∈ ball (0 : E) r) : expm v ∈ φ.target :=
    (hExpSmall v (ball_subset_ball hrrS hv)).2.2
  have hSnhds : S ∈ 𝓝 p := by
    dsimp [S]
    exact hExpBall_nhds r hr0 hrrS
  have hS_in : ∀ v ∈ ball (0 : E) r, ExpM v ∈ S := by
    intro v hv
    exact mem_image_of_mem ExpM hv
  have hExpCont : ContinuousOn ExpM (ball (0 : E) r) := by
    have hf : ContinuousOn expm (ball (0 : E) r) := hContU.mono hBallU
    have hM : ∀ v ∈ ball (0 : E) r, expm v ∈ φ.target := hExpTgt
    have hg : ContinuousOn (fun y : E => (extChartAt I p).symm y) (extChartAt I p).target :=
      continuousOn_extChartAt_symm (I := I) p
    have hcomp : ContinuousOn (fun v : E => (extChartAt I p).symm (expm v)) (ball (0 : E) r) :=
      ContinuousOn.comp hg hf hM
    refine hcomp.congr ?_
    intro v hv
    rfl
  have hInjSub : Function.Injective (fun v : {v : E // v ∈ ball (0 : E) r} => ExpM v.1) := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hEq
    have hφEa : (extChartAt I p) (ExpM a) = expm a := by
      have hE : ExpM a = (extChartAt I p).symm (expm a) := rfl
      rw [hE]
      exact PartialEquiv.right_inv (extChartAt I p) (hExpTgt a ha)
    have hφEb : (extChartAt I p) (ExpM b) = expm b := by
      have hE : ExpM b = (extChartAt I p).symm (expm b) := rfl
      rw [hE]
      exact PartialEquiv.right_inv (extChartAt I p) (hExpTgt b hb)
    have hφEq0 : expm a = expm b := by
      have h := congrArg (fun z : M => (extChartAt I p) z) hEq
      rw [hφEa, hφEb] at h
      exact h
    have hUa : a ∈ U := hBallU ha
    have hUb : b ∈ U := hBallU hb
    have hφEq0' : (fun v : U => expm v.1) ⟨a, hUa⟩ = (fun v : U => expm v.1) ⟨b, hUb⟩ := by
      simpa using hφEq0
    have hsub := hInj hφEq0'
    have hab : a = b := congrArg Subtype.val hsub
    exact Subtype.ext hab
  have hSurj : Set.SurjOn ExpM (ball (0 : E) r) S := by
    intro y hy
    exact hy
  have hInvS : ∀ y ∈ S, invM y ∈ ball (0 : E) r ∧ ExpM (invM y) = y := by
    intro y hy
    rcases hy with ⟨v, hv, hEqv⟩
    have hUv : v ∈ U := hBallU hv
    have hyexp : y = (extChartAt I p).symm (expm v) := by
      dsimp [ExpM] at hEqv
      exact hEqv.symm
    have hysrc : y ∈ (extChartAt I p).source := by
      rw [hyexp]
      exact (extChartAt I p).map_target (hExpTgt v hv)
    have hφy : (extChartAt I p) y = expm v := by
      rw [hyexp]
      exact PartialEquiv.right_inv (extChartAt I p) (hExpTgt v hv)
    constructor
    · -- invM y = modelInv (φ y) = modelInv (expm v) = v ∈ ball 0 r
      have hm : modelInv (expm v) = v := hInv2 v hUv
      dsimp [invM]
      rw [hφy, hm]
      exact hv
    · -- ExpM (invM y) = φ.symm (expm (modelInv (φ y))) = φ.symm (φ y) = y
      have hyV : expm v ∈ V := (hExpSmall v (ball_subset_ball hrrS hv)).2.1
      have hφyV : (extChartAt I p) y ∈ V := by rw [hφy]; exact hyV
      have h1 : expm (modelInv ((extChartAt I p) y)) = (extChartAt I p) y := (hInv1 ((extChartAt I p) y) hφyV).2
      have h2 : (extChartAt I p).symm ((extChartAt I p) y) = y :=
        PartialEquiv.left_inv (extChartAt I p) hysrc
      dsimp [invM, ExpM]
      -- show φ.symm (expm (modelInv (φ y))) = y
      rw [h1]
      exact h2
  have hInvExp : ∀ v ∈ ball (0 : E) r, invM (ExpM v) = v := by
    intro v hv
    have hUv : v ∈ U := hBallU hv
    have hTv : expm v ∈ φ.target := hExpTgt v hv
    have hφExp : (extChartAt I p) (ExpM v) = expm v := by
      dsimp [ExpM]
      exact PartialEquiv.right_inv (extChartAt I p) hTv
    have hm : modelInv (expm v) = v := hInv2 v hUv
    dsimp [invM, ExpM]
    rw [hφExp, hm]
  -- the radial identity
  have hRadial : ∀ v ∈ ball (0 : E) r,
      edist p (ExpM v) = ENNReal.ofReal (Real.sqrt (B0 v v)) := by
    intro v hv
    let s₀ : ℝ := Real.sqrt (B0 v v)
    have hUv : v ∈ U := hBallU hv
    have hvρm : v ∈ ball (0 : E) ρm := ball_subset_ball (le_trans hrrS hrSρm) hv
    have hs0nonneg : 0 ≤ s₀ := by dsimp [s₀]; exact Real.sqrt_nonneg _
    have hLdef : ENNReal.ofReal s₀ = ENNReal.ofReal (Real.sqrt (B0 v v)) := rfl
    -- upper bound: the model geodesic curve to exp v has length s₀
    have hUp : edist p (ExpM v) ≤ ENNReal.ofReal s₀ := by
      rcases hGeoCurves v hvρm with ⟨cv, velv, hcv0, hcv1, hcvd, hcvsp, hcvstay, hcvformula, hcvO⟩
      let γv : ℝ → M := fun t => (extChartAt I p).symm (cv t)
      have hγeq (t : ℝ) : γv t = (extChartAt I p).symm (cv t) := rfl
      have hγv0 : γv 0 = p := by
        dsimp [γv]
        rw [hcv0]
        exact (extChartAt I p).left_inv (mem_extChartAt_source p)
      have hγv1 : γv 1 = ExpM v := by
        dsimp [γv, ExpM]
        rw [hcv1]
        rfl
      have hcvCont : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 cv (Icc (0 : ℝ) 1) := by
        rcases hcvO with ⟨O, hOopen, hOIcc, hcvC1⟩
        exact (contMDiffOn_iff_contDiffOn).mpr (hcvC1.mono hOIcc)
      have hcvMaps : Set.MapsTo cv (Icc (0 : ℝ) 1) (extChartAt I p).target := by
        intro t ht
        exact hδTsub (ball_subset_ball hδa_le_δT (hcvstay t ht))
      have hγvC : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γv (Icc (0 : ℝ) 1) := by
        dsimp [γv]
        exact (contMDiffOn_extChartAt_symm (I := I) p).comp hcvCont hcvMaps
      have hPt (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
          ‖(mfderiv% γv t) 1‖ₑ = ENNReal.ofReal s₀ := by
        have hsp := hSpeedClause (γ := γv) (c := cv) (t := t) (u := velv t)
        have hcb : cv t ∈ ball (extChartAt I p p) ρs :=
          ball_subset_ball hδa_le_ρs (hcvstay t ht)
        have hmain := hsp (fun s => hγeq s) hcb (hcvd t ht)
        rw [hmain]
        exact congrArg ENNReal.ofReal (by simpa [s₀, B0] using hcvsp t ht)
      have hpl : Manifold.pathELength I γv 0 1 ≤ ENNReal.ofReal s₀ := by
        rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
        calc
          (∫⁻ t in Icc (0 : ℝ) 1, ‖(mfderiv% γv t) 1‖ₑ)
              = ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal s₀ :=
                  MeasureTheory.setLIntegral_congr_fun measurableSet_Icc hPt
          _ = ENNReal.ofReal s₀ * volume (Icc (0 : ℝ) 1) := MeasureTheory.setLIntegral_const _ _
          _ = ENNReal.ofReal s₀ := by
              rw [Real.volume_Icc]
              simp
          _ ≤ ENNReal.ofReal s₀ := le_rfl
      have hγdist : Manifold.riemannianEDist I p (ExpM v) ≤ Manifold.pathELength I γv 0 1 :=
        Manifold.riemannianEDist_le_pathELength (I := I) hγvC hγv0 hγv1 zero_le_one
      rw [IsRiemannianManifold.out (I := I) p (ExpM v)]
      exact hγdist.trans hpl
    -- lower bound: every path from p to ExpM v has length ≥ s₀
    have hLo : ENNReal.ofReal s₀ ≤ edist p (ExpM v) := by
      by_cases hge : ENNReal.ofReal s₀ ≤ edist p (ExpM v)
      · exact hge
      · have hlt : edist p (ExpM v) < ENNReal.ofReal s₀ := lt_of_not_ge hge
        have hlt' : Manifold.riemannianEDist I p (ExpM v) < ENNReal.ofReal s₀ := by
          rwa [← IsRiemannianManifold.out (I := I) p (ExpM v)]
        rcases Manifold.exists_lt_locally_constant_of_riemannianEDist_lt (I := I) hlt' zero_lt_one
          with ⟨γ, hγ0, hγ1, hγsm, hγlen, hγloc0, hγloc1⟩
        have hγOn (s : Set ℝ) : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s := hγsm.contMDiffOn
        -- all points of γ over [0,1] lie inside Sbig (metric-ball argument)
        have hsmlt_c : ENNReal.ofReal s₀ < ENNReal.ofReal c := by
          have hltc : s₀ < c := by simpa [s₀, B0] using (hsmall v hv)
          exact (ENNReal.ofReal_lt_ofReal_iff hc0).mpr hltc
        have hγin : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ ExpM '' ball (0 : E) rS := by
          intro t ht
          have hdist_le : edist p (γ t) ≤ Manifold.pathELength I γ 0 1 := by
            have htmp : Manifold.riemannianEDist I p (γ t) ≤ Manifold.pathELength I γ 0 1 := by
              have hb : γ t = γ t := rfl
              have hm : Manifold.riemannianEDist I p (γ t) ≤ Manifold.pathELength I γ 0 t :=
                Manifold.riemannianEDist_le_pathELength (I := I) (hγOn (Icc (0 : ℝ) t))
                  hγ0 hb ht.1
              exact hm.trans (Manifold.pathELength_mono (a := 0) (a' := 0) (b := t) (b' := 1)
                (le_rfl) ht.2)
            rw [← IsRiemannianManifold.out (I := I) p (γ t)] at htmp
            exact htmp
          have hltc2 : edist p (γ t) < ENNReal.ofReal c := lt_of_le_of_lt hdist_le
            (lt_trans hγlen hsmlt_c)
          exact hcball (γ t) hltc2
        have hγsrc : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (extChartAt I p).source := by
          intro t ht
          rcases hγin t ht with ⟨w, hw, hEqw⟩
          have hEqs : γ t = (extChartAt I p).symm (expm w) :=
            hEqw.symm.trans (show ExpM w = (extChartAt I p).symm (expm w) from rfl)
          rw [hEqs]
          exact (extChartAt I p).map_target ((hExpSmall w hw).2.2)
        -- coordinate curve of γ
        let ccoor : ℝ → E := fun t => (extChartAt I p) (γ t)
        let gamT : ℝ → M := fun t => (extChartAt I p).symm (ccoor t)
        have hγeqgamT : Set.EqOn γ gamT (Icc (0 : ℝ) 1) := by
          intro t ht
          dsimp [gamT, ccoor]
          exact (PartialEquiv.left_inv (extChartAt I p) (hγsrc t ht)).symm
        have hplEq : Manifold.pathELength I γ 0 1 = Manifold.pathELength I gamT 0 1 :=
          Manifold.pathELength_congr hγeqgamT
        -- gamT is C¹ on an open set containing [0,1]; its coordinate curve ccoor is C¹ there
        have hOγ : ∃ O : Set ℝ, IsOpen O ∧ Icc (0 : ℝ) 1 ⊆ O ∧ ContDiffOn ℝ 1 ccoor O := by
          let O : Set ℝ := γ ⁻¹' (extChartAt I p).source
          have hγcont : Continuous γ := hγsm.continuous
          have hOopen : IsOpen O := hγcont.isOpen_preimage (extChartAt I p).source
            (isOpen_extChartAt_source (I := I) p)
          have hOIcc : Icc (0 : ℝ) 1 ⊆ O := by
            intro t ht
            simpa [O] using (hγsrc t ht)
          have hγOnO : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ O := hγsm.contMDiffOn
          have hsub : O ⊆ γ ⁻¹' (chartAt H p).source := by
            intro t ht
            simpa [O, extChartAt_source] using ht
          have hphi : ContMDiffOn I 𝓘(ℝ, E) 1 (extChartAt I p) (chartAt H p).source := by
            have hfull : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I p) (chartAt H p).source :=
              contMDiffOn_extChartAt (I := I) (x := p)
            exact hfull.of_le (by norm_num : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))
          have hcomp : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 ((extChartAt I p) ∘ γ) O := by
            exact ContMDiffOn.comp hphi hγOnO hsub
          have hcomp' : ContDiffOn ℝ 1 ((extChartAt I p) ∘ γ) O :=
            contMDiffOn_iff_contDiffOn.mp hcomp
          refine ⟨O, hOopen, hOIcc, ?_⟩
          convert hcomp' using 1
          funext t
          rfl
        -- staying in V and agreement ball along the way
        have hccoorV : ∀ s ∈ Icc (0 : ℝ) 1, ccoor s ∈ V := by
          intro s hs
          rcases hγin s hs with ⟨w, hw, hEqw⟩
          have hval : ccoor s = expm w := by
            dsimp [ccoor]
            have hEqs : γ s = (extChartAt I p).symm (expm w) :=
              hEqw.symm.trans (show ExpM w = (extChartAt I p).symm (expm w) from rfl)
            rw [hEqs]
            exact PartialEquiv.right_inv (extChartAt I p) ((hExpSmall w hw).2.2)
          rw [hval]
          exact (hExpSmall w hw).2.1
        have hccoorAgree : ∀ s ∈ Icc (0 : ℝ) 1, ccoor s ∈ ball (extChartAt I p p) ρs := by
          intro s hs
          rcases hγin s hs with ⟨w, hw, hEqw⟩
          have hval : ccoor s = expm w := by
            dsimp [ccoor]
            have hEqs : γ s = (extChartAt I p).symm (expm w) :=
              hEqw.symm.trans (show ExpM w = (extChartAt I p).symm (expm w) from rfl)
            rw [hEqs]
            exact PartialEquiv.right_inv (extChartAt I p) ((hExpSmall w hw).2.2)
          have hd : expm w ∈ ball (extChartAt I p p) δa := (hExpSmall w hw).1
          rw [hval]
          exact ball_subset_ball hδa_le_ρs hd
        -- model minimality + coordinate length identity
        have hccoor0 : ccoor 0 = x₀ := by
          dsimp [ccoor, x₀]
          rw [hγ0]
        have hccoor1 : ccoor 1 = expm v := by
          dsimp [ccoor]
          rw [hγ1]
          have hE : ExpM v = (extChartAt I p).symm (expm v) := rfl
          rw [hE]
          exact PartialEquiv.right_inv (extChartAt I p) (hExpTgt v hv)
        have hMlen : Real.sqrt ((ge x₀) v v) ≤ Model.mgLength ge ccoor 0 1 := by
          exact hMin v hUv ccoor hccoor0 hccoor1 hOγ hccoorV
        -- pointwise speed identity for gamT on (0,1)
        have hgamTder : ∀ t ∈ Ioo (0 : ℝ) 1,
            ‖(mfderiv% gamT t) 1‖ₑ = ENNReal.ofReal
              (Real.sqrt ((ge (ccoor t)) (deriv ccoor t) (deriv ccoor t))) := by
          intro t ht
          rcases hOγ with ⟨O, hOopen, hOIcc, hCcoor⟩
          have htcc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
          have hsp := hSpeedClause (γ := gamT) (c := ccoor) (t := t) (u := deriv ccoor t)
          have hγe : ∀ s : ℝ, gamT s = (extChartAt I p).symm (ccoor s) := by
            intro s
            rfl
          have hder : HasDerivAt ccoor (deriv ccoor t) t := by
            have hOmem : O ∈ 𝓝 t := hOopen.mem_nhds (hOIcc htcc)
            have hdf : DifferentiableAt ℝ ccoor t :=
              (hCcoor.differentiableOn (by norm_num : (1 : ℕ∞ω) ≠ 0)).differentiableAt hOmem
            exact hdf.hasDerivAt
          exact hsp hγe (hccoorAgree t htcc) hder
        -- pathELength of gamT ≥ ofReal (mgLength)
        have hgamTlen : ENNReal.ofReal (Model.mgLength ge ccoor 0 1) ≤ Manifold.pathELength I gamT 0 1 := by
          let sp : ℝ → ℝ := fun t => Real.sqrt ((ge (ccoor t)) (deriv ccoor t) (deriv ccoor t))
          have hsp0 : ∀ t, 0 ≤ sp t := fun t => Real.sqrt_nonneg _
          have hIoo_ae : (Ioo (0 : ℝ) 1) =ᵐ[MeasureTheory.volume] (Icc (0 : ℝ) 1) :=
            (MeasureTheory.Ioo_ae_eq_Ioc (a := (0:ℝ)) (b := (1:ℝ))).trans
              (MeasureTheory.Ioc_ae_eq_Icc (a := (0:ℝ)) (b := (1:ℝ)))
          have h1 : Manifold.pathELength I gamT 0 1 = ∫⁻ t in Ioo (0 : ℝ) 1, ‖(mfderiv% gamT t) 1‖ₑ := by
            rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
            exact (setLIntegral_congr (s := Icc (0 : ℝ) 1) (t := Ioo (0 : ℝ) 1) hIoo_ae.symm)
          have h2 : (∫⁻ t in Ioo (0 : ℝ) 1, ‖(mfderiv% gamT t) 1‖ₑ)
              = ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (sp t) := by
            refine setLIntegral_congr_fun measurableSet_Ioo ?_
            intro t ht
            dsimp [sp]
            exact hgamTder t ht
          -- sp is continuous on the open interval, hence ae-strongly measurable there
          have hspcont : ContinuousOn sp (Ioo (0 : ℝ) 1) := by
            rcases hOγ with ⟨O0, hO0open, hO0Icc, hCcoor0⟩
            have hsub : Ioo (0 : ℝ) 1 ⊆ O0 := fun t ht => hO0Icc ⟨le_of_lt ht.1, le_of_lt ht.2⟩
            have hfd : ContinuousOn (fun t : ℝ => fderiv ℝ ccoor t) O0 :=
              hCcoor0.continuousOn_fderiv_of_isOpen hO0open le_rfl
            have hderCont : ContinuousOn (fun t : ℝ => deriv ccoor t) O0 :=
              deriv_contDiffOn_contOn hCcoor0 hO0open
            have hcc : ContinuousOn ccoor O0 := hCcoor0.continuousOn
            have hccIoo : ContinuousOn ccoor (Ioo (0 : ℝ) 1) := hcc.mono hsub
            have hdIoo : ContinuousOn (fun t : ℝ => deriv ccoor t) (Ioo (0 : ℝ) 1) :=
              hderCont.mono hsub
            have hg : ContinuousOn (fun t : ℝ => ge (ccoor t)) (Ioo (0 : ℝ) 1) := by
              have hgfull : Continuous ge := hgeC.continuous
              have hgo : ContinuousOn ge univ := hgfull.continuousOn
              exact ContinuousOn.comp hgo hccIoo (by intro t ht; trivial)
            have hq1 : ContinuousOn (fun t : ℝ => (ge (ccoor t)) (deriv ccoor t)) (Ioo (0 : ℝ) 1) :=
              ContinuousOn.clm_apply hg hdIoo
            have hq2 : ContinuousOn (fun t : ℝ => ((ge (ccoor t)) (deriv ccoor t)) (deriv ccoor t))
                (Ioo (0 : ℝ) 1) := ContinuousOn.clm_apply hq1 hdIoo
            have hsp0' : sp = fun t : ℝ => Real.sqrt (((ge (ccoor t)) (deriv ccoor t)) (deriv ccoor t)) := by
              rfl
            rw [hsp0']
            exact hq2.sqrt
          have hspmeas : AEStronglyMeasurable sp (MeasureTheory.volume.restrict (Ioo (0 : ℝ) 1)) :=
            hspcont.aestronglyMeasurable measurableSet_Ioo
          have h3 : ENNReal.ofReal (∫ t in Ioo (0 : ℝ) 1, sp t)
              ≤ ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (sp t) := by
            let μ : Measure ℝ := MeasureTheory.volume.restrict (Ioo (0 : ℝ) 1)
            change ENNReal.ofReal (∫ x, sp x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (sp x) ∂μ
            have hmeas : AEStronglyMeasurable sp μ := by
              simpa [μ] using hspmeas
            by_cases hfi : Integrable sp μ
            · have hE := MeasureTheory.integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hsp0) hmeas
              rw [hE]
              exact ENNReal.ofReal_toReal_le (a := (∫⁻ x, ENNReal.ofReal (sp x) ∂μ))
            · have hz : (∫ x, sp x ∂μ) = 0 := integral_undef hfi
              rw [hz]
              simp
          have h4 : Model.mgLength ge ccoor 0 1 = ∫ t in Ioo (0 : ℝ) 1, sp t := by
            unfold Model.mgLength Model.mgSpeed
            rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
            -- interval integral over Ioc equals set integral over Ioo (restricted measures equal)
            have hrest : MeasureTheory.volume.restrict (Ioo (0 : ℝ) 1) =
                MeasureTheory.volume.restrict (Ioc (0 : ℝ) 1) := by
              exact MeasureTheory.Measure.restrict_congr_set
                (MeasureTheory.Ioo_ae_eq_Ioc (a := (0:ℝ)) (b := (1:ℝ)))
            calc
              (∫ t in Ioc (0 : ℝ) 1, Real.sqrt ((ge (ccoor t)) (deriv ccoor t) (deriv ccoor t)))
                  = ∫ t, Real.sqrt ((ge (ccoor t)) (deriv ccoor t) (deriv ccoor t)) ∂(MeasureTheory.volume.restrict (Ioc (0 : ℝ) 1)) := rfl
              _ = ∫ t, Real.sqrt ((ge (ccoor t)) (deriv ccoor t) (deriv ccoor t)) ∂(MeasureTheory.volume.restrict (Ioo (0 : ℝ) 1)) := by
                  rw [hrest]
              _ = ∫ t in Ioo (0 : ℝ) 1, Real.sqrt ((ge (ccoor t)) (deriv ccoor t) (deriv ccoor t)) := rfl
          have hmg : ENNReal.ofReal (Model.mgLength ge ccoor 0 1) ≤
              ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (sp t) := by
            rw [h4]
            -- sp definitional: rw needs exact: hsp0' again
            change ENNReal.ofReal (∫ t in Ioo (0 : ℝ) 1,
              Real.sqrt ((ge (ccoor t)) (deriv ccoor t) (deriv ccoor t)))
                ≤ ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal
                  (Real.sqrt ((ge (ccoor t)) (deriv ccoor t) (deriv ccoor t)))
            exact h3
          calc
            ENNReal.ofReal (Model.mgLength ge ccoor 0 1) ≤
                ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (sp t) := hmg
            _ = ∫⁻ t in Ioo (0 : ℝ) 1, ‖(mfderiv% gamT t) 1‖ₑ := h2.symm
            _ = Manifold.pathELength I gamT 0 1 := h1.symm
        have hcontra : ENNReal.ofReal s₀ ≤ Manifold.pathELength I γ 0 1 := by
          calc
            ENNReal.ofReal s₀ = ENNReal.ofReal (Real.sqrt ((ge x₀) v v)) := by
              simpa [s₀, B0]
            _ ≤ ENNReal.ofReal (Model.mgLength ge ccoor 0 1) :=
              ENNReal.ofReal_le_ofReal hMlen
            _ ≤ Manifold.pathELength I gamT 0 1 := hgamTlen
            _ = Manifold.pathELength I γ 0 1 := hplEq.symm
        exact False.elim ((lt_of_le_of_lt hcontra hγlen).ne rfl)
    exact le_antisymm hUp hLo
  -- assemble the answer
  let ρe : ℝ := min r (τe / 4)
  have hρe0 : 0 < ρe := by
    dsimp [ρe]
    exact lt_min hr0 (by positivity)
  have hρele : ρe ≤ r := by dsimp [ρe]; exact min_le_left _ _
  have hρeτe4 : ρe ≤ τe / 4 := by
    dsimp [ρe]
    exact min_le_right r (τe / 4)
  have hρeρm : ρe ≤ ρm := by
    dsimp [ρe]
    exact le_trans (min_le_right r (τe / 4)) (by nlinarith [hτele, hτe0])
  have hRadial' : ∀ v ∈ ball (0 : E) r,
      edist p (ExpM v) = ENNReal.ofReal (Real.sqrt ((ge (extChartAt I p p)) v v)) := by
    intro v hv
    simpa [B0, x₀] using hRadial v hv
  have hExpExpM : ∀ v ∈ ball (0 : E) ρe, ExpM v = (extChartAt I p).symm (expm v) := by
    intro v hv
    rfl
  have hRaySmall : ∀ u : E, ‖u‖ ≤ 1 → Real.sqrt ((ge (extChartAt I p p)) u u) = 1 →
      ∀ t ∈ Ioo (-(τe / 4)) (τe / 4), expm (t • u) = (Φm (extChartAt I p p, u) t).1 := by
    intro u hu hu1 t ht
    have hu2 : ‖u‖ ≤ 2 := by linarith
    have hge : ((ge (extChartAt I p p)) u) u = 1 := by
      have hnonneg : 0 ≤ ((ge (extChartAt I p p)) u) u := by
        by_cases hu0 : u = 0
        · subst u; simp
        · exact le_of_lt (hgePos (extChartAt I p p) u hu0)
      have hs : Real.sqrt (((ge (extChartAt I p p)) u) u) = 1 := hu1
      nlinarith [Real.sq_sqrt hnonneg, hs]
    have ht' : t ∈ Ioo (-(τe / 2)) (τe / 2) := by
      constructor <;> linarith [ht.1, ht.2]
    have hm := hRayProp u hu2 hge t ht'
    simpa [x₀] using hm
  have hcvSmall : ∃ ρT > 0, ρT ≤ ρs ∧
      ball x₀ ρT ⊆ (extChartAt I p).target ∧
      (∀ v ∈ ball (0 : E) ρe, ∃ cv velv : ℝ → E,
        cv 0 = extChartAt I p p ∧ cv 1 = expm v ∧
        (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt cv (velv t) t) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
           Real.sqrt ((ge (cv t)) (velv t) (velv t)) = Real.sqrt ((ge (extChartAt I p p)) v v)) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, cv t ∈ ball x₀ ρT) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, cv t = (Φm (x₀, (1 / τe) • v) (τe * t)).1) ∧
        (∃ O : Set ℝ, IsOpen O ∧ Icc (0 : ℝ) 1 ⊆ O ∧ ContDiffOn ℝ 1 cv O)) := by
    refine ⟨δa, hδa0, hδa_le_ρs, ?_, ?_⟩
    · intro y hy
      exact hδTsub (ball_subset_ball hδa_le_δT hy)
    · intro v hv
      have hvρm : v ∈ ball (0 : E) ρm := ball_subset_ball hρeρm hv
      rcases hGeoCurves v hvρm with ⟨cv, velv, hcv0, hcv1, hcvd, hcvsp, hcvstay, hcvformula, hcvO⟩
      refine ⟨cv, velv, ?_, hcv1, hcvd, ?_, ?_, ?_, hcvO⟩
      · simpa [x₀] using hcv0
      · intro t ht
        simpa [x₀] using hcvsp t ht
      · intro t ht
        exact hcvstay t ht
      · intro t ht
        simpa [x₀] using hcvformula t ht
  refine ⟨ρs, hρs0, ge, hgeC, hgeSymm, hgePos, hgeAgree, ⟨r, hr0, ExpM, S, invM,
    hExpM0, hSnhds, hS_in, hExpCont, hInjSub, hSurj, hInvS, hInvExp, hRadial',
    ⟨ρe, hρe0, τe, hτe0, hρele, hρeτe4, Φm, expm,
      hExpExpM, (by simpa [x₀] using hExp0), (by simpa [ρe] using (hExpC1.mono (ball_subset_ball hρeρm))),
      (by
        intro z hz
        constructor
        · exact (hΦm z hz).1
        · intro t ht
          exact hODEbig z hz t ht),
      (by
        intro v hv
        have hvρm : v ∈ ball (0 : E) ρm := ball_subset_ball hρeρm hv
        simpa [x₀] using hExpFlow v hvρm),
      hRaySmall, hcvSmall⟩⟩⟩
end Submission
