import Mathlib
import Submission.Work.OddBound.PolygonChart
import Submission.Work.OddBound.PiExtChart
import Submission.Work.OddBound.IndexBound
import Submission.Work.OddBound.exists_shorter_closed_curve_of_negative_index
import Submission.Work.OddBound.LiftKit
import Submission.Work.OddBound.design.IndexTransfer
import Submission.Work.OddBound.indexTransfer.Infra
import Submission.Work.OddBound.indexTransfer.gonEnergy_le_integral_curveSpeed_sq
import Submission.Work.OddBound.indexTransfer.secondVariation_unscaled
import Submission.Work.OddBound.indexTransfer.contMDiffOn_variation_unscaled
import Submission.Work.OddBound.indexTransfer.hasDerivAt_deriv_comp_line_of_fderiv_eq_zero
import Submission.Work.OddBound.indexTransfer.second_deriv_nonpos_of_eventually_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.OddBound.indexTransfer

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length
open Submission.InjRadius Submission.IndexIntrinsic Submission.CurvatureVec

set_option maxHeartbeats 2000000

/-- A `C²` function of one variable is differentiable on a neighbourhood of any point. -/
private lemma eventually_differentiableAt_of_contDiffAt_two {f : ℝ → ℝ} {x : ℝ}
    (h : ContDiffAt ℝ 2 f x) : ∀ᶠ y in nhds x, DifferentiableAt ℝ f y := by
  have h' : ContDiffWithinAt ℝ 2 f Set.univ x := h
  obtain ⟨u, hu, p, hp⟩ := h' 1 (by norm_num)
  have hu' : u ∈ nhds x := by simpa using hu
  have hdo : DifferentiableOn ℝ f u := (hp.contDiffOn).differentiableOn (by norm_num)
  exact hdo.eventually_differentiableAt hu'

theorem hasNegDefPlane_of_negativeDirichletIndex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {T : ℝ} (hT : 0 < T) {p : M} {c : ℝ → M}
    (hcsm : ContMDiff 𝓘(ℝ) I ∞ c)
    (hcgeo : ∀ t : ℝ, Submission.Geodesic.IsGeodesicAt (I := I) cov c t)
    (hcne : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) c t ≠ 0)
    (hcsp : ∀ t ∈ Set.Icc (0:ℝ) T, Submission.Length.curveSpeed (I := I) c t = 1)
    (hc0 : c 0 = p) (hcT : c T = p)
    {N : ℕ} (hN : 3 ≤ N) {w : Fin (N - 1) → M}
    (hsample : ∀ i : Fin (N + 1), c (((i : ℕ) : ℝ) * T / N) = Work.OddBound.gonVert p w (i : ℕ))
    (hsides : ∀ i : Fin N, Work.OddBound.gonSideLen (I := I) p w i = T / (N : ℝ))
    {x : Fin (N - 1) → M}
    (hwsrc : w ∈ (Work.OddBound.piExtChart (I := I) x).source)
    [ChartedSpace ((Fin (N - 1)) → E) ((Fin (N - 1)) → M)]
    (he : Work.OddBound.piExtChart (I := I) x ∈ atlas ((Fin (N - 1)) → E) ((Fin (N - 1)) → M))
    (hC2 : ContDiffAt ℝ 2
      (fun u : (Fin (N - 1)) → E =>
        Work.OddBound.gonEnergy (I := I) p ((Work.OddBound.piExtChart (I := I) x).symm u))
      ((Work.OddBound.piExtChart (I := I) x) w))
    (hF0 : fderiv ℝ
      (fun u : (Fin (N - 1)) → E =>
        Work.OddBound.gonEnergy (I := I) p ((Work.OddBound.piExtChart (I := I) x).symm u))
      ((Work.OddBound.piExtChart (I := I) x) w) = 0)
    {V W : (t : ℝ) → TangentSpace I (c t)}
    (hVsm : ∀ s ∈ Set.Icc (-1) (T + 1), SmoothAlongAt (I := I) c V s)
    (hV0 : V 0 = 0) (hVT : V T = 0)
    (hWsm : ∀ s ∈ Set.Icc (-1) (T + 1), SmoothAlongAt (I := I) c W s)
    (hW0 : W 0 = 0) (hWT : W T = 0)
    (hneg : ∀ a b : ℝ, (a, b) ≠ 0 →
      ∫ t in (0:ℝ)..T, idxAlong (cov := cov) c
        (fun s : ℝ => a • V s + b • W s)
        (covAlong cov (fun s : ℝ => a • V s + b • W s)) t < 0) :
    Work.OddBound.HasNegDefPlane ((Fin (N - 1)) → E) (Work.OddBound.gonEnergy (I := I) p) w := by
  classical
  have hcsmOn : ContMDiffOn 𝓘(ℝ) I ∞ c Set.univ := hcsm.contMDiffOn
  -- #### the variation family
  set z : (ℝ × ℝ) → Fin (N - 1) → M :=
    fun q i => GExp (cov := cov) hmet (c ((((i : ℕ) : ℝ) + 1) * T / N))
      (q.1 • V ((((i : ℕ) : ℝ) + 1) * T / N)
        + q.2 • W ((((i : ℕ) : ℝ) + 1) * T / N)) with hzdef
  set F : ((Fin (N - 1)) → E) → ℝ :=
    fun u => Work.OddBound.gonEnergy (I := I) p
      ((Work.OddBound.piExtChart (I := I) x).symm u) with hFdef
  set φ : (ℝ × ℝ) → ((Fin (N - 1)) → E) :=
    fun q => (Work.OddBound.piExtChart (I := I) x) (z q) with hφdef
  -- `z 0 = w`
  have hz0 : z 0 = w := by
    funext i
    have h1 : z 0 i = c ((((i : ℕ) : ℝ) + 1) * T / N) := by
      rw [hzdef]
      simp
    rw [h1]
    have h2 := hsample ⟨(i : ℕ) + 1, by omega⟩
    rw [Nat.cast_add, Nat.cast_one] at h2
    rw [h2, Work.OddBound.gonVert_succ p w i.isLt]
  -- every vertex lies in the source of its extended chart
  have hsrcx : ∀ i : Fin (N - 1), w i ∈ (Work.OddBound.extChartHomeo (I := I) (x i)).source := by
    have h := hwsrc
    simp only [Work.OddBound.piExtChart, OpenPartialHomeomorph.pi, PartialEquiv.pi_source,
      Set.mem_pi, Set.mem_univ, true_implies] at h
    exact h
  -- #### smoothness of the family in `q`
  have hz_sm : ∀ i : Fin (N - 1),
      ContMDiffAt (modelWithCornersSelf ℝ (ℝ × ℝ)) I 2 (fun q : ℝ × ℝ => z q i) 0 := by
    intro i
    set s : ℝ := (((i : ℕ) : ℝ) + 1) * T / N with hsdef
    let hclm : (ℝ × ℝ) →L[ℝ] E :=
      (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (show E from V s) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (show E from W s)
    have hclm_apply : ∀ q : ℝ × ℝ, hclm q = (q.1 • V s + q.2 • W s : E) := by
      intro q
      simp only [hclm]
      rfl
    have hlin : ContMDiffAt (modelWithCornersSelf ℝ (ℝ × ℝ)) (modelWithCornersSelf ℝ E) 2
        (⇑hclm) 0 := hclm.contMDiffAt
    have hg : ContMDiffAt (modelWithCornersSelf ℝ E) I 2
        (fun u : E => GExp (cov := cov) hmet (c s) (show TangentSpace I (c s) from u))
        (hclm 0) :=
      (Submission.GExpSmooth.exists_contMDiffAt_GExp (cov := cov) hmet (c s)
        ((hclm 0 : E) : TangentSpace I (c s))).of_le (WithTop.coe_le_coe.mpr le_top)
    refine (hg.comp 0 hlin).congr_of_eventuallyEq ?_
    filter_upwards with q
    simp only [Function.comp_apply, hclm_apply, hzdef]
    rw [hsdef]
  have hzcont : ContinuousAt z 0 := by
    rw [continuousAt_pi]
    intro i
    exact (hz_sm i).continuousAt
  have hφsm : ContDiffAt ℝ 2 φ 0 := by
    rw [hφdef]
    have hcoord : ∀ i : Fin (N - 1),
        ContMDiffAt (modelWithCornersSelf ℝ (ℝ × ℝ)) (modelWithCornersSelf ℝ E) 2
          (fun q : ℝ × ℝ => extChartAt I (x i) (z q i)) 0 := by
      intro i
      have hsrcw : w i ∈ (chartAt H (x i)).source := by
        rw [← Work.OddBound.extChartHomeo_source (I := I) (x i)]
        exact hsrcx i
      have hchart : ContMDiffAt I (modelWithCornersSelf ℝ E) 2
          (↑(extChartAt I (x i))) (z 0 i) := by
        rw [hz0]
        exact contMDiffAt_extChartAt' (I := I) (x := x i) (n := 2) hsrcw
      exact hchart.comp 0 (hz_sm i)
    have hpi : (fun q : ℝ × ℝ => (Work.OddBound.piExtChart (I := I) x) (z q))
        = fun q : ℝ × ℝ => fun i : Fin (N - 1) => extChartAt I (x i) (z q i) := by
      funext q i
      simp only [Work.OddBound.piExtChart, OpenPartialHomeomorph.pi_apply,
        Work.OddBound.extChartHomeo_coe, extChartAt_coe, Function.comp_apply]
    show ContDiffAt ℝ 2 (fun q : ℝ × ℝ => fun i : Fin (N - 1) =>
      extChartAt I (x i) (z q i)) 0
    exact (contDiffAt_pi).mpr (fun i => (contMDiffAt_iff_contDiffAt).mp (hcoord i))
  have hphi0 : φ 0 = (Work.OddBound.piExtChart (I := I) x) w := by
    rw [hφdef]
    show (Work.OddBound.piExtChart (I := I) x) (z 0) = _
    rw [hz0]
  have hF_c2 : ContDiffAt ℝ 2 F ((Work.OddBound.piExtChart (I := I) x) w) := by
    rw [hFdef]; exact hC2
  have hF_d0 : fderiv ℝ F ((Work.OddBound.piExtChart (I := I) x) w) = 0 := by
    rw [hFdef]; exact hF0
  -- #### the polygon energy at `w`
  have hgonw : Work.OddBound.gonEnergy (I := I) p w = T ^ 2 / 2 := by
    rw [Work.OddBound.gonEnergy]
    have hsum : (∑ i : Fin N, (Work.OddBound.gonSideLen (I := I) p w i) ^ 2)
        = (N : ℝ) * (T / (N : ℝ)) ^ 2 := by
      simp only [hsides]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hsum]
    have hNpos : (0:ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    field_simp
    try ring
  -- #### the main step
  have key : ∀ X : ℝ × ℝ, X ≠ 0 →
      (fderiv ℝ (fderiv ℝ F) ((Work.OddBound.piExtChart (I := I) x) w))
        ((fderiv ℝ φ 0) X) ((fderiv ℝ φ 0) X) < 0 := by
    intro X hX
    set Z : (t : ℝ) → TangentSpace I (c t) := fun s => X.1 • V s + X.2 • W s with hZdef
    have hZsm : ∀ s ∈ Set.Icc (0 - 1) (T + 1), SmoothAlongAt (I := I) c Z s := by
      intro s hs
      have hs' : s ∈ Set.Icc (-1 : ℝ) (T + 1) := by simpa using hs
      rw [hZdef]
      exact Submission.ConjEnergy.SmoothAlongAt_add (I := I)
        (Submission.EnergyRay.SmoothAlongAt_smul (I := I) X.1 (hVsm s hs'))
        (Submission.EnergyRay.SmoothAlongAt_smul (I := I) X.2 (hWsm s hs'))
    set Efun : ℝ → ℝ := fun σ => ∫ t in (0:ℝ)..T, (Submission.Length.curveSpeed (I := I)
      (fun s : ℝ => GExp (cov := cov) hmet (c s) (σ • Z s)) t) ^ 2 with hEfundef
    set hXfun : ℝ → ℝ := fun σ => Work.OddBound.gonEnergy (I := I) p (z (σ • X)) with hhXdef
    set gXfun : ℝ → ℝ := fun σ => T / 2 * Efun σ with hgXdef
    set κ : ℝ → ℝ := fun σ => hXfun σ - gXfun σ with hκdef
    -- `z (σ • X)` is the sampling of the variation curve
    have hzagree : ∀ σ : ℝ, z (σ • X) = fun i : Fin (N - 1) =>
        GExp (cov := cov) hmet (c ((((i : ℕ) : ℝ) + 1) * T / N))
          (σ • Z ((((i : ℕ) : ℝ) + 1) * T / N)) := by
      intro σ
      funext i
      rw [hzdef, hZdef]
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, smul_add, smul_smul]
    have hend0 : ∀ σ : ℝ, (fun s : ℝ => GExp (cov := cov) hmet (c s) (σ • Z s)) 0 = p := by
      intro σ
      have h00 : (σ • Z 0 : TangentSpace I (c 0)) = 0 := by
        rw [hZdef]
        simp [hV0, hW0]
      show GExp (cov := cov) hmet (c 0) (σ • Z 0) = p
      rw [h00, GExp_zero, hc0]
    have hendT : ∀ σ : ℝ, (fun s : ℝ => GExp (cov := cov) hmet (c s) (σ • Z s)) T = p := by
      intro σ
      have hTT : (σ • Z T : TangentSpace I (c T)) = 0 := by
        rw [hZdef]
        simp [hVT, hWT]
      show GExp (cov := cov) hmet (c T) (σ • Z T) = p
      rw [hTT, GExp_zero, hcT]
    -- (1) the comparison inequality
    have hcomp : ∀ᶠ σ in nhds (0:ℝ), hXfun σ ≤ gXfun σ := by
      filter_upwards [contMDiffOn_variation_unscaled (cov := cov) (γ := c) (V := Z)
        (a := 0) (b := T) hmet htor hcsmOn hZsm hT] with σ hσ
      obtain ⟨hsm, -⟩ := hσ
      have hble := gonEnergy_le_integral_curveSpeed_sq (I := I) (T := T) (p := p)
        (Φ := fun s : ℝ => GExp (cov := cov) hmet (c s) (σ • Z s))
        (N := N) hT (hend0 σ) (hendT σ) (hsm.of_le (WithTop.coe_le_coe.mpr le_top)) (by omega)
      rw [← hzagree σ] at hble
      rw [hhXdef, hgXdef, hEfundef]
      exact hble
    -- (2) the second variation of the comparison functional
    obtain ⟨hEderiv, hEdiff0, hEdiffev⟩ := secondVariation_unscaled (cov := cov) hmet htor
      hcsmOn hcgeo hcne (V := Z) (a := 0) (b := T) hZsm hT
    have hIval : (∫ t in (0:ℝ)..T, Submission.IndexIntrinsic.idxAlong (cov := cov) c Z
        (Submission.JacobiGlobal.covAlong cov Z) t) < 0 := by
      have h := hneg X.1 X.2 (by simpa using hX)
      rwa [← hZdef] at h
    -- (3) the local maximum argument
    have heqX : (fun σ : ℝ => F (φ (σ • X))) =ᶠ[nhds (0:ℝ)] hXfun := by
      have hzcontX : ContinuousAt (fun σ : ℝ => z (σ • X)) 0 := by
        have h1 : ContinuousAt (fun σ : ℝ => σ • X) 0 := by fun_prop
        have hpt : ((0:ℝ) • X : ℝ × ℝ) = 0 := zero_smul ℝ X
        have hz' : ContinuousAt z ((0:ℝ) • X) := by rw [hpt]; exact hzcont
        exact hz'.comp (f := fun σ : ℝ => σ • X) h1
      filter_upwards [(hzcontX).preimage_mem_nhds
        ((Work.OddBound.piExtChart (I := I) x).open_source.mem_nhds
          (by rw [zero_smul, hz0]; exact hwsrc))]
        with σ hσ
      rw [hFdef, hφdef, hhXdef]
      show Work.OddBound.gonEnergy (I := I) p
        ((Work.OddBound.piExtChart (I := I) x).symm ((Work.OddBound.piExtChart (I := I) x) (z (σ • X))))
        = Work.OddBound.gonEnergy (I := I) p (z (σ • X))
      rw [(Work.OddBound.piExtChart (I := I) x).left_inv hσ]
    have hhX_C2 : ContDiffAt ℝ 2 hXfun 0 := by
      have hlin : ContDiffAt ℝ 2 (fun σ : ℝ => σ • X) 0 := by
        have hcd : ContDiff ℝ 2 (fun σ : ℝ => σ • X) := by fun_prop
        exact hcd.contDiffAt
      have hpt : ((0:ℝ) • X : ℝ × ℝ) = 0 := zero_smul ℝ X
      have hφat : ContDiffAt ℝ 2 φ ((0:ℝ) • X) := by rw [hpt]; exact hφsm
      have hφX : ContDiffAt ℝ 2 (fun σ : ℝ => φ (σ • X)) 0 :=
        ContDiffAt.comp (f := fun σ : ℝ => σ • X) (g := φ) (x := (0:ℝ)) hφat hlin
      have hpt2 : φ ((0:ℝ) • X) = (Work.OddBound.piExtChart (I := I) x) w := by
        rw [zero_smul, hphi0]
      have hFat : ContDiffAt ℝ 2 F (φ ((0:ℝ) • X)) := by rw [hpt2]; exact hF_c2
      exact (ContDiffAt.comp (f := fun σ : ℝ => φ (σ • X)) (g := F) (x := (0:ℝ))
        hFat hφX).congr_of_eventuallyEq heqX.symm
    have hhX_diff : DifferentiableAt ℝ hXfun 0 := hhX_C2.differentiableAt (by norm_num)
    have hhX_diffe : ∀ᶠ σ in nhds (0:ℝ), DifferentiableAt ℝ hXfun σ :=
      eventually_differentiableAt_of_contDiffAt_two hhX_C2
    have hgX_diff : DifferentiableAt ℝ gXfun 0 := by
      rw [hgXdef, hEfundef]
      exact hEdiff0.const_mul (T / 2)
    have hgX_diffe : ∀ᶠ σ in nhds (0:ℝ), DifferentiableAt ℝ gXfun σ := by
      rw [hgXdef, hEfundef]
      exact hEdiffev.mono (fun σ h => h.const_mul (T / 2))
    have hderivX : HasDerivAt (deriv hXfun)
        ((fderiv ℝ (fderiv ℝ F) ((Work.OddBound.piExtChart (I := I) x) w))
          ((fderiv ℝ φ 0) X) ((fderiv ℝ φ 0) X)) 0 := by
      have hbase := hasDerivAt_deriv_comp_line_of_fderiv_eq_zero (F := F)
        (x₀ := (Work.OddBound.piExtChart (I := I) x) w) (φ := φ) (X := X)
        hF_c2 hφsm hphi0 hF_d0
      refine hbase.congr_of_eventuallyEq ?_
      rw [hhXdef]
      exact heqX.symm.deriv
    have hderivG : HasDerivAt (deriv gXfun)
        (T * (∫ t in (0:ℝ)..T, Submission.IndexIntrinsic.idxAlong (cov := cov) c Z
          (Submission.JacobiGlobal.covAlong cov Z) t)) 0 := by
      have hev : deriv gXfun =ᶠ[nhds (0:ℝ)]
          fun σ : ℝ => T / 2 * deriv (fun σ : ℝ => ∫ t in (0:ℝ)..T, (Submission.Length.curveSpeed
            (I := I) (fun s : ℝ => GExp (cov := cov) hmet (c s) (σ • Z s)) t) ^ 2) σ := by
        filter_upwards [hEdiffev] with σ hσ
        rw [hgXdef, hEfundef]
        exact deriv_const_mul (T / 2) hσ
      have h2 : HasDerivAt (fun σ : ℝ => T / 2 * deriv (fun σ : ℝ => ∫ t in (0:ℝ)..T,
          (Submission.Length.curveSpeed (I := I)
            (fun s : ℝ => GExp (cov := cov) hmet (c s) (σ • Z s)) t) ^ 2) σ)
          (T / 2 * (2 * (∫ t in (0:ℝ)..T, Submission.IndexIntrinsic.idxAlong (cov := cov) c Z
            (Submission.JacobiGlobal.covAlong cov Z) t))) 0 := by
        exact hEderiv.const_mul (T / 2)
      refine (h2.congr_of_eventuallyEq hev).congr_deriv ?_
      ring
    have hκ1 : DifferentiableAt ℝ κ 0 := by
      rw [hκdef]
      exact hhX_diff.sub hgX_diff
    have hκ3 : ∀ᶠ σ in nhds (0:ℝ), DifferentiableAt ℝ κ σ := by
      filter_upwards [hhX_diffe, hgX_diffe] with σ h1 h2
      rw [hκdef]
      exact h1.sub h2
    have hX0 : hXfun 0 = T ^ 2 / 2 := by
      rw [hhXdef]
      show Work.OddBound.gonEnergy (I := I) p (z ((0:ℝ) • X)) = T ^ 2 / 2
      rw [zero_smul, hz0]
      exact hgonw
    have hE0 : Efun 0 = T := by
      show (∫ t in (0:ℝ)..T, (Submission.Length.curveSpeed (I := I)
        (fun s : ℝ => GExp (cov := cov) hmet (c s) ((0:ℝ) • Z s)) t) ^ 2) = T
      have hfun : (fun s : ℝ => GExp (cov := cov) hmet (c s) ((0:ℝ) • Z s)) = c := by
        funext s
        rw [zero_smul, GExp_zero]
      rw [hfun]
      have hae : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Ι (0:ℝ) T →
          (Submission.Length.curveSpeed (I := I) c t) ^ 2 = 1 := by
        filter_upwards with t ht
        rw [Set.uIoc_of_le hT.le] at ht
        rw [hcsp t ⟨ht.1.le, ht.2⟩, one_pow]
      rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const, smul_eq_mul,
        mul_one, sub_zero]
    have hgX0 : gXfun 0 = T ^ 2 / 2 := by
      show T / 2 * Efun 0 = T ^ 2 / 2
      rw [hE0]
      ring
    have h4 : ∀ᶠ σ in nhds (0:ℝ), κ σ ≤ κ 0 := by
      have hκ0 : κ 0 = 0 := by
        show hXfun 0 - gXfun 0 = 0
        rw [hX0, hgX0]; ring
      filter_upwards [hcomp] with σ hσ
      rw [hκ0]
      show hXfun σ - gXfun σ ≤ 0
      linarith
    have hκ2 : HasDerivAt (deriv κ)
        ((fderiv ℝ (fderiv ℝ F) ((Work.OddBound.piExtChart (I := I) x) w))
          ((fderiv ℝ φ 0) X) ((fderiv ℝ φ 0) X)
          - T * (∫ t in (0:ℝ)..T, Submission.IndexIntrinsic.idxAlong (cov := cov) c Z
              (Submission.JacobiGlobal.covAlong cov Z) t)) 0 := by
      show HasDerivAt (deriv (fun σ : ℝ => hXfun σ - gXfun σ)) _ 0
      have hev : deriv (fun σ : ℝ => hXfun σ - gXfun σ) =ᶠ[nhds (0:ℝ)]
          (deriv hXfun - deriv gXfun) := by
        filter_upwards [hhX_diffe, hgX_diffe] with σ h1 h2
        exact deriv_sub h1 h2
      exact (hderivX.sub hderivG).congr_of_eventuallyEq hev
    have hle : (fderiv ℝ (fderiv ℝ F) ((Work.OddBound.piExtChart (I := I) x) w))
        ((fderiv ℝ φ 0) X) ((fderiv ℝ φ 0) X) < 0 := by
      have hnp := second_deriv_nonpos_of_eventually_le (f := κ) (c := (fderiv ℝ (fderiv ℝ F)
        ((Work.OddBound.piExtChart (I := I) x) w)) ((fderiv ℝ φ 0) X) ((fderiv ℝ φ 0) X)
          - T * (∫ t in (0:ℝ)..T, Submission.IndexIntrinsic.idxAlong (cov := cov) c Z
              (Submission.JacobiGlobal.covAlong cov Z) t)) hκ1 hκ2 hκ3 h4
      have hTpos : (0:ℝ) < T := hT
      nlinarith [hnp, mul_neg_of_pos_of_neg hTpos hIval]
    exact hle
  -- ### conclusion
  refine Work.OddBound.hasNegDefPlane_of_chart (H' := (Fin (N - 1)) → E)
    (P := Fin (N - 1) → M) (f := Work.OddBound.gonEnergy (I := I) p) (z := w)
    (e := Work.OddBound.piExtChart (I := I) x)
    (v := (fderiv ℝ φ 0) ((1 : ℝ), (0 : ℝ)))
    (w := (fderiv ℝ φ 0) ((0 : ℝ), (1 : ℝ))) he hwsrc ?_
  intro a b hab
  have hsum : a • (fderiv ℝ φ 0) ((1:ℝ), (0:ℝ)) + b • (fderiv ℝ φ 0) ((0:ℝ), (1:ℝ))
      = (fderiv ℝ φ 0) (a, b) := by
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    ext <;> simp
  rw [hsum]
  simpa only [hFdef] using key (a, b) hab

end Work.OddBound.indexTransfer
