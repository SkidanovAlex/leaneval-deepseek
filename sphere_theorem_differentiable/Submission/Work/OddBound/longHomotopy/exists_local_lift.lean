import Mathlib
import Submission.Work.OddBound.LiftKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.OddBound.longHomotopy

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open LeanEval.Geometry.SphereTheorem Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length Submission.InjRadius

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]

/-! ## The local lift of a curve under the exponential map

Given a `C¹` curve `h : [0,S] → M` and a vector `v ∈ T_pM` of norm `< π/√K` whose exponential
image is `h t`, the curve has a *local lift* to the tangent space at `p` near `t`: a continuous
`W` on some `[t,t'] ⊆ [0,S]` with `GExp p (W s) = h s`, `W t = v`, and the radial estimate
`‖W s‖ ≤ ‖v‖ + length h t s`.

The proof is the inverse function theorem: below the conjugate radius `π/√K` the differential of
`GExp p` is invertible (`Submission.ConjCut`), so `GExp p` — written as a map on the model space
`E` — is a *local diffeomorphism* at `v` (`Submission.XuLift.isLocalDiffeomorphAt_GExp`).  Its
local inverse `Ψ` is then composed with `h`, which is legitimate on a (right-)neighbourhood of `t`
because `h` is continuous there.  The radial estimate is the hypothesis `hD2`.  -/

/-- **The inverse tangent-bundle trivialisation at its base point is the canonical identification**
`E → T_pM`.  (`frameVector` with equal base point and evaluation point, cf.
`Submission.Geodesic.frameVector`, is the defeq inclusion.) -/
private lemma symmL_trivializationAt_self {p : M} (u : E) :
    (trivializationAt E (TangentSpace I) p).symmL ℝ p u = (show TangentSpace I p from u) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (𝕜 := ℝ) (b₀ := p) (b := p)
    (mem_chart_source H p)]
  exact tangentCoordChange_self (I := I) (x := p) (z := p) (v := u)
    (mem_extChartAt_source (I := I) p)

/-- **`C¹`-smoothness transfers from the model space `E` to the tangent space at `p`.**

The tangent-bundle trivialisation at its own base point is a continuous linear map `E → T_pM`
raising the model-space smoothness of an `E`-valued function to the fibre-level smoothness needed
by the `T_pM`-valued statements (`hD2`, `ContDiffOn ℝ 1 ·`). -/
private lemma contDiffOn_tangentSpace {p : M} {F : ℝ → E} {s : Set ℝ}
    (hF : ContDiffOn ℝ 1 F s) :
    ContDiffOn ℝ 1 (fun x : ℝ => (show TangentSpace I p from F x)) s := by
  have hcm : ContDiff ℝ 1
      (fun u : E => (trivializationAt E (TangentSpace I) p).symmL ℝ p u) :=
    ContinuousLinearMap.contDiff ((trivializationAt E (TangentSpace I) p).symmL ℝ p)
  have h1 : ContDiffOn ℝ 1
      (fun x : ℝ => (trivializationAt E (TangentSpace I) p).symmL ℝ p (F x)) s :=
    hcm.comp_contDiffOn hF
  refine h1.congr (fun x _ => ?_)
  show (show TangentSpace I p from F x)
    = (trivializationAt E (TangentSpace I) p).symmL ℝ p (F x)
  rw [symmL_trivializationAt_self (I := I) (p := p) (u := F x)]

/-- **The length of a curve depends only on its germ.** -/
private lemma curveLength_congr_of_eventuallyEq {u v : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (huv : ∀ t ∈ Set.Ioo a b, u =ᶠ[𝓝 t] v) :
    curveLength (I := I) u a b = curveLength (I := I) v a b := by
  rw [Submission.Length.curveLength_def, Submission.Length.curveLength_def]
  refine intervalIntegral.integral_congr_Ioo_of_le hab (fun t ht => ?_)
  exact Submission.GeodesicSpeed.curveSpeed_congr_of_eventuallyEq (I := I) (huv t ht)

/-- **The differential of `GExp p` is invertible at every vector of norm `< π/√K`.**

For a non-zero vector this is Rauch's conjugate-radius bound (`Submission.ConjCut`); at the origin
it is `d GExp_0 = id` (`Submission.GExpLocalInj.mfderiv_GExp_zero`). -/
private lemma isInvertible_mfderiv_GExp_of_norm_lt
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {K : ℝ} (hK : 0 < K) (hcurv : Submission.RauchK.CurvLe cov K)
    {p : M} {v : TangentSpace I p} (hv : ‖v‖ < Real.pi / Real.sqrt K) :
    (mfderiv 𝓘(ℝ, E) I
      (fun u : E => GExp (cov := cov) hmet p (show TangentSpace I p from u))
      (show E from v)).IsInvertible := by
  rcases eq_or_ne v 0 with hv0 | hv0
  · subst hv0
    change (mfderiv 𝓘(ℝ, E) I
      (fun u : E => GExp (cov := cov) hmet p (show TangentSpace I p from u))
      (0 : E)).IsInvertible
    rw [Submission.GExpLocalInj.mfderiv_GExp_zero (cov := cov) hmet p]
    exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩
  · exact Submission.ConjCut.isInvertible_mfderiv_GExp_of_norm_lt_pi_div_sqrt
      (cov := cov) hmet htor hcurv hK hv0 hv

theorem exists_local_lift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {K : ℝ} (hK : 0 < K) (hcurv : Submission.RauchK.CurvLe cov K)
    {p : M} {h : ℝ → M} {S t : ℝ} (hS : 0 < S)
    (hc : ContMDiffOn 𝓘(ℝ) I 1 h (Set.Icc (0 : ℝ) S)) (h0 : h 0 = p)
    (ht : t ∈ Set.Icc (0 : ℝ) S) (htS : t < S)
    {v : TangentSpace I p} (hv : ‖v‖ < Real.pi / Real.sqrt K)
    (hvt : GExp (cov := cov) hmet p v = h t)
    (hGauss : ∀ (v η : TangentSpace I p) (u : ℝ),
      Inner.inner ℝ
        (curveVelocity (I := I) (fun r : ℝ => GExp (cov := cov) hmet p (u • (v + r • η))) 0)
        (curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • v)) u)
        = u * Inner.inner ℝ η v)
    (hD2 : ∀ {W : ℝ → TangentSpace I p} {a b : ℝ}, a ≤ b → ContDiffOn ℝ 1 W (Set.Icc a b) →
      ‖W b‖ ≤ ‖W a‖ + curveLength (I := I)
        (fun s : ℝ => GExp (cov := cov) hmet p (W s)) a b) :
    ∃ t' : ℝ, t < t' ∧ t' ≤ S ∧ ∃ W : ℝ → TangentSpace I p,
      ContinuousOn W (Set.Icc t t') ∧ W t = v ∧
      (∀ s ∈ Set.Icc t t', GExp (cov := cov) hmet p (W s) = h s) ∧
      (∀ s ∈ Set.Icc t t', ‖W s‖ ≤ ‖v‖ + curveLength (I := I) h t s) := by
  classical
  -- ## Step 1: the differential of the exponential map at `v` is invertible, and `GExp p` is a
  -- local diffeomorphism there
  have hinv := isInvertible_mfderiv_GExp_of_norm_lt (cov := cov) hmet htor hK hcurv
    (p := p) (v := v) hv
  have hf : IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞
      (Submission.XuLift.gexpMap (cov := cov) hmet p) (show E from v) :=
    Submission.XuLift.isLocalDiffeomorphAt_GExp (cov := cov) hmet p hinv
  -- ## Step 2: `h t` lies in the source of the local inverse
  have hsrc : h t ∈ hf.localInverse.source := by
    rw [← hvt]
    exact hf.localInverse_mem_source
  -- ## Step 3: a right-neighbourhood of `t` on which `h` stays in the source
  have hmem : {s : ℝ | h s ∈ hf.localInverse.source} ∈ 𝓝[Set.Icc (0 : ℝ) S] t :=
    (hc.continuousOn.continuousWithinAt ht).preimage_mem_nhdsWithin
      (hf.localInverse.open_source.mem_nhds hsrc)
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhdsWithin_iff.mp hmem
  set t' : ℝ := min (t + ε / 2) ((t + S) / 2) with ht'def
  have htt' : t < t' := by
    rw [ht'def]; exact lt_min (by linarith) (by linarith)
  have ht'S : t' ≤ S := by
    rw [ht'def]; exact le_trans (min_le_right _ _) (by linarith)
  have hsub : ∀ s ∈ Set.Icc t t', h s ∈ hf.localInverse.source := by
    intro s hs
    refine hεsub ⟨?_, ?_⟩
    · rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hs.1, hεpos], by
        have h2 : t' ≤ t + ε / 2 := by rw [ht'def]; exact min_le_left _ _
        linarith [hs.2, h2, hεpos]⟩
    · exact ⟨le_trans ht.1 hs.1, le_trans hs.2 ht'S⟩
  -- ## Step 4: the lift
  let W : ℝ → TangentSpace I p := fun s => (show TangentSpace I p from hf.localInverse (h s))
  have hWt : W t = v := by
    show (show TangentSpace I p from hf.localInverse (h t)) = v
    rw [← hvt]
    exact congrArg (fun u : E => (show TangentSpace I p from u))
      (hf.localInverse_left_inv (x' := (show E from v)) hf.localInverse_mem_target)
  have hWG : ∀ s ∈ Set.Icc t t', GExp (cov := cov) hmet p (W s) = h s := by
    intro s hs
    exact hf.localInverse_right_inv (hsub s hs)
  have hWc : ContinuousOn W (Set.Icc t t') := by
    have hcontΨ : ContinuousOn (fun y : M => hf.localInverse y) hf.localInverse.source :=
      hf.localInverse_contMDiffOn.continuousOn
    have h1 : ContinuousOn (fun s : ℝ => hf.localInverse (h s)) (Set.Icc t t') :=
      hcontΨ.comp (hc.continuousOn.mono (fun u hu => ⟨le_trans ht.1 hu.1, le_trans hu.2 ht'S⟩))
        (fun u hu => hsub u hu)
    exact h1
  have hWcd : ContDiffOn ℝ 1 W (Set.Icc t t') := by
    have hΨ1 : ContMDiffOn I 𝓘(ℝ, E) 1 (fun y : M => hf.localInverse y)
        hf.localInverse.source :=
      hf.localInverse_contMDiffOn.of_le
        (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) from WithTop.coe_le_coe.mpr le_top)
    have hhc : ContMDiffOn 𝓘(ℝ) I 1 h (Set.Icc t t') :=
      hc.mono (fun u hu => ⟨le_trans ht.1 hu.1, le_trans hu.2 ht'S⟩)
    have hcomp : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1 (fun u : ℝ => hf.localInverse (h u))
        (Set.Icc t t') :=
      hΨ1.comp hhc (fun u hu => hsub u hu)
    have hcd : ContDiffOn ℝ 1 (fun u : ℝ => hf.localInverse (h u)) (Set.Icc t t') :=
      hcomp.contDiffOn
    exact contDiffOn_tangentSpace (p := p) hcd
  refine ⟨t', htt', ht'S, W, hWc, hWt, hWG, ?_⟩
  -- ## Step 5: the radial estimate
  intro s hs
  have hts : t ≤ s := hs.1
  have hWcd' : ContDiffOn ℝ 1 W (Set.Icc t s) :=
    hWcd.mono (Set.Icc_subset_Icc_right hs.2)
  have hb := hD2 hts hWcd'
  have hlen : curveLength (I := I)
      (fun u : ℝ => GExp (cov := cov) hmet p (W u)) t s = curveLength (I := I) h t s := by
    refine curveLength_congr_of_eventuallyEq hts (fun u hu => ?_)
    have hmem' : Set.Ioo t t' ∈ 𝓝 u :=
      isOpen_Ioo.mem_nhds ⟨hu.1, lt_of_lt_of_le hu.2 hs.2⟩
    filter_upwards [hmem'] with u' hu''
    exact hWG u' ⟨hu''.1.le, hu''.2.le⟩
  rw [hlen, hWt] at hb
  exact hb

end Work.OddBound.longHomotopy
