import Mathlib
import Submission.Work.RiemLib.RauchK
import Submission.Work.RiemLib.Geodesic
import Submission.Work.RiemLib.GeodesicSpeed
import Submission.Work.RiemLib.Length
import Submission.Work.RiemLib.Distance
import Submission.Work.RiemLib.InjRadius
import Submission.Work.RiemLib.InjBall
import Submission.Work.RiemLib.SegmentDomain
import Submission.Work.RiemLib.XuMain
import Submission.Work.RiemLib.EDist
import Submission.Work.RiemLib.GExpRay2
import Submission.Work.RiemLib.GExpJoint
import Submission.Work.RiemLib.GExpFlow
import Submission.Work.RiemLib.Commons.Geometry.Manifold.exists_finite_cover_isCompact_subset_chartAt
import Submission.Work.RiemLib.GeodesicGlobal
import Submission.Work.RiemLib.GExpLocalInj
import Submission.Work.RiemLib.CutStep2
import Submission.Work.RiemLib.XuLift
import Submission.Work.RiemLib.ChartPieces
import Submission.Work.RiemLib.ChartIndep
import Submission.Work.RiemLib.CoeffSmooth2
import Submission.Work.RiemLib.JacobiGlobal
import Submission.Work.RiemLib.Commons.Analysis.ODE.exists_linearODE_solution_Icc
import Submission.Work.RiemLib.IndexCorner2
import Submission.Work.RiemLib.InjHalf
import Submission.Work.RiemLib.LensLoop
import Submission.Work.RiemLib.UniformInj
import Submission.Work.RiemLib.ConjRadius
import Submission.Work.RiemLib.ConjCut
import Submission.Work.RiemLib.SingularConj
import Submission.Work.RiemLib.RayConj
import Submission.Work.RiemLib.Gauss
import Submission.Work.RiemLib.ExpBound2
import Submission.Work.RiemLib.JacobiGauss
import Submission.Work.RiemLib.Minimal
import Submission.Work.RiemLib.Work.Lift.eqOn_of_locallyInjective_of_comp_eq
import Submission.Work.RiemLib.Work.GeodesicConstSpeed.curveVelocity_ne_zero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.style.haveILetI false

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
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]

/-! ## Local injectivity of the exponential map

Two inputs from the main tree: `GExp p` is a local diffeomorphism at `0` (its differential there is
the identity), and — under `sec ≤ K` — at every non-zero vector of norm `< π/√K` (Rauch). -/

/-- **`GExp p` is locally injective at the origin.**  The differential of `GExp p` at `0` is the
identity (`Submission.GExpLocalInj.mfderiv_GExp_zero`), so the inverse function theorem in the form
`locallyInjectiveAtGExp_of_injective_mfderiv` applies. -/
lemma locallyInjectiveAtGExp_zero
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (p : M) :
    Submission.CutStep2.LocallyInjectiveAtGExp (I := I) hmet p 0 := by
  refine Submission.GExpLocalInj.locallyInjectiveAtGExp_of_injective_mfderiv (cov := cov) hmet ?_
  intro a b hab
  have h0 := Submission.GExpLocalInj.mfderiv_GExp_zero (cov := cov) hmet p
  have hab' : (mfderiv 𝓘(ℝ, E) I (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet p
        (show TangentSpace I p from w)) (0 : E)) a
      = (mfderiv 𝓘(ℝ, E) I (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet p
        (show TangentSpace I p from w)) (0 : E)) b := hab
  rw [h0] at hab'
  exact hab'

/-- **`GExp p` is locally injective at every vector of norm `< π/√K`**, the origin included: at a
non-zero vector this is `Submission.RayConj.locallyInjectiveAtGExp_of_norm_lt_pi_div_sqrt`. -/
lemma locallyInjectiveAtGExp_of_norm_lt_pi_div_sqrt'
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {K : ℝ} (hK : 0 < K) (hcurv : Submission.RauchK.CurvLe cov K)
    {p : M} {w : TangentSpace I p} (hw : ‖w‖ < Real.pi / Real.sqrt K) :
    Submission.CutStep2.LocallyInjectiveAtGExp (I := I) hmet p w := by
  by_cases hw0 : w = 0
  · subst hw0
    exact locallyInjectiveAtGExp_zero (cov := cov) hmet p
  · exact Submission.RayConj.locallyInjectiveAtGExp_of_norm_lt_pi_div_sqrt (cov := cov) hmet htor
      hcurv hK hw0 hw

/-! ## Geodesics with vanishing velocity

A geodesic whose velocity vanishes at one interior point is constant on the interval: the velocity
vanishes everywhere (`Work.GeodesicConstSpeed.curveVelocity_ne_zero`), so the extended length
`pathELength` of the curve between any two of its points is `0`, and `riemannianEDist` — which is
bounded by `pathELength` — vanishes, forcing the two points to coincide. -/

/-- **A geodesic whose velocity vanishes at an interior point is constant on the interval.** -/
private lemma isConst_of_curveVelocity_eq_zero_aux
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) [RegularSpace M]
    {a b : ℝ} (ha : a < 0) (hb : 0 < b) {γ : ℝ → M}
    (hsm : ContMDiffOn 𝓘(ℝ) I ∞ γ (Set.Ioo a b))
    (hgeo : ∀ t ∈ Set.Ioo a b, Submission.Geodesic.IsGeodesicAt cov γ t)
    (h0 : Submission.Geodesic.curveVelocity (I := I) γ 0 = 0) :
    ∀ t ∈ Set.Ioo a b, γ t = γ 0 := by
  have hcont : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_of_contMDiffRiemannianBundle (I := I) (n := ∞)
  haveI : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) := hcont
  have hvel : ∀ t ∈ Set.Ioo a b, Submission.Geodesic.curveVelocity (I := I) γ t = 0 := by
    intro t ht
    by_contra hne
    exact (Work.GeodesicConstSpeed.curveVelocity_ne_zero (cov := cov) hmet (a := a) (b := b)
      hsm hgeo ht hne 0 ⟨ha, hb⟩) h0
  intro s hs
  rcases le_total 0 s with h0s | hs0
  · have hsub : Set.Icc 0 s ⊆ Set.Ioo a b :=
      fun t ht => ⟨by linarith [hs.1, ht.1], by linarith [hs.2, ht.2]⟩
    have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc 0 s) :=
      (hsm.mono hsub).of_le (WithTop.coe_le_coe.mpr le_top)
    have hle := Manifold.riemannianEDist_le_pathELength (I := I) (x := γ 0) (y := γ s)
      (a := 0) (b := s) hγ rfl rfl h0s
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc] at hle
    have hzero : (∫⁻ t in Set.Icc (0 : ℝ) s, ‖(mfderiv% γ t) (1 : ℝ)‖ₑ) = 0 := by
      rw [lintegral_eq_zero_of_ae_eq_zero]
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have h1 : (mfderiv% γ t) (1 : ℝ) = 0 := hvel t (hsub ht)
      rw [h1]
      simp
    have hdist : Manifold.riemannianEDist I (γ 0) (γ s) = 0 :=
      le_antisymm (hzero ▸ hle) zero_le
    exact ((Submission.EDist.riemannianEDist_eq_zero_iff (I := I)).mp hdist).symm
  · have hsub : Set.Icc s 0 ⊆ Set.Ioo a b :=
      fun t ht => ⟨by linarith [hs.1, ht.1], by linarith [hs.2, ht.2]⟩
    have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc s 0) :=
      (hsm.mono hsub).of_le (WithTop.coe_le_coe.mpr le_top)
    have hle := Manifold.riemannianEDist_le_pathELength (I := I) (x := γ s) (y := γ 0)
      (a := s) (b := 0) hγ rfl rfl hs0
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc] at hle
    have hzero : (∫⁻ t in Set.Icc s (0 : ℝ), ‖(mfderiv% γ t) (1 : ℝ)‖ₑ) = 0 := by
      rw [lintegral_eq_zero_of_ae_eq_zero]
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have h1 : (mfderiv% γ t) (1 : ℝ) = 0 := hvel t (hsub ht)
      rw [h1]
      simp
    have hdist : Manifold.riemannianEDist I (γ s) (γ 0) = 0 :=
      le_antisymm (hzero ▸ hle) zero_le
    exact (Submission.EDist.riemannianEDist_eq_zero_iff (I := I)).mp hdist

theorem lift_of_geodesic_ray
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {K : ℝ} (hK : 0 < K) (hcurv : Submission.RauchK.CurvLe cov K)
    {p : M} {h : ℝ → M} {S : ℝ} (hS : 0 ≤ S)
    (hgeo : ∀ t : ℝ, Submission.Geodesic.IsGeodesicAt (I := I) cov h t)
    (hhsm : ContMDiff 𝓘(ℝ) I ∞ h) (h0 : h 0 = p)
    {W : ℝ → TangentSpace I p} (hWc : ContinuousOn W (Set.Icc 0 S)) (hW0 : W 0 = 0)
    (hWG : ∀ s ∈ Set.Icc (0 : ℝ) S, Submission.GlobalExp.GExp (cov := cov) hmet p (W s) = h s)
    (hb : ∀ s ∈ Set.Icc (0 : ℝ) S, ‖W s‖ < Real.pi / Real.sqrt K) :
    ∀ s ∈ Set.Icc (0 : ℝ) S, W s = s • Submission.Geodesic.curveVelocity (I := I) h 0 := by
  classical
  set v : TangentSpace I p := Submission.Geodesic.curveVelocity (I := I) h 0 with hv
  -- Step 1: the geodesic `h` is the `GExp`-ray of its initial velocity.
  have hray : ∀ s ∈ Set.Icc (0 : ℝ) S,
      Submission.GlobalExp.GExp (cov := cov) hmet p (s • v) = h s := by
    intro s hs
    by_cases hv0 : v = 0
    · -- the velocity vanishes at `0`, so `h` is constantly `p`
      have hconst := isConst_of_curveVelocity_eq_zero_aux (cov := cov) hmet
        (a := -1) (b := S + 1) (by norm_num) (by linarith) hhsm.contMDiffOn
        (fun t _ => hgeo t) (by rw [← hv]; exact hv0)
      rw [hv0, smul_zero, Submission.GlobalExp.GExp_zero]
      exact ((hconst s ⟨by linarith [hs.1], by linarith [hs.2]⟩).trans h0).symm
    · -- the velocity is nowhere zero, and the existing ray identification applies
      have hne : ∀ t ∈ Set.Ioo (-1 : ℝ) (S + 1), Submission.Geodesic.curveVelocity (I := I) h t ≠ 0 :=
        Work.GeodesicConstSpeed.curveVelocity_ne_zero (cov := cov) hmet (a := -1) (b := S + 1)
          hhsm.contMDiffOn (fun t _ => hgeo t) ⟨by norm_num, by linarith⟩ hv0
      exact (Submission.GExpRayIdent.eqOn_Icc_GExp_of_isGeodesicAt (cov := cov) hmet hv0
        (a := -1) (b := S + 1) (T := S) (by norm_num) hS (by linarith) hhsm.contMDiffOn
        (fun t _ => hgeo t) hne h0 rfl s hs).symm
  -- Step 2: the two continuous lifts of `h` through `GExp p` agree, by the clopen argument.
  have hu₂ : ContinuousOn (fun s : ℝ => s • v) (Set.Icc 0 S) :=
    (continuous_id.smul continuous_const).continuousOn
  have hmain : ∀ s ∈ Set.Icc (0 : ℝ) S, W s = s • v :=
    Work.Lift.eqOn_of_locallyInjective_of_comp_eq
      (f := fun w : TangentSpace I p => Submission.GlobalExp.GExp (cov := cov) hmet p w)
      (u₁ := W) (u₂ := fun s : ℝ => s • v) (γ := h) hS hWc hu₂
      (fun s hs => hWG s hs) (fun s hs => hray s hs) (by simp [hW0])
      (fun s hs =>
        locallyInjectiveAtGExp_of_norm_lt_pi_div_sqrt' (cov := cov) hmet htor hK hcurv (hb s hs))
  intro s hs
  have hs' := hmain s hs
  rw [hv] at hs'
  exact hs'

end Work.OddBound.longHomotopy
