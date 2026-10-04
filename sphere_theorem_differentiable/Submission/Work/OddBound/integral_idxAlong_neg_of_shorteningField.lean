import Mathlib
import Submission.Work.OddBound.Defs
import Submission.Work.OddBound.continuousOn_idxAlong_of_smoothOn
import Submission.Work.OddBound.continuousOn_normSq_covAlong_of_smoothOn

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.OddBound

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length
open Submission.InjRadius Submission.IndexIntrinsic Submission.CurvatureVec

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The pointwise inequality behind the negativity of the index integral.**  For a unit-speed
curve `γ` (`curveSpeed γ t = 1` on `[0,L]`), a unit normal field `V` along `γ` and a lower bound `δ`
for the sectional curvature in the planes spanned by `V t` and `γ'(t)`, one has

`idxAlong γ V (∇V) t = ‖∇V t‖² - ⟪R(V,γ')γ',V⟫ ≤ ‖∇V t‖² - δ`.

Indeed `V t` and `γ'(t)` are both unit and orthogonal, so the curvature pairing is `≥ δ` by
hypothesis. -/
lemma idxAlong_le_normSq_sub
    {γ : ℝ → M} {V : (t : ℝ) → TangentSpace I (γ t)} {L δ : ℝ}
    (hspeed : ∀ t ∈ Icc (0 : ℝ) L, curveSpeed (I := I) γ t = 1)
    (hV : IsUnitNormalField (I := I) γ L V)
    (hcurv : ∀ t ∈ Icc (0 : ℝ) L, ∀ u v : TangentSpace I (γ t), ‖u‖ = 1 → ‖v‖ = 1 →
      inner ℝ u v = 0 → δ ≤ inner ℝ (curvVec cov (γ t) u v v) u) :
    ∀ t ∈ Icc (0 : ℝ) L,
      idxAlong (cov := cov) γ V (covAlong cov V) t ≤ ‖covAlong cov V t‖ ^ 2 - δ := by
  intro t ht
  obtain ⟨hVn, hVo⟩ := hV t ht
  have hv1 : ‖curveVelocity (I := I) γ t‖ = 1 := by
    rw [← Submission.GeodesicSpeed.curveSpeed_eq_norm]
    exact hspeed t ht
  have hc := hcurv t ht (V t) (curveVelocity (I := I) γ t) hVn hv1 hVo
  rw [idxAlong, real_inner_self_eq_norm_sq]
  linarith

/-- **The index integral of a shortening field is negative.**  `γ` is a **unit-speed** closed
geodesic of length `L` with sectional curvature `≥ δ` on `[0,L]`; `V` is a shortening field
(`‖V t‖ = 1`, `V t ⊥ γ'(t)`, `∫₀^L ‖∇V‖² < δ L`).  Pointwise,
`idxAlong γ V (∇V) t = ‖∇V t‖² - ⟪R(V,γ')γ',V⟫ ≤ ‖∇V t‖² - δ`
(because `V`, `γ'` are unit and orthogonal, so `⟪R(V,γ')γ',V⟫ = sec(V,γ') ≥ δ`); integrating and
using `hV.smallDeriv` gives `∫₀^L idxAlong < 0`.
The unit-speed hypothesis is essential: the curvature term scales by `‖γ'‖²`.
This is the second-variation input of the odd-dimensional Klingenberg argument. -/
theorem integral_idxAlong_neg_of_shorteningField
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} {L δ : ℝ} (hL : 0 < L)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (-1) (L + 1)))
    (hne : ∀ t ∈ Ioo (-1) (L + 1), curveVelocity (I := I) γ t ≠ 0)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) L, curveSpeed (I := I) γ t = 1)
    (hδ : 0 < δ) (hV : IsShorteningField cov γ L δ)
    (hcurv : ∀ t ∈ Icc (0 : ℝ) L, ∀ u v : TangentSpace I (γ t), ‖u‖ = 1 → ‖v‖ = 1 →
      inner ℝ u v = 0 → δ ≤ inner ℝ (curvVec cov (γ t) u v v) u) :
    ∫ t in (0 : ℝ)..L, idxAlong (cov := cov) γ hV.field (covAlong cov hV.field) t < 0 := by
  -- the hypothesis is stated on the window `Ioo (-1) (L+1)`; the field lemmas want `Ioo (0-1) (L+1)`
  have hγ' : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo ((0 : ℝ) - 1) (L + 1)) := by
    simpa only [zero_sub] using hγ
  have hne' : ∀ t ∈ Ioo ((0 : ℝ) - 1) (L + 1), curveVelocity (I := I) γ t ≠ 0 := by
    intro t ht
    exact hne t (by simpa only [zero_sub] using ht)
  -- the shortening field is smooth along `γ` on `Icc 0 L`
  have hsm : ∀ t ∈ Icc (0 : ℝ) L, SmoothAlongAt (I := I) γ hV.field t :=
    fun t ht => hV.smooth t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- continuity of the two integrands on `[0,L]`
  have hcont : ContinuousOn (fun t => idxAlong (cov := cov) γ hV.field (covAlong cov hV.field) t)
      (Icc (0 : ℝ) L) :=
    continuousOn_idxAlong_of_smoothOn (cov := cov) htor hL.le hγ' hne' hsm
  have hcontZ : ContinuousOn (fun t => ‖covAlong cov hV.field t‖ ^ 2) (Icc (0 : ℝ) L) :=
    continuousOn_normSq_covAlong_of_smoothOn (cov := cov) htor hL.le hγ' hne' hsm
  have hint : IntervalIntegrable
      (fun t => idxAlong (cov := cov) γ hV.field (covAlong cov hV.field) t) volume (0 : ℝ) L :=
    hcont.intervalIntegrable_of_Icc hL.le
  have hintZ : IntervalIntegrable (fun t => ‖covAlong cov hV.field t‖ ^ 2) volume (0 : ℝ) L :=
    hcontZ.intervalIntegrable_of_Icc hL.le
  have hint2 : IntervalIntegrable (fun t => ‖covAlong cov hV.field t‖ ^ 2 - δ) volume (0 : ℝ) L :=
    hintZ.sub intervalIntegrable_const
  -- the pointwise bound
  have hpoint := idxAlong_le_normSq_sub (cov := cov) (V := hV.field) (L := L) (δ := δ) hspeed
    hV.unitNormal hcurv
  -- replace the integrand by a function that is dominated *everywhere* by `‖∇V‖² - δ`
  set F : ℝ → ℝ := fun t => if t ∈ Icc (0 : ℝ) L
    then idxAlong (cov := cov) γ hV.field (covAlong cov hV.field) t
    else ‖covAlong cov hV.field t‖ ^ 2 - δ with hFdef
  have hFcont : ContinuousOn F (Icc (0 : ℝ) L) :=
    hcont.congr (fun t ht => by simp only [hFdef, ht, if_true])
  have hFint : IntervalIntegrable F volume (0 : ℝ) L := hFcont.intervalIntegrable_of_Icc hL.le
  have hFle : F ≤ fun t => ‖covAlong cov hV.field t‖ ^ 2 - δ := by
    intro t
    by_cases ht : t ∈ Icc (0 : ℝ) L
    · simp only [hFdef, ht, if_true]
      exact hpoint t ht
    · simp only [hFdef, ht, if_false]
      exact le_rfl
  have hle := intervalIntegral.integral_mono hL.le hFint hint2 hFle
  have hcongr : (∫ t in (0 : ℝ)..L, F t)
      = ∫ t in (0 : ℝ)..L, idxAlong (cov := cov) γ hV.field (covAlong cov hV.field) t := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le hL.le] at ht
    simp only [hFdef, ht, if_true]
  rw [hcongr] at hle
  have hval : (∫ t in (0 : ℝ)..L, (‖covAlong cov hV.field t‖ ^ 2 - δ))
      = (∫ t in (0 : ℝ)..L, ‖covAlong cov hV.field t‖ ^ 2) - δ * L := by
    rw [intervalIntegral.integral_sub hintZ intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  rw [hval] at hle
  have hsmall : (∫ t in (0 : ℝ)..L, ‖covAlong cov hV.field t‖ ^ 2) < δ * L := hV.smallDeriv
  linarith [hsmall]

end Work.OddBound
