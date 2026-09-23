import Submission.GeodesicSpeed
import Submission.LensLoop
import Submission.GExpVelocity

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GeodesicSpeed
open Submission.GlobalExp
open Submission.Length

namespace Submission.BrokenLength

noncomputable section

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

/-! ## 1. The length of a curve of constant speed -/

/-- **The length of a curve of constant speed.**  If the speed of `γ` is constantly `c` on `[a,b]`,
then `curveLength γ a b = c (b - a)`.  This is the computation that makes the length of a *broken*
curve (and hence the shortening step) explicit. -/
theorem curveLength_eq_mul_of_curveSpeed_eq {γ : ℝ → M} {a b c : ℝ} (hab : a ≤ b)
    (hspeed : ∀ t ∈ Icc a b, curveSpeed (I := I) γ t = c) :
    curveLength (I := I) γ a b = c * (b - a) := by
  rw [curveLength_def]
  rw [intervalIntegral.integral_congr
    (fun t ht => hspeed t (by rwa [uIcc_of_le hab] at ht))]
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]

/-- **The length of a unit-speed curve** is the elapsed time. -/
theorem curveLength_eq_sub_of_curveSpeed_eq_one {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hspeed : ∀ t ∈ Icc a b, curveSpeed (I := I) γ t = 1) :
    curveLength (I := I) γ a b = b - a := by
  rw [curveLength_eq_mul_of_curveSpeed_eq hab hspeed, one_mul]

/-! ## 2. The length of a broken curve -/

/-- **The length of a broken curve.**  If `γ` has constant speed `c₁` on `[a,m]` and constant speed
`c₂` on `[m,b]` (the two sides of the corner at time `m`), then its length is the sum of the two
pieces, `c₁ (m - a) + c₂ (b - m)`. -/
theorem curveLength_broken {γ : ℝ → M} {a m b c₁ c₂ : ℝ} (ham : a ≤ m) (hmb : m ≤ b)
    (h₁ : ∀ t ∈ Icc a m, curveSpeed (I := I) γ t = c₁)
    (h₂ : ∀ t ∈ Icc m b, curveSpeed (I := I) γ t = c₂)
    (hint₁ : IntervalIntegrable (curveSpeed (I := I) γ) MeasureTheory.volume a m)
    (hint₂ : IntervalIntegrable (curveSpeed (I := I) γ) MeasureTheory.volume m b) :
    curveLength (I := I) γ a b = c₁ * (m - a) + c₂ * (b - m) := by
  rw [← curveLength_add_of_integrable γ hint₁ hint₂,
    curveLength_eq_mul_of_curveSpeed_eq ham h₁, curveLength_eq_mul_of_curveSpeed_eq hmb h₂]

/-- **The length of a broken unit-speed curve** — e.g. of a closed loop made of two unit-speed
geodesic arcs — is the total elapsed time `b - a`. -/
theorem curveLength_broken_of_unit {γ : ℝ → M} {a m b : ℝ} (ham : a ≤ m) (hmb : m ≤ b)
    (h₁ : ∀ t ∈ Icc a m, curveSpeed (I := I) γ t = 1)
    (h₂ : ∀ t ∈ Icc m b, curveSpeed (I := I) γ t = 1)
    (hint₁ : IntervalIntegrable (curveSpeed (I := I) γ) MeasureTheory.volume a m)
    (hint₂ : IntervalIntegrable (curveSpeed (I := I) γ) MeasureTheory.volume m b) :
    curveLength (I := I) γ a b = b - a := by
  rw [curveLength_broken ham hmb h₁ h₂ hint₁ hint₂]
  ring

/-! ## 3. The length of the `GExp`-rays (the pieces of the broken loop) -/

/-- **The speed of a `GExp`-ray is the norm of its direction** (at every time, including `0`). -/
theorem curveSpeed_GExp_ray (hmet : IsMetricCompatible cov) (p : M)
    {ξ : TangentSpace I p} (hξ : ξ ≠ 0) (t : ℝ) :
    curveSpeed (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) t = ‖ξ‖ := by
  rw [curveSpeed_eq_norm]
  rcases eq_or_ne t 0 with h0 | h0
  · subst h0
    have hpt : GExp (cov := cov) hmet p ((0 : ℝ) • ξ) = p := by
      rw [zero_smul, GExp_zero]
    rw [Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet p hξ, hpt]
  · exact Submission.LensLoop.norm_curveVelocity_GExp_smul_ne (cov := cov) hmet p hξ h0

/-- **The length of a `GExp`-ray** over `[a,b]` is `‖ξ‖ (b - a)`. -/
theorem curveLength_GExp_ray (hmet : IsMetricCompatible cov) (p : M) {ξ : TangentSpace I p}
    (hξ : ξ ≠ 0) {a b : ℝ} (hab : a ≤ b) :
    curveLength (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) a b = ‖ξ‖ * (b - a) :=
  curveLength_eq_mul_of_curveSpeed_eq hab
    (fun t _ => curveSpeed_GExp_ray (cov := cov) hmet p hξ t)

/-- **The length of a unit-speed `GExp`-ray** over `[a,b]` is `b - a`. -/
theorem curveLength_GExp_ray_of_norm_one (hmet : IsMetricCompatible cov) (p : M)
    {ξ : TangentSpace I p} (hξ1 : ‖ξ‖ = 1) {a b : ℝ} (hab : a ≤ b) :
    curveLength (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) a b = b - a := by
  have hξ0 : ξ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hξ1
    norm_num at hξ1
  rw [curveLength_eq_mul_of_curveSpeed_eq hab
      (fun t _ => curveSpeed_GExp_ray (cov := cov) hmet p hξ0 t), hξ1, one_mul]

end

end Submission.BrokenLength
