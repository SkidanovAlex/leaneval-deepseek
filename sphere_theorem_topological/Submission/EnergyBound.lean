import Submission.GlobalBM
import Submission.Commons.Analysis.Calculus.exists_lt_of_deriv_eq_zero_of_hasDerivAt_deriv_neg
import Submission.Commons.Analysis.Calculus.exists_lt_of_hasDerivAt_deriv_neg
import Submission.Minimal
import Submission.GeodesicSpeed
import Submission.Length

/-!
# The energy lower bound, and the shortening lemma

Three lemmas completing the variational machinery of the `σ ≤ κ` argument:

* `edist_le_sqrt_mul_energy`: for a `C¹` curve with continuous speed on `[0,L]`, the distance between
  its endpoints is at most `√(L · ∫‖γ'‖²)` (distance ≤ length ≤ Cauchy–Schwarz).
* `le_energy_of_edist_eq`: if the endpoints are at distance exactly `L`, then **`L ≤ ∫‖γ'‖²`** — the
  quantitative form of "geodesics minimise the energy" (`L = d ≤ √(L E)` gives `L ≤ E`).
* `false_of_deriv_deriv_neg_of_min`: **the shortening lemma** — a function with a global minimum at
  `0` cannot satisfy `f'(0) = 0` and `f''(0) < 0`.

Together with `Submission/SecondVarGeo.energy_first_deriv_chart_eq_zero` (which produces
`HasDerivAt E 0 0`) and `Submission.SecondVarGeo.energy_second_deriv_chart` (which produces
`HasDerivAt (deriv E) c 0` with `c < 0`), these give the contradiction that closes the shortening
argument: a variation by geodesics with fixed endpoints along a minimising geodesic with an interior
conjugate point would give a curve of energy `< L` joining two points at distance `L`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory
open Submission.Length
open Submission.Geodesic

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless]

namespace Submission.EnergyBound

noncomputable section

variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-- **The distance between the endpoints is at most `√(L · energy)`** for any `C¹` curve on `[0,L]`
with continuous speed: this is `d ≤ length ≤ √(L·∫‖γ'‖²)` (the second step is Cauchy–Schwarz). -/
theorem edist_le_sqrt_mul_energy [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov)
    {γ : ℝ → M} {L : ℝ} (hL : 0 < L)
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 γ (Icc 0 L))
    (hspc : ContinuousOn (fun t => curveSpeed (I := I) γ t) (Icc 0 L)) :
    Manifold.riemannianEDist I (γ 0) (γ L)
      ≤ ENNReal.ofReal (Real.sqrt (L * ∫ t in (0 : ℝ)..L, curveSpeed (I := I) γ t ^ 2)) := by
  have h1 : Manifold.riemannianEDist I (γ 0) (γ L) ≤ Manifold.pathELength I γ 0 L :=
    Manifold.riemannianEDist_le_pathELength (x := γ 0) (y := γ L) (a := 0) (b := L)
      (γ := γ) hγ rfl rfl hL.le
  have hlen : Manifold.pathELength I γ 0 L
      = ENNReal.ofReal (∫ t in (0 : ℝ)..L, curveSpeed (I := I) γ t) := by
    refine Commons.Geometry.Manifold.pathELength_eq_ofReal_integral_of_enorm_eq_nonneg (I := I)
      (γ := γ) (a := 0) (b := L) (f := fun t => curveSpeed (I := I) γ t) hL.le
      (hspc.integrableOn_Icc) (fun t _ => curveSpeed_nonneg (I := I) γ t) ?_
    intro t ht
    show ‖curveVelocity (I := I) γ t‖ₑ = ENNReal.ofReal (curveSpeed (I := I) γ t)
    rw [Submission.Minimal.enorm_eq_ofReal_norm,
      Submission.GeodesicSpeed.curveSpeed_eq_norm (I := I) γ t]
  rw [hlen] at h1
  refine h1.trans ?_
  have hint : 0 ≤ ∫ t in (0 : ℝ)..L, curveSpeed (I := I) γ t :=
    intervalIntegral.integral_nonneg hL.le (fun t _ => curveSpeed_nonneg (I := I) γ t)
  rw [ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg (L * ∫ t in (0 : ℝ)..L, curveSpeed (I := I) γ t ^ 2))]
  have hspc' : ContinuousOn (fun t => curveSpeed (I := I) γ t) (uIcc 0 L) := by
    rwa [uIcc_of_le hL.le]
  have hcs := Commons.Analysis.Calculus.sq_intervalIntegral_le_length_mul_intervalIntegral_sq
    (f := fun t => curveSpeed (I := I) γ t) hL.le hspc'
    (fun t _ => curveSpeed_nonneg (I := I) γ t)
  rw [← Real.sqrt_sq hint]
  exact Real.sqrt_le_sqrt (by simpa using hcs)

/-- **The energy of a curve joining two points at distance `L` is at least `L`.**  This is the
quantitative form of "geodesics minimise energy": `L = d ≤ √(L·E)` gives `L ≤ E`. -/
theorem le_energy_of_edist_eq [ContMDiffCovariantDerivative cov ∞] (hmet : IsMetricCompatible cov)
    {γ : ℝ → M} {L : ℝ} (hL : 0 < L)
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 γ (Icc 0 L))
    (hspc : ContinuousOn (fun t => curveSpeed (I := I) γ t) (Icc 0 L))
    (hmin : Manifold.riemannianEDist I (γ 0) (γ L) = ENNReal.ofReal L) :
    L ≤ ∫ t in (0 : ℝ)..L, curveSpeed (I := I) γ t ^ 2 := by
  have h := edist_le_sqrt_mul_energy (cov := cov) hmet hL hγ hspc
  rw [hmin] at h
  rw [ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg (L * ∫ t in (0 : ℝ)..L, curveSpeed (I := I) γ t ^ 2))] at h
  have hE : 0 ≤ ∫ t in (0 : ℝ)..L, curveSpeed (I := I) γ t ^ 2 :=
    intervalIntegral.integral_nonneg hL.le (fun t _ => pow_nonneg (curveSpeed_nonneg (I := I) γ t) 2)
  have h2 : L ^ 2 ≤ (Real.sqrt (L * ∫ t in (0 : ℝ)..L, curveSpeed (I := I) γ t ^ 2)) ^ 2 :=
    pow_le_pow_left₀ hL.le h 2
  rw [Real.sq_sqrt (by positivity)] at h2
  nlinarith [hL]

/-- **The shortening lemma**: a function with a minimum at `0` cannot have `f'(0) = 0` and
`f''(0) < 0`.  This is the second-derivative test used by every "shortening" argument. -/
theorem false_of_deriv_deriv_neg_of_min {f : ℝ → ℝ} {L c : ℝ}
    (hmin : ∀ σ, L ≤ f σ) (h0 : f 0 = L)
    (h1 : HasDerivAt f 0 0) (h2 : HasDerivAt (deriv f) c 0) (hc : c < 0) : False := by
  obtain ⟨δ, hδpos, hδ⟩ :=
    Commons.Analysis.Calculus.exists_lt_of_hasDerivAt_deriv_neg h1 h2 hc
  have hlt : f (δ / 2) < f 0 := hδ (δ / 2) (by linarith) (by linarith)
  have hge : L ≤ f (δ / 2) := hmin (δ / 2)
  rw [h0] at hlt
  linarith

/-- **The shortening lemma in its Fermat form.**  A function with a *global* minimum at `0` cannot
have `f''(0) < 0` (in the sense `HasDerivAt (deriv f) c 0` with `c < 0`); the vanishing of the first
derivative at `0` is then automatic from Fermat's theorem (local minimum + differentiability), so the
hypothesis `HasDerivAt f 0 0` of `false_of_deriv_deriv_neg_of_min` is replaced by differentiability
at `0`.

This is the form used by the global `σ ≤ κ` argument: the energy `E` of a variation with fixed
endpoints satisfies `E(σ) ≥ L = E(0)` (distance between the endpoints), and `E` is differentiable at
`0` (`Submission.SecondVarGlobal.energy_second_deriv_cover`), so `deriv E 0 = 0` needs no separate
first-variation computation. -/
theorem false_of_deriv_deriv_neg_of_min_of_differentiableAt {f : ℝ → ℝ} {L c : ℝ}
    (hmin : ∀ σ, L ≤ f σ) (h0 : f 0 = L) (hdiff : DifferentiableAt ℝ f 0)
    (h2 : HasDerivAt (deriv f) c 0) (hc : c < 0) : False := by
  have hloc : IsLocalMin f 0 :=
    Filter.Eventually.of_forall (fun σ => by rw [h0]; exact hmin σ)
  have h1 : deriv f 0 = 0 := hloc.deriv_eq_zero
  obtain ⟨δ, hδpos, hδ⟩ :=
    Commons.Analysis.Calculus.exists_lt_of_deriv_eq_zero_of_hasDerivAt_deriv_neg
      hdiff.continuousAt h1 h2 hc
  have hlt : f (δ / 2) < f 0 := hδ (δ / 2) (by linarith) (by linarith)
  have hge : L ≤ f (δ / 2) := hmin (δ / 2)
  rw [h0] at hlt
  linarith

end

end Submission.EnergyBound

