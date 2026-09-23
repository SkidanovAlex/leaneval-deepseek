import Submission.Work.OddBound.IndexBound
import Submission.Work.OddBound.IndexDirichlet
import Submission.SyngeWindow

/-!
# The *correct* form of "Morse index ≤ 1" for the loop-space minimax

The classical loop-space minimax (Klingenberg 1961; Abresch--Meyer Theorem 1.6, Remark 4.4) produces
a closed geodesic whose **Morse index** is at most one, i.e. the index form on the space of variation
fields has **at most one negative direction**: there is no *two-dimensional* space of fields on which
the index form is negative definite.

This is **strictly weaker** than the condition `DirichletIndexAtMostOne` used earlier in this
directory ("any two fields with negative index integral are proportional").  The difference matters
and the earlier form is *not* what a minimax yields:

* the index form of a *nondegenerate* critical point has a finite-dimensional negative space; if the
  index is one and there is a *kernel* direction (e.g. the great circle on the round sphere, whose
  Dirichlet form has one negative and one zero direction), then there are many non-proportional
  fields with negative index integral, while the Morse index is still one;
* concretely, on the unit round `S²` a great circle `γ` of length `2π` has
  `I(sin (s/2) • X, sin (s/2) • X) < 0` and `I(sin (s/2) • X + ε sin s • X, ·) < 0` for small `ε`,
  with the two fields independent, although its Dirichlet index is `1`.  Since the minimax of the
  round sphere *is* a great circle, `DirichletIndexAtMostOne` is a false conclusion of the minimax,
  while the "no negative-definite plane" form below is the true one.

The key point for the Klingenberg estimate is that the *index bound* is strong enough to rule out
the corrected conclusion: the two test fields `sin (π s / L) • X₁`, `sin (π s / L) • X₂` of a
parallel normal pair span a two-dimensional space on which the index form is negative definite as
soon as `L > π/√(δ+ε)` (`not_dirichletIndexLeOne_of_parallelNormalPair`, delegated).

## The definition

`DirichletIndexLeOne cov γ L` says: for any two smooth Dirichlet fields `V, W` along `γ` (vanishing
at `0` and `L`), there is a non-trivial linear combination `a • V + b • W` whose index integral is
**non-negative**.  Equivalently (taking the contrapositive) there is no two-dimensional space of
Dirichlet fields on which the index form is negative definite.  This is exactly the conclusion of
the minimax over `1`-parameter families on the based loop space `Ω_p M`, and exactly what the index
bound contradicts.
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
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length
open Submission.InjRadius Submission.IndexIntrinsic Submission.CurvatureVec

namespace Work.OddBound

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


/-! ## 0. Two helpers for the *zero* field -/

/-- The covariant derivative of the zero field is zero. -/
lemma covAlong_zero (htor : cov.torsion = 0) (γ : ℝ → M)
    (W : (t : ℝ) → TangentSpace I (γ t)) (t : ℝ) :
    covAlong (γ := γ) cov (fun _ : ℝ => (0 : TangentSpace I (γ t))) t = 0 := by
  simpa using Submission.IndexScale.covAlong_smul (cov := cov) htor γ W (0 : ℝ) t

/-- The index integral of the zero field vanishes. -/
lemma intervalIntegral_idxAlong_zero (htor : cov.torsion = 0) (γ : ℝ → M)
    (W : (t : ℝ) → TangentSpace I (γ t)) (L : ℝ) :
    (∫ t in (0 : ℝ)..L, idxAlong (cov := cov) γ (fun _ : ℝ => (0 : TangentSpace I (γ t)))
        (covAlong (γ := γ) cov (fun _ : ℝ => (0 : TangentSpace I (γ t)))) t) = 0 := by
  have hpt : ∀ t : ℝ, idxAlong (cov := cov) γ (fun _ : ℝ => (0 : TangentSpace I (γ t)))
      (covAlong (γ := γ) cov (fun _ : ℝ => (0 : TangentSpace I (γ t)))) t = 0 := by
    intro t
    rw [idxAlong, covAlong_zero (cov := cov) htor γ W t, inner_zero_left, inner_zero_right,
      sub_zero]
  rw [intervalIntegral.integral_congr (g := fun _ : ℝ => 0) (fun t _ => hpt t)]
  simp

/-! ## 1. The corrected notion -/

/-- **`Morse index ≤ 1` in its correct form.**  Along a geodesic `γ` with parameter length `L`,
there is no two-dimensional space of smooth Dirichlet fields (fields vanishing at `0` and `L`) on
which the index form is negative definite.

Written in negation-friendly (existential-combination) form: every pair of Dirichlet fields `V, W`
has a non-trivial linear combination whose index integral is `≥ 0`.

This is the conclusion of the loop-space minimax (Klingenberg 1961; Abresch--Meyer Theorem 1.6 and
Remark 4.4), and is *strictly weaker* than `DirichletIndexAtMostOne`
(`dirichletIndexLeOne_of_dirichletIndexAtMostOne`). -/
def DirichletIndexLeOne (cov : CovariantDerivative I E (TangentSpace I (M := M))) (γ : ℝ → M)
    (L : ℝ) : Prop :=
  ∀ (V W : (t : ℝ) → TangentSpace I (γ t)),
    (∀ s ∈ Icc (-1) (L + 1), SmoothAlongAt (I := I) γ V s) → V 0 = 0 → V L = 0 →
    (∀ s ∈ Icc (-1) (L + 1), SmoothAlongAt (I := I) γ W s) → W 0 = 0 → W L = 0 →
    ∃ a b : ℝ, (a, b) ≠ 0 ∧
      0 ≤ ∫ t in (0 : ℝ)..L, idxAlong (cov := cov) γ
        (fun s : ℝ => a • V s + b • W s)
        (covAlong cov (fun s : ℝ => a • V s + b • W s)) t

/-! ## 1bis. Proof design for the strong index bound

The delegated lemma `Work.OddBound.not_dirichletIndexLeOne_of_parallelNormalPair` (module
`Submission.Work.OddBound.strongIndex.not_dirichletIndexLeOne_of_parallelNormalPair`) constructs the
negative-definite plane as follows; this is the *complete* design, all ingredients already existing.

Given **metric compatibility** `hmet : IsMetricCompatible cov`, a `ParallelNormalPair` `hp`
(fields `X₁`, `X₂`) along a unit-speed geodesic `γ` of length `L` with `π < √(δ+ε)·L` and curvature
`≥ δ + ε` on orthonormal pairs, take

  `V := fun s => Real.sin (Real.pi * s / L) • hp.X₁ s`,
  `W := fun s => Real.sin (Real.pi * s / L) • hp.X₂ s`.

Both are `SmoothAlongAt` on `Icc (-1) (L+1)` (`dirichletField_smooth` with `hp.smooth₁/₂`) and vanish
at `0` and `L` (`dirichletField_zero`, `dirichletField_at_right`).  For `(a,b) ≠ 0` put
`Z := fun s => a • V s + b • W s`; then

  * `covAlong cov Z t = deriv (fun s => Real.sin (Real.pi * s / L)) t • (a • hp.X₁ t + b • hp.X₂ t)`

    (`covAlong_add_smul` + `Submission.IndexScale.covAlong_smul` + `covAlong_dirichletField` applied
    to each of `hp.X₁`, `hp.X₂`, which are parallel on `[0,L]`);
  * the *quadratic form* `A := ‖a • hp.X₁ t + b • hp.X₂ t‖ ^ 2` is **independent of `t`**: the inner
    product `t ↦ inner ℝ (hp.X₁ t) (hp.X₂ t)` is constant on `[0,L]` because its derivative vanishes
    there (`Submission.IndexIntrinsic2.hasDerivAt_inner_bilAlong` or
    `Submission.Variation.metricCompatible_deriv_inner` with `cov.torsion = 0` and metric
    compatibility, applied to the two fields whose covariant derivatives vanish on `[0,L]`), and the
    norms are one (`hp.unitNormal₁/₂`); in particular `A > 0` because `X₁, X₂` are pointwise
    independent (`hp.independent`);
  * `a • hp.X₁ t + b • hp.X₂ t` is orthogonal to `curveVelocity γ t` (`hp.unitNormal₁/₂`);
  * hence, with `c := a • hp.X₁ t + b • hp.X₂ t` and writing `curvVec` in the first and last slots,

    `inner ℝ (curvVec cov (γ t) c γ' γ') c = ‖c‖ ^ 2 * inner ℝ (curvVec cov (γ t) u γ' γ') u`
    with `u := ‖c‖⁻¹ • c` (unit, orthogonal to `γ'`, which is unit by `hspeed`), so `hcurv` gives
    `inner ℝ (curvVec cov (γ t) c γ' γ') c ≥ (δ + ε) * ‖c‖ ^ 2 = (δ+ε) * A`;
  * therefore, using `idxAlong`'s definition and integrating with `intervalIntegral_cos_sq_pi_mul_div`
    (and the analogous `sin²` integral),

    `∫₀^L idxAlong γ Z (∇Z) ≤ A * ((π/L)^2 * (L/2) - (δ+ε) * (L/2)) = A * (π^2 - (δ+ε) L^2) / (2L) < 0`

    because `π^2 < (δ+ε) * L^2` (`Real.pi / Real.sqrt (δ+ε) < L`).

This yields `DirichletIndexNotLeOne cov γ L` with the two fields `V`, `W`. -/

/-- **The two-dimensional negation of the corrected notion**: a pair of smooth Dirichlet fields
spanning a two-dimensional space on which the index form is *negative definite*. -/
def DirichletIndexNotLeOne (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (γ : ℝ → M) (L : ℝ) : Prop :=
  ∃ (V W : (t : ℝ) → TangentSpace I (γ t)),
    (∀ s ∈ Icc (-1) (L + 1), SmoothAlongAt (I := I) γ V s) ∧ V 0 = 0 ∧ V L = 0 ∧
    (∀ s ∈ Icc (-1) (L + 1), SmoothAlongAt (I := I) γ W s) ∧ W 0 = 0 ∧ W L = 0 ∧
    ∀ a b : ℝ, (a, b) ≠ 0 →
      ∫ t in (0 : ℝ)..L, idxAlong (cov := cov) γ
        (fun s : ℝ => a • V s + b • W s)
        (covAlong cov (fun s : ℝ => a • V s + b • W s)) t < 0

/-- The negation of `DirichletIndexLeOne` is the existence of a negative-definite plane. -/
lemma dirichletIndexNotLeOne_of_not_dirichletIndexLeOne {γ : ℝ → M} {L : ℝ}
    (h : ¬ DirichletIndexLeOne (I := I) (cov := cov) γ L) :
    DirichletIndexNotLeOne (I := I) (cov := cov) γ L := by
  by_contra hcon
  apply h
  intro V W hVsm hV0 hVL hWsm hW0 hWL
  by_contra hcon2
  push_neg at hcon2
  exact hcon ⟨V, W, hVsm, hV0, hVL, hWsm, hW0, hWL, hcon2⟩

/-- A negative-definite plane refutes the corrected notion. -/
lemma not_dirichletIndexLeOne_of_dirichletIndexNotLeOne {γ : ℝ → M} {L : ℝ}
    (h : DirichletIndexNotLeOne (I := I) (cov := cov) γ L) :
    ¬ DirichletIndexLeOne (I := I) (cov := cov) γ L := by
  rintro hle
  obtain ⟨V, W, hVsm, hV0, hVL, hWsm, hW0, hWL, hneg⟩ := h
  obtain ⟨a, b, hab, hge⟩ := hle V W hVsm hV0 hVL hWsm hW0 hWL
  exact absurd (hneg a b hab) (not_lt.mpr hge)

/-- **The old (`DirichletIndexAtMostOne`) form implies the corrected form.**  If every two fields
with negative index integral are proportional, then there is no two-dimensional space on which the
index form is negative definite. -/
theorem dirichletIndexLeOne_of_dirichletIndexAtMostOne (htor : cov.torsion = 0)
    {γ : ℝ → M} {L : ℝ}
    (h : DirichletIndexAtMostOne (I := I) (cov := cov) γ L) :
    DirichletIndexLeOne (I := I) (cov := cov) γ L := by
  intro V W hVsm hV0 hVL hWsm hW0 hWL
  by_contra hcon
  push_neg at hcon
  -- the two fields themselves have negative index integrals
  have hVneg : (∫ t in (0 : ℝ)..L, idxAlong (cov := cov) γ V (covAlong cov V) t) < 0 := by
    have h1 := hcon 1 0 (by norm_num : ((1 : ℝ), (0 : ℝ)) ≠ 0)
    rw [show (fun s : ℝ => (1 : ℝ) • V s + (0 : ℝ) • W s) = V from by
      funext s; simp] at h1
    exact h1
  have hWneg : (∫ t in (0 : ℝ)..L, idxAlong (cov := cov) γ W (covAlong cov W) t) < 0 := by
    have h1 := hcon 0 1 (by norm_num : ((0 : ℝ), (1 : ℝ)) ≠ 0)
    rw [show (fun s : ℝ => (0 : ℝ) • V s + (1 : ℝ) • W s) = W from by
      funext s; simp] at h1
    exact h1
  obtain ⟨c, hc⟩ := h V W hVsm hV0 hVL hWsm hW0 hWL hVneg hWneg
  rcases eq_or_ne c 0 with hc0 | hcne
  · -- `W = 0`: the combination `W` itself has index integral `0`, not negative
    have h1 := hcon 0 1 (by norm_num : ((0 : ℝ), (1 : ℝ)) ≠ 0)
    have hzero : (fun s : ℝ => (0 : ℝ) • V s + (1 : ℝ) • W s) = fun _ : ℝ => 0 := by
      funext s
      rw [zero_smul, one_smul, hc s, hc0, zero_smul, add_zero]
    rw [hzero] at h1
    rw [intervalIntegral_idxAlong_zero (cov := cov) htor γ W L] at h1
    exact absurd h1 (lt_irrefl (0 : ℝ))
  · -- `W = c V` with `c ≠ 0`: the combination `c • V - W` vanishes identically
    have h1 := hcon c (-1) (by simp [hcne] : ((c : ℝ), (-1 : ℝ)) ≠ 0)
    have hzero : (fun s : ℝ => c • V s + (-1 : ℝ) • W s) = fun _ : ℝ => 0 := by
      funext s
      rw [hc s, neg_one_smul]
      exact add_neg_cancel _
    rw [hzero] at h1
    rw [intervalIntegral_idxAlong_zero (cov := cov) htor γ W L] at h1
    exact absurd h1 (lt_irrefl (0 : ℝ))

end

end Work.OddBound
