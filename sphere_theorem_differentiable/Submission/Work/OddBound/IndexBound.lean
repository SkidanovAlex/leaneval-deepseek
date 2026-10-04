import Submission.Work.OddBound.Defs
import Submission.Work.OddBound.Shortening
import Submission.Work.OddBound.covAlong_smul_varying
import Submission.Work.OddBound.smoothAlongAt_smul_varying
import Submission.Commons.Analysis.Calculus.intervalIntegral_sin_sq_pi_mul_div
import Submission.Work.OddBound.continuousOn_idxAlong_of_smoothOn
import Submission.Work.OddBound.continuousOn_normSq_covAlong_of_smoothOn

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The index bound of the odd-dimensional Klingenberg estimate

The classical proof of Klingenberg's length bound in odd dimensions
(Klingenberg 1961; Abresch--Meyer, *Injectivity radius estimates and sphere theorems*, Theorem 1.6)
does **not** shorten the shortest closed geodesic by a parallel/holonomy field.  Instead it runs a
*minimax* on the loop space which produces a **long** closed geodesic `c̄` of length `≥ 2π/√K` and
**Morse index `≤ 1`**; the contradiction is then an *index computation* for `c̄`, which is
elementary:

> for a closed unit-speed geodesic `γ` of length `L` in a manifold with `sec ≥ δ`, the `n-1`
> *Dirichlet fields* `V_j(s) = sin (π s / L) • X_j(s)` (with `X_1, …, X_{n-1}` parallel orthonormal
> normal fields along `γ`) are **periodic** (they vanish at `s = 0` and `s = L`), linearly
> independent, and satisfy
> ```
> I(V_j, V_j) = ∫₀^L ( π²/L² cos²(π s/L) - sin²(π s/L) sec(X_j, γ') ) ≤ π²/(2L) - δ L/2,
> ```
> which is `< 0` as soon as `L > π/√δ`.  Hence `index(γ) ≥ n - 1`, so a geodesic with index `≤ 1`
> must be short — and then the pinching `sec > K/4` and `L ≥ 2π/√K` contradict each other.

This module formalises the index computation, in the form needed by the assembly: a geodesic of
length `L ≥ π/√δ` whose curvature on the planes of the Dirichlet fields is `≥ δ + ε` for some
`ε > 0` **cannot** satisfy `IndexAtMostOne` (`Work.OddBound.not_indexAtMostOne_of_parallelNormalPair`).

## What is here

* `IndexAtMostOne cov γ L` — the *negation-friendly* formulation of `Morse index ≤ 1`: there are no
  two linearly independent smooth periodic fields along `γ` whose index integral is negative.  It is
  the conclusion of the loop-space minimax (`MinimaxInput`, module
  `Submission.Work.OddBound.Minimax`).
* `ParallelNormalPair cov γ L` — two independent unit parallel normal fields along `γ`, smooth on the
  enlarged window `[-1, L+1]` (so that the second-variation engine applies);
* `dirichletField L X` — the field `s ↦ sin (π s / L) • X s`;
* the computations (`covAlong_dirichletField`, `idxAlong_dirichletField`,
  `integral_deriv_sin_sq_pi_mul_div`) and the main theorem
  `not_indexAtMostOne_of_parallelNormalPair`.

## Conventions

The window is `[0, L]`; the curvature bound is stated on *orthonormal pairs* (`‖u‖ = ‖v‖ = 1`,
`u ⊥ v`) at the points of the geodesic, exactly as in `Submission.RauchK.CurvLe` and in the
pinching hypothesis of the sphere theorem.  `IndexAtMostOne` uses the index integrand
`Submission.IndexIntrinsic.idxAlong` (`⟨∇V,∇V⟩ - ⟨R(V,γ')γ',V⟩`), so that the second-variation
engine `Work.OddBound.exists_shorter_closed_curve_of_negative_index` applies verbatim.
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

/-! ## 1. The index-at-most-one condition and the parallel normal pair -/

/-- **`Morse index ≤ 1`, in negation-friendly form.**  There are no two linearly independent smooth
periodic fields along the closed geodesic `γ` whose index integral `∫₀^L idxAlong` is negative.

This is the (weak) form of the conclusion of the loop-space minimax of Klingenberg's theorem: the
minimax geodesic `c̄` has at most one negative direction, so this statement holds for it
(`Submission.Work.OddBound.Minimax.MinimaxInput`).  Smooth periodic fields are a legitimate class of
variations of *closed* curves (`V L = V 0`), and the index integral is the second variation of the
energy along them; the vanishing of the index integral on tangential fields (`V = f • γ'`) means the
definition needs no normality hypothesis. -/
def IndexAtMostOne (cov : CovariantDerivative I E (TangentSpace I (M := M))) (γ : ℝ → M)
    (L : ℝ) : Prop :=
  ∀ (V W : (t : ℝ) → TangentSpace I (γ t)),
    (∀ s ∈ Icc (-1) (L + 1), SmoothAlongAt (I := I) γ V s) → V L = V 0 →
    (∀ s ∈ Icc (-1) (L + 1), SmoothAlongAt (I := I) γ W s) → W L = W 0 →
    (∫ t in (0 : ℝ)..L, idxAlong (cov := cov) γ V (covAlong cov V) t) < 0 →
    (∫ t in (0 : ℝ)..L, idxAlong (cov := cov) γ W (covAlong cov W) t) < 0 →
    ∃ c : ℝ, ∀ t : ℝ, W t = c • V t

/-- **Two independent parallel unit normal fields along a closed geodesic**, smooth on the enlarged
window `[-1, L+1]`.

Such a pair exists along *every* closed geodesic of a manifold of dimension `≥ 3`
(`Work.OddBound.exists_parallelNormalPair`): take two independent vectors of the normal space of
`γ(0)` and transport them.  Unlike Synge's fixed vector, periodicity of `X₁, X₂` is **not** required —
the Dirichlet fields built from them are periodic for free. -/
structure ParallelNormalPair (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (γ : ℝ → M) (L : ℝ) where
  /-- The first parallel normal field. -/
  X₁ : (t : ℝ) → TangentSpace I (γ t)
  /-- The second parallel normal field. -/
  X₂ : (t : ℝ) → TangentSpace I (γ t)
  smooth₁ : ∀ t ∈ Icc (-1) (L + 1), SmoothAlongAt (I := I) γ X₁ t
  smooth₂ : ∀ t ∈ Icc (-1) (L + 1), SmoothAlongAt (I := I) γ X₂ t
  parallel₁ : ∀ t ∈ Icc (0 : ℝ) L, covAlong cov X₁ t = 0
  parallel₂ : ∀ t ∈ Icc (0 : ℝ) L, covAlong cov X₂ t = 0
  unitNormal₁ : IsUnitNormalField (I := I) γ L X₁
  unitNormal₂ : IsUnitNormalField (I := I) γ L X₂
  /-- The two fields are pointwise independent (a genuine two-dimensional space of test fields). -/
  independent : ∀ t ∈ Icc (0 : ℝ) L, ¬ ∃ c : ℝ, X₂ t = c • X₁ t

/-- The existence form of a parallel normal pair. -/
def ExistsParallelNormalPair (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (γ : ℝ → M) (L : ℝ) : Prop :=
  Nonempty (ParallelNormalPair cov γ L)

/-! ## 2. The Dirichlet field of a parallel normal field

Everything below is stated for the **explicit** field `fun s => Real.sin (Real.pi * s / L) • X s`
(the "Dirichlet field" of `X`), which is the form the second-variation engine consumes. -/

/-- The sine coefficient `s ↦ sin (π s / L)` of the Dirichlet field is globally `C^∞` (written
`π * s / L`, so that no division by a possibly vanishing `L` appears). -/
lemma contDiff_sin_dirichlet (L : ℝ) :
    ContDiff ℝ ∞ (fun s : ℝ => Real.sin (Real.pi * s / L)) := by
  have h1 : ContDiff ℝ ∞ (fun s : ℝ => (Real.pi / L) * s) := contDiff_const.mul contDiff_id
  have h2 : (fun s : ℝ => Real.sin (Real.pi * s / L))
      = fun s : ℝ => Real.sin ((Real.pi / L) * s) := by
    funext s; ring_nf
  rw [h2]; exact h1.sin

/-- The derivative of the sine coefficient. -/
lemma deriv_sin_dirichlet (L : ℝ) (t : ℝ) :
    deriv (fun s : ℝ => Real.sin (Real.pi * s / L)) t
      = (Real.pi / L) * Real.cos (Real.pi * t / L) := by
  have h1 : HasDerivAt (fun s : ℝ => Real.pi * s / L) (Real.pi / L) t := by
    simpa using ((hasDerivAt_id t).const_mul Real.pi).div_const L
  rw [(h1.sin).deriv, mul_comm]

/-- The Dirichlet field of a field smooth along `γ` is smooth along `γ`. -/
lemma dirichletField_smooth {γ : ℝ → M} {L : ℝ} {X : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ}
    (hX : SmoothAlongAt (I := I) γ X t) :
    SmoothAlongAt (I := I) γ (fun s : ℝ => Real.sin (Real.pi * s / L) • X s) t :=
  smoothAlongAt_smul_varying isOpen_univ (mem_univ t) hX (contDiff_sin_dirichlet L).contDiffOn

/-- **The Dirichlet field of any field is periodic**: it vanishes at both ends.  This is why no
periodicity of `X` is needed in the index bound. -/
lemma dirichletField_periodic {γ : ℝ → M} {L : ℝ} (hL : L ≠ 0)
    (X : (t : ℝ) → TangentSpace I (γ t)) :
    (fun s : ℝ => Real.sin (Real.pi * s / L) • X s) L
      = (fun s : ℝ => Real.sin (Real.pi * s / L) • X s) 0 := by
  have h1 : Real.pi * L / L = Real.pi := by field_simp
  have h2 : Real.pi * 0 / L = 0 := by ring
  show Real.sin (Real.pi * L / L) • X L = Real.sin (Real.pi * 0 / L) • X 0
  rw [h1, h2, Real.sin_pi, Real.sin_zero, zero_smul, zero_smul]

/-- **The covariant derivative of the Dirichlet field of a parallel field**: `∇V = f' • X`. -/
lemma covAlong_dirichletField (htor : cov.torsion = 0)
    {γ : ℝ → M} {L : ℝ} {X : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ}
    (hXsm : SmoothAlongAt (I := I) γ X t) (hXpar : covAlong cov X t = 0) :
    covAlong cov (fun s : ℝ => Real.sin (Real.pi * s / L) • X s) t
      = deriv (fun s : ℝ => Real.sin (Real.pi * s / L)) t • X t := by
  have h := covAlong_smul_varying (I := I) (cov := cov) htor (γ := γ) (X := X)
    (f := fun s : ℝ => Real.sin (Real.pi * s / L)) (U := univ) isOpen_univ (mem_univ t)
    hXsm (contDiff_sin_dirichlet L).contDiffOn (dirichletField_smooth (L := L) hXsm)
  rw [h, hXpar, smul_zero, add_zero]

/-! ## 3. The index integral of a Dirichlet field -/

/-- **The pointwise value of the index integrand on a Dirichlet field**: it is the square of the
derivative of the sine, minus the curvature pairing of `X` weighted by the square of the sine. -/
lemma idxAlong_dirichletField (htor : cov.torsion = 0)
    {γ : ℝ → M} {L : ℝ} {X : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ}
    (hXsm : SmoothAlongAt (I := I) γ X t) (hXpar : covAlong cov X t = 0) :
    idxAlong (cov := cov) γ (fun s : ℝ => Real.sin (Real.pi * s / L) • X s)
        (covAlong cov (fun s : ℝ => Real.sin (Real.pi * s / L) • X s)) t
      = (deriv (fun s : ℝ => Real.sin (Real.pi * s / L)) t) ^ 2 * ‖X t‖ ^ 2
        - (Real.sin (Real.pi * t / L)) ^ 2
          * inner ℝ (curvVec cov (γ t) (X t) (curveVelocity (I := I) γ t)
              (curveVelocity (I := I) γ t)) (X t) := by
  rw [idxAlong, covAlong_dirichletField (I := I) (cov := cov) htor hXsm hXpar,
    curvVec_smul_left (cov := cov) (hcov := inferInstance) (x := γ t)
      (c := Real.sin (Real.pi * t / L)) (u := X t)
      (v := curveVelocity (I := I) γ t) (w := curveVelocity (I := I) γ t)]
  rw [real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  ring

/-- **The pointwise bound on the index integrand of a Dirichlet field.**  For a unit-speed `γ`, a
unit normal parallel field `X` and a lower curvature bound `δ + ε` on the planes `span{X t, γ'(t)}`,

`idxAlong γ V (∇V) t ≤ f'(t)² - (δ + ε) f(t)²`,  `f(t) = sin (π t / L)`. -/
lemma idxAlong_dirichletField_le (htor : cov.torsion = 0)
    {γ : ℝ → M} {L δ ε : ℝ} {X : (t : ℝ) → TangentSpace I (γ t)}
    (hXsm : ∀ t ∈ Icc (-1) (L + 1), SmoothAlongAt (I := I) γ X t)
    (hXpar : ∀ t ∈ Icc (0 : ℝ) L, covAlong cov X t = 0)
    (hXun : IsUnitNormalField (I := I) γ L X)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) L, curveSpeed (I := I) γ t = 1)
    (hcurv : ∀ t ∈ Icc (0 : ℝ) L, ∀ u v : TangentSpace I (γ t), ‖u‖ = 1 → ‖v‖ = 1 →
      inner ℝ u v = 0 → δ + ε ≤ inner ℝ (curvVec cov (γ t) u v v) u)
    (hε : 0 < ε) :
    ∀ t ∈ Icc (0 : ℝ) L,
      idxAlong (cov := cov) γ (fun s : ℝ => Real.sin (Real.pi * s / L) • X s)
          (covAlong cov (fun s : ℝ => Real.sin (Real.pi * s / L) • X s)) t
        ≤ (deriv (fun s : ℝ => Real.sin (Real.pi * s / L)) t) ^ 2
          - (δ + ε) * (Real.sin (Real.pi * t / L)) ^ 2 := by
  intro t ht
  obtain ⟨hXn, hXo⟩ := hXun t ht
  have hv1 : ‖curveVelocity (I := I) γ t‖ = 1 := by
    rw [← Submission.GeodesicSpeed.curveSpeed_eq_norm]
    exact hspeed t ht
  have hsec := hcurv t ht (X t) (curveVelocity (I := I) γ t) hXn hv1 hXo
  rw [idxAlong_dirichletField (cov := cov) htor
      (hXsm t ⟨by linarith [ht.1], by linarith [ht.2]⟩) (hXpar t ht), hXn, one_pow, mul_one]
  nlinarith [mul_le_mul_of_nonneg_right hsec (sq_nonneg (Real.sin (Real.pi * t / L)))]


/-! ## 4. The integral of the index integrand and the index bound -/

/-- The cosine companion of `Commons.Analysis.Calculus.intervalIntegral_sin_sq_pi_mul_div`. -/
lemma intervalIntegral_cos_sq_pi_mul_div (L : ℝ) (hL : 0 < L) :
    (∫ t in (0 : ℝ)..L, Real.cos (Real.pi * t / L) ^ 2) = L / 2 := by
  have hpt : ∀ t : ℝ, Real.cos (Real.pi * t / L) ^ 2
      = 1 - Real.sin (Real.pi * t / L) ^ 2 := by
    intro t
    linarith [Real.sin_sq_add_cos_sq (Real.pi * t / L)]
  rw [intervalIntegral.integral_congr (fun t _ => hpt t)]
  have hcont : Continuous fun t : ℝ => Real.sin (Real.pi * t / L) ^ 2 := by fun_prop
  rw [intervalIntegral.integral_sub intervalIntegrable_const (hcont.intervalIntegrable 0 L),
    intervalIntegral.integral_const,
    Commons.Analysis.Calculus.intervalIntegral_sin_sq_pi_mul_div L hL]
  simp only [sub_zero, smul_eq_mul, mul_one]
  ring

/-- **The derivative-square integral**: `∫₀^L (d/dt sin (π t / L))² = π²/(2L)`. -/
lemma intervalIntegral_deriv_sin_sq_pi_mul_div (L : ℝ) (hL : 0 < L) :
    (∫ t in (0 : ℝ)..L, (deriv (fun s : ℝ => Real.sin (Real.pi * s / L)) t) ^ 2)
      = Real.pi ^ 2 / (2 * L) := by
  have hpt : ∀ t : ℝ, (deriv (fun s : ℝ => Real.sin (Real.pi * s / L)) t) ^ 2
      = (Real.pi / L) ^ 2 * Real.cos (Real.pi * t / L) ^ 2 := by
    intro t
    rw [deriv_sin_dirichlet L t]
    ring
  rw [intervalIntegral.integral_congr (fun t _ => hpt t), intervalIntegral.integral_const_mul,
    intervalIntegral_cos_sq_pi_mul_div L hL]
  have hL0 : L ≠ 0 := ne_of_gt hL
  field_simp
  try ring

/-- **The index integral of a Dirichlet field is negative.**  For a unit-speed `γ` of "length" `L`
(speed one on `[0,L]`), a unit normal *parallel* field `X` along it, and a curvature lower bound
`δ + ε` (`ε > 0`) on the planes `span{X t, γ'(t)}`, if `π/√δ ≤ L` then

`∫₀^L idxAlong γ V (∇V) < 0`,  `V(s) = sin (π s / L) • X s`.

The strictness `ε > 0` is what makes the *boundary* case `L = π/√δ` work; it is exactly what strict
quarter-pinching (`sec > K/4` pointwise, hence `sec ≥ K/4 + ε` for some `ε > 0` on a compact
manifold) provides. -/
theorem integral_idxAlong_dirichletField_neg (htor : cov.torsion = 0)
    {γ : ℝ → M} (hγsm : ContMDiffOn 𝓘(ℝ) I ∞ γ univ)
    (hne : ∀ t : ℝ, curveVelocity (I := I) γ t ≠ 0)
    {L δ ε : ℝ} (hL : 0 < L)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) L, curveSpeed (I := I) γ t = 1)
    (hδ : 0 < δ) (hε : 0 < ε) (hπ : Real.pi / Real.sqrt δ ≤ L)
    (hcurv : ∀ t ∈ Icc (0 : ℝ) L, ∀ u v : TangentSpace I (γ t), ‖u‖ = 1 → ‖v‖ = 1 →
      inner ℝ u v = 0 → δ + ε ≤ inner ℝ (curvVec cov (γ t) u v v) u)
    {X : (t : ℝ) → TangentSpace I (γ t)}
    (hXsm : ∀ t ∈ Icc (-1) (L + 1), SmoothAlongAt (I := I) γ X t)
    (hXpar : ∀ t ∈ Icc (0 : ℝ) L, covAlong cov X t = 0)
    (hXun : IsUnitNormalField (I := I) γ L X) :
    (∫ t in (0 : ℝ)..L, idxAlong (cov := cov) γ
        (fun s : ℝ => Real.sin (Real.pi * s / L) • X s)
        (covAlong cov (fun s : ℝ => Real.sin (Real.pi * s / L) • X s)) t) < 0 := by
  -- continuity of the integrand
  have hγ' : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo ((0 : ℝ) - 1) (L + 1)) := by
    simpa only [zero_sub] using hγsm.mono (Set.subset_univ _)
  have hne' : ∀ t ∈ Ioo ((0 : ℝ) - 1) (L + 1), curveVelocity (I := I) γ t ≠ 0 :=
    fun t _ => hne t
  have hVsm : ∀ t ∈ Icc (0 : ℝ) L, SmoothAlongAt (I := I) γ
      (fun s : ℝ => Real.sin (Real.pi * s / L) • X s) t := fun t ht =>
    dirichletField_smooth (L := L) (hXsm t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hcont := continuousOn_idxAlong_of_smoothOn (cov := cov) htor hL.le hγ' hne' hVsm
  have hint : IntervalIntegrable (fun t => idxAlong (cov := cov) γ
      (fun s : ℝ => Real.sin (Real.pi * s / L) • X s)
      (covAlong cov (fun s : ℝ => Real.sin (Real.pi * s / L) • X s)) t) volume (0 : ℝ) L :=
    hcont.intervalIntegrable_of_Icc hL.le
  -- the dominating function and its integral
  have hcontA : Continuous fun t : ℝ => (Real.pi / L) ^ 2 * Real.cos (Real.pi * t / L) ^ 2 := by
    fun_prop
  have hcontB : Continuous fun t : ℝ => (δ + ε) * Real.sin (Real.pi * t / L) ^ 2 := by fun_prop
  have hintA : IntervalIntegrable (fun t : ℝ => (Real.pi / L) ^ 2 * Real.cos (Real.pi * t / L) ^ 2)
      volume (0 : ℝ) L := hcontA.intervalIntegrable 0 L
  have hintB : IntervalIntegrable (fun t : ℝ => (δ + ε) * Real.sin (Real.pi * t / L) ^ 2)
      volume (0 : ℝ) L := hcontB.intervalIntegrable 0 L
  -- the pointwise inequality holds on `[0,L]`; extend it to a *global* domination
  set G : ℝ → ℝ := fun t => if t ∈ Icc (0 : ℝ) L
    then idxAlong (cov := cov) γ (fun s : ℝ => Real.sin (Real.pi * s / L) • X s)
      (covAlong cov (fun s : ℝ => Real.sin (Real.pi * s / L) • X s)) t
    else (Real.pi / L) ^ 2 * Real.cos (Real.pi * t / L) ^ 2
      - (δ + ε) * Real.sin (Real.pi * t / L) ^ 2 with hGdef
  have hGcont : ContinuousOn G (Icc (0 : ℝ) L) :=
    hcont.congr (fun t ht => by simp only [hGdef, ht, if_true])
  have hGint : IntervalIntegrable G volume (0 : ℝ) L := hGcont.intervalIntegrable_of_Icc hL.le
  have hGle : G ≤ fun t => (Real.pi / L) ^ 2 * Real.cos (Real.pi * t / L) ^ 2
      - (δ + ε) * Real.sin (Real.pi * t / L) ^ 2 := by
    intro t
    by_cases ht : t ∈ Icc (0 : ℝ) L
    · simp only [hGdef, ht, if_true]
      have h1 := idxAlong_dirichletField_le (cov := cov) htor hXsm hXpar hXun hspeed hcurv hε t ht
      rw [deriv_sin_dirichlet L t, mul_pow] at h1
      exact h1
    · simp only [hGdef, ht, if_false]
      exact le_rfl
  have hle := intervalIntegral.integral_mono hL.le hGint (hintA.sub hintB) hGle
  have hcongr : (∫ t in (0 : ℝ)..L, G t) = ∫ t in (0 : ℝ)..L, idxAlong (cov := cov) γ
      (fun s : ℝ => Real.sin (Real.pi * s / L) • X s)
      (covAlong cov (fun s : ℝ => Real.sin (Real.pi * s / L) • X s)) t := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le hL.le] at ht
    simp only [hGdef, ht, if_true]
  rw [hcongr] at hle
  -- value of the dominating integral
  have hval : (∫ t in (0 : ℝ)..L, ((Real.pi / L) ^ 2 * Real.cos (Real.pi * t / L) ^ 2
      - (δ + ε) * Real.sin (Real.pi * t / L) ^ 2))
      = Real.pi ^ 2 / (2 * L) - (δ + ε) * (L / 2) := by
    rw [intervalIntegral.integral_sub hintA hintB, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral_cos_sq_pi_mul_div L hL,
      Commons.Analysis.Calculus.intervalIntegral_sin_sq_pi_mul_div L hL]
    have hL0 : L ≠ 0 := ne_of_gt hL
    field_simp
    try ring
  rw [hval] at hle
  -- the value is negative
  have hkey : Real.pi ^ 2 / (2 * L) - (δ + ε) * (L / 2) < 0 := by
    have h2 : Real.pi ^ 2 < (δ + ε) * L ^ 2 := by
      have h1 : Real.pi ≤ L * Real.sqrt δ := (div_le_iff₀ (Real.sqrt_pos.mpr hδ)).mp hπ
      have h3 : Real.pi ^ 2 ≤ (L * Real.sqrt δ) ^ 2 :=
        pow_le_pow_left₀ (le_of_lt Real.pi_pos) h1 2
      have h4 : (L * Real.sqrt δ) ^ 2 = L ^ 2 * δ := by
        rw [mul_pow, Real.sq_sqrt hδ.le]
      have h5 : L ^ 2 * δ < L ^ 2 * (δ + ε) := by
        have : (0 : ℝ) < L ^ 2 := by positivity
        nlinarith [hε]
      linarith
    have hnum : Real.pi ^ 2 - (δ + ε) * L ^ 2 < 0 := by linarith
    have hpos : (0 : ℝ) < 2 * L := by linarith
    have hsplit : Real.pi ^ 2 / (2 * L) - (δ + ε) * (L / 2)
        = (Real.pi ^ 2 - (δ + ε) * L ^ 2) / (2 * L) := by
      field_simp
    rw [hsplit]
    exact div_neg_of_neg_of_pos hnum hpos
  linarith [hle, hkey]

/-- **The index bound of the odd-dimensional Klingenberg estimate.**  A closed unit-speed geodesic
`γ` of length `L ≥ π/√δ` in a manifold whose curvature on the planes of a parallel normal pair is
`≥ δ + ε` (`ε > 0`) does **not** have Morse index `≤ 1`.

The two Dirichlet fields `V_j = sin (π · / L) • X_j` are smooth periodic fields with negative index
integrals (`integral_idxAlong_dirichletField_neg`, one for each `X_j`), and they are linearly
independent because `X_1, X_2` are pointwise independent and the sine does not vanish at `L/2`. -/
theorem not_indexAtMostOne_of_parallelNormalPair (htor : cov.torsion = 0)
    {γ : ℝ → M} (hγsm : ContMDiffOn 𝓘(ℝ) I ∞ γ univ)
    (hne : ∀ t : ℝ, curveVelocity (I := I) γ t ≠ 0)
    {L δ ε : ℝ} (hL : 0 < L)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) L, curveSpeed (I := I) γ t = 1)
    (hδ : 0 < δ) (hε : 0 < ε) (hπ : Real.pi / Real.sqrt δ ≤ L)
    (hcurv : ∀ t ∈ Icc (0 : ℝ) L, ∀ u v : TangentSpace I (γ t), ‖u‖ = 1 → ‖v‖ = 1 →
      inner ℝ u v = 0 → δ + ε ≤ inner ℝ (curvVec cov (γ t) u v v) u)
    (hp : ParallelNormalPair (I := I) cov γ L) :
    ¬ IndexAtMostOne (I := I) (cov := cov) γ L := by
  intro hidx
  have hL0 : L ≠ 0 := ne_of_gt hL
  have hsm₁ : ∀ s ∈ Icc (-1) (L + 1), SmoothAlongAt (I := I) γ
      (fun u : ℝ => Real.sin (Real.pi * u / L) • hp.X₁ u) s := fun s hs =>
    dirichletField_smooth (L := L) (hp.smooth₁ s hs)
  have hsm₂ : ∀ s ∈ Icc (-1) (L + 1), SmoothAlongAt (I := I) γ
      (fun u : ℝ => Real.sin (Real.pi * u / L) • hp.X₂ u) s := fun s hs =>
    dirichletField_smooth (L := L) (hp.smooth₂ s hs)
  have hneg₁ := integral_idxAlong_dirichletField_neg (cov := cov) htor hγsm hne hL hspeed hδ hε
    hπ hcurv hp.smooth₁ hp.parallel₁ hp.unitNormal₁
  have hneg₂ := integral_idxAlong_dirichletField_neg (cov := cov) htor hγsm hne hL hspeed hδ hε
    hπ hcurv hp.smooth₂ hp.parallel₂ hp.unitNormal₂
  obtain ⟨c, hc⟩ := hidx _ _ hsm₁ (dirichletField_periodic hL0 hp.X₁) hsm₂
    (dirichletField_periodic hL0 hp.X₂) hneg₁ hneg₂
  -- evaluate at the midpoint, where the sine equals one
  refine hp.independent (L / 2) ⟨by linarith, by linarith⟩ ⟨c, ?_⟩
  have hmid : Real.pi * (L / 2) / L = Real.pi / 2 := by
    field_simp
    try ring
  have hval := hc (L / 2)
  rw [hmid, Real.sin_pi_div_two] at hval
  simpa using hval

end

end Work.OddBound

