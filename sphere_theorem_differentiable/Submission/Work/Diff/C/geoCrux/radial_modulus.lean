import Mathlib
import Submission.Work.Diff.C.geoCrux.RadialBase
import Submission.Work.Diff.C.geoCrux.RauchInputDefs
import Submission.Work.Diff.C.geoCrux.Port.InjCore
import Submission.Work.Diff.C.geoCrux.Port.TwoCentreCore
import Submission.Work.Diff.C.geoCrux.Port.SharpPieces
import Submission.Work.Diff.C.geoCrux.sturm_anchored_lower
import Submission.Work.Diff.C.geoCrux.sturm_anchored_upper

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.Diff.C.GeoCrux.RadialModulusProp`: the modulus of the radial variation field

## The statement

For a centre `q`, orthonormal `v, w ∈ T_qM` and `t ∈ (0, ρ₀]`, `ρ₀ := π - arccos (1-c)`, the radial
variation field

`Z t = curveVelocity (fun r ↦ GExp q (t • (v + r • w))) 0`

(the Jacobi field along the ray `γ s = GExp q (s • v)` with `Z 0 = 0`, `∇_s Z (0) = w`) satisfies

`sin t / 2 ≤ ‖Z t‖ ≤ sin t + 3 (ε₁ (1 + (log (2/t))²) + t²) t`.

## The route taken here: *two centres*, not two radii at one centre

The naive route — Sturm/Grönwall comparison of `log ‖Z‖` against `log ∘ sin` using only the shape
operator of the spheres around **`q`** — cannot work near `t = 0`.  The shape-operator hypothesis at
scale `s` reads `|II(s) - cot s| ≤ ε₁ / sin s`, whose integral `∫₀^t ds / sin s` diverges, so the
comparison needs an *anchor* at a small positive scale; and the anchor (`‖Z s‖ ≈ s` at scale `√ε₁`)
is **not** a consequence of the shape operator of the spheres around `q` alone.  The exact Riccati
identity `(E sin²)' = -sin² (D + E²)` (`E = II - cot`, `D = R_γ - 1`) shows that this datum sees the
curvature only through the weighted integral `∫ sin² (R - 1)`, so a thin spike of *any* height is
invisible to it (this is exactly why `Work.Diff.C.GeoCrux.CurvBoundProp` and `ShapeFiniteDiffProp`
are false).  The naive route is therefore genuinely blocked.

**The second centre repairs it.**  `hHess` bounds the shape operator of the geodesic spheres around
**every** point; in particular, at the base point `q` with centre `γ(τ)`,

`Hess (rdist (γ τ)) (q) = cot τ · Id + O(ε₁ / sin τ)`  on  `γ'(0)^⊥`.

Write `B(t) := -Hess (rdist (γ t)) (q)|_{γ'(0)^⊥}` (self-adjoint on `V := γ'(0)^⊥`); the hypothesis
is `‖B(t) + cot t · Id‖ ≤ ε₁ / sin t`.  Two exact facts about the Jacobi structure along `γ` turn
this into the modulus.

**(1) Wronskian + shapes.**  Let `Z_w` be the forward field (`Z_w 0 = 0`, `∇Z_w(0) = w`) and, for
`σ < τ`, let `J_w` be the field vanishing at `γ(τ)` with `J_w 0 = w`.  The Wronskian
`⟨∇Z_w, J_w⟩ - ⟨Z_w, ∇J_w⟩` is constant, equal to `⟨w,w⟩`, and the two shape identities
`∇Z_w(σ) = II_q(γσ)·Z_w(σ)` (valid because `Z_w 0 = 0`) and
`∇J_w(σ) = -Hess (rdist (γτ))(γσ)·J_w(σ)` (valid because `J_w τ = 0`) give

`⟨(II_q(γσ) + Hess (rdist (γτ))(γσ)) Z_w(σ), J_w(σ)⟩ = ‖w‖²`,

i.e. with `II_q = cot σ · Id + E₁`, `Hess = cot(τ-σ)·Id + Ē`, `‖E₁‖ ≤ ε₁/sin σ`,
`‖Ē‖ ≤ ε₁/sin(τ-σ)`, `κ := cot σ + cot(τ-σ)`, `δ := ε₁(1/sin σ + 1/sin(τ-σ))`:

`1 = (κ + e) ⟨Z_w(σ), J_w(σ)⟩`,   `|e| ≤ δ`.

**(2) The backward field at `σ`.**  The field vanishing at `γ(τ)` with value `w` at `q` satisfies, at
every `s > 0`,

`J_w(s) = Z_{(B(τ) - B(s)) w}(s)`

(`= Y(s)(B(τ) - B(s))w` for the fundamental solution `Y`), because `Y(s)B(s) + Ŷ(s) = 0` for
`s > 0` (`Ŷ` the second fundamental solution) while `J_w(s) = Y(s)B(τ) + Ŷ(s)`.

Write `B(τ) - B(σ) = λ·Id + Δ`, `λ := cot σ - cot τ`, `‖Δ‖ ≤ η := ε₁(1/sin σ + 1/sin τ)`.  Then

`J_w(σ) = λ Z_w(σ) + Z_{Δ w}(σ)`, and `‖Z_ξ(σ)‖ ≤ M(σ)‖ξ‖` with `M(σ) := ‖Y(σ)‖`; hence
`⟨Z_w(σ), J_w(σ)⟩ = λ‖Z_w(σ)‖² + θ` with `|θ| ≤ η M(σ) ‖Z_w(σ)‖`.  Combining with (1):

`1 ≤ (κ + δ)(λ y_w² + η M y_w)`  and  `1 ≥ (κ - δ)(λ y_w² - η M y_w)`,

and the same inequality taken at the norm-maximising `w` (`y_w = M`) bounds `M` itself:
`(κ - δ)(λ - η) M² ≤ 1`.  With `τ := 2σ` one has the exact identity `κλ = 1/sin²σ`,
`η/λ = ε₁(2cos σ + 1)`, `δ/κ = ε₁/cos σ`, so that `η/λ ≤ 3ε₁` and `δ/κ ≤ 3ε₁`, and the extraction
gives `sin σ (1 - 8ε₁) ≤ ‖Z_w(σ)‖ ≤ sin σ (1 + 5ε₁)`.

For `σ ∈ (ρ₀/2, ρ₀]` the short-range Sturm/Grönwall propagation from the anchor `σ₀ := ρ₀/2` finishes
the interval, with room to spare against the weak error term `3(ε₁(1+log²(2/σ)) + σ²)σ` of the
target.

## What is proved here and what is delegated

The geometric inputs are stated below in the bare "closed `Prop`" style of
`geoCrux/RauchInputDefs.lean`, so that they can be delegated (the harness elaborates a delegated
statement in a file with no `open`s):

* `RadialCutDataProp` — the minimising/non-conjugacy consequences of the cut-locus input
  (`Work.Diff.C.GeoCrux.CutInjectProp`, `Submission.Work.Diff.C.geoCrux.cut_inject`; in flight as
  `geoCrux/cutTime_ge.lean` + `geoCrux/injectivity_radius.lean`).
* `RadialTwoCentreProp` — the two-centre inequality above, in the *scalar* form in which it is used.

The extraction (`Work.Diff.C.geoCrux.modulus_upper` / `modulus_lower`), the numerical endgame and the
assembly are done in this file.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric

namespace Work.Diff.C.geoCrux

/-! The definitions `rho0`, `twoK`, `twoL`, `twoD`, `twoE` live in the module
`Submission.Work.Diff.C.geoCrux.RadialBase` (imported above), so that the two-centre modules can be
placed below this file in the import graph. -/

/-- **The cut-locus data.**  Every unit-speed ray from every point is minimising up to `ρ₀` and every
sub-segment of it is minimising.

This is the consequence of `Work.Diff.C.GeoCrux.CutInjectProp` used by the two-centre argument:
minimising supplies `∇ (rdist z)(γ s) = ± γ'(s)` (hence the shape identities), and the injectivity of
the exponential map supplies the existence and invertibility of the backward Jacobi fields. -/
abbrev RadialCutDataProp : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c)
    (hcut : ∀ q : M, Submission.InjRadius.InjAtLeast hmet q (Real.pi - Real.arccos (1 - c))),
    ∀ (q : M) (v : TangentSpace I q), Inner.inner ℝ v v = 1 →
    ∀ t : ℝ, 0 < t → t ≤ Real.pi - Real.arccos (1 - c) →
      rdist (I := I) (M := M) q
          (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v)) = t ∧
        ∀ s : ℝ, 0 < s → s < t →
          rdist (I := I) (M := M)
              (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v))
              (Submission.GlobalExp.GExp (cov := cov) hmet q (s • v)) = t - s

/-- **The two-centre inequality** (the geometric core of the modulus estimate), in the scalar form in
which it is consumed.

For `0 < σ < τ ≤ 2σ` with `τ ≤ ρ₀`, writing `κ := cot σ + cot(τ-σ)`, `λ := cot σ - cot τ`,
`δ := ε₁ (1/sin σ + 1/sin(τ-σ))`, `η := ε₁ (1/sin σ + 1/sin τ)`, `y_w := ‖Z_w(σ)‖` for the forward
field `Z_w` (`Z_ξ(s) := curveVelocity (fun r ↦ GExp q (s • (v + r • ξ))) 0`, `ξ ⊥ v`) and `M` for the
operator norm of `ξ ↦ Z_ξ(σ)`:

* `‖Z_ξ(σ)‖ ≤ M ‖ξ‖` for all `ξ ⊥ v`;
* `(κ - δ)(λ - η) M² ≤ 1`  (the inequality taken at the norm-maximising direction);
* for every unit `w ⊥ v`:  `1 ≤ (κ + δ)(λ y_w² + η M y_w)`  and  `1 ≥ (κ - δ)(λ y_w² - η M y_w)`.

These are (1) + (2) of the module docstring; the identity `κλ = 1/sin²σ` (valid for `τ = 2σ`) and the
numerical bounds on `η/λ`, `δ/κ` are *not* part of the statement — they are proved in this file. -/
abbrev RadialTwoCentreProp : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    (hdiam : ∀ x y : M, rdist (I := I) (M := M) x y ≤ Real.pi)
    (q : M) (v : TangentSpace I q) (hv : Inner.inner ℝ v v = 1)
    (σ τ : ℝ) (hσ : 0 < σ) (hστ : σ < τ) (hτ2 : τ ≤ 2 * σ)
    (hτ : τ ≤ Real.pi - Real.arccos (1 - c)),
    ∃ N : ℝ, 0 ≤ N ∧
      (∀ ξ : TangentSpace I q, Inner.inner ℝ v ξ = 0 →
        ‖Submission.Geodesic.curveVelocity (I := I) (M := M)
          (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q
            (σ • (v + r • ξ))) 0‖ ≤ N * ‖ξ‖) ∧
      0 < twoK σ τ ∧ 0 < twoL σ τ ∧
      (twoK σ τ - twoD ε₁ σ τ) * (twoL σ τ - twoE ε₁ σ τ) * N ^ 2 ≤ 1 ∧
      ∀ w : TangentSpace I q, Inner.inner ℝ v w = 0 → Inner.inner ℝ w w = 1 →
        1 ≤ (twoK σ τ + twoD ε₁ σ τ) *
              (twoL σ τ * ‖Submission.Geodesic.curveVelocity (I := I) (M := M)
                  (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q
                    (σ • (v + r • w))) 0‖ ^ 2
                + twoE ε₁ σ τ * N * ‖Submission.Geodesic.curveVelocity (I := I) (M := M)
                  (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q
                    (σ • (v + r • w))) 0‖) ∧
        1 ≥ (twoK σ τ - twoD ε₁ σ τ) *
              (twoL σ τ * ‖Submission.Geodesic.curveVelocity (I := I) (M := M)
                  (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q
                    (σ • (v + r • w))) 0‖ ^ 2
                - twoE ε₁ σ τ * N * ‖Submission.Geodesic.curveVelocity (I := I) (M := M)
                  (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q
                    (σ • (v + r • w))) 0‖)

/-! ## The extraction: from the two-centre inequalities to the modulus bounds

The following is the *pure real-analysis* heart of the argument (see the module docstring).  The two
inequalities

`1 ≥ (κ - δ)(λ y² - η N y)`,  `1 ≤ (κ + δ)(λ y² + η N y)`,  `(κ - δ)(λ - η) N² ≤ 1`

with `κλ = 1/sin²σ`, `η ≤ 3ε₁λ`, `δ ≤ 3ε₁κ` give the two-sided bound
`sin σ/2 ≤ y ≤ sin σ (1 + 7ε₁)`. -/

/-- `√x + √y ≥ √(x+y)` for `x, y ≥ 0`. -/
theorem sqrt_add_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have h1 : 0 ≤ Real.sqrt x + Real.sqrt y := by positivity
  have hsq : (Real.sqrt (x + y)) ^ 2 = x + y := Real.sq_sqrt (by linarith)
  calc Real.sqrt (x + y) = Real.sqrt ((Real.sqrt (x + y)) ^ 2) :=
        (Real.sqrt_sq (Real.sqrt_nonneg _)).symm
    _ ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [hsq, add_sq, Real.sq_sqrt hx, Real.sq_sqrt hy]
        nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y]
    _ = Real.sqrt x + Real.sqrt y := Real.sqrt_sq h1

/-- **Step 1 (operator-norm bound).**  `N ≤ sin σ (1 + 6ε₁)`. -/
theorem twoCentre_N_bound {σ κ lam η δ N ε₁ : ℝ}
    (hsin : 0 < Real.sin σ) (hε₁ : 0 ≤ ε₁) (hε₁' : ε₁ ≤ 1 / 24)
    (hκ : 0 < κ) (hlam : 0 < lam) (hη : 0 ≤ η) (hδ : 0 ≤ δ) (hN : 0 ≤ N)
    (hκlam : κ * lam = 1 / (Real.sin σ) ^ 2)
    (hηlam : η ≤ 3 * ε₁ * lam) (hδκ : δ ≤ 3 * ε₁ * κ)
    (hN2 : (κ - δ) * (lam - η) * N ^ 2 ≤ 1) :
    N ≤ Real.sin σ * (1 + 6 * ε₁) := by
  have h3ε : 3 * ε₁ ≤ 1 / 8 := by linarith
  have hδlt : δ < κ := by nlinarith [hδκ, hκ, h3ε]
  have hηlt : η < lam := by nlinarith [hηlam, hlam, h3ε]
  have hκδ : 0 < κ - δ := by linarith
  have hlamη : 0 < lam - η := by linarith
  have hprod : κ * lam * (1 - 6 * ε₁) ≤ (κ - δ) * (lam - η) := by
    have h1 : κ - 3 * ε₁ * κ ≤ κ - δ := by linarith [hδκ]
    have h2 : lam - 3 * ε₁ * lam ≤ lam - η := by linarith [hηlam]
    have h3 : 0 ≤ κ - 3 * ε₁ * κ := by nlinarith [hκ, hε₁, h3ε]
    have h4 : 0 ≤ lam - 3 * ε₁ * lam := by nlinarith [hlam, hε₁, h3ε]
    have h5 : (κ - 3 * ε₁ * κ) * (lam - 3 * ε₁ * lam) ≤ (κ - δ) * (lam - η) :=
      mul_le_mul h1 h2 h4 (le_of_lt hκδ)
    have hid : (κ - 3 * ε₁ * κ) * (lam - 3 * ε₁ * lam) - κ * lam * (1 - 6 * ε₁)
        = κ * lam * (3 * ε₁) ^ 2 := by ring
    have h6 : κ * lam * (1 - 6 * ε₁) ≤ (κ - 3 * ε₁ * κ) * (lam - 3 * ε₁ * lam) := by
      have h7 : 0 ≤ κ * lam * (3 * ε₁) ^ 2 := by positivity
      linarith [hid, h7]
    linarith
  have hstep : N ^ 2 * (1 - 6 * ε₁) ≤ (Real.sin σ) ^ 2 := by
    have h1 : κ * lam * (1 - 6 * ε₁) * N ^ 2 ≤ (κ - δ) * (lam - η) * N ^ 2 :=
      mul_le_mul_of_nonneg_right hprod (sq_nonneg N)
    have h2 : κ * lam * (1 - 6 * ε₁) * N ^ 2 ≤ 1 := le_trans h1 hN2
    have h3 : κ * lam * (1 - 6 * ε₁) * N ^ 2 = N ^ 2 * (1 - 6 * ε₁) / (Real.sin σ) ^ 2 := by
      rw [hκlam]; ring
    rw [h3] at h2
    exact (div_le_one₀ (by positivity : (0:ℝ) < (Real.sin σ) ^ 2)).mp h2
  have hN2' : N ^ 2 ≤ (Real.sin σ * (1 + 6 * ε₁)) ^ 2 := by
    have h7 : 0 < 1 - 6 * ε₁ := by linarith
    have h8 : N ^ 2 ≤ (Real.sin σ) ^ 2 / (1 - 6 * ε₁) := (le_div_iff₀ h7).mpr hstep
    have h9 : (Real.sin σ) ^ 2 / (1 - 6 * ε₁) ≤ (Real.sin σ * (1 + 6 * ε₁)) ^ 2 := by
      rw [div_le_iff₀ h7]
      have h1 : 1 ≤ (1 + 6 * ε₁) ^ 2 * (1 - 6 * ε₁) := by
        have h2 : ε₁ ^ 2 ≤ ε₁ / 24 := by nlinarith [mul_le_mul_of_nonneg_left hε₁' hε₁]
        have h4 : ε₁ ^ 3 ≤ ε₁ ^ 2 / 24 := by nlinarith [mul_le_mul_of_nonneg_left h2 hε₁]
        nlinarith [h2, h4, hε₁, hε₁']
      have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (Real.sin σ))
      nlinarith [h2, sq_nonneg (Real.sin σ)]
    linarith
  have h11 : 0 ≤ Real.sin σ * (1 + 6 * ε₁) := by positivity
  calc N = Real.sqrt (N ^ 2) := (Real.sqrt_sq hN).symm
    _ ≤ Real.sqrt ((Real.sin σ * (1 + 6 * ε₁)) ^ 2) := Real.sqrt_le_sqrt hN2'
    _ = Real.sin σ * (1 + 6 * ε₁) := Real.sqrt_sq h11

/-- **Step 2 (upper bound for the modulus).**  `y ≤ sin σ (1 + 7ε₁)`. -/
theorem twoCentre_y_upper {σ κ lam η δ N y ε₁ : ℝ}
    (hsin : 0 < Real.sin σ) (hε₁ : 0 ≤ ε₁) (hε₁' : ε₁ ≤ 1 / 24)
    (hκ : 0 < κ) (hlam : 0 < lam) (hη : 0 ≤ η) (hN : 0 ≤ N) (hy : 0 ≤ y)
    (hNbound : N ≤ Real.sin σ * (1 + 6 * ε₁))
    (hκlam : κ * lam = 1 / (Real.sin σ) ^ 2)
    (hηlam : η ≤ 3 * ε₁ * lam) (hδκ : δ ≤ 3 * ε₁ * κ)
    (hub : (κ - δ) * (lam * y ^ 2 - η * N * y) ≤ 1) (hκδ : 0 < κ - δ) :
    y ≤ Real.sin σ * (1 + 7 * ε₁) := by
  have hκ0 : κ ≠ 0 := ne_of_gt hκ
  have hlam0 : lam ≠ 0 := ne_of_gt hlam
  have hsin0 : Real.sin σ ≠ 0 := ne_of_gt hsin
  have ha : lam * y ^ 2 ≤ (1 + 6 * ε₁) / κ + η * N * y := by
    have h2 : lam * y ^ 2 - η * N * y ≤ 1 / (κ - δ) := by
      rw [le_div_iff₀ hκδ]; linarith [hub]
    have h3 : 1 / (κ - δ) ≤ (1 + 6 * ε₁) / κ := by
      rw [div_le_div_iff₀ hκδ hκ]
      have h1 : δ * (1 + 6 * ε₁) ≤ 3 * ε₁ * κ * (1 + 6 * ε₁) :=
        mul_le_mul_of_nonneg_right hδκ (by linarith)
      have h2 : 18 * ε₁ ^ 2 * κ ≤ 3 * ε₁ * κ := by
        have h3 : ε₁ * (18 * ε₁) ≤ ε₁ * 3 :=
          mul_le_mul_of_nonneg_left (by linarith [hε₁'] : 18 * ε₁ ≤ 3) hε₁
        nlinarith [h3, hκ]
      nlinarith [h1, h2, hκ, hε₁, hε₁']
    linarith
  have hb : y ^ 2 ≤ (Real.sin σ) ^ 2 * (1 + 6 * ε₁)
      + (3 * ε₁ * (Real.sin σ * (1 + 6 * ε₁))) * y := by
    have h4 : y ^ 2 ≤ ((1 + 6 * ε₁) / κ + η * N * y) / lam := (le_div_iff₀ hlam).mpr (by rw [mul_comm]; exact ha)
    have h5 : ((1 + 6 * ε₁) / κ + η * N * y) / lam
        = (Real.sin σ) ^ 2 * (1 + 6 * ε₁) + (η / lam) * N * y := by
      rw [add_div, div_div, mul_div_assoc]
      have h6 : (1 + 6 * ε₁) / (κ * lam) = (Real.sin σ) ^ 2 * (1 + 6 * ε₁) := by
        rw [hκlam, one_div, div_inv_eq_mul]; ring
      rw [h6]; ring
    rw [h5] at h4
    have h7 : (η / lam) * N * y ≤ (3 * ε₁) * N * y := by
      have h8 : η / lam ≤ 3 * ε₁ := by rw [div_le_iff₀ hlam]; linarith [hηlam]
      have hNy : 0 ≤ N * y := mul_nonneg hN hy
      have := mul_le_mul_of_nonneg_right h8 hNy
      nlinarith [this]
    have h9 : (3 * ε₁) * N * y ≤ (3 * ε₁ * (Real.sin σ * (1 + 6 * ε₁))) * y := by
      have h10 : 0 ≤ 3 * ε₁ * y := by positivity
      nlinarith [hNbound, h10, hε₁, hy]
    linarith [h4, h7, h9]
  set A : ℝ := (Real.sin σ) ^ 2 * (1 + 6 * ε₁) with hA
  set B : ℝ := 3 * ε₁ * (Real.sin σ * (1 + 6 * ε₁)) with hB
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hb' : y ^ 2 ≤ A + B * y := by rw [hA, hB]; linarith [hb]
  have hq : (y - B / 2) ^ 2 ≤ A + B ^ 2 / 4 := by nlinarith [hb']
  have hle : y - B / 2 ≤ Real.sqrt (A + B ^ 2 / 4) := by
    by_cases hc : y - B / 2 < 0
    · nlinarith [Real.sqrt_nonneg (A + B ^ 2 / 4), hc]
    · push_neg at hc
      have h := Real.sqrt_le_sqrt hq
      rwa [Real.sqrt_sq hc] at h
  have hsub : Real.sqrt (A + B ^ 2 / 4) ≤ Real.sqrt A + Real.sqrt (B ^ 2 / 4) :=
    sqrt_add_le A (B ^ 2 / 4) hA0 (by positivity)
  have hsqrtB : Real.sqrt (B ^ 2 / 4) = B / 2 := by
    rw [show B ^ 2 / 4 = (B / 2) ^ 2 by ring, Real.sqrt_sq (by linarith)]
  have hsqrtA : Real.sqrt A ≤ Real.sin σ * (1 + 3 * ε₁) := by
    have h : Real.sqrt A = Real.sin σ * Real.sqrt (1 + 6 * ε₁) := by
      rw [hA, Real.sqrt_mul (sq_nonneg (Real.sin σ)), Real.sqrt_sq hsin.le]
    rw [h]
    have h2 : Real.sqrt (1 + 6 * ε₁) ≤ 1 + 3 * ε₁ := by
      have h3 := Real.sqrt_le_sqrt (show (1:ℝ) + 6 * ε₁ ≤ (1 + 3 * ε₁) ^ 2 by nlinarith [hε₁])
      rwa [Real.sqrt_sq (by linarith : (0:ℝ) ≤ 1 + 3 * ε₁)] at h3
    exact mul_le_mul_of_nonneg_left h2 hsin.le
  have hfinal : y ≤ Real.sin σ * (1 + 7 * ε₁) := by
    have h1 : y ≤ B + Real.sqrt A := by linarith [hle, hsub, hsqrtB.le]
    rw [hB] at h1
    nlinarith [h1, hε₁, hsin]
  exact hfinal

/-- **Step 3 (lower bound for the modulus).**  `sin σ/2 ≤ y`. -/
theorem twoCentre_y_lower {σ κ lam η δ N y ε₁ : ℝ}
    (hsin : 0 < Real.sin σ) (hε₁ : 0 ≤ ε₁) (hε₁' : ε₁ ≤ 1 / 24)
    (hκ : 0 < κ) (hlam : 0 < lam) (hη : 0 ≤ η) (hδ : 0 ≤ δ) (hN : 0 ≤ N) (hy : 0 ≤ y)
    (hNbound : N ≤ Real.sin σ * (1 + 6 * ε₁))
    (hκlam : κ * lam = 1 / (Real.sin σ) ^ 2)
    (hηlam : η ≤ 3 * ε₁ * lam) (hδκ : δ ≤ 3 * ε₁ * κ)
    (hlb : 1 ≤ (κ + δ) * (lam * y ^ 2 + η * N * y)) :
    Real.sin σ / 2 ≤ y := by
  by_contra hcon
  push_neg at hcon
  have hκδ : 0 < κ + δ := by linarith [hκ, hδκ, hε₁]
  have ha : 1 / (κ + δ) ≤ lam * y ^ 2 + η * N * y := by
    rw [div_le_iff₀ hκδ]; linarith [hlb]
  have hb : (1 - 3 * ε₁) / κ ≤ 1 / (κ + δ) := by
    rw [div_le_div_iff₀ hκ hκδ]
    have h1 : δ * (1 - 3 * ε₁) ≤ δ := by nlinarith [hδ, hε₁]
    nlinarith [h1, hδκ, hε₁, hκ]
  have hc : (1 - 3 * ε₁) / κ - η * N * y ≤ lam * y ^ 2 := by linarith [ha, hb]
  have hd : y ^ 2 ≥ (Real.sin σ) ^ 2 * (1 - 3 * ε₁) - (3 * ε₁ * (Real.sin σ * (1 + 6 * ε₁))) * y := by
    have he : ((1 - 3 * ε₁) / κ - η * N * y) / lam ≤ y ^ 2 := by
      rw [div_le_iff₀ hlam]; linarith [hc]
    have hf : ((1 - 3 * ε₁) / κ - η * N * y) / lam
        = (Real.sin σ) ^ 2 * (1 - 3 * ε₁) - (η / lam) * N * y := by
      rw [sub_div, div_div]
      have h6 : (1 - 3 * ε₁) / (κ * lam) = (Real.sin σ) ^ 2 * (1 - 3 * ε₁) := by
        rw [hκlam, one_div, div_inv_eq_mul]; ring
      rw [h6]
      ring
    rw [hf] at he
    have h7 : (η / lam) * N * y ≤ (3 * ε₁) * N * y := by
      have h8 : η / lam ≤ 3 * ε₁ := by rw [div_le_iff₀ hlam]; linarith [hηlam]
      have hNy : 0 ≤ N * y := mul_nonneg hN hy
      have := mul_le_mul_of_nonneg_right h8 hNy
      nlinarith [this]
    have h9 : (3 * ε₁) * N * y ≤ (3 * ε₁ * (Real.sin σ * (1 + 6 * ε₁))) * y := by
      have h10 : 0 ≤ 3 * ε₁ * y := by positivity
      nlinarith [hNbound, h10, hε₁, hy]
    linarith [he, h7, h9]
  have hf1 : (3 * ε₁ * (Real.sin σ * (1 + 6 * ε₁))) * y
      ≤ (3 * ε₁ * (Real.sin σ * (1 + 6 * ε₁))) * (Real.sin σ / 2) := by
    have hc2 : 0 ≤ 3 * ε₁ * (Real.sin σ * (1 + 6 * ε₁)) := by positivity
    exact mul_le_mul_of_nonneg_left (le_of_lt hcon) hc2
  have hf2 : (Real.sin σ) ^ 2 * (1 - 5 * ε₁)
      ≤ (Real.sin σ) ^ 2 * (1 - 3 * ε₁) - (3 * ε₁ * (Real.sin σ * (1 + 6 * ε₁))) * (Real.sin σ / 2) := by
    nlinarith [hε₁, hsin, sq_nonneg (Real.sin σ)]
  have hf3 : Real.sin σ * (1 - 5 * ε₁) ≤ y := by
    have h20 : Real.sqrt ((Real.sin σ) ^ 2 * (1 - 5 * ε₁)) ≤ Real.sqrt (y ^ 2) :=
      Real.sqrt_le_sqrt (le_trans hf2 (by linarith [hd, hf1]))
    have h21 : Real.sqrt ((Real.sin σ) ^ 2 * (1 - 5 * ε₁))
        = Real.sin σ * Real.sqrt (1 - 5 * ε₁) := by
      rw [Real.sqrt_mul (sq_nonneg (Real.sin σ)), Real.sqrt_sq hsin.le]
    rw [h21, Real.sqrt_sq hy] at h20
    have h22 : 1 - 5 * ε₁ ≤ Real.sqrt (1 - 5 * ε₁) := by
      have h23 : (0:ℝ) ≤ 1 - 5 * ε₁ := by linarith
      nlinarith [Real.sq_sqrt h23, Real.sqrt_nonneg (1 - 5 * ε₁), h23, hε₁]
    nlinarith [h20, h22, hsin, hε₁]
  nlinarith [hf3, hcon, hε₁, hsin]

/-- **The extraction: two-sided modulus bound.** -/
theorem modulus_two_sided {σ κ lam η δ N y ε₁ : ℝ}
    (hsin : 0 < Real.sin σ) (hε₁ : 0 ≤ ε₁) (hε₁' : ε₁ ≤ 1 / 24)
    (hκ : 0 < κ) (hlam : 0 < lam) (hη : 0 ≤ η) (hδ : 0 ≤ δ) (hN : 0 ≤ N) (hy : 0 ≤ y)
    (hκlam : κ * lam = 1 / (Real.sin σ) ^ 2)
    (hηlam : η ≤ 3 * ε₁ * lam) (hδκ : δ ≤ 3 * ε₁ * κ)
    (hN2 : (κ - δ) * (lam - η) * N ^ 2 ≤ 1)
    (hub : (κ - δ) * (lam * y ^ 2 - η * N * y) ≤ 1)
    (hlb : 1 ≤ (κ + δ) * (lam * y ^ 2 + η * N * y)) :
    Real.sin σ / 2 ≤ y ∧ y ≤ Real.sin σ * (1 + 7 * ε₁) := by
  have h3ε : 3 * ε₁ ≤ 1 / 8 := by linarith
  have hδlt : δ < κ := by nlinarith [hδκ, hκ, h3ε]
  have hκδ : 0 < κ - δ := by linarith
  have hNbound := twoCentre_N_bound hsin hε₁ hε₁' hκ hlam hη hδ hN hκlam hηlam hδκ hN2
  exact ⟨twoCentre_y_lower hsin hε₁ hε₁' hκ hlam hη hδ hN hy hNbound hκlam hηlam hδκ hlb,
    twoCentre_y_upper hsin hε₁ hε₁' hκ hlam hη hN hy hNbound hκlam hηlam hδκ hub hκδ⟩

/-! ## The trigonometric facts at the two-scale choice `τ = 2σ`

For `τ = 2σ` (with `0 < σ`, `2σ < π`) one has `κ = 2cot σ`, `λ = 1/sin(2σ)`, hence `κλ = 1/sin²σ`;
moreover `η = ε₁(1/sin σ + 1/sin 2σ) ≤ 3ε₁λ` (because `sin 2σ = 2 sin σ cos σ`) and
`δ = 2ε₁/sin σ ≤ 3ε₁κ` (because `cot σ ≥ 1/(2 sin σ)` as soon as `cos σ ≥ 1/2`). -/

/-- `twoK σ (2σ) = 2 cot σ`. -/
theorem twoK_two_mul (σ : ℝ) : twoK σ (2 * σ) = 2 * Real.cot σ := by
  simp only [twoK]
  rw [show 2 * σ - σ = σ by ring]
  ring

/-- `twoD ε₁ σ (2σ) = ε₁ (2/sin σ)`. -/
theorem twoD_two_mul (ε₁ σ : ℝ) : twoD ε₁ σ (2 * σ) = ε₁ * (2 / Real.sin σ) := by
  simp only [twoD]
  rw [show 2 * σ - σ = σ by ring]
  ring

/-- `twoE ε₁ σ (2σ) = ε₁ (1/sin σ + 1/sin(2σ))`. -/
theorem twoE_two_mul (ε₁ σ : ℝ) :
    twoE ε₁ σ (2 * σ) = ε₁ * (1 / Real.sin σ + 1 / Real.sin (2 * σ)) := by
  simp only [twoE]

/-- `twoL σ (2σ) = 1/sin(2σ)`: the numerical identity `cot σ - cot 2σ = 1/sin 2σ`. -/
theorem twoL_two_mul {σ : ℝ} (hσ : 0 < σ) (h2σ : 2 * σ < Real.pi) :
    twoL σ (2 * σ) = 1 / Real.sin (2 * σ) := by
  have hspos : 0 < Real.sin σ := Real.sin_pos_of_pos_of_lt_pi hσ (by linarith [Real.pi_pos, h2σ])
  have hs2pos : 0 < Real.sin (2 * σ) := Real.sin_pos_of_pos_of_lt_pi (by linarith) h2σ
  have hsin0 : Real.sin σ ≠ 0 := ne_of_gt hspos
  have hsin2 : Real.sin (2 * σ) ≠ 0 := ne_of_gt hs2pos
  have hnum : Real.cos σ * Real.sin (2 * σ) - Real.sin σ * Real.cos (2 * σ) = Real.sin σ := by
    have h := Real.sin_sub (2 * σ) σ
    rw [show (2:ℝ) * σ - σ = σ by ring] at h
    linarith [h]
  simp only [twoL]
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin,
    div_sub_div _ _ hsin0 hsin2, hnum]
  field_simp

/-- `κ λ = 1/sin²σ` at `τ = 2σ`. -/
theorem twoK_mul_twoL {σ : ℝ} (hσ : 0 < σ) (h2σ : 2 * σ < Real.pi) :
    twoK σ (2 * σ) * twoL σ (2 * σ) = 1 / (Real.sin σ) ^ 2 := by
  have hspos : 0 < Real.sin σ := Real.sin_pos_of_pos_of_lt_pi hσ (by linarith [Real.pi_pos, h2σ])
  have hsin2 : Real.sin (2 * σ) = 2 * Real.sin σ * Real.cos σ := Real.sin_two_mul σ
  have hcospos : 0 < Real.cos σ := by
    have h : 0 < Real.sin (2 * σ) := Real.sin_pos_of_pos_of_lt_pi (by linarith) h2σ
    rw [hsin2] at h; nlinarith
  rw [twoK_two_mul, twoL_two_mul hσ h2σ, hsin2, Real.cot_eq_cos_div_sin]
  field_simp

/-- `η ≤ 3 ε₁ λ` at `τ = 2σ`. -/
theorem twoE_le_twoL {σ ε₁ : ℝ} (hε₁ : 0 ≤ ε₁) (hσ : 0 < σ) (h2σ : 2 * σ < Real.pi)
    (hcos : Real.cos σ ≥ 1 / 2) :
    twoE ε₁ σ (2 * σ) ≤ 3 * ε₁ * twoL σ (2 * σ) := by
  have hspos : 0 < Real.sin σ := Real.sin_pos_of_pos_of_lt_pi hσ (by linarith [Real.pi_pos, h2σ])
  have hcpos : 0 < Real.cos σ := by linarith
  have hsin2 : Real.sin (2 * σ) = 2 * Real.sin σ * Real.cos σ := Real.sin_two_mul σ
  rw [twoE_two_mul, twoL_two_mul hσ h2σ, hsin2]
  have hkey : 1 / Real.sin σ ≤ 1 / (Real.sin σ * Real.cos σ) :=
    one_div_le_one_div_of_le (by positivity : (0:ℝ) < Real.sin σ * Real.cos σ)
      (by nlinarith [hspos, hcpos, hcos, Real.cos_le_one σ])
  have h3 : (1:ℝ) / Real.sin σ + 1 / (2 * Real.sin σ * Real.cos σ)
      ≤ 3 * (1 / (2 * Real.sin σ * Real.cos σ)) := by
    have h2 : 1 / (Real.sin σ * Real.cos σ) = 2 * (1 / (2 * Real.sin σ * Real.cos σ)) := by
      field_simp
    linarith [hkey, h2.le, h2.ge]
  calc ε₁ * (1 / Real.sin σ + 1 / (2 * Real.sin σ * Real.cos σ))
      ≤ ε₁ * (3 * (1 / (2 * Real.sin σ * Real.cos σ))) := mul_le_mul_of_nonneg_left h3 hε₁
    _ = 3 * ε₁ * (1 / (2 * Real.sin σ * Real.cos σ)) := by ring

/-- `δ ≤ 3 ε₁ κ` at `τ = 2σ`. -/
theorem twoD_le_twoK {σ ε₁ : ℝ} (hε₁ : 0 ≤ ε₁) (hσ : 0 < σ) (h2σ : 2 * σ < Real.pi)
    (hcos : Real.cos σ ≥ 1 / 2) :
    twoD ε₁ σ (2 * σ) ≤ 3 * ε₁ * twoK σ (2 * σ) := by
  have hspos : 0 < Real.sin σ := Real.sin_pos_of_pos_of_lt_pi hσ (by linarith [Real.pi_pos, h2σ])
  have hcot : Real.cot σ = Real.cos σ / Real.sin σ := Real.cot_eq_cos_div_sin σ
  rw [twoD_two_mul, twoK_two_mul, hcot]
  have h1 : 2 / Real.sin σ ≤ 3 * (2 * (Real.cos σ / Real.sin σ)) := by
    have h2 : 2 ≤ 3 * (2 * Real.cos σ) := by nlinarith [hcos]
    have h3 : 2 / Real.sin σ ≤ (3 * (2 * Real.cos σ)) / Real.sin σ := by
      rw [div_le_div_iff₀ hspos hspos]
      exact mul_le_mul_of_nonneg_right h2 (le_of_lt hspos)
    calc 2 / Real.sin σ ≤ (3 * (2 * Real.cos σ)) / Real.sin σ := h3
      _ = 3 * (2 * (Real.cos σ / Real.sin σ)) := by ring
  calc ε₁ * (2 / Real.sin σ) ≤ ε₁ * (3 * (2 * (Real.cos σ / Real.sin σ))) :=
        mul_le_mul_of_nonneg_left h1 hε₁
    _ = 3 * ε₁ * (2 * (Real.cos σ / Real.sin σ)) := by ring

/-- **The modulus bounds for `σ ≤ ρ₀/2` from the two-centre data at `τ = 2σ`.** -/
theorem modulus_of_twoCentre {c σ ε₁ N y : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hσ : 0 < σ)
    (h2σ : 2 * σ ≤ Real.pi - Real.arccos (1 - c))
    (hε₁ : 0 ≤ ε₁) (hε₁' : ε₁ ≤ 1 / 24) (hcos : Real.cos σ ≥ 1 / 2)
    (hN : 0 ≤ N) (hy : 0 ≤ y)
    (hN2 : (twoK σ (2 * σ) - twoD ε₁ σ (2 * σ)) *
      (twoL σ (2 * σ) - twoE ε₁ σ (2 * σ)) * N ^ 2 ≤ 1)
    (hub : (twoK σ (2 * σ) - twoD ε₁ σ (2 * σ)) *
      (twoL σ (2 * σ) * y ^ 2 - twoE ε₁ σ (2 * σ) * N * y) ≤ 1)
    (hlb : 1 ≤ (twoK σ (2 * σ) + twoD ε₁ σ (2 * σ)) *
      (twoL σ (2 * σ) * y ^ 2 + twoE ε₁ σ (2 * σ) * N * y)) :
    Real.sin σ / 2 ≤ y ∧ y ≤ Real.sin σ * (1 + 7 * ε₁) := by
  have hρ : Real.pi - Real.arccos (1 - c) < Real.pi := by
    have h : 0 < Real.arccos (1 - c) := Real.arccos_pos.mpr (by linarith)
    linarith
  have h2π : 2 * σ < Real.pi := lt_of_le_of_lt h2σ hρ
  have hspos : 0 < Real.sin σ := Real.sin_pos_of_pos_of_lt_pi hσ (by linarith)
  have hLpos : 0 < twoL σ (2 * σ) := by
    rw [twoL_two_mul hσ h2π]
    exact one_div_pos.mpr (Real.sin_pos_of_pos_of_lt_pi (by linarith) h2π)
  have hKpos : 0 < twoK σ (2 * σ) := by
    rw [twoK_two_mul, Real.cot_eq_cos_div_sin]
    have : 0 < Real.cos σ := by linarith
    positivity
  have hDnn : 0 ≤ twoD ε₁ σ (2 * σ) := by
    rw [twoD_two_mul]
    exact mul_nonneg hε₁ (by positivity)
  have hEnn : 0 ≤ twoE ε₁ σ (2 * σ) := by
    rw [twoE_two_mul]
    have h2 := Real.sin_pos_of_pos_of_lt_pi (by linarith) h2π
    positivity
  exact modulus_two_sided hspos hε₁ hε₁' hKpos hLpos hEnn hDnn hN hy
    (twoK_mul_twoL hσ h2π) (twoE_le_twoL hε₁ hσ h2π hcos) (twoD_le_twoK hε₁ hσ h2π hcos)
    hN2 hub hlb

/-! ## The sharp lower bound of the two-centre extraction

The extraction `modulus_two_sided` above gives the lower bound `sin σ / 2 ≤ y`, which is all that the
propagation from the anchor `π/3` needs *if* the propagation factor is `≥ 1`.  It is not: the factor
`(tan (t/2) / tan (δ/2)) ^ (-ε₁)` is slightly below `1` for `t > δ`.  The anchor must therefore
carry the sharper bound `sin σ (1 - 5ε₁) ≤ y`, which is what the same two-centre data gives (the
proof of `twoCentre_y_lower` in fact produces it, with room to spare). -/

/-- **Step 3' (sharpened lower bound for the modulus).**  `sin σ (1 - 5ε₁) ≤ y`. -/
theorem twoCentre_y_lower_sharp {σ κ lam η δ N y ε₁ : ℝ}
    (hsin : 0 < Real.sin σ) (hε₁ : 0 ≤ ε₁) (hε₁' : ε₁ ≤ 1 / 24)
    (hκ : 0 < κ) (hlam : 0 < lam) (hη : 0 ≤ η) (hδ : 0 ≤ δ) (hN : 0 ≤ N) (hy : 0 ≤ y)
    (hNbound : N ≤ Real.sin σ * (1 + 6 * ε₁))
    (hκlam : κ * lam = 1 / (Real.sin σ) ^ 2)
    (hηlam : η ≤ 3 * ε₁ * lam) (hδκ : δ ≤ 3 * ε₁ * κ)
    (hlb : 1 ≤ (κ + δ) * (lam * y ^ 2 + η * N * y)) :
    Real.sin σ * (1 - 5 * ε₁) ≤ y := by
  by_contra hcon
  push_neg at hcon
  have hκδ : 0 < κ + δ := by
    have : 3 * ε₁ ≤ 1 / 8 := by linarith
    nlinarith [hκ, hδκ, hε₁]
  have ha : 1 / (κ + δ) ≤ lam * y ^ 2 + η * N * y := by
    rw [div_le_iff₀ hκδ]; linarith [hlb]
  have hb : (1 - 3 * ε₁) / κ ≤ 1 / (κ + δ) := by
    rw [div_le_div_iff₀ hκ hκδ]
    have h1 : δ * (1 - 3 * ε₁) ≤ δ := by nlinarith [hδ, hε₁]
    nlinarith [h1, hδκ, hε₁, hκ]
  have hc : (1 - 3 * ε₁) / κ - η * N * y ≤ lam * y ^ 2 := by linarith [ha, hb]
  have hd : (Real.sin σ) ^ 2 * (1 - 3 * ε₁)
      - (3 * ε₁ * (Real.sin σ * (1 + 6 * ε₁))) * y ≤ y ^ 2 := by
    have he : ((1 - 3 * ε₁) / κ - η * N * y) / lam ≤ y ^ 2 := by
      rw [div_le_iff₀ hlam]; linarith [hc]
    have hf : ((1 - 3 * ε₁) / κ - η * N * y) / lam
        = (Real.sin σ) ^ 2 * (1 - 3 * ε₁) - (η / lam) * N * y := by
      rw [sub_div, div_div]
      have h6 : (1 - 3 * ε₁) / (κ * lam) = (Real.sin σ) ^ 2 * (1 - 3 * ε₁) := by
        rw [hκlam, one_div, div_inv_eq_mul]; ring
      rw [h6]; ring
    rw [hf] at he
    have h7 : (η / lam) * N * y ≤ (3 * ε₁) * N * y := by
      have h8 : η / lam ≤ 3 * ε₁ := by rw [div_le_iff₀ hlam]; linarith [hηlam]
      have hNy : 0 ≤ N * y := mul_nonneg hN hy
      have := mul_le_mul_of_nonneg_right h8 hNy
      nlinarith [this]
    have h9 : (3 * ε₁) * N * y ≤ (3 * ε₁ * (Real.sin σ * (1 + 6 * ε₁))) * y := by
      have h10 : 0 ≤ 3 * ε₁ * y := by positivity
      nlinarith [hNbound, h10, hε₁, hy]
    linarith [he, h7, h9]
  rcases eq_or_lt_of_le hε₁ with hε0 | hεpos
  · -- `ε₁ = 0`: the bound is `sin σ ≤ y`
    rw [← hε0] at hd hcon
    simp only [mul_zero, sub_zero, mul_one, add_zero, zero_mul] at hd hcon
    have hA : y * y ≤ y * Real.sin σ := mul_le_mul_of_nonneg_left hcon.le hy
    have hB : y * Real.sin σ < Real.sin σ * Real.sin σ :=
      mul_lt_mul_of_pos_right hcon hsin
    nlinarith [hd, hA, hB]
  · have hcoef : 0 < 3 * ε₁ * (Real.sin σ * (1 + 6 * ε₁)) := by positivity
    have hu : 0 < Real.sin σ * (1 - 5 * ε₁) := mul_pos hsin (by linarith)
    have hy2 : y ^ 2 < (Real.sin σ * (1 - 5 * ε₁)) ^ 2 := by
      have h1 : y * y ≤ (Real.sin σ * (1 - 5 * ε₁)) * y :=
        mul_le_mul_of_nonneg_right hcon.le hy
      have h2 : (Real.sin σ * (1 - 5 * ε₁)) * y < (Real.sin σ * (1 - 5 * ε₁))
          * (Real.sin σ * (1 - 5 * ε₁)) := mul_lt_mul_of_pos_left hcon hu
      nlinarith [h1, h2]
    have hstrict : (3 * ε₁ * (Real.sin σ * (1 + 6 * ε₁))) * y
        < (3 * ε₁ * (Real.sin σ * (1 + 6 * ε₁))) * (Real.sin σ * (1 - 5 * ε₁)) :=
      mul_lt_mul_of_pos_left hcon hcoef
    have hkey : (1 - 3 * ε₁) < (1 - 5 * ε₁) ^ 2 + 3 * ε₁ * (1 + 6 * ε₁) * (1 - 5 * ε₁) := by
      have h1 : (Real.sin σ) ^ 2 * (1 - 3 * ε₁)
          < (Real.sin σ) ^ 2 * ((1 - 5 * ε₁) ^ 2 + 3 * ε₁ * (1 + 6 * ε₁) * (1 - 5 * ε₁)) := by
        have hle : (Real.sin σ) ^ 2 * (1 - 3 * ε₁)
            ≤ y ^ 2 + (3 * ε₁ * (Real.sin σ * (1 + 6 * ε₁))) * y := by linarith [hd]
        nlinarith [hle, hy2, hstrict, sq_nonneg (Real.sin σ)]
      exact lt_of_mul_lt_mul_left h1 (sq_nonneg (Real.sin σ))
    nlinarith [hkey, hε₁, hε₁', hεpos]

/-- **The sharp two-sided modulus bound.** -/
theorem modulus_two_sided_sharp {σ κ lam η δ N y ε₁ : ℝ}
    (hsin : 0 < Real.sin σ) (hε₁ : 0 ≤ ε₁) (hε₁' : ε₁ ≤ 1 / 24)
    (hκ : 0 < κ) (hlam : 0 < lam) (hη : 0 ≤ η) (hδ : 0 ≤ δ) (hN : 0 ≤ N) (hy : 0 ≤ y)
    (hκlam : κ * lam = 1 / (Real.sin σ) ^ 2)
    (hηlam : η ≤ 3 * ε₁ * lam) (hδκ : δ ≤ 3 * ε₁ * κ)
    (hN2 : (κ - δ) * (lam - η) * N ^ 2 ≤ 1)
    (hub : (κ - δ) * (lam * y ^ 2 - η * N * y) ≤ 1)
    (hlb : 1 ≤ (κ + δ) * (lam * y ^ 2 + η * N * y)) :
    Real.sin σ * (1 - 5 * ε₁) ≤ y ∧ y ≤ Real.sin σ * (1 + 7 * ε₁) := by
  have h3ε : 3 * ε₁ ≤ 1 / 8 := by linarith
  have hδlt : δ < κ := by nlinarith [hδκ, hκ, h3ε]
  have hκδ : 0 < κ - δ := by linarith
  have hNbound := twoCentre_N_bound hsin hε₁ hε₁' hκ hlam hη hδ hN hκlam hηlam hδκ hN2
  exact ⟨twoCentre_y_lower_sharp hsin hε₁ hε₁' hκ hlam hη hδ hN hy hNbound hκlam hηlam hδκ hlb,
    twoCentre_y_upper hsin hε₁ hε₁' hκ hlam hη hN hy hNbound hκlam hηlam hδκ hub hκδ⟩

/-- **The sharp modulus bounds for `σ ≤ ρ₀/2` from the two-centre data at `τ = 2σ`.** -/
theorem modulus_of_twoCentre_sharp {c σ ε₁ N y : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hσ : 0 < σ)
    (h2σ : 2 * σ ≤ Real.pi - Real.arccos (1 - c))
    (hε₁ : 0 ≤ ε₁) (hε₁' : ε₁ ≤ 1 / 24) (hcos : Real.cos σ ≥ 1 / 2)
    (hN : 0 ≤ N) (hy : 0 ≤ y)
    (hN2 : (twoK σ (2 * σ) - twoD ε₁ σ (2 * σ)) *
      (twoL σ (2 * σ) - twoE ε₁ σ (2 * σ)) * N ^ 2 ≤ 1)
    (hub : (twoK σ (2 * σ) - twoD ε₁ σ (2 * σ)) *
      (twoL σ (2 * σ) * y ^ 2 - twoE ε₁ σ (2 * σ) * N * y) ≤ 1)
    (hlb : 1 ≤ (twoK σ (2 * σ) + twoD ε₁ σ (2 * σ)) *
      (twoL σ (2 * σ) * y ^ 2 + twoE ε₁ σ (2 * σ) * N * y)) :
    Real.sin σ * (1 - 5 * ε₁) ≤ y ∧ y ≤ Real.sin σ * (1 + 7 * ε₁) := by
  have hρ : Real.pi - Real.arccos (1 - c) < Real.pi := by
    have h : 0 < Real.arccos (1 - c) := Real.arccos_pos.mpr (by linarith)
    linarith
  have h2π : 2 * σ < Real.pi := lt_of_le_of_lt h2σ hρ
  have hspos : 0 < Real.sin σ := Real.sin_pos_of_pos_of_lt_pi hσ (by linarith)
  have hLpos : 0 < twoL σ (2 * σ) := by
    rw [twoL_two_mul hσ h2π]
    exact one_div_pos.mpr (Real.sin_pos_of_pos_of_lt_pi (by linarith) h2π)
  have hKpos : 0 < twoK σ (2 * σ) := by
    rw [twoK_two_mul, Real.cot_eq_cos_div_sin]
    have : 0 < Real.cos σ := by linarith
    positivity
  have hDnn : 0 ≤ twoD ε₁ σ (2 * σ) := by
    rw [twoD_two_mul]
    exact mul_nonneg hε₁ (by positivity)
  have hEnn : 0 ≤ twoE ε₁ σ (2 * σ) := by
    rw [twoE_two_mul]
    have h2 := Real.sin_pos_of_pos_of_lt_pi (by linarith) h2π
    positivity
  exact modulus_two_sided_sharp hspos hε₁ hε₁' hKpos hLpos hEnn hDnn hN hy
    (twoK_mul_twoL hσ h2π) (twoE_le_twoL hε₁ hσ h2π hcos) (twoD_le_twoK hε₁ hσ h2π hcos)
    hN2 hub hlb

/-! ## The arithmetic of the two ranges

For `t ≤ π/3` the two-centre extraction itself is already strong enough, and only the elementary
comparison `7ε₁ sin t ≤ 3ε₁(1 + log²(2/t))t + 3t³` is needed.  For `t ∈ (π/3, ρ₀]` the anchored
comparison contributes the factor `(tan (t/2)/tan (π/6))^{ε₁}`, which is bounded by `1111/1000`
using `4 ε₁ π < c ≤ 1/4` (whence `ε₁ ≤ c/12`) and `tan (t/2) ≤ √(2/c)`. -/

/-- `cos (ρ₀/2) = √(c/2)`. -/
lemma cos_half_rho0 {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) :
    Real.cos ((Real.pi - Real.arccos (1 - c)) / 2) = Real.sqrt (c / 2) := by
  have h1 : (1 : ℝ) - c ≤ 1 := by linarith
  have h2 : -1 ≤ (1 : ℝ) - c := by linarith
  have hle : Real.pi - Real.arccos (1 - c) ≤ Real.pi := by
    have := Real.arccos_nonneg (1 - c); linarith
  have hge : -Real.pi ≤ Real.pi - Real.arccos (1 - c) := by
    have := Real.arccos_le_pi (1 - c); linarith [Real.pi_pos]
  rw [Real.cos_half hge hle, Real.cos_pi_sub, Real.cos_arccos h2 h1]
  congr 1
  ring

/-- `0 < arccos (1 - c)` for `0 < c`. -/
lemma arccos_one_sub_pos {c : ℝ} (hc : 0 < c) : 0 < Real.arccos (1 - c) :=
  Real.arccos_pos.mpr (by linarith)

/-- `ρ₀ < π` for `0 < c`. -/
lemma rho0_lt_pi' {c : ℝ} (hc : 0 < c) : rho0 c < Real.pi := by
  have h := arccos_one_sub_pos hc
  rw [rho0]; linarith

/-- `tan (t/2) ≤ √(2/c)` for `t ≤ ρ₀`. -/
lemma tan_half_le {c t : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4)
    (ht : Real.pi / 3 ≤ t) (htρ : t ≤ Real.pi - Real.arccos (1 - c)) :
    Real.tan (t / 2) ≤ Real.sqrt (2 / c) := by
  have hc2 : 0 < c / 2 := by linarith
  have hρ0le : Real.pi - Real.arccos (1 - c) ≤ Real.pi := le_of_lt (rho0_lt_pi' hc)
  have hcos : Real.sqrt (c / 2) ≤ Real.cos (t / 2) := by
    rw [← cos_half_rho0 hc hc1]
    refine Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) ?_ ?_
    · linarith
    · linarith
  have hcpos2 : 0 < Real.cos (t / 2) := lt_of_lt_of_le (Real.sqrt_pos_of_pos hc2) hcos
  have hsin1 : Real.sin (t / 2) ≤ 1 := Real.sin_le_one _
  rw [Real.tan_eq_sin_div_cos]
  have h1 : Real.sin (t / 2) / Real.cos (t / 2) ≤ 1 / Real.cos (t / 2) := by
    rw [div_le_div_iff₀ hcpos2 hcpos2]
    nlinarith [hsin1, hcpos2]
  have h2 : 1 / Real.cos (t / 2) ≤ 1 / Real.sqrt (c / 2) :=
    one_div_le_one_div_of_le (Real.sqrt_pos_of_pos hc2) hcos
  have h3 : 1 / Real.sqrt (c / 2) = Real.sqrt (2 / c) := by
    rw [Real.sqrt_div (le_of_lt hc) 2, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2) c]
    field_simp
  linarith [h1, h2, h3.le]

/-- `log (tan (t/2)) ≤ (1/2) log (2/c)`. -/
lemma log_tan_half_le {c t : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4)
    (ht : Real.pi / 3 ≤ t) (htρ : t ≤ Real.pi - Real.arccos (1 - c)) :
    Real.log (Real.tan (t / 2)) ≤ (1 / 2) * Real.log (2 / c) := by
  have ht0 : 0 < t := by linarith [Real.pi_gt_three]
  have htπ : t < Real.pi := lt_of_le_of_lt htρ (rho0_lt_pi' hc)
  have htanpos : 0 < Real.tan (t / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)
  have h2c : 0 < 2 / c := by positivity
  have h1 := tan_half_le hc hc1 ht htρ
  have h2 : Real.log (Real.tan (t / 2)) ≤ Real.log (Real.sqrt (2 / c)) :=
    Real.log_le_log htanpos h1
  rw [Real.log_sqrt (le_of_lt h2c)] at h2
  linarith [h2]

/-- `log (tan (t/2) / tan (π/6)) ≤ (1/2) log (2/c) + 1`. -/
lemma log_tan_ratio_le {c t : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4)
    (ht : Real.pi / 3 ≤ t) (htρ : t ≤ Real.pi - Real.arccos (1 - c)) :
    Real.log (Real.tan (t / 2) / Real.tan (Real.pi / 6))
      ≤ (1 / 2) * Real.log (2 / c) + 1 := by
  have ht0 : 0 < t := by linarith [Real.pi_gt_three]
  have htπ : t < Real.pi := lt_of_le_of_lt htρ (rho0_lt_pi' hc)
  have htanpos : 0 < Real.tan (t / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)
  have h6 : Real.tan (Real.pi / 6) = 1 / Real.sqrt 3 := Real.tan_pi_div_six
  have h6pos : 0 < Real.tan (Real.pi / 6) := by rw [h6]; positivity
  have hsqrt3 : 0 < Real.sqrt 3 := Real.sqrt_pos_of_pos (by norm_num)
  have hlog : Real.log (Real.tan (t / 2) / Real.tan (Real.pi / 6))
      = Real.log (Real.tan (t / 2)) + Real.log (Real.sqrt 3) := by
    rw [Real.log_div (ne_of_gt htanpos) (ne_of_gt h6pos), h6,
      Real.log_div one_ne_zero (ne_of_gt hsqrt3), Real.log_one]
    ring
  rw [hlog]
  have h1 := log_tan_half_le hc hc1 ht htρ
  have h2 : Real.log (Real.sqrt 3) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos hsqrt3
    have h3 : Real.sqrt 3 - 1 ≤ 1 := by
      have h4 : Real.sqrt 3 ≤ 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
      linarith
    linarith
  linarith

/-- **The propagation factor is at most `1111/1000`.** -/
lemma tan_ratio_rpow_le {c ε₁ t : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c) (ht : Real.pi / 3 ≤ t) (htρ : t ≤ rho0 c) :
    (Real.tan (t / 2) / Real.tan (Real.pi / 6)) ^ ε₁ ≤ 1111 / 1000 := by
  have ht0 : 0 < t := by linarith [Real.pi_gt_three]
  have htπ : t < Real.pi := lt_of_le_of_lt htρ (rho0_lt_pi' hc)
  have htanpos : 0 < Real.tan (t / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)
  have h6pos : 0 < Real.tan (Real.pi / 6) := by rw [Real.tan_pi_div_six]; positivity
  have hratio : 0 < Real.tan (t / 2) / Real.tan (Real.pi / 6) := div_pos htanpos h6pos
  have hlog := log_tan_ratio_le hc hc1 ht htρ
  have hε12 : ε₁ ≤ c / 12 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 12)]
    nlinarith [hnum2, Real.pi_gt_three]
  have h2c : 0 < 2 / c := by positivity
  have hlog2 : Real.log (2 / c) ≤ 2 / c - 1 := Real.log_le_sub_one_of_pos h2c
  have hkey : ε₁ * Real.log (Real.tan (t / 2) / Real.tan (Real.pi / 6)) ≤ 3 / 32 := by
    have h1 : ε₁ * Real.log (Real.tan (t / 2) / Real.tan (Real.pi / 6))
        ≤ ε₁ * ((1 / 2) * Real.log (2 / c) + 1) := mul_le_mul_of_nonneg_left hlog hε₁
    have h3 : (1 / 2) * Real.log (2 / c) + 1 ≤ (1 / 2) * (2 / c - 1) + 1 := by linarith
    have h7 : ε₁ * ((1 / 2) * Real.log (2 / c) + 1)
        ≤ ε₁ * ((1 / 2) * (2 / c - 1) + 1) := mul_le_mul_of_nonneg_left h3 hε₁
    have h4 : ε₁ * ((1 / 2) * (2 / c - 1) + 1) ≤ (c / 12) * ((1 / 2) * (2 / c - 1) + 1) :=
      mul_le_mul_of_nonneg_right hε12 (by
        have hc2 : (1 : ℝ) ≤ 2 / c := by
          rw [le_div_iff₀ hc]; linarith [hc1]
        have : (0 : ℝ) ≤ 2 / c - 1 := by linarith
        have hlog2' : (0 : ℝ) ≤ (1 / 2) * (2 / c - 1) + 1 := by linarith
        linarith)
    have h5 : (c / 12) * ((1 / 2) * (2 / c - 1) + 1) = 1 / 12 + c / 24 := by
      field_simp; ring
    have h6 : 1 / 12 + c / 24 ≤ 3 / 32 := by nlinarith [hc1]
    linarith [h1, h7, h4, h5.le, h6]
  rw [Real.rpow_def_of_pos hratio ε₁]
  have h8 : Real.log (Real.tan (t / 2) / Real.tan (Real.pi / 6)) * ε₁ ≤ 3 / 32 := by
    rw [mul_comm]; exact hkey
  have h9 : Real.exp (Real.log (Real.tan (t / 2) / Real.tan (Real.pi / 6)) * ε₁)
      ≤ Real.exp (3 / 32) := Real.exp_le_exp.mpr h8
  have hx : 0 < (1111 : ℝ) / 1000 := by norm_num
  have h10 : Real.exp (3 / 32) ≤ 1111 / 1000 := by
    have hlow : 1 - 1 / ((1111 : ℝ) / 1000) ≤ Real.log ((1111 : ℝ) / 1000) := by
      have h := Real.log_le_sub_one_of_pos (show 0 < 1 / ((1111 : ℝ) / 1000) by positivity)
      rw [Real.log_div one_ne_zero (ne_of_gt hx), Real.log_one] at h
      linarith
    have h11 : (1 : ℝ) - 1 / ((1111 : ℝ) / 1000) = 111 / 1111 := by norm_num
    rw [h11] at hlow
    have h12 : (3 : ℝ) / 32 ≤ 111 / 1111 := by norm_num
    have h13 : (3 : ℝ) / 32 ≤ Real.log ((1111 : ℝ) / 1000) := le_trans h12 hlow
    exact (Real.le_log_iff_exp_le hx).mp h13
  linarith [h9, h10]

/-- **The arithmetic in the range `t ≤ π/3`.** -/
lemma radial_num_small {ε₁ t : ℝ} (hε₁ : 0 ≤ ε₁) (hε₁' : ε₁ ≤ 1 / 24) (ht0 : 0 < t)
    (ht : t ≤ Real.pi / 3) :
    Real.sin t * (1 + 7 * ε₁)
      ≤ Real.sin t + 3 * (ε₁ * (1 + (Real.log (2 / t)) ^ 2) + t ^ 2) * t := by
  have hsint : 0 ≤ Real.sin t :=
    le_of_lt (Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [Real.pi_pos]))
  by_cases h : (1 / 2 : ℝ) ≤ t
  · have ht3 : ((1 : ℝ) / 2) ^ 3 ≤ t ^ 3 :=
      pow_le_pow_left₀ (by norm_num) h 3
    have h2 : 7 * ε₁ ≤ 3 * t ^ 3 := by
      have h2a : 7 * ε₁ ≤ 7 * (1 / 24) := by linarith [hε₁']
      nlinarith [h2a, ht3]
    have h4 : Real.sin t ≤ 1 := Real.sin_le_one t
    have h3 : 7 * ε₁ * Real.sin t ≤ 3 * t ^ 3 := by
      have h5 : 7 * ε₁ * Real.sin t ≤ (3 * t ^ 3) * 1 :=
        mul_le_mul h2 h4 hsint (by positivity)
      linarith [h5]
    have h6 : 0 ≤ ε₁ * (1 + (Real.log (2 / t)) ^ 2) * t := by positivity
    have h7 : Real.sin t * (1 + 7 * ε₁) = Real.sin t + 7 * ε₁ * Real.sin t := by ring
    have h8 : Real.sin t + 3 * (ε₁ * (1 + (Real.log (2 / t)) ^ 2) + t ^ 2) * t
        = Real.sin t + 3 * ε₁ * (1 + (Real.log (2 / t)) ^ 2) * t + 3 * t ^ 3 := by ring
    rw [h7, h8]
    linarith [h3, h6]
  · push_neg at h
    have hlog : (7 : ℝ) / 3 ≤ 1 + (Real.log (2 / t)) ^ 2 := by
      have h1 : Real.log 4 ≤ Real.log (2 / t) := by
        apply Real.log_le_log (by norm_num)
        rw [le_div_iff₀ ht0]; linarith
      have h2 : (4 : ℝ) / 3 ≤ Real.log 4 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        push_cast
        nlinarith [Real.log_two_gt_d9]
      have h3 : (4 : ℝ) / 3 ≤ Real.log (2 / t) := le_trans h2 h1
      have h4 : (0 : ℝ) ≤ Real.log (2 / t) := le_trans (by norm_num) h3
      have h5 : ((4 : ℝ) / 3) * ((4 : ℝ) / 3) ≤ (Real.log (2 / t)) * (Real.log (2 / t)) := by
        nlinarith [h3, h4]
      nlinarith [h5]
    have hsle : Real.sin t ≤ t := Real.sin_le ht0.le
    have h11 : 7 * ε₁ * Real.sin t ≤ 7 * ε₁ * t := by
      have h14 : (0 : ℝ) ≤ 7 * ε₁ := by linarith
      exact mul_le_mul_of_nonneg_left hsle h14
    have h12 : 7 * ε₁ * t ≤ 3 * ε₁ * (1 + (Real.log (2 / t)) ^ 2) * t := by
      have h13 : (7 : ℝ) / 3 ≤ 1 + (Real.log (2 / t)) ^ 2 := hlog
      have h15 : (0 : ℝ) ≤ 3 * ε₁ * t := by nlinarith [hε₁, ht0]
      have h16 : (3 * ε₁ * t) * (7 / 3) ≤ (3 * ε₁ * t) * (1 + (Real.log (2 / t)) ^ 2) :=
        mul_le_mul_of_nonneg_left h13 h15
      have h17 : 7 * ε₁ * t = (3 * ε₁ * t) * (7 / 3) := by ring
      have h18 : (3 * ε₁ * t) * (1 + (Real.log (2 / t)) ^ 2)
          = 3 * ε₁ * (1 + (Real.log (2 / t)) ^ 2) * t := by ring
      linarith [h16, h17.ge, h17.le, h18.ge, h18.le]
    have ht3pos : (0 : ℝ) ≤ 3 * t ^ 3 := by positivity
    have h7 : Real.sin t * (1 + 7 * ε₁) = Real.sin t + 7 * ε₁ * Real.sin t := by ring
    have h8 : Real.sin t + 3 * (ε₁ * (1 + (Real.log (2 / t)) ^ 2) + t ^ 2) * t
        = Real.sin t + 3 * ε₁ * (1 + (Real.log (2 / t)) ^ 2) * t + 3 * t ^ 3 := by ring
    rw [h7, h8]
    linarith [h11, h12, ht3pos]

/-- **The arithmetic in the range `t ∈ [π/3, ρ₀]` (upper bound).** -/
lemma radial_num_large {c ε₁ t : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c) (ht : Real.pi / 3 ≤ t) (htρ : t ≤ rho0 c) :
    Real.sin t * (1 + 7 * ε₁) * (Real.tan (t / 2) / Real.tan (Real.pi / 6)) ^ ε₁
      ≤ Real.sin t + 3 * (ε₁ * (1 + (Real.log (2 / t)) ^ 2) + t ^ 2) * t := by
  have hε₁' : ε₁ ≤ 1 / 24 := by nlinarith [hε₁, hnum2, hc1, Real.pi_gt_three]
  have ht1 : 1 ≤ t := by linarith [Real.pi_gt_three]
  have htπ : t < Real.pi := lt_of_le_of_lt htρ (rho0_lt_pi' hc)
  have hsin0 : 0 ≤ Real.sin t :=
    le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_gt_three]) htπ)
  have h1 := tan_ratio_rpow_le hc hc1 hε₁ hnum2 ht htρ
  have htanpos : 0 < Real.tan (t / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith [Real.pi_gt_three]) (by linarith)
  have h6pos : 0 < Real.tan (Real.pi / 6) := by rw [Real.tan_pi_div_six]; positivity
  have hR0 : 0 ≤ (Real.tan (t / 2) / Real.tan (Real.pi / 6)) ^ ε₁ :=
    Real.rpow_nonneg (le_of_lt (div_pos htanpos h6pos)) ε₁
  have hB : 1 + 7 * ε₁ ≤ 31 / 24 := by linarith [hε₁']
  have hs1 : Real.sin t ≤ 1 := Real.sin_le_one t
  have hAB : Real.sin t * (1 + 7 * ε₁) ≤ (1 : ℝ) * (31 / 24) := by
    have hB' : (0 : ℝ) ≤ 1 + 7 * ε₁ := by linarith [hε₁]
    have h7 : Real.sin t * (1 + 7 * ε₁) ≤ 1 * (1 + 7 * ε₁) := by nlinarith [hs1, hB']
    have h8 : 1 * (1 + 7 * ε₁) ≤ 1 * (31 / 24) := by linarith [hB]
    linarith [h7, h8]
  have hABR : Real.sin t * (1 + 7 * ε₁) * (Real.tan (t / 2) / Real.tan (Real.pi / 6)) ^ ε₁
      ≤ (1 : ℝ) * (31 / 24) * (1111 / 1000) :=
    mul_le_mul hAB h1 hR0 (by norm_num)
  have hrhs : (3 : ℝ)
      ≤ Real.sin t + 3 * (ε₁ * (1 + (Real.log (2 / t)) ^ 2) + t ^ 2) * t := by
    have ht3 : (1 : ℝ) ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ (by norm_num) ht1 3
    have h3 : (3 : ℝ) ≤ 3 * t ^ 3 := by
      have : (1 : ℝ) ≤ t ^ 3 := by simpa using ht3
      linarith
    have h4 : 0 ≤ 3 * (ε₁ * (1 + (Real.log (2 / t)) ^ 2)) * t := by
      have h5 : (0 : ℝ) ≤ 1 + (Real.log (2 / t)) ^ 2 := by positivity
      have h6 : (0 : ℝ) ≤ ε₁ * (1 + (Real.log (2 / t)) ^ 2) := mul_nonneg hε₁ h5
      exact mul_nonneg (mul_nonneg (by norm_num) h6) (by linarith [ht1])
    have h7 : Real.sin t + 3 * (ε₁ * (1 + (Real.log (2 / t)) ^ 2) + t ^ 2) * t
        = Real.sin t + 3 * ε₁ * (1 + (Real.log (2 / t)) ^ 2) * t + 3 * t ^ 3 := by ring
    rw [h7]
    linarith [h3, h4, hsin0]
  have h6 : (1 : ℝ) * (31 / 24) * (1111 / 1000) ≤ 3 := by norm_num
  linarith [hABR, hrhs, h6]

/-- **The arithmetic in the range `t ∈ [π/3, ρ₀]` (lower bound).** -/
lemma radial_lower_arith {c ε₁ t : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c) (ht : Real.pi / 3 ≤ t) (htρ : t ≤ rho0 c) :
    (1 / 2 : ℝ) ≤ (1 - 5 * ε₁) * (Real.tan (t / 2) / Real.tan (Real.pi / 6)) ^ (-ε₁) := by
  have hε₁' : ε₁ ≤ 1 / 24 := by nlinarith [hε₁, hnum2, hc1, Real.pi_gt_three]
  have htπ : t < Real.pi := lt_of_le_of_lt htρ (rho0_lt_pi' hc)
  have h1 := tan_ratio_rpow_le hc hc1 hε₁ hnum2 ht htρ
  have htanpos : 0 < Real.tan (t / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith [Real.pi_gt_three]) (by linarith)
  have h6pos : 0 < Real.tan (Real.pi / 6) := by rw [Real.tan_pi_div_six]; positivity
  have hratio : 0 < Real.tan (t / 2) / Real.tan (Real.pi / 6) := div_pos htanpos h6pos
  have h2 : (1 : ℝ) / (1111 / 1000) ≤ (1 : ℝ)
      / (Real.tan (t / 2) / Real.tan (Real.pi / 6)) ^ ε₁ :=
    one_div_le_one_div_of_le (Real.rpow_pos_of_pos hratio ε₁) h1
  have h2' : (1 : ℝ) / (1111 / 1000)
      ≤ (Real.tan (t / 2) / Real.tan (Real.pi / 6)) ^ (-ε₁) := by
    rw [Real.rpow_neg (le_of_lt hratio), inv_eq_one_div]
    exact h2
  have h3 : (19 : ℝ) / 24 ≤ 1 - 5 * ε₁ := by linarith [hε₁']
  have h4 : (0 : ℝ) ≤ 1 - 5 * ε₁ := by linarith [hε₁']
  have h5 : (1 : ℝ) / (1111 / 1000) = 1000 / 1111 := by norm_num
  rw [h5] at h2'
  have h7 : (19 / 24) * (1000 / 1111)
      ≤ (1 - 5 * ε₁) * (Real.tan (t / 2) / Real.tan (Real.pi / 6)) ^ (-ε₁) :=
    mul_le_mul h3 h2' (by norm_num) h4
  have h8 : (1 / 2 : ℝ) ≤ (19 / 24) * (1000 / 1111) := by norm_num
  linarith [h7, h8]

/-- `2π/3 < ρ₀` for `0 < c ≤ 1/4`. -/
lemma two_thirds_lt_rho0 {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) :
    2 * Real.pi / 3 < Real.pi - Real.arccos (1 - c) := by
  have hhalf : Real.arccos ((1 : ℝ) / 2) = Real.pi / 3 := by
    rw [← Real.cos_pi_div_three]
    exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])
  have hlt : Real.arccos (1 - c) < Real.pi / 3 := by
    have h := Real.arccos_lt_arccos (x := (1 : ℝ) / 2) (y := 1 - c)
      (by norm_num) (by linarith) (by linarith)
    rwa [hhalf] at h
  linarith

theorem radial_modulus : Work.Diff.C.GeoCrux.RadialModulusProp := by
  intro E iE1 iE2 iE3 iE4 H iH I M iM1 iM2 iM3 iM4 iRB iCM iBL iNE iCS iPC cov iCD
    hmet htor c ε₁ hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad hdiam q v w hv hw hvw t ht
  obtain ⟨ht0, htρ⟩ := ht
  have hv1 : ‖v‖ = 1 := by
    have h : ‖v‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hv
    nlinarith [norm_nonneg v]
  have hw1 : ‖w‖ = 1 := by
    have h : ‖w‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hw
    nlinarith [norm_nonneg w]
  have hv0 : v ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hv1; norm_num at hv1
  have hw0 : w ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hw1; norm_num at hw1
  have hε₁' : ε₁ ≤ 1 / 24 := by nlinarith [hε₁, hnum2, hc1, Real.pi_gt_three]
  have htπ : t < Real.pi := lt_of_le_of_lt htρ (rho0_lt_pi' hc)
  have hcut : ∀ x : M, Submission.InjRadius.InjAtLeast hmet x (rho0 c) := fun x =>
    Work.Diff.C.geoCrux.Port.inj_radius_core hmet htor hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad x
  by_cases ht3 : t ≤ Real.pi / 3
  · -- ## 1. `t ≤ π/3`: the two-centre extraction at the pair `(t, 2t)`
    have h2t_lt : 2 * t < rho0 c := by
      have h := two_thirds_lt_rho0 hc hc1
      have h2 : 2 * t ≤ 2 * (Real.pi / 3) := by linarith
      rw [rho0]
      linarith
    obtain ⟨N, hN0, hNZ, hKpos, hLpos, hN2, hrest⟩ :=
      Work.Diff.C.geoCrux.Port.twoCentreCore (E := E) (H := H) (I := I) (M := M) (cov := cov)
        hmet htor hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad hcut q v hv t (2 * t)
        ht0 (by linarith) le_rfl h2t_lt
    obtain ⟨hlb, hub⟩ := hrest w hvw hw
    have hy : 0 ≤ ‖Submission.Geodesic.curveVelocity (I := I) (M := M)
        (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • (v + r • w))) 0‖ :=
      norm_nonneg _
    have hcos : Real.cos t ≥ 1 / 2 := by
      have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := t) (y := Real.pi / 3) ht0.le
        (by linarith [Real.pi_pos]) ht3
      rwa [Real.cos_pi_div_three] at h
    have hmain := modulus_of_twoCentre_sharp hc hc1 ht0 h2t_lt.le hε₁ hε₁' hcos hN0 hy hN2 hub hlb
    refine ⟨?_, ?_⟩
    · have hsint : 0 ≤ Real.sin t := le_of_lt (Real.sin_pos_of_pos_of_lt_pi ht0 htπ)
      have h2 : Real.sin t / 2 ≤ Real.sin t * (1 - 5 * ε₁) := by
        nlinarith [hε₁, hε₁', hsint]
      exact le_trans h2 hmain.1
    · have hnum := radial_num_small hε₁ hε₁' ht0 ht3
      exact le_trans hmain.2 hnum
  · -- ## 2. `π/3 < t ≤ ρ₀`: the anchor at `π/3` and the anchored Sturm comparison
    push_neg at ht3
    have hδ0 : 0 < Real.pi / 3 := by linarith [Real.pi_pos]
    have h2δπ : 2 * (Real.pi / 3) < rho0 c := by
      rw [rho0]
      have h := two_thirds_lt_rho0 hc hc1
      linarith
    have hπ3ρ : Real.pi / 3 ≤ rho0 c := by linarith [h2δπ]
    obtain ⟨N, hN0, hNZ, hKpos, hLpos, hN2, hrest⟩ :=
      Work.Diff.C.geoCrux.Port.twoCentreCore (E := E) (H := H) (I := I) (M := M) (cov := cov)
        hmet htor hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad hcut q v hv (Real.pi / 3)
        (2 * (Real.pi / 3)) hδ0 (by linarith) le_rfl h2δπ
    obtain ⟨hlb, hub⟩ := hrest w hvw hw
    have hyδ : 0 ≤ ‖Submission.Geodesic.curveVelocity (I := I) (M := M)
        (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q
          ((Real.pi / 3) • (v + r • w))) 0‖ :=
      norm_nonneg _
    have hcosδ : Real.cos (Real.pi / 3) ≥ 1 / 2 := by rw [Real.cos_pi_div_three]
    have hmain := modulus_of_twoCentre_sharp hc hc1 hδ0 h2δπ.le hε₁ hε₁' hcosδ hN0 hyδ hN2 hub hlb
    have hZfδ : ‖Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w (Real.pi / 3)‖
        = ‖Submission.Geodesic.curveVelocity (I := I) (M := M)
            (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q
              ((Real.pi / 3) • (v + r • w))) 0‖ :=
      Work.Diff.C.geoCrux.Port.Zf_norm_eq (cov := cov) hmet q v w (Real.pi / 3)
    have hanchorU : ‖Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w (Real.pi / 3)‖
        ≤ Real.sin (Real.pi / 3) * (1 + 7 * ε₁) := by
      rw [hZfδ]; exact hmain.2
    have hanchorL : Real.sin (Real.pi / 3) * (1 - 5 * ε₁)
        ≤ ‖Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w (Real.pi / 3)‖ := by
      rw [hZfδ]; exact hmain.1
    have hposδ : 0 < ‖Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w (Real.pi / 3)‖ := by
      rw [norm_pos_iff]
      exact Work.Diff.C.geoCrux.Port.sharp.Zf_ne_zero (I := I) (M := M) (cov := cov)
        hmet htor hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad hcut q v hv w hvw hw0 (Real.pi / 3)
        hδ0 hπ3ρ
    have hpost : 0 < ‖Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w t‖ := by
      rw [norm_pos_iff]
      exact Work.Diff.C.geoCrux.Port.sharp.Zf_ne_zero (I := I) (M := M) (cov := cov)
        hmet htor hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad hcut q v hv w hvw hw0 t ht0 htρ
    have hder : ∀ s ∈ Set.Icc (Real.pi / 3) t,
        HasDerivAt (fun s : ℝ =>
          Real.log ‖Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w s‖)
          (Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov
                (Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w) s)
              (Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w s)
            / Inner.inner ℝ (Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w s)
              (Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w s)) s := by
      intro s hs
      have hs0 : 0 < s := lt_of_lt_of_le hδ0 hs.1
      have htρ' : t ≤ rho0 c := by rw [rho0]; exact htρ
      have hsρ : s ≤ rho0 c := le_trans hs.2 htρ'
      have hne : Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w s ≠ 0 :=
        Work.Diff.C.geoCrux.Port.sharp.Zf_ne_zero (I := I) (M := M) (cov := cov)
          hmet htor hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad hcut q v hv w hvw hw0 s hs0 hsρ
      exact Work.Diff.C.jld_log_norm_hasDerivAt (I := I) (M := M) (cov := cov) hmet htor
        (Work.Diff.C.geoCrux.Port.tcGam_contMDiff (cov := cov) hmet hv0)
        (fun u => Submission.RayJacobi.isJacobiAt_GExp_variation (cov := cov) hmet htor hv0 hv1 u)
        (fun u => Work.Diff.C.geoCrux.Port.tcVel_ne_zero (cov := cov) hmet hv0 u) hne
    have hwbU : ∀ s ∈ Set.Ioo (0 : ℝ) t,
        Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov
            (Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w) s)
          (Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w s)
        / Inner.inner ℝ (Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w s)
          (Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w s)
        ≤ Real.cot s + ε₁ / Real.sin s := fun s hs =>
      Work.Diff.C.geoCrux.Port.sharp.logderiv_le (I := I) (M := M) (cov := cov)
        hmet htor hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad hcut q v hv w hvw hw0 s hs.1
        (lt_of_lt_of_le hs.2 htρ)
    have hwbL : ∀ s ∈ Set.Ioo (0 : ℝ) t,
        Real.cot s - ε₁ / Real.sin s
        ≤ Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov
            (Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w) s)
          (Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w s)
        / Inner.inner ℝ (Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w s)
          (Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w s) := fun s hs =>
      Work.Diff.C.geoCrux.Port.sharp.logderiv_ge (I := I) (M := M) (cov := cov)
        hmet htor hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad hcut q v hv w hvw hw0 s hs.1
        (lt_of_lt_of_le hs.2 htρ)
    have hupper := Work.Diff.C.geoCrux.sturm_anchored_upper
      (v := fun s : ℝ => ‖Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w s‖)
      (w := fun s : ℝ => Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov
          (Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w) s)
        (Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w s)
        / Inner.inner ℝ (Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w s)
          (Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w s))
      (A := Real.log (1 + 7 * ε₁)) hδ0 ht3 hε₁ htπ hposδ hpost hder hwbU (by
        rw [Real.exp_log (by linarith)]
        simpa [mul_comm] using hanchorU)
    have hlower := Work.Diff.C.geoCrux.sturm_anchored_lower
      (v := fun s : ℝ => ‖Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w s‖)
      (w := fun s : ℝ => Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov
          (Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w) s)
        (Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w s)
        / Inner.inner ℝ (Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w s)
          (Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w s))
      (A := Real.log (1 - 5 * ε₁)) hδ0 ht3 hε₁ htπ hposδ hpost hder hwbL (by
        rw [Real.exp_log (by linarith [hε₁'])]
        simpa [mul_comm] using hanchorL)
    have hupper' : ‖Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w t‖
        ≤ Real.sin t * (1 + 7 * ε₁) * (Real.tan (t / 2) / Real.tan (Real.pi / 6)) ^ ε₁ := by
      rw [Real.exp_log (by linarith)] at hupper
      rw [show (Real.pi / 3) / 2 = Real.pi / 6 from by ring] at hupper
      calc ‖Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w t‖
          ≤ (1 + 7 * ε₁) * Real.sin t * (Real.tan (t / 2) / Real.tan (Real.pi / 6)) ^ ε₁ := hupper
        _ = Real.sin t * (1 + 7 * ε₁)
            * (Real.tan (t / 2) / Real.tan (Real.pi / 6)) ^ ε₁ := by ring
    have hlower' : (1 - 5 * ε₁) * Real.sin t * (Real.tan (t / 2) / Real.tan (Real.pi / 6)) ^ (-ε₁)
        ≤ ‖Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w t‖ := by
      rw [Real.exp_log (by linarith [hε₁'])] at hlower
      rw [show (Real.pi / 3) / 2 = Real.pi / 6 from by ring] at hlower
      exact hlower
    have hZft : ‖Work.Diff.C.geoCrux.Port.Zf (cov := cov) hmet q v w t‖
        = ‖Submission.Geodesic.curveVelocity (I := I) (M := M)
            (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • (v + r • w))) 0‖ :=
      Work.Diff.C.geoCrux.Port.Zf_norm_eq (cov := cov) hmet q v w t
    refine ⟨?_, ?_⟩
    · have h2 := radial_lower_arith hc hc1 hε₁ hnum2 (le_of_lt ht3) htρ
      have hs := Real.sin_pos_of_pos_of_lt_pi ht0 htπ
      have h3 : Real.sin t / 2 ≤ (1 - 5 * ε₁) * Real.sin t
          * (Real.tan (t / 2) / Real.tan (Real.pi / 6)) ^ (-ε₁) := by
        calc Real.sin t / 2 = (1 / 2) * Real.sin t := by ring
          _ ≤ ((1 - 5 * ε₁) * (Real.tan (t / 2) / Real.tan (Real.pi / 6)) ^ (-ε₁))
              * Real.sin t := mul_le_mul_of_nonneg_right h2 hs.le
          _ = (1 - 5 * ε₁) * Real.sin t
              * (Real.tan (t / 2) / Real.tan (Real.pi / 6)) ^ (-ε₁) := by ring
      rw [← hZft]
      exact le_trans h3 hlower'
    · have hnum := radial_num_large hc hc1 hε₁ hnum2 (le_of_lt ht3) htρ
      rw [← hZft]
      exact le_trans hupper' hnum


end Work.Diff.C.geoCrux
