import Mathlib
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.fb_cap_depth

/-!
# The far-ball excess ("cap depth") bound

`Work.Diff.C.far_ball_excess` is the statement that the antipodal cap
`{z | rdist q z ≥ π - arccos (1-c)}` of `q = qpt hmet p e (Fin.succ k)` has depth
`rdist q z ≤ π + arcsin (2 ε₁)`.  It is consumed by `Diff/C/dip_far_ball` (and by
`dip_cap_exit`, `dip_model_through`, `dip_model_sharp`, `dip_far_sharp`), which combine it with the
far-sphere diameter bound to get the diameter of the cap.

The previous attempt in this file (an explicit second-variation argument, with the midpoint of the
minimising geodesic from `q` to `z` and the two shape-operator comparisons) did not compile; the
statement is now a wrapper around the completed proof `Work.Diff.C.fb_cap_depth`
(module `Diff/C/fb_cap_depth`), which proves exactly it.
-/

namespace Work.Diff.C

open Bundle
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- **Myers-type ("excess") bound for the far ball.**  In the setting of `Work.Diff.C.dip_far_ball`
(a metric which is a round unit sphere up to `ε₁`, formalised as `HessBoundRegion` for the functions
`fcos q = cos ∘ rdist q`; `p` a base point, `e` an orthonormal family, `q := qpt hmet p e (Fin.succ k)`
the point at distance `π/2` from `p`, and `rdist p y ≤ π` for all `y`), every point `z` at distance
at least `π - arccos (1-c)` from `q` satisfies `rdist q z ≤ π + arcsin (2ε₁)`.

Intended route: for a minimising geodesic `γ` from `q` to `z` (length `L`), the function
`F = rdist q + rdist z` has global minimum `L` on `γ`, so its Hessian is positive semidefinite at
every point of `γ`.  Where BOTH the centre-`q` and the centre-`z` Hessian comparisons are available
(`t ∈ (L-π+δ, π-δ)`, `δ = arccos (1-c)`, nonempty because `L ≤ rdist p q + rdist p z ≤ 3π/2`), the
two Hessian bounds — obtained from `hHess` by the second-order chain rule for the Hessian of
`cos ∘ F` (`Work.Diff.C.rhess_comp` with `c = Real.cos`, `Real.deriv_cos`,
`Real.iteratedDeriv_cos`) plus the eikonal identity `hgrad` and `sin (rdist z ·) > 0` — give, for
`V ⊥ γ'`, that `cot t + cot (L-t) ≥ -ε₁(1/sin t + 1/sin (L-t))`, whence
`sin L ≥ -ε₁(sin t + sin (L-t)) ≥ -2ε₁`; since `L ∈ [π-δ, 3π/2]`, this gives `L ≤ π + arcsin (2ε₁)`.
(Exact constants are immaterial; anything of the shape `π + small + small·ε₁` is enough.)

NOTE: the workspace has a duplicate declaration (`Work.Diff.C.inner_rgrad_mvfderiv'` appears in both
`Submission.Work.Diff.C.init_data` and `Submission.Work.Diff.C.ray_cos_compare`), so a file must not
import both; with the modules listed below there is no clash, and the `cos`-chain rule can be

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
re-derived from `Work.Diff.C.rhess_comp` if needed.  Also note that in dimension `1` there is no
nonzero `V ⊥ γ'`, so that (vacuous) case needs no argument. -/
theorem far_ball_excess
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {α c ε₁ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hc : 0 < c) (hc1 : c ≤ 1 / 4)
    (hε₁ : 0 ≤ ε₁) (hnum1 : 3 * c ≤ 1 - Real.cos α) (hnum2 : 4 * ε₁ * Real.pi < c)
    {p : M} {e : Fin (Module.finrank ℝ E) → TangentSpace I p}
    (hON : ∀ i j, Inner.inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (hsmC : ∀ (q y : M), -1 + c ≤ Work.Diff.C.fcos (I := I) (M := M) q y →
      ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat) (Work.Diff.C.fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, Work.Diff.C.HessBoundRegion (I := I) (M := M) cov c ε₁ (Work.Diff.C.fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (Work.Diff.C.fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < Work.Diff.C.fcos (I := I) (M := M) q y →
      Inner.inner ℝ (Work.Diff.C.rgrad (I := I) (M := M) (Work.Diff.C.fcos (I := I) (M := M) q) y)
        (Work.Diff.C.rgrad (I := I) (M := M) (Work.Diff.C.fcos (I := I) (M := M) q) y)
        = 1 - (Work.Diff.C.fcos (I := I) (M := M) q y) ^ 2)
    (hinit : Work.Diff.C.InitData (I := I) (M := M) (cov := cov) hmet p e)
    (hdiam : ∀ y : M, Work.Diff.C.rdist (I := I) (M := M) p y ≤ Real.pi)
    {k : Fin (Module.finrank ℝ E)} :
    ∀ z : M,
      Real.pi - Real.arccos (1 - c)
          ≤ Work.Diff.C.rdist (I := I) (M := M) (Work.Diff.C.qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)) z →
      Work.Diff.C.rdist (I := I) (M := M) (Work.Diff.C.qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)) z
        ≤ Real.pi + Real.arcsin (2 * ε₁) := by
  intro z hz
  exact fb_cap_depth (I := I) (M := M) (cov := cov) hmet htor hα hα1 hc hc1 hε₁ hnum1 hnum2
    hON hsmC hHess hcont hgrad hinit hdiam z hz

end Work.Diff.C
