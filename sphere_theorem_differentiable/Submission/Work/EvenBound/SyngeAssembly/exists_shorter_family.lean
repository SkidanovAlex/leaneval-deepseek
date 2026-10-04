import Mathlib
import Submission.Work.EvenBound.Imports
import Submission.Work.EvenBound.SyngeConst.synge_shortening_const_speed

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.EvenBound.SyngeAssembly

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

/-- `∀ᶠ` statements on `𝓝[<] 0` transfer to `𝓝[>] 0` along the reflection `σ ↦ -σ`.
(Elementary filter fact, proved here from the metric description of `𝓝[<]`/`𝓝[>]` on `ℝ`.) -/
lemma eventually_nhdsGT_neg_of_eventually_nhdsLT {P : ℝ → Prop}
    (h : ∀ᶠ ρ in 𝓝[<] (0 : ℝ), P ρ) : ∀ᶠ σ in 𝓝[>] (0 : ℝ), P (-σ) := by
  obtain ⟨ε, hε, hball⟩ :=
    Metric.eventually_nhds_iff_ball.mp (eventually_nhdsWithin_iff.mp h)
  refine eventually_nhdsWithin_iff.mpr (Metric.eventually_nhds_iff_ball.mpr ⟨ε, hε, ?_⟩)
  intro σ hσε hσpos
  refine hball (-σ) ?_ (neg_lt_zero.mpr (show (0 : ℝ) < σ from hσpos))
  have hdist : dist (-σ) (0 : ℝ) = dist σ (0 : ℝ) := by simp
  rw [Metric.mem_ball] at hσε ⊢
  rwa [hdist]

/-- **A one-sided shortening family of a `1`-periodic constant-speed closed geodesic.**  Let `γ` be a
`1`-periodic geodesic of constant speed `2m` with non-vanishing velocity, carrying a smooth,
parallel, periodic, unit, normal field `Z` on the window `[-1,2]`, and suppose the sectional
curvature at orthonormal pairs along `γ` is `≥ δ > 0`.  Then there are a field `Z'` (either `Z` or
`-Z`), still periodic and smooth on the window, and `d > 0`, such that the closed curves
`t ↦ GExp (γ t) (σ • (d • Z' t))` have length `< 2m` for *all sufficiently small `σ > 0`*.

*Proof.*  Apply `Work.EvenBound.SyngeConst.synge_shortening_const_speed` with `L := 1`, `c := 2m`
(it needs `γ 1 = γ 0` from `hper`, the constant speed `2m`, the field data on `[-1,2]`, and the
curvature bound `δ` along `γ`; its conclusion is the disjunction
`(∀ᶠ σ in 𝓝[>] 0, ·) ∨ (∀ᶠ σ in 𝓝[<] 0, ·)`).  If the first branch holds, take `Z' := Z`.  If the
second branch holds, take `Z' := -Z` and the *same* `d`: for `σ > 0` the vector
`σ • (d • (-Z t))` equals `(-σ) • (d • Z t)` (`smul_smul`, `smul_neg`), so the curve family for
`Z'` at `σ` is the family for `Z` at `-σ` and has the same length; the transfer of
`∀ᶠ σ in 𝓝[<] 0` to `∀ᶠ σ in 𝓝[>] 0` is the filter statement
`(𝓝[>] (0:ℝ)).map (fun σ => -σ) = 𝓝[<] (0:ℝ)`.  Smoothness of `-Z` is
`Submission.EnergyRay.SmoothAlongAt_smul` at `-1` (or the chart-coordinate argument) and `Z' 1 = Z' 0`
is `congrArg`. -/
theorem exists_shorter_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} {m : ℝ} (hm : 0 < m) (hper : ∀ t : ℝ, γ (t + 1) = γ t)
    (hγsm : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hgeo : ∀ t : ℝ, Submission.Geodesic.IsGeodesicAt cov γ t)
    (hne : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0)
    (hsp : ∀ t ∈ Set.Icc (0 : ℝ) 1, Submission.Length.curveSpeed (I := I) γ t = 2 * m)
    {Z : (t : ℝ) → TangentSpace I (γ t)} (hZ1 : Z 1 = Z 0)
    (hZsm : ∀ s ∈ Set.Icc (0 - 1) ((1 : ℝ) + 1),
      Submission.JacobiGlobal.SmoothAlongAt (I := I) γ Z s)
    (hZpar : ∀ s ∈ Set.Icc (0 - 1) ((1 : ℝ) + 1), Submission.JacobiGlobal.covAlong cov Z s = 0)
    (hZ1n : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Z t‖ = 1)
    (hZn : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      inner ℝ (Z t) (Submission.Geodesic.curveVelocity (I := I) γ t) = 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hcurv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u v : TangentSpace I (γ t), ‖u‖ = 1 → ‖v‖ = 1 →
      inner ℝ u v = 0 → δ ≤ inner ℝ (Submission.CurvatureVec.curvVec cov (γ t) u v v) u) :
    ∃ (Z' : (t : ℝ) → TangentSpace I (γ t)) (d : ℝ), 0 < d ∧ Z' 1 = Z' 0 ∧
      (∀ s ∈ Set.Icc (0 - 1) ((1 : ℝ) + 1),
        Submission.JacobiGlobal.SmoothAlongAt (I := I) γ Z' s) ∧
      (∀ᶠ σ in 𝓝[>] (0 : ℝ),
        Submission.Length.curveLength (I := I)
          (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (γ t) (σ • (d • Z' t))) 0 1 < 2 * m) := by
  classical
  -- Synge's shortening lemma at constant speed `2m` on the period window `[0,1]`.
  obtain ⟨d, hdpos, hbranch⟩ :=
    Work.EvenBound.SyngeConst.synge_shortening_const_speed (L := 1) (c := 2 * m)
      hmet htor hγsm hgeo hne zero_lt_one (by linarith) (by simpa using hper 0) hsp
      hZsm hZpar hZ1 hZ1n hZn hδ hcurv
  rcases hbranch with hpos | hneg
  · -- The shortening happens for `σ > 0`; keep `Z` itself.
    refine ⟨Z, d, hdpos, hZ1, hZsm, ?_⟩
    filter_upwards [hpos] with σ hσ
    have h1 := hσ.1
    rw [mul_one] at h1
    exact h1
  · -- The shortening happens for `σ < 0`; flip the field to `-Z` and read the family backwards.
    refine ⟨fun t => (-1 : ℝ) • Z t, d, hdpos, ?_, ?_, ?_⟩
    · show (-1 : ℝ) • Z 1 = (-1 : ℝ) • Z 0
      rw [hZ1]; try rfl
    · intro s hs
      exact Submission.EnergyRay.SmoothAlongAt_smul (I := I) (-1 : ℝ) (hZsm s hs)
    · -- `σ • (d • ((-1) • Z t)) = (-σ) • (d • Z t)`, so the `Z'`-family at `σ` is the `Z`-family at `-σ`.
      have hvec : ∀ (σ t : ℝ), σ • (d • ((-1 : ℝ) • Z t)) = (-σ) • (d • Z t) := by
        intro σ t
        module
      have hneg' : ∀ᶠ ρ in 𝓝[<] (0 : ℝ),
          Submission.Length.curveLength (I := I)
            (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (γ t) (ρ • (d • Z t))) 0 1 < 2 * m := by
        refine hneg.mono fun ρ hρ => ?_
        have h1 := hρ.1
        rwa [mul_one] at h1
      have hmain : ∀ᶠ σ in 𝓝[>] (0 : ℝ),
          Submission.Length.curveLength (I := I)
            (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (γ t) ((-σ) • (d • Z t))) 0 1 < 2 * m :=
        eventually_nhdsGT_neg_of_eventually_nhdsLT hneg'
      refine hmain.mono fun σ hσ => ?_
      show Submission.Length.curveLength (I := I)
          (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (γ t) (σ • (d • ((-1 : ℝ) • Z t)))) 0 1 < 2 * m
      rwa [show (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (γ t) (σ • (d • ((-1 : ℝ) • Z t))))
              = (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (γ t) ((-σ) • (d • Z t))) from
            funext fun t => by rw [hvec σ t]]

end Work.EvenBound.SyngeAssembly
