import Mathlib
import Submission.Work.OddBound.indexTransfer.Infra

namespace Work.OddBound.indexTransfer

/-- **Smoothness of the unscaled geodesic variation.**  Let `γ` be a globally `C^∞` curve on a
compact manifold, `V` a field along `γ` that is smooth along `γ` on the enlarged window
`[a-1, b+1]`.  Then for all `σ` sufficiently close to `0` the variation

  `t ↦ GExp (γ t) (σ • V t)`

is `C^∞` on `[a, b]` and its Riemannian speed is continuous there.

The proof uses the family form
`Submission.EnergyRaySmooth.contMDiffOn_geodesic_family`, which produces the *scaled* statement
`t ↦ GExp (γ t) (σ • (d • V t))` for all `d` in a small right interval `(0, c₀]`.  Fixing a single
value `d = c₀/2` and reparametrising `σ ↦ σ / d` (a homeomorphism of `ℝ` fixing `0`, under which
`(σ/d) • (d • V t) = σ • V t`) removes the auxiliary scale. -/
theorem contMDiffOn_variation_unscaled
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ℕ∞) : WithTop ℕ∞) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ℕ∞) : WithTop ℕ∞)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} (hγsm : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I ((⊤ : ℕ∞) : WithTop ℕ∞) γ Set.univ)
    {V : (t : ℝ) → TangentSpace I (γ t)} {a b : ℝ}
    (hVs : ∀ s ∈ Set.Icc (a - 1) (b + 1), Submission.JacobiGlobal.SmoothAlongAt (I := I) γ V s)
    (hab : a < b) :
    ∀ᶠ σ in nhds (0 : ℝ),
      ContMDiffOn (modelWithCornersSelf ℝ ℝ) I ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (γ t) (σ • V t))
        (Set.Icc a b) ∧
      ContinuousOn (fun t : ℝ => Submission.Length.curveSpeed (I := I) (fun t' : ℝ =>
        Submission.GlobalExp.GExp (cov := cov) hmet (γ t') (σ • V t')) t) (Set.Icc a b) := by
  obtain ⟨c₀, hc₀pos, hfam⟩ :=
    Submission.EnergyRaySmooth.contMDiffOn_geodesic_family (cov := cov) hmet htor hγsm hVs hab
  set d : ℝ := c₀ / 2 with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  have hdne : d ≠ 0 := ne_of_gt hdpos
  have hdle : d ≤ c₀ := by rw [hd]; linarith
  have hev := hfam d ⟨hdpos, hdle⟩
  have hg : Filter.Tendsto (fun σ : ℝ => σ / d) (nhds (0 : ℝ)) (nhds (0 : ℝ)) := by
    simpa using ((continuousAt_id (x := (0 : ℝ))).tendsto.div_const d)
  filter_upwards [hg.eventually hev] with σ hσ
  have hsm : ∀ t : ℝ, (σ / d) • (d • V t) = σ • V t := by
    intro t; rw [smul_smul, div_mul_cancel₀ σ hdne]
  exact ⟨by simpa only [hsm] using hσ.1, by simpa only [hsm] using hσ.2⟩

end Work.OddBound.indexTransfer
