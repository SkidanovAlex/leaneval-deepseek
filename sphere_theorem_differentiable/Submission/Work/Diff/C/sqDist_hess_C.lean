import Mathlib
import Submission.Work.Diff.C.GExp_localInverse
import Submission.Work.Diff.C.exists_contMDiff_eventuallyEq_of_contMDiffOn_vec
import Submission.Work.Diff.C.sqNorm_hess_smooth
import Submission.Work.Diff.C.mvfderiv_inner_pair
import Submission.Work.Diff.C.grad_smoothAt
import Submission.Work.Diff.C.hess_upper
import Submission.Work.Diff.C.rdist_continuous

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open scoped Bundle Manifold ContDiff Topology
open Bundle ContDiff Set VectorField Metric Filter

set_option linter.unusedSectionVars false

/-! ## Two germ-locality lemmas for the gradient

`rgrad` is defined from `mfderiv` (through the Riesz isomorphism), and `mfderiv` is a germ-local
object; hence so is `rgrad` and the gradient field. -/

/-- **Germ-locality of `rgrad`.**  Two functions that agree near `x` have the same gradient at
`x`. -/
lemma rgrad_congr
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {F G : M → ℝ} {x : M} (h : F =ᶠ[𝓝 x] G) :
    rgrad (I := I) (M := M) F x = rgrad (I := I) (M := M) G x := by
  have h' : mfderiv I (𝓘(ℝ, ℝ)) F x = mfderiv I (𝓘(ℝ, ℝ)) G x :=
    Filter.EventuallyEq.mfderiv_eq h
  unfold rgrad
  rw [h']

/-- **Germ-locality of the gradient field.**  If `F` and `G` agree near `x`, then their gradient
fields agree near `x`. -/
lemma rgrad_eventually_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {F G : M → ℝ} {x : M} (h : F =ᶠ[𝓝 x] G) :
    ∀ᶠ y in 𝓝 x, rgrad (I := I) (M := M) F y = rgrad (I := I) (M := M) G y := by
  obtain ⟨s, hs, hxy⟩ := Filter.eventually_iff_exists_mem.mp h
  filter_upwards [isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hs)] with y hy
  exact rgrad_congr (I := I) (M := M)
    (Filter.eventually_iff_exists_mem.mpr
      ⟨interior s, isOpen_interior.mem_nhds hy, fun z hz => hxy z (interior_subset hz)⟩)

/-- **The squared distance function at its centre.**  `y ↦ rdist q y ^ 2` is `C^∞` at `q`, its
gradient vanishes at `q`, and its Hessian at `q` is `2 g(q)`.  (`∞` here is smoothness, i.e.
`((⊤ : ℕ∞) : WithTop ℕ∞)`, NOT `(⊤ : WithTop ℕ∞)` which is `ω`/analytic.)

Ingredients already in the workspace:
* `Submission.Work.Diff.C.GExp_localInverse` (PROVED): there is `Φ : M → T_qM`, smooth near `q`,
  with `Φ q = 0`, `mfderiv Φ q = id`, and `rdist q y = ‖Φ y‖` for `y` near `q`;
* `Submission.Work.Diff.C.exists_contMDiff_eventuallyEq_of_contMDiffOn_vec` (PROVED): a map that is
  smooth near `q` agrees near `q` with a globally smooth map;
* `Submission.Work.Diff.C.sqNorm_hess_smooth` (statement + documented route, currently a `sorry`):
  for a globally smooth `Φ : M → T_qM` with `Φ q = 0`, `F y = ⟪Φ y, Φ y⟫` has `∇F(q) = 0` and
  `Hess F(q)(V,W) = 2⟪dΦ_q V, dΦ_q W⟫`;
* `Submission.Work.Diff.C.mvfderiv_inner_pair` (statement, currently a `sorry`): product rule for
  `mvfderiv` of an inner product of two maps into a normed space (Mathlib: `HasFDerivAt.inner`);
* `Submission.Work.Diff.C.grad_smoothAt`, `...cov_rgrad_eq_cov_extension`,
  `...rhess_eq_cov_extension` (PROVED): smoothness of `∇F` and germ-locality of `cov` (so `rhess`
  may be computed from any smooth section agreeing with `∇F` near the point).
Sketch: `rgrad` and `rhess` are germ-local, so one may replace `Φ` by a globally smooth extension
`Φ'` of it; `⟪v,v⟫ = ‖v‖ ^ 2` and `rdist q y = ‖Φ y‖` give `⟪Φ' y, Φ' y⟫ =ᶠ (rdist q ·)^2` near
`q`, and `dΦ'_q = dΦ_q = id`. -/
theorem sqDist_hess_C
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
    (q : M) :
    ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : M => (Work.Diff.C.rdist (I := I) (M := M) q y) ^ 2) q ∧
      Work.Diff.C.rgrad (I := I) (M := M)
        (fun y : M => (Work.Diff.C.rdist (I := I) (M := M) q y) ^ 2) q = 0 ∧
      (∀ V W : TangentSpace I q,
        Work.Diff.C.rhess cov
          (fun y : M => (Work.Diff.C.rdist (I := I) (M := M) q y) ^ 2) q V W
          = 2 * Inner.inner ℝ V W) := by
  classical
  -- The local inverse of the exponential map at `q`.
  obtain ⟨Φ, hΦsm, hΦ0, hΦmf, hΦeq⟩ := GExp_localInverse (I := I) (M := M) hmet htor q
  -- A globally smooth map agreeing with `Φ` near `q`.
  obtain ⟨U, hUnev, hΦon⟩ :
      ∃ U ∈ 𝓝 q, ContMDiffOn I (𝓘(ℝ, TangentSpace I q)) ((⊤ : ℕ∞) : WithTop ℕ∞) Φ U :=
    ⟨{y | ContMDiffAt I (𝓘(ℝ, TangentSpace I q)) ((⊤ : ℕ∞) : WithTop ℕ∞) Φ y}, hΦsm,
      fun y hy => hy.contMDiffWithinAt⟩
  obtain ⟨Φ', hΦ'sm, hΦ'eq⟩ :=
    exists_contMDiff_eventuallyEq_of_contMDiffOn_vec (I := I) (M := M) (x := q) hUnev hΦon
  have hΦ'q : Φ' q = 0 := by rw [hΦ'eq.eq_of_nhds, hΦ0]
  -- The comparison function `F' y = ⟪Φ' y, Φ' y⟫`, globally smooth.
  have hF'sm : ContMDiff I (𝓘(ℝ, ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : M => Inner.inner ℝ (Φ' y) (Φ' y)) :=
    fun y => SqNormAux.contMDiffAt_inner_pair (hΦ'sm y) (hΦ'sm y)
  obtain ⟨hrgradF', hrhessF'⟩ := sqNorm_hess_smooth (I := I) (M := M) hmet hΦ'sm hΦ'q
  -- `rdist q · ^ 2` and `F'` agree near `q`.
  have hev : (fun y : M => (rdist (I := I) (M := M) q y) ^ 2)
      =ᶠ[𝓝 q] (fun y : M => Inner.inner ℝ (Φ' y) (Φ' y)) := by
    filter_upwards [hΦeq, hΦ'eq] with y hy hy'
    rw [hy.2, hy', real_inner_self_eq_norm_sq]
  refine ⟨?_, ?_, ?_⟩
  · -- Smoothness at `q`
    exact (hF'sm q).congr_of_eventuallyEq hev
  · -- vanishing gradient at `q`
    rw [rgrad_congr (I := I) (M := M) hev, hrgradF']
  · -- the Hessian
    intro V W
    have h𝒱sm : ContMDiff I I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
        (T% (fun y : M => rgrad (I := I) (M := M)
          (fun z : M => Inner.inner ℝ (Φ' z) (Φ' z)) y)) :=
      fun y => grad_smoothAt (I := I) (M := M) (hF'sm y)
    have h𝒱eq : ∀ᶠ y in 𝓝 q,
        rgrad (I := I) (M := M) (fun z : M => Inner.inner ℝ (Φ' z) (Φ' z)) y
          = rgrad (I := I) (M := M)
              (fun z : M => (rdist (I := I) (M := M) q z) ^ 2) y :=
      rgrad_eventually_eq (I := I) (M := M) hev.symm
    have hkey := rhess_eq_cov_extension (I := I) (M := M) (cov := cov)
      (F := fun z : M => (rdist (I := I) (M := M) q z) ^ 2) (x := q)
      (𝒱 := fun y : M => rgrad (I := I) (M := M)
        (fun z : M => Inner.inner ℝ (Φ' z) (Φ' z)) y)
      h𝒱sm h𝒱eq V W
    have hA : Inner.inner ℝ ((cov (fun y : M => rgrad (I := I) (M := M)
        (fun z : M => Inner.inner ℝ (Φ' z) (Φ' z)) y) q) V) W
        = rhess cov (fun z : M => Inner.inner ℝ (Φ' z) (Φ' z)) q V W := rfl
    have hmf' : mvfderiv I Φ' q = ContinuousLinearMap.id ℝ (TangentSpace I q) := by
      have h1 : mfderiv I (𝓘(ℝ, TangentSpace I q)) Φ' q
          = mfderiv I (𝓘(ℝ, TangentSpace I q)) Φ q :=
        Filter.EventuallyEq.mfderiv_eq hΦ'eq
      rw [mvfderiv_eq_mfderiv, h1, hΦmf]
    rw [hkey, hA, hrhessF' V W, hmf']
    simp

end Work.Diff.C
