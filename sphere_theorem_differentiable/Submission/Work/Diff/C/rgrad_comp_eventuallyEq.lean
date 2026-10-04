import Mathlib
import Submission.Work.Diff.C.rhess_comp_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- **Eventual chain rule for the gradient.**  With `F` smooth at `x` (`C^∞` in the weak
pointwise sense) and `c` smooth at `F x` (again the weak pointwise `ContDiffAt`), the gradient of
the composite `c ∘ F` agrees near `x` with `y ↦ (deriv c (F y)) • ∇F y`.  Only first-order
regularity is needed at nearby points, and the pointwise chain rule is
`Work.Diff.C.rgrad_comp_hasDerivAt` (in the imported module). -/
theorem rgrad_comp_eventuallyEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {c : ℝ → ℝ} {F : M → ℝ} {x : M}
    (hc : ContDiffAt ℝ ∞ c (F x)) (hF : CMDiffAt ∞ F x) :
    (fun y : M => Work.Diff.C.rgrad (I := I) (fun z : M => c (F z)) y) =ᶠ[𝓝 x]
      (fun y : M => deriv c (F y) • Work.Diff.C.rgrad (I := I) F y) := by
  -- `C^∞` at a point (both on the manifold and on the line) only gives `C^n` on a neighborhood
  -- for each *finite* `n`; first order is all we need, and first order *does* propagate to a
  -- neighborhood.
  have hF1 : ContMDiffAt I 𝓘(ℝ, ℝ) (1 : ℕ∞ω) F x := hF.of_le (by decide)
  have hFev : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) F y :=
    ((contMDiffAt_iff_contMDiffAt_nhds (n := (1 : ℕ∞ω)) (by decide)).1 hF1).mono
      (fun y hy => hy.mdifferentiableAt (by decide))
  have hc1 : ContDiffAt ℝ (1 : ℕ∞ω) c (F x) := hc.of_le (by decide)
  have hcev : ∀ᶠ z in 𝓝 (F x), ContDiffAt ℝ (1 : ℕ∞ω) c z := hc1.eventually (by decide)
  -- pull the differentiability of `c` back along the continuous `F`
  have hcevF : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ (1 : ℕ∞ω) c (F y) :=
    hF.continuousAt.tendsto.eventually hcev
  filter_upwards [hFev, hcevF] with y hyF hyc
  exact rgrad_comp_hasDerivAt hyF (hyc.hasStrictDerivAt (by decide)).hasDerivAt

end Work.Diff.C
