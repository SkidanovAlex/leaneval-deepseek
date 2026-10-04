import Mathlib
import Submission.Work.Diff.GE.covRxn.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE.covRxnA

open scoped Manifold

/-- The `i`-th component of the derivative is the derivative of the `i`-th component.

PROOF ROUTE (the version without `hθ` is false, since `mfderiv` is `0` at non-differentiable
points).  Use `MDifferentiableAt.mvfderiv` on both sides, which rewrites `d% f x` into
`fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ,·) x f) (range I) (extChartAt I x x)`; the chart
representation of the target `Π i, Fi i` is `(θ ∘ (extChartAt I x).symm)` (`writtenInExtChartAt`
composed with the self model, whose chart is the identity: `extChartAt_self_eq`,
`modelWithCornersSelf_coe`), and `fderivWithin_apply` (Mathlib, `Analysis/Calculus/FDeriv/Prod.lean`,
`@[simp] hasFDerivWithinAt_pi'`/`differentiableWithinAt_pi` nearby) gives

`(fderivWithin ℝ Φ s z v) i = fderivWithin ℝ (fun z => Φ z i) s z v`

for `Φ : E → Π i, Fi i`, `s = range I`, `z = extChartAt I x x` (with
`UniqueDiffWithinAt ℝ (range I) (extChartAt I x x)`, from `ModelWithCorners.uniqueDiffWithinAt_image`).
The hypotheses needed are `DifferentiableWithinAt ℝ Φ (range I) (extChartAt I x x)` (from `hθ` via
`MDifferentiableWithinAt.differentiableWithinAt_comp_extChartAt_symm`, `s = univ`) and the
componentwise differentiability of `Φ` (`differentiableWithinAt_pi`).  Do NOT try
`ContinuousLinearMap.mdifferentiableAt` on `ContinuousLinearMap.proj i` (the `𝕜 = ℝ` semiring
instances `Real.semiring` vs `Field.toSemifield.toSemiring ℝ` do not unify); if you prefer the
chain-rule route, get the projection's `MDiffAt` from
`(show DifferentiableAt ℝ (fun w : Π i, Fi i => w i) w from by fun_prop).mdifferentiableAt`. -/
theorem mvfderiv_pi_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι : Type*} [Fintype ι] {Fi : ι → Type*} [∀ i, NormedAddCommGroup (Fi i)]
    [∀ i, NormedSpace ℝ (Fi i)]
    (θ : M → Π i, Fi i) (x : M) (v : TangentSpace I x) (i : ι)
    (hθ : MDifferentiableAt I (modelWithCornersSelf ℝ (Π i, Fi i)) θ x) :
    mvfderiv I (fun y : M => θ y i) x v = mvfderiv I θ x v i := by
  -- the `i`-th component of `θ` is differentiable, being the projection composed with `θ`
  have hproj : MDifferentiableAt 𝓘(ℝ, Π i, Fi i) 𝓘(ℝ, Fi i)
      (fun w : Π i, Fi i => w i) (θ x) :=
    (differentiableAt_apply (𝕜 := ℝ) i (θ x)).mdifferentiableAt
  have hL : MDifferentiableAt I 𝓘(ℝ, Fi i) (fun y : M => θ y i) x := hproj.comp x hθ
  -- write both derivatives as the derivative of the chart representation
  have h1 := hθ.mvfderiv
  have h2 := hL.mvfderiv
  -- the chart representation in the charts is differentiable (this is `hθ` read in charts)
  have hΦ : DifferentiableWithinAt ℝ
      (writtenInExtChartAt I 𝓘(ℝ, Π i, Fi i) x θ) (Set.range I) ((extChartAt I x) x) := by
    have h := hθ.mdifferentiableWithinAt.differentiableWithinAt_writtenInExtChartAt
      (I' := 𝓘(ℝ, Π i, Fi i)) (s := Set.univ)
    simpa only [Set.preimage_univ, Set.univ_inter] using h
  -- the range of the model with corners is `UniqueDiffWithinAt` at the relevant point
  have hs : UniqueDiffWithinAt ℝ (Set.range I) ((extChartAt I x) x) := by
    have h := UniqueMDiffOn.uniqueDiffWithinAt_range_inter (I := I) (s := Set.univ)
      (uniqueMDiffOn_univ) x ((extChartAt I x) x)
      ⟨(extChartAt I x).map_source (mem_extChartAt_source x), trivial⟩
    simpa only [Set.preimage_univ, Set.inter_univ] using h
  rw [h2, h1]
  -- the two chart representations are the same, up to taking the `i`-th component
  have hΨ : writtenInExtChartAt I 𝓘(ℝ, Fi i) x (fun y : M => θ y i)
      = fun z => writtenInExtChartAt I 𝓘(ℝ, Π i, Fi i) x θ z i := by
    funext z
    simp only [writtenInExtChartAt, Function.comp_apply, ext_chart_model_space_apply]
  rw [hΨ, fderivWithin_apply hΦ hs i]
  rfl

end Work.Diff.GE.covRxnA
