import Mathlib
import Submission.Work.Diff.EXT.contMDiffAt_mvfderiv_along_field

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Joint smoothness of the iterated `t`-derivative at `t = 0`

For `Ψ : ℝ × M → ℝ` jointly `C^∞` near `(0, x)`, the function

`y ↦ ∂_s ∂_τ Ψ (τ, y) |_{s = τ = 0}`

is `C^∞` at `x`.  The proof is a two-step application of the parametric fact that the
derivative in the *first* variable of a jointly smooth family of one-variable functions is
again jointly smooth:

`parametric_deriv_contDiffWithinAt` states that if `Φ : ℝ × E → ℝ` is `C^∞` on
`univ ×ˢ U` at `(t₀, ξ₀)` then so is `p ↦ deriv (fun τ => Φ (τ, p.2)) p.1`
(Mathlib's `ContDiffWithinAt.fderivWithin_apply` applied with `t = univ`).
Applying this twice and composing with `ξ ↦ (0, ξ)` produces the second derivative at `0`;
the transfer to `M` is the chart criterion `contMDiffAt_iff_source`.
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Work.Diff.EXT

namespace Work.Diff.EXT.evolX

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The parametric derivative of a jointly smooth family of functions of one variable.**
If `Φ : ℝ × E → ℝ` is `C^∞` on `univ ×ˢ U` at `(t₀, ξ₀)`, then
`p ↦ deriv (fun τ => Φ (τ, p.2)) p.1` is `C^∞` on `univ ×ˢ U` at `(t₀, ξ₀)`.

This is Mathlib's `ContDiffWithinAt.fderivWithin_apply` with parameter space `ℝ × E`, inner
variable space `ℝ` (taken within `univ`) and evaluation point `p.1`; the Fréchet derivative
within `univ` is `deriv`. -/
lemma parametric_deriv_contDiffWithinAt {U : Set E} {Φ : ℝ × E → ℝ} {t₀ : ℝ} {ξ₀ : E}
    (hξ : ξ₀ ∈ U) (hΦ : ContDiffWithinAt ℝ ∞ Φ (univ ×ˢ U) (t₀, ξ₀)) :
    ContDiffWithinAt ℝ ∞ (fun p : ℝ × E => deriv (fun τ : ℝ => Φ (τ, p.2)) p.1)
      (univ ×ˢ U) (t₀, ξ₀) := by
  -- the uncurried family `(p, τ) ↦ Φ (τ, p.2)` as a composition of `Φ` with a linear map
  have hf : ContDiffWithinAt ℝ ∞ (Function.uncurry (fun (p : ℝ × E) => fun τ : ℝ => Φ (τ, p.2)))
      (((univ : Set ℝ) ×ˢ U) ×ˢ (univ : Set ℝ)) ((t₀, ξ₀), t₀) := by
    have hψ : ContDiffWithinAt ℝ ∞ (fun q : (ℝ × E) × ℝ => (q.2, q.1.2))
        (((univ : Set ℝ) ×ˢ U) ×ˢ (univ : Set ℝ)) ((t₀, ξ₀), t₀) :=
      (((ContinuousLinearMap.snd ℝ (ℝ × E) ℝ).prod
        ((ContinuousLinearMap.snd ℝ ℝ E).comp
          (ContinuousLinearMap.fst ℝ (ℝ × E) ℝ)))).contDiff.contDiffWithinAt
    exact ContDiffWithinAt.comp (x := ((t₀, ξ₀), t₀)) (g := Φ)
      (f := fun q : (ℝ × E) × ℝ => (q.2, q.1.2))
      (s := ((univ : Set ℝ) ×ˢ U) ×ˢ (univ : Set ℝ)) (t := (univ : Set ℝ) ×ˢ U)
      hΦ hψ (fun q hq => ⟨trivial, hq.1.2⟩)
  have hg : ContDiffWithinAt ℝ ∞ (fun p : ℝ × E => p.1) (univ ×ˢ U) (t₀, ξ₀) :=
    (ContinuousLinearMap.fst ℝ ℝ E).contDiff.contDiffWithinAt
  have hk : ContDiffWithinAt ℝ ∞ (fun _ : ℝ × E => (1 : ℝ)) (univ ×ˢ U) (t₀, ξ₀) :=
    contDiffWithinAt_const
  have hmain := ContDiffWithinAt.fderivWithin_apply
    (f := fun (p : ℝ × E) => fun τ : ℝ => Φ (τ, p.2))
    (g := fun p : ℝ × E => p.1) (k := fun _ : ℝ × E => (1 : ℝ))
    (t := (univ : Set ℝ)) (s := (univ : Set ℝ) ×ˢ U) (x₀ := (t₀, ξ₀))
    (ht := uniqueDiffOn_univ) (hmn := le_of_eq rfl)
    (hx₀ := ⟨trivial, hξ⟩) (hst := fun _ _ => trivial) hf hg hk
  refine hmain.congr (fun p _ => ?_) ?_
  · simp only [deriv, fderivWithin_univ]
  · simp only [deriv, fderivWithin_univ]

theorem jointSmoothAt_iteratedDeriv_two_tzero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {Ψ : ℝ × M → ℝ} {x : M}
    (hΨ : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ)
      (⊤ : ℕ∞) Ψ (0, x)) :
    ContMDiffAt I (modelWithCornersSelf ℝ ℝ) (⊤ : ℕ∞)
      (fun y : M => deriv (fun s : ℝ => deriv (fun τ : ℝ => Ψ (τ, y)) s) 0) x := by
  have hΨ' : JointSmoothAt I M Ψ 0 x := hΨ
  -- the family written in the chart at `x`
  have hΦsm : ContDiffWithinAt ℝ ∞ (fun p : ℝ × E => Ψ (p.1, (extChartAt I x).symm p.2))
      (univ ×ˢ (extChartAt I x).target) (0, (extChartAt I x) x) :=
    contDiffWithinAt_infty.2 (fun k => contDiffWithinAt_chart_family k hΨ')
  have hξ : (extChartAt I x) x ∈ (extChartAt I x).target := mem_extChartAt_target x
  -- first `∂_τ`, then `∂_s`, in the chart
  have h1 := parametric_deriv_contDiffWithinAt hξ hΦsm
  have h2 := parametric_deriv_contDiffWithinAt hξ h1
  -- evaluate the second `t`-derivative at `0`
  have hψ0 : ContDiffWithinAt ℝ ∞ (fun ξ : E => ((0 : ℝ), ξ)) (extChartAt I x).target
      ((extChartAt I x) x) :=
    (ContinuousLinearMap.inr ℝ ℝ E).contDiff.contDiffWithinAt
  have h3 : ContDiffWithinAt ℝ ∞
      (fun ξ : E => deriv (fun s : ℝ => deriv (fun τ : ℝ => Ψ (τ, (extChartAt I x).symm ξ)) s) 0)
      (extChartAt I x).target ((extChartAt I x) x) :=
    ContDiffWithinAt.comp _ h2 hψ0 (fun ξ hξ' => ⟨trivial, hξ'⟩)
  -- the chart target agrees with the model range near the image of `x`
  have hTev : (extChartAt I x).target =ᶠ[𝓝 ((extChartAt I x) x)] Set.range I := by
    obtain ⟨u, hu, huT⟩ := (mem_nhdsWithin_iff_exists_mem_nhds_inter).1
      (extChartAt_target_mem_nhdsWithin (I := I) x)
    filter_upwards [hu] with z hz
    exact propext ⟨fun h => extChartAt_target_subset_range x h,
      fun h => huT ⟨hz, h⟩⟩
  -- transfer back to the manifold
  refine (contMDiffAt_iff_source (I := I) (I' := 𝓘(ℝ, ℝ)) (x := x)).2 ?_
  rw [contMDiffWithinAt_iff_contDiffWithinAt]
  exact h3.congr_set hTev

end

end Work.Diff.EXT.evolX
