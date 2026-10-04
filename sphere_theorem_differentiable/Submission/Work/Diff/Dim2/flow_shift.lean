import Mathlib
import Submission.Work.Diff.Dim2.Lib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set

/-- **The time-shift (group) law for a flow in the two-parameter convention.**

The contract `Submission.Diff.SmoothFlow` (proved by `Submission.Work.Diff.ODE.flow_smooth`,
reachable through `Submission.Work.Diff.Dim2.Lib`) produces a flow in the convention
`Φ s t x` = "position at time `t` of the integral curve through `x` at time `s`", with
`Φ s s x = x` and the cocycle `Φ t u (Φ s t x) = Φ s u x`.  The *level crossing engine*
`Submission.GSCross`, on the other hand, works with a flow in the convention
`φ x t` = "position at time `t` of the integral curve through `x` at time `0`", with `φ x 0 = x` and
`φ (φ x s) t = φ x (s + t)`.

The two are related by `φ x t := Φ 0 t x`, and the missing ingredient is exactly the statement
below: `Φ 0 t (Φ 0 s x) = Φ 0 (s + t) x`.  Both sides are integral curves of the (time independent)
field `V` and they agree at `t = 0`, so this is uniqueness of solutions of an autonomous ODE --
`Submission.Work.Diff.ODE.eqOn_Ioo_of_isXCurveOn` (or Mathlib's
`isMIntegralCurveOn_Ioo_eqOn_of_contMDiff`) after rewriting the `HasMFDerivAt` form of the contract
into the `IsXCurve`/`IsMIntegralCurve` form.  The boundaryless hypothesis and the smoothness of the
section `x ↦ ⟨x, V x⟩` are what the cited uniqueness lemmas want; the latter is derivable from
`hΦsm` and `hΦself` alone (`V y = ∂_τ Φ s τ y|_{τ=s}`) but is taken as a hypothesis here. -/
theorem flow_shift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless]
    {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M}
    (hVsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))))
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2))
    (hΦself : ∀ s x, Φ s s x = x)
    (hΦderiv : ∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x)))) :
    ∀ s t x, Φ 0 t (Φ 0 s x) = Φ 0 (s + t) x := by
  -- `V` is a `C¹` (indeed `C^∞`) section, so Mathlib's uniqueness theorem for integral curves
  -- of an autonomous field applies.
  have hv : ContMDiff I I.tangent 1 (fun y : M => (⟨y, V y⟩ : TangentBundle I M)) :=
    hVsm.of_le (by simp)
  intro s t x
  -- the two curves are integral curves of `V`
  have hγ1 : IsMIntegralCurve (fun τ : ℝ => Φ 0 τ (Φ 0 s x)) V :=
    fun τ => hΦderiv 0 τ (Φ 0 s x)
  have hbase : IsMIntegralCurve (fun τ : ℝ => Φ 0 τ x) V := fun τ => hΦderiv 0 τ x
  have hγ2 : IsMIntegralCurve (fun τ : ℝ => Φ 0 (τ + s) x) V := hbase.comp_add s
  -- they agree at time `0`
  have h0 : (fun τ : ℝ => Φ 0 τ (Φ 0 s x)) 0 = (fun τ : ℝ => Φ 0 (τ + s) x) 0 := by
    simp only [hΦself, zero_add]
  -- hence they are equal, by uniqueness of integral curves on a boundaryless manifold
  have heq : (fun τ : ℝ => Φ 0 τ (Φ 0 s x)) = (fun τ : ℝ => Φ 0 (τ + s) x) :=
    isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hv hγ1 hγ2 h0
  have ht := congrFun heq t
  simpa [add_comm] using ht

end Work.Diff.Dim2
