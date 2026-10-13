import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The fundamental theorem of calculus along a radial slice of `pzIter 2 Ψ`.**

For data of the weak class, and for almost every angle `θ` (the only angles that can fail are
the two endpoints `0`, `π/2` of `Iθ`), every radial slice `s ↦ ∂_z²Ψ(s,θ)` is interval
integrable and integrates to the difference of the first `∂_z`-derivative:

`∫_{r}^{ρ} ∂_z²Ψ(s,θ) ds = ∂_zΨ(ρ,θ) - ∂_zΨ(r,θ)`, for all `ρ ∈ [r, z₁]` with `r > 0`.

This is the elementary FTC that removes a `∂_z` between the `(k-1)`-level datum `D_z^{k-1}Ψ`
and the level-`k` estimate: the weak class gives `C^∞`-smoothness of `Ψ` on the open quadrant
`(0,∞) × (0,π/2)`, hence of every `z`-slice at an interior angle, and `pzIter 2 Ψ` is exactly
the `z`-derivative of the slice of `pzIter 1 Ψ = pz Ψ` there. -/
theorem aeSliceFtcPzIter2 {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 1 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    {r z₁ : ℝ} (hr : 0 < r) (hrz : r ≤ z₁) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ∀ ρ ∈ Set.Icc r z₁,
        IntervalIntegrable (fun s : ℝ => Work.Spaces.pzIter 2 Ψ s θ)
          MeasureTheory.volume r ρ ∧
        (∫ s in r..ρ, Work.Spaces.pzIter 2 Ψ s θ)
          = Work.Spaces.pz Ψ ρ θ - Work.Spaces.pz Ψ r θ
  := by
  -- `Ψ` is `C^∞` on the open quadrant, from the weak hypothesis bundle.
  have hF : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- It suffices to prove the claim at every *interior* angle.
  refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo ?_
  intro θ hθ ρ hρ
  have hle : r ≤ ρ := hρ.1
  -- The slice `s ↦ ∂_z²Ψ(s,θ)` is continuous, hence interval integrable.
  have hcont : ContinuousOn (fun s : ℝ => Work.Spaces.pzIter 2 Ψ s θ) (Set.uIcc r ρ) := by
    rw [Set.uIcc_of_le hle]
    exact ((hF.pzIter 2).curry_z hθ).continuousOn.mono
      (fun s hs => lt_of_lt_of_le hr hs.1)
  have hint : IntervalIntegrable (fun s : ℝ => Work.Spaces.pzIter 2 Ψ s θ)
      MeasureTheory.volume r ρ := hcont.intervalIntegrable
  refine ⟨hint, ?_⟩
  -- The slice `s ↦ ∂_zΨ(s,θ)` has derivative `∂_z²Ψ` at every point of `[r,ρ]`.
  have hderiv : ∀ x ∈ Set.uIcc r ρ,
      HasDerivAt (fun z' : ℝ => Work.Spaces.pzIter 1 Ψ z' θ)
        (Work.Spaces.pzIter 2 Ψ x θ) x := by
    intro x hx
    rw [Set.uIcc_of_le hle] at hx
    have hxpos : 0 < x := lt_of_lt_of_le hr hx.1
    have hd := hF.hasDerivAt_slice_pzIter 1 hθ hxpos
    simpa using hd
  -- The fundamental theorem of calculus on the interval.
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simpa using hftc

end Work.FTS.EllipticEst.remov
