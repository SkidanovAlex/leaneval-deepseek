import Mathlib
import Submission.Work.Diff.T.lc_deps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.T

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]

/-- **Reading a manifold derivative in the chart at `x₀`.** If `g : M → ℝ` is differentiable at
`p`, which lies in the chart source of `x₀`, then the manifold derivative of `g` at `p` applied to
the *frame vector* with coordinates `v` is the ordinary Fréchet derivative of `g` read in the chart
`extChartAt I x₀` at the chart coordinates of `p`, applied to `v`. -/
theorem mvfderiv_frameVector_real
    (x₀ : M) {p : M} (hp : p ∈ (chartAt H x₀).source) {g : M → ℝ}
    (hg : MDifferentiableAt I 𝓘(ℝ,ℝ) g p) (v : E) :
    mvfderiv I g p (Submission.Geodesic.frameVector (I := I) x₀ p v)
      = fderiv ℝ (fun x : E ↦ g ((extChartAt I x₀).symm x)) ((extChartAt I x₀) p) v := by
  let Φ : E → ℝ := fun y => g ((extChartAt I x₀).symm y)
  have hps : p ∈ (extChartAt I x₀).source := by rw [extChartAt_source]; exact hp
  have hsymm : (extChartAt I x₀).symm ((extChartAt I x₀) p) = p := (extChartAt I x₀).left_inv hps
  have htgt : (extChartAt I x₀) p ∈ (extChartAt I x₀).target := (extChartAt I x₀).map_source hps
  -- `Φ = g ∘ (extChartAt I x₀).symm` is differentiable at the chart coordinates of `p`
  have hΦd : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) Φ ((extChartAt I x₀) p) := by
    have hes : MDiffAt[Set.range I] (extChartAt I x₀).symm ((extChartAt I x₀) p) :=
      mdifferentiableWithinAt_extChartAt_symm (I := I) htgt
    have hgp : MDiffAt[Set.univ] g ((extChartAt I x₀).symm ((extChartAt I x₀) p)) := by
      rw [hsymm]; exact mdifferentiableWithinAt_univ.2 hg
    have h1 : MDiffAt[Set.range I] (g ∘ (extChartAt I x₀).symm) ((extChartAt I x₀) p) :=
      MDifferentiableWithinAt.comp ((extChartAt I x₀) p) hgp hes (fun _ _ => trivial)
    rw [show (Set.range I) = Set.univ from ModelWithCorners.Boundaryless.range_eq_univ] at h1
    exact mdifferentiableWithinAt_univ.1 h1
  have hΦ' : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) Φ ((extChartAt I x₀) p)
      (fderiv ℝ Φ ((extChartAt I x₀) p)) := by
    have h := hΦd.hasMFDerivAt
    rwa [mfderiv_eq_fderiv] at h
  have he : HasMFDerivAt I 𝓘(ℝ,E) (extChartAt I x₀) p
      (mfderiv I 𝓘(ℝ,E) (extChartAt I x₀) p) :=
    (mdifferentiableAt_extChartAt (I := I) hp).hasMFDerivAt
  have hcomp := HasMFDerivAt.comp (x := p) (f := extChartAt I x₀) (g := Φ) hΦ' he
  have hev : g =ᶠ[𝓝 p] (Φ ∘ (extChartAt I x₀)) := by
    filter_upwards [(chartAt H x₀).open_source.mem_nhds hp] with x hx
    have hxs : x ∈ (extChartAt I x₀).source := by rwa [extChartAt_source]
    show g x = g ((extChartAt I x₀).symm ((extChartAt I x₀) x))
    rw [(extChartAt I x₀).left_inv hxs]
  -- chain rule, written in the chart at `x₀`
  have hkey : mfderiv I 𝓘(ℝ,ℝ) g p
      = (fderiv ℝ Φ ((extChartAt I x₀) p)) ∘L (mfderiv I 𝓘(ℝ,E) (extChartAt I x₀) p) :=
    (hcomp.congr_of_eventuallyEq_abuse hev).mfderiv
  -- the frame vector is the derivative of the inverse chart applied to `v`; the derivative of the
  -- chart inverts this
  have hframe : Submission.Geodesic.frameVector (I := I) x₀ p v
      = (mfderiv[Set.range I] (extChartAt I x₀).symm ((extChartAt I x₀) p)) v := by
    rw [Submission.Geodesic.frameVector, TangentBundle.symmL_trivializationAt (I := I) hp]
    rfl
  have hvf : (mfderiv I 𝓘(ℝ,E) (extChartAt I x₀) p)
      ((mfderiv[Set.range I] (extChartAt I x₀).symm ((extChartAt I x₀) p)) v) = v := by
    have h := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' (I := I) (x := x₀) (y := p) hps
    have h2 : ((mfderiv I 𝓘(ℝ,E) (extChartAt I x₀) p) ∘L
        (mfderiv[Set.range I] (extChartAt I x₀).symm ((extChartAt I x₀) p))) v = v := by
      rw [h]; rfl
    exact h2
  have hX : mvfderiv I g p (Submission.Geodesic.frameVector (I := I) x₀ p v)
      = (mfderiv I 𝓘(ℝ,ℝ) g p)
          ((mfderiv[Set.range I] (extChartAt I x₀).symm ((extChartAt I x₀) p)) v) := by
    rw [hframe]
    rfl
  rw [hX, hkey]
  show (fderiv ℝ Φ ((extChartAt I x₀) p))
        ((mfderiv I 𝓘(ℝ,E) (extChartAt I x₀) p)
          ((mfderiv[Set.range I] (extChartAt I x₀).symm ((extChartAt I x₀) p)) v))
      = fderiv ℝ (fun x : E ↦ g ((extChartAt I x₀).symm x)) ((extChartAt I x₀) p) v
  exact (ContinuousLinearMap.comp_apply _ _ _).trans
    (congrArg (fun w => (fderiv ℝ Φ ((extChartAt I x₀) p)) w) hvf)

end Work.Diff.T
