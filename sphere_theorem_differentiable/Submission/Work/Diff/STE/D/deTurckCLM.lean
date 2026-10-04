/-
# Layer D, step 1: the DeTurck operator is a continuous bilinear form

The DeTurck operator `P(g) = -2 Ric(g) + L_{W(g)} g` is defined in
`Submission/Work/Diff/STE/LieMet.lean` as a *function* of two tangent vectors,

`deTurckOp g gbar x u v = -2 * ricAt (lcOf g) x u v + lieMet g (deTurckVec g gbar) x u v`.

The Galerkin scheme of Layer D runs on sections of `Sym² T*M`, i.e. on *continuous* bilinear forms
(`Work.Diff.STE.Bil = Π x, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ`), so before `P(g)` can be
fed into the mollifier `J` its pointwise value has to be packaged as an element of
`TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ`.  This file performs that packaging:

`deTurckCLM` produces, for every `x`, a continuous bilinear form `B` with `B u v = deTurckOp g gbar x u v`
for all `u v`.

Mathematically the point is that `deTurckOp g gbar x` is bilinear in `(u,v)`:

* `lieMet` is *definitionally* bilinear, being built from the continuous linear maps
  `g.inner x : TₓM →L TₓM →L ℝ` and `(lcOf g) W x : TₓM →L TₓM`;
* `ricAt (lcOf g) x` is bilinear in its two value slots by the curvature multilinearity
  `Work.Diff.GE.rmVec_add_middle` etc. (available once the Levi–Civita connection is smooth, which is
  the hypothesis `hLC : LCSmooth I M`); these are the four lemmas
  `Work.Diff.EXT.ricAt_add_middle_L`, `ricAt_smul_middle_L`, `ricAt_add_last_L`, `ricAt_smul_last_L`.

Bilinearity gives a linear map `TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ`; since `E` is
finite dimensional, all linear maps out of `TangentSpace I x` are automatically continuous, so that
linear map is upgraded to `TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ` by applying
`LinearMap.toContinuousLinearMap` twice (first to the inner functional, which turns
`TangentSpace I x →ₗ[ℝ] ℝ` into `TangentSpace I x →L[ℝ] ℝ`, then to the outer map).

No Riemannian structure on the bundle is needed for this: the `LinearMap.toContinuousLinearMap`
equivalence only asks for finite dimension and Hausdorffness of the (topological) tangent space, both
of which are automatic instances for `TangentSpace I x`.
-/
import Mathlib
import Submission.Work.Diff.STE.LieMet
import Submission.Work.Diff.EXT.ric_bound_of_curvBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Work.Diff.STE.DeTurck

namespace Work.Diff.STE.D

theorem deTurckCLM
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g gbar : Submission.Diff.SMet I M) (x : M) :
    ∃ B : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ,
      ∀ u v : TangentSpace I x,
        B u v = Work.Diff.STE.DeTurck.deTurckOp g gbar x u v := by
  -- Smoothness of the Levi-Civita connection of `g`, from the frozen contract `LCSmooth`.
  have hcov : (Submission.Diff.lcOf g).ContMDiffCovariantDerivative ∞ := (hLC g).1.some
  -- Bilinearity of the DeTurck operator, in the four forms required by `LinearMap.mk₂`.
  have hadd1 : ∀ u₁ u₂ v, Work.Diff.STE.DeTurck.deTurckOp g gbar x (u₁ + u₂) v
      = Work.Diff.STE.DeTurck.deTurckOp g gbar x u₁ v
        + Work.Diff.STE.DeTurck.deTurckOp g gbar x u₂ v := by
    intro u₁ u₂ v
    simp only [deTurckOp_apply, lieMet, Work.Diff.EXT.ricAt_add_middle_L g hcov x u₁ u₂ v,
      map_add, add_apply]
    ring
  have hsmul1 : ∀ (c : ℝ) u v, Work.Diff.STE.DeTurck.deTurckOp g gbar x (c • u) v
      = c • Work.Diff.STE.DeTurck.deTurckOp g gbar x u v := by
    intro c u v
    simp only [deTurckOp_apply, lieMet, Work.Diff.EXT.ricAt_smul_middle_L g hcov x c u v,
      map_smul, smul_apply, smul_eq_mul]
    ring
  have hadd2 : ∀ u v₁ v₂, Work.Diff.STE.DeTurck.deTurckOp g gbar x u (v₁ + v₂)
      = Work.Diff.STE.DeTurck.deTurckOp g gbar x u v₁
        + Work.Diff.STE.DeTurck.deTurckOp g gbar x u v₂ := by
    intro u v₁ v₂
    simp only [deTurckOp_apply, lieMet, Work.Diff.EXT.ricAt_add_last_L g hcov x u v₁ v₂,
      map_add]
    ring
  have hsmul2 : ∀ (c : ℝ) u v, Work.Diff.STE.DeTurck.deTurckOp g gbar x u (c • v)
      = c • Work.Diff.STE.DeTurck.deTurckOp g gbar x u v := by
    intro c u v
    simp only [deTurckOp_apply, lieMet, Work.Diff.EXT.ricAt_smul_last_L g hcov x c u v,
      map_smul, smul_eq_mul]
    ring
  -- The bilinear form of the DeTurck operator, as a linear map in its first argument.
  let f : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun u v => Work.Diff.STE.DeTurck.deTurckOp g gbar x u v)
      hadd1 hsmul1 hadd2 hsmul2
  -- `TangentSpace I x` is finite dimensional and Hausdorff, so linear maps out of it are
  -- automatically continuous; this upgrades `f` (twice) to a continuous bilinear form.
  let inner : (TangentSpace I x →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
    LinearMap.toContinuousLinearMap
  let B : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
    (LinearMap.toContinuousLinearMap :
      (TangentSpace I x →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ)) ≃ₗ[ℝ]
        (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)))
      (inner.toLinearMap.comp f)
  refine ⟨B, ?_⟩
  intro u v
  simp only [B, inner, f, LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearMap.mk₂_apply]

end Work.Diff.STE.D
