import Mathlib
import Submission.Work.Diff.GE.rmP_jointSmooth
import Submission.Work.Diff.EXT.ricCore

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Joint smoothness of `rmP` without compactness

The lemma `Work.Diff.GE.rmP_jointSmooth` proves that for a jointly smooth family of metrics
`G : ℝ → SMet I M` (smooth on `J × M`, `J` open) and smooth fields `A B C D`, the function

`(t, x) ↦ rmP (G t) x (A x) (B x) (C x) (D x)`

is jointly `C^∞` at `(t₀, x)`.  Its statement, however, assumes `[CompactSpace M]` and an
*analytic* manifold structure `[IsManifold I ((⊤ : ENat) : WithTop ENat) M]`, neither of which is used by the
proof: every helper it relies on (`cRm_jointSmooth`, `rmC4_jointSmooth`, the joint smoothness of
the Christoffel symbol and of its derivatives, `mvfderiv_jointSmooth_frame`, ...) is stated for a
merely smooth manifold `[IsManifold I ∞ M]`, and the final assembly is local: it works in the chart
at the base point `x` only.

This file redoes that assembly under the hypotheses actually needed, in the form required by the
`EXT` area: `Work.Diff.EXT.JointSmoothAt` (joint `C^∞` at `(t₀, x)`) on an open time set `J`.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

theorem rmP_jointSmoothNoCompact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : Submission.Diff.JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M)
    {A B C D : Π y : M, TangentSpace I y}
    (hA : Work.Diff.GE.SmoothField (I := I) (M := M) A)
    (hB : Work.Diff.GE.SmoothField (I := I) (M := M) B)
    (hC : Work.Diff.GE.SmoothField (I := I) (M := M) C)
    (hD : Work.Diff.GE.SmoothField (I := I) (M := M) D) :
    Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ Submission.Diff.rmP (G p.1) p.2 (A p.2) (B p.2) (C p.2) (D p.2)) t₀ x := by
  letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨(G t₀).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun y : M ↦ TangentSpace I y) := inferInstance
  set Ψ : ℝ × M → ℝ := fun p ↦ ∑ i, ∑ j, ∑ k, ∑ l,
      ((cBasis (E := E)).coord i (Submission.ChartCurv.coordFun (I := I) x A p.2))
      * ((cBasis (E := E)).coord j (Submission.ChartCurv.coordFun (I := I) x B p.2))
      * ((cBasis (E := E)).coord k (Submission.ChartCurv.coordFun (I := I) x C p.2))
      * ((cBasis (E := E)).coord l (Submission.ChartCurv.coordFun (I := I) x D p.2))
      * cRm (G p.1) x p.2 (cBasis (E := E) i) (cBasis (E := E) j) (cBasis (E := E) k)
          (cBasis (E := E) l) with hΨdef
  have hcoef : ∀ (V : Π y : M, TangentSpace I y), Work.Diff.GE.SmoothField (I := I) (M := M) V →
      ∀ m : Fin (Module.finrank ℝ E),
        ContMDiffAt ((𝓘(ℝ,ℝ)).prod I) 𝓘(ℝ,ℝ) ∞
          (fun p : ℝ × M ↦ (cBasis (E := E)).coord m
            (Submission.ChartCurv.coordFun (I := I) x V p.2)) (t₀, x) := by
    intro V hV m
    have hV' : ContMDiffAt I 𝓘(ℝ,E) ∞ (Submission.ChartCurv.coordFun (I := I) x V) x :=
      Submission.ChartCurv.contMDiffAt_coordFun (I := I) x hV (mem_chart_source H x)
    exact (LinearMap.toContinuousLinearMap ((cBasis (E := E)).coord m)).contMDiffAt.comp
      (t₀, x) (hV'.comp (t₀, x) contMDiffAt_snd)
  have hΨ : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ)
      (⊤ : ℕ∞) Ψ (t₀, x) := by
    rw [hΨdef]
    refine ContMDiffAt.sum (fun i _ ↦ ?_)
    refine ContMDiffAt.sum (fun j _ ↦ ?_)
    refine ContMDiffAt.sum (fun k _ ↦ ?_)
    refine ContMDiffAt.sum (fun l _ ↦ ?_)
    exact ((((hcoef A hA i).mul (hcoef B hB j)).mul (hcoef C hC k)).mul
      (hcoef D hD l)).mul (cRm_jointSmooth (I := I) (M := M) hJ hG ht₀ x i j k l)
  refine hΨ.congr_of_eventuallyEq ?_
  rw [nhds_prod_eq, hΨdef]
  filter_upwards [Filter.prod_mem_prod Filter.univ_mem
      ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))] with p hp
  rw [rmP_eq_sum_rmC4 (I := I) hLC G x p.1 hp.2]
  refine Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl (fun j _ ↦
    Finset.sum_congr rfl (fun k _ ↦ Finset.sum_congr rfl (fun l _ ↦ ?_))))
  rw [rmC4_eq_cRm (I := I) hLC G x p.1 hp.2 i j k l]

end Work.Diff.GE
