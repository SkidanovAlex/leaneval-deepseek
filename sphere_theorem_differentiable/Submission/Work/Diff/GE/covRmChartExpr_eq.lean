import Mathlib
import Submission.Work.Diff.GE.deps
import Submission.Work.Diff.GE.koszul
import Submission.Work.Diff.GE.rmChartExpr_eq
import Submission.Work.Diff.GE.covRm_linear
import Submission.Work.Diff.GE.Kato3.CovRmKit
import Submission.Work.Diff.GE.chrB_eq_sum_gramInv
import Submission.ChartConnection

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The chart expression for the `∇Rm` components

`Work.Diff.GE.covRmChartExpr` is the *coordinate* expression for `∇Rm` in the coordinate frame
`σ_i = frameVector x₀ · (bb i)` of the chart at `x₀`:

`(∇Rm)_m i j k l = ∂_m (Rm_i j k l) - ∑_n Γ^n_{mi} Rm_n j k l - ∑_n Γ^n_{mj} Rm_i n k l
                     - ∑_n Γ^n_{mk} Rm_i j n l - ∑_n Γ^n_{ml} Rm_i j k n`,

with `Γ^n_{ab} = chrCoord G x₀ n a b` the Christoffel symbols of the coordinate frame and
`Rm_i j k l = rmChartExpr G x₀ i j k l` the chart curvature components.  This file proves that it
computes the geometric `∇Rm`, i.e. that it agrees with the frozen `Work.Diff.GE.covRmC5`.

The proof is the standard "covariant derivative of a tensor in a frame" computation, structured as
follows (all in `namespace CovRmChartAux`):

* `mvfderiv_rmP_field_eq_dOp` : the derivative term `∂_m(Rm_i j k l)` of the chart expression is the
  `mvfderiv` of the pairing `rmP` over the four coordinate frame slots, taken with *globally* smooth
  fields agreeing with the frame near the point (this is the germ equality with `rmChartExpr`, using
  `Work.Diff.GE.rmChartExpr_eq`);
* `lcOf_field_eq_sum_chrCoord` : the connection vector `∇_{σ_m} σ_a` of a smooth field agreeing with
  the frame vector `σ_a` near the point is `∑_n chrCoord n m a • σ_n` (torsion-freeness swaps the two
  frame directions, `chrB` is the coordinate Christoffel vector, `chrB_eq_sum_chrCoord` raises the
  lower index with the inverse Gram matrix);
* `rmP_corr_fst/snd/thd/fth` : the four connection corrections of `dRmPhi`, expanded with the
  multilinearity of `rmP` (`rmP_sum_fst`, …) and `Work.Diff.GE.rmChartExpr_eq`;
* the assembly rewrites `covRmC5` into `dRmPhi` on global smooth fields
  (`Work.Diff.GE.Kato3.covRm_field_form`), expands `dRmPhi`, substitutes the five identities and
  compares with the unfolded definition of `covRmChartExpr`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Geodesic Submission.ChartCurv Submission.ChartConnection

namespace CovRmChartAux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

noncomputable section

/-- A globally `C^∞` section agreeing with the coordinate frame field `σ_i` near a point of the
chart. -/
theorem exists_cmdiff_eventuallyEq_cBasis (x₀ : M) (i : Fin (Module.finrank ℝ E)) {y : M}
    (hy : y ∈ (chartAt H x₀).source) :
    ∃ X : Π z : M, TangentSpace I z, CMDiff ∞ (T% X) ∧
      X =ᶠ[𝓝 y] frameSection (I := I) x₀ (cBasis (E := E) i) :=
  Submission.ChartConnection.exists_contMDiff_section_eventuallyEq_frameSection (I := I) x₀
    (cBasis (E := E) i) hy

/-! ## The derivative term -/

/-- The derivative term `∂_m (Rm_i j k l)` of the chart expression, computed through `rmP` on
globally smooth fields which agree with the coordinate frame near the point. -/
theorem mvfderiv_rmP_field_eq_dOp (hLC : LCSmooth I M) (G : ℝ → SMet I M) (x₀ : M) {y : M}
    (hy : y ∈ (chartAt H x₀).source) (t : ℝ) (m i j k l : Fin (Module.finrank ℝ E))
    {X₁ X₂ X₃ X₄ : Π z : M, TangentSpace I z}
    (he₁ : X₁ =ᶠ[𝓝 y] frameSection (I := I) x₀ (cBasis (E := E) i))
    (he₂ : X₂ =ᶠ[𝓝 y] frameSection (I := I) x₀ (cBasis (E := E) j))
    (he₃ : X₃ =ᶠ[𝓝 y] frameSection (I := I) x₀ (cBasis (E := E) k))
    (he₄ : X₄ =ᶠ[𝓝 y] frameSection (I := I) x₀ (cBasis (E := E) l)) :
    mvfderiv I (fun z : M ↦ rmP (G t) z (X₁ z) (X₂ z) (X₃ z) (X₄ z)) y
        (cFrame (I := I) x₀ m y)
      = dOp (I := I) x₀ m (rmChartExpr (I := I) G x₀ i j k l) t y := by
  have hsrc : ∀ᶠ z in 𝓝 y, z ∈ (chartAt H x₀).source :=
    (chartAt H x₀).open_source.mem_nhds hy
  have hgerm : (fun z : M ↦ rmP (G t) z (X₁ z) (X₂ z) (X₃ z) (X₄ z))
      =ᶠ[𝓝 y] (fun z : M ↦ rmChartExpr (I := I) G x₀ i j k l t z) := by
    filter_upwards [he₁, he₂, he₃, he₄, hsrc] with z h₁ h₂ h₃ h₄ hz
    rw [h₁, h₂, h₃, h₄, ← rmChartExpr_eq (I := I) hLC G x₀ t hz i j k l]
    rfl
  rw [mvfderiv_congr_eventuallyEq (I := I) hgerm]
  rfl

/-! ## The connection corrections -/

/-- The connection vector `∇_{σ_m} σ_a` of a smooth field agreeing with `σ_a` near the point, in the
coordinate frame: it is `∑_n Γ^n_{ma} σ_n` with `Γ^n_{ma} = chrCoord G x₀ n m a`. -/
theorem lcOf_field_eq_sum_chrCoord (hLC : LCSmooth I M) (G : ℝ → SMet I M) (x₀ : M) {y : M}
    (hy : y ∈ (chartAt H x₀).source) (t : ℝ) (m a : Fin (Module.finrank ℝ E))
    {X : Π z : M, TangentSpace I z} (hX : CMDiff ∞ (T% X))
    (hXeq : X =ᶠ[𝓝 y] frameSection (I := I) x₀ (cBasis (E := E) a)) :
    lcOf (G t) X y (cFrame (I := I) x₀ m y)
      = ∑ n, chrCoord (I := I) G x₀ n m a t y • cFrame (I := I) x₀ n y := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  obtain ⟨-, htor, -⟩ := hLC (G t)
  have hmem : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by simpa using hy
  have h1 : lcOf (G t) X y
      = lcOf (G t) (frameSection (I := I) x₀ (cBasis (E := E) a)) y :=
    Work.Diff.GE.Kato3.lcOf_congr_eventuallyEq (G t) (hX.mdifferentiableAt (by simp))
      (mdiffAt_frameSection (I := I) x₀ (cBasis (E := E) a) hy) hXeq
  have h2 : frameVector (I := I) x₀ y
        (chrB (lcOf (G t)) x₀ y (cBasis (E := E) m) (cBasis (E := E) a))
      = lcOf (G t) (frameSection (I := I) x₀ (cBasis (E := E) m)) y
          (frameVector (I := I) x₀ y (cBasis (E := E) a)) := by
    rw [chrB_apply, christoffelEval_def]
    exact Bundle.Trivialization.symmL_continuousLinearMapAt _ hmem _
  rw [h1, cFrame_apply,
    cov_frameSection_frameVector_comm (cov := lcOf (G t)) htor x₀ y hy
      (cBasis (E := E) a) (cBasis (E := E) m),
    ← h2, chrB_eq_sum_gramInv (I := I) G x₀ t hy m a, frameVector_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [chrCoord, Matrix.mulVec, dotProduct, cFrame_apply]

/-- The connection correction of the **first** slot of `dRmPhi`, in coordinates. -/
theorem rmP_corr_fst (hLC : LCSmooth I M) (G : ℝ → SMet I M) (x₀ : M) {y : M}
    (hy : y ∈ (chartAt H x₀).source) (t : ℝ) (m a b c d : Fin (Module.finrank ℝ E))
    {X : Π z : M, TangentSpace I z} (hX : CMDiff ∞ (T% X))
    (hXeq : X =ᶠ[𝓝 y] frameSection (I := I) x₀ (cBasis (E := E) a)) :
    rmP (G t) y (lcOf (G t) X y (cFrame (I := I) x₀ m y)) (cFrame (I := I) x₀ b y)
        (cFrame (I := I) x₀ c y) (cFrame (I := I) x₀ d y)
      = ∑ n, chrCoord (I := I) G x₀ n m a t y * rmChartExpr (I := I) G x₀ n b c d t y := by
  rw [lcOf_field_eq_sum_chrCoord (I := I) hLC G x₀ hy t m a hX hXeq,
    rmP_sum_fst (I := I) hLC (G t) y Finset.univ (fun n => chrCoord (I := I) G x₀ n m a t y)
      (fun n => cFrame (I := I) x₀ n y) (cFrame (I := I) x₀ b y) (cFrame (I := I) x₀ c y)
      (cFrame (I := I) x₀ d y)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← rmChartExpr_eq (I := I) hLC G x₀ t hy n b c d]
  rfl

/-- The connection correction of the **second** slot of `dRmPhi`, in coordinates. -/
theorem rmP_corr_snd (hLC : LCSmooth I M) (G : ℝ → SMet I M) (x₀ : M) {y : M}
    (hy : y ∈ (chartAt H x₀).source) (t : ℝ) (m a b c d : Fin (Module.finrank ℝ E))
    {X : Π z : M, TangentSpace I z} (hX : CMDiff ∞ (T% X))
    (hXeq : X =ᶠ[𝓝 y] frameSection (I := I) x₀ (cBasis (E := E) a)) :
    rmP (G t) y (cFrame (I := I) x₀ b y) (lcOf (G t) X y (cFrame (I := I) x₀ m y))
        (cFrame (I := I) x₀ c y) (cFrame (I := I) x₀ d y)
      = ∑ n, chrCoord (I := I) G x₀ n m a t y * rmChartExpr (I := I) G x₀ b n c d t y := by
  rw [lcOf_field_eq_sum_chrCoord (I := I) hLC G x₀ hy t m a hX hXeq,
    rmP_sum_snd (I := I) hLC (G t) y Finset.univ (fun n => chrCoord (I := I) G x₀ n m a t y)
      (fun n => cFrame (I := I) x₀ n y) (cFrame (I := I) x₀ b y) (cFrame (I := I) x₀ c y)
      (cFrame (I := I) x₀ d y)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← rmChartExpr_eq (I := I) hLC G x₀ t hy b n c d]
  rfl

/-- The connection correction of the **third** slot of `dRmPhi`, in coordinates. -/
theorem rmP_corr_thd (hLC : LCSmooth I M) (G : ℝ → SMet I M) (x₀ : M) {y : M}
    (hy : y ∈ (chartAt H x₀).source) (t : ℝ) (m a b c d : Fin (Module.finrank ℝ E))
    {X : Π z : M, TangentSpace I z} (hX : CMDiff ∞ (T% X))
    (hXeq : X =ᶠ[𝓝 y] frameSection (I := I) x₀ (cBasis (E := E) a)) :
    rmP (G t) y (cFrame (I := I) x₀ b y) (cFrame (I := I) x₀ c y)
        (lcOf (G t) X y (cFrame (I := I) x₀ m y)) (cFrame (I := I) x₀ d y)
      = ∑ n, chrCoord (I := I) G x₀ n m a t y * rmChartExpr (I := I) G x₀ b c n d t y := by
  rw [lcOf_field_eq_sum_chrCoord (I := I) hLC G x₀ hy t m a hX hXeq,
    rmP_sum_thd (I := I) hLC (G t) y Finset.univ (fun n => chrCoord (I := I) G x₀ n m a t y)
      (fun n => cFrame (I := I) x₀ n y) (cFrame (I := I) x₀ b y) (cFrame (I := I) x₀ c y)
      (cFrame (I := I) x₀ d y)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← rmChartExpr_eq (I := I) hLC G x₀ t hy b c n d]
  rfl

/-- The connection correction of the **fourth** slot of `dRmPhi`, in coordinates. -/
theorem rmP_corr_fth (hLC : LCSmooth I M) (G : ℝ → SMet I M) (x₀ : M) {y : M}
    (hy : y ∈ (chartAt H x₀).source) (t : ℝ) (m a b c d : Fin (Module.finrank ℝ E))
    {X : Π z : M, TangentSpace I z} (hX : CMDiff ∞ (T% X))
    (hXeq : X =ᶠ[𝓝 y] frameSection (I := I) x₀ (cBasis (E := E) a)) :
    rmP (G t) y (cFrame (I := I) x₀ b y) (cFrame (I := I) x₀ c y) (cFrame (I := I) x₀ d y)
        (lcOf (G t) X y (cFrame (I := I) x₀ m y))
      = ∑ n, chrCoord (I := I) G x₀ n m a t y * rmChartExpr (I := I) G x₀ b c d n t y := by
  rw [lcOf_field_eq_sum_chrCoord (I := I) hLC G x₀ hy t m a hX hXeq,
    rmP_sum_fth (I := I) hLC (G t) y Finset.univ (fun n => chrCoord (I := I) G x₀ n m a t y)
      (fun n => cFrame (I := I) x₀ n y) (cFrame (I := I) x₀ b y) (cFrame (I := I) x₀ c y)
      (cFrame (I := I) x₀ d y)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← rmChartExpr_eq (I := I) hLC G x₀ t hy b c d n]
  rfl

end

end CovRmChartAux

open CovRmChartAux

/-- **The chart expression for the components of `∇Rm`.**  On the chart at `x₀`, the coordinate
expression `covRmChartExpr` of the covariant derivative of the curvature in the coordinate frame
agrees with the geometric components `covRmC5`. -/
theorem covRmChartExpr_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (hLC : LCSmooth I M) (G : ℝ → SMet I M) (x₀ : M) (t : ℝ) {y : M}
    (hy : y ∈ (chartAt H x₀).source) (m i j k l : Fin (Module.finrank ℝ E)) :
    covRmC5 (I := I) G x₀ t y m i j k l = covRmChartExpr (I := I) G x₀ m i j k l t y := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  -- globally smooth fields agreeing with the coordinate frame near `y`
  obtain ⟨X₁, hX₁sm, hX₁eq⟩ := exists_cmdiff_eventuallyEq_cBasis (I := I) x₀ i hy
  obtain ⟨X₂, hX₂sm, hX₂eq⟩ := exists_cmdiff_eventuallyEq_cBasis (I := I) x₀ j hy
  obtain ⟨X₃, hX₃sm, hX₃eq⟩ := exists_cmdiff_eventuallyEq_cBasis (I := I) x₀ k hy
  obtain ⟨X₄, hX₄sm, hX₄eq⟩ := exists_cmdiff_eventuallyEq_cBasis (I := I) x₀ l hy
  have hX₁y : X₁ y = cFrame (I := I) x₀ i y := hX₁eq.eq_of_nhds
  have hX₂y : X₂ y = cFrame (I := I) x₀ j y := hX₂eq.eq_of_nhds
  have hX₃y : X₃ y = cFrame (I := I) x₀ k y := hX₃eq.eq_of_nhds
  have hX₄y : X₄ y = cFrame (I := I) x₀ l y := hX₄eq.eq_of_nhds
  -- step 1: `covRmC5` is `dRmPhi` on the smooth fields
  have hstep : covRmC5 (I := I) G x₀ t y m i j k l
      = dRmPhi (G t) y (cFrame (I := I) x₀ m y) X₁ X₂ X₃ X₄ := by
    simp only [covRmC5]
    rw [← hX₁y, ← hX₂y, ← hX₃y, ← hX₄y]
    exact Work.Diff.GE.Kato3.covRm_field_form hLC (G t) y (cFrame (I := I) x₀ m y)
      hX₁sm hX₂sm hX₃sm hX₄sm
  rw [hstep, dRmPhi]
  rw [hX₁y, hX₂y, hX₃y, hX₄y]
  -- step 2: the five identities
  have hder := mvfderiv_rmP_field_eq_dOp (I := I) hLC G x₀ hy t m i j k l hX₁eq hX₂eq hX₃eq hX₄eq
  have hc1 := rmP_corr_fst (I := I) hLC G x₀ hy t m i j k l hX₁sm hX₁eq
  have hc2 := rmP_corr_snd (I := I) hLC G x₀ hy t m j i k l hX₂sm hX₂eq
  have hc3 := rmP_corr_thd (I := I) hLC G x₀ hy t m k i j l hX₃sm hX₃eq
  have hc4 := rmP_corr_fth (I := I) hLC G x₀ hy t m l i j k hX₄sm hX₄eq
  rw [hder, hc1, hc2, hc3, hc4]
  simp only [covRmChartExpr]

end Work.Diff.GE
