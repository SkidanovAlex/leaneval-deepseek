import Mathlib
import Submission.Diff.Grad
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.GE.rmChartExpr_joint_smooth
import Submission.Work.Diff.GE.covRmChartExpr_joint_smooth
import Submission.Work.Diff.GE.rmNormSq_eq_N4
import Submission.Work.Diff.GE.scalAt_eq_N2
import Submission.Work.Diff.GE.dRmNormSq_eq_N5
import Submission.Work.Diff.GE.rmChartExpr_eq
import Submission.Work.Diff.GE.covRmChartExpr_eq
import Submission.Work.Diff.GE.joint_deriv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

CONTEXT: this is one area of the Brendle–Schoen differentiable sphere theorem, driven by the lead. Read HANDOFF.md.
The contracts in Submission/Diff/Interfaces.lean and Submission/Diff/Alg.lean are frozen. Your statement's hypotheses are other
areas' contracts: USE them, do not re-prove them. Go wide: file all the independent sub-lemmas at once,
each with an exact statement, and write your assembly against their statements. If your statement looks
false or unprovable as stated, say so at once in `declare_false` with a precise reason. The lead will fix it.
ROUTE. In a chart, rmC, covRm and the frame come from g, g⁻¹ and finitely many coordinate derivatives of g.
They are smooth in (t,x) by JointSmooth. The chosen frame `onFrame` is NOT smooth in x (Classical.epsilon), but the NORMS are
frame-independent. Express them as smooth contractions with g⁻¹ in coordinates: |Rm|² = g^{ia}g^{jb}g^{kc}g^{ld}R_ijkl R_abcd.
-/

/-! ## ROUTE OF THE PROOF (final, third session)

The result is `ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞ (fun p ↦ u (G p.1) p.2) (Ico 0 T ×ˢ univ)`
for `u ∈ {rmNormSq, dRmNormSq, scalAt}` and `G` a Ricci flow on `[0,T)`.

The three norms are *frame independent*, although the chosen frame `onFrame` is not smooth in `x`.
The proof replaces the orthonormal frame by the (smooth!) *coordinate* frame of the chart at a point
and contracts with the inverse Gram matrix:

* chart data (definitions): `Submission/Work/Diff/GE/norms_defs.lean`
  (`cFrame`, `mComp`, `dOp`, `GramM`, `GramInv`, `fPair`, `koszulPair`, `rmC4`, `covRmC5`,
   `chrCoord`, `rmChartExpr`, `covRmChartExpr`, and the frame-independent contractions
   `N4`, `N2`, `N5`; `N4 Γ R = ∑ Γ⁻¹⊗Γ⁻¹⊗Γ⁻¹⊗Γ⁻¹ R R` etc.).
* pointwise identification (all proved, imported):
  - `Work.Diff.GE.rmChartExpr_eq` : `rmC4 G x₀ t y i j k l = rmChartExpr G x₀ i j k l t y`
    on the chart at `x₀`;
  - `Work.Diff.GE.covRmChartExpr_eq` : `covRmC5 G x₀ t y m i j k l
    = covRmChartExpr G x₀ m i j k l t y` on the chart at `x₀`;
  - `Work.Diff.GE.rmNormSq_eq_N4`, `Work.Diff.GE.scalAt_eq_N2`, `Work.Diff.GE.dRmNormSq_eq_N5` :
    `rmNormSq (G t) y = N4 (GramM G x₀ t y) (rmC4 G x₀ t y)`, `scalAt (G t) y = N2 (GramM …) (rmC4 …)`,
    `dRmNormSq (G t) y = N5 (GramM …) (covRmC5 …)`.
* joint smoothness of the chart data on the half-open time interval (proved, imported):
  `Work.Diff.GE.mComp_jointSmoothOn`, `Work.Diff.GE.gramInv_jointSmoothOn`,
  `Work.Diff.GE.rmChartExpr_joint_smooth`, `Work.Diff.GE.covRmChartExpr_joint_smooth`,
  all `ContMDiffOn … (Ico 0 T ×ˢ (chartAt H x₀).source)`, with the `y`-derivative lemma
  `Work.Diff.GE.joint_deriv` supplied as the explicit hypothesis `hder`
  (so these are smoothness statements for the *fixed* chart centre `x₀`, and they never mention the
  geometric curvature).
* the contraction step (this file):
  `Work.Diff.GE.rmNormSq_chart_jointSmoothOn`, `Work.Diff.GE.scalAt_chart_jointSmoothOn`,
  `Work.Diff.GE.dRmNormSq_chart_jointSmoothOn`: the full contractions
  `N4 (GramM …) (rmChartExpr …)` (resp. `N2`, and `N5` with `covRmChartExpr`) are jointly `C^∞` on
  `Ico 0 T ×ˢ (chartAt H x₀).source` — finite sums and products of jointly smooth components.
* assembly (this file): for `p = (t,x) ∈ Ico 0 T ×ˢ univ` take the chart centre `x₀ := x`; the set
  `Ico 0 T ×ˢ (chartAt H x).source` lies in `𝓝[Ico 0 T ×ˢ univ] (t,x)`
  (`Work.Diff.GE.chartLocal_mem_nhdsWithin`), so `ContMDiffWithinAt.mono_of_mem_nhdsWithin`
  transfers the chart-local statement, after rewriting the geometric quantity as the contraction
  with `rmNormSq_eq_N4` (+ `rmChartExpr_eq`) etc.

Note that `t = 0` is *not* a problem of substance: `JointSmooth G (Ico 0 T)` is smoothness
*within* the half-space, and all the derivative/regularity lemmas used above are stated with
`ContMDiffWithinAt`/`ContDiffWithinAt` on `Ico 0 T ×ˢ ·`, so the one-sided smoothness at `t = 0`
is carried along (this is what `partial_fderiv_smooth` and `joint_deriv` do).
-/

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

section Contraction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- A metric family jointly smooth on `[0,T) × M` is jointly smooth on the chart-local set
`[0,T) × (chartAt H x₀).source`. -/
theorem metSmoothOn_chart {G : ℝ → SMet I M} {T : ℝ} (hJs : JointSmooth G (Ico 0 T)) (x₀ : M) :
    MetSmoothOn (I := I) (M := M) G (Ico 0 T ×ˢ (chartAt H x₀).source) := by
  have h0 : MetSmoothOn (I := I) (M := M) G (Ico 0 T ×ˢ (univ : Set M)) := hJs
  exact h0.mono (fun p hp => ⟨hp.1, mem_univ _⟩)

/-- **The contraction step for `|Rm|²`.**  In a chart, `|Rm|²` is the full contraction `N4` of the
coordinate curvature components `rmChartExpr` with the inverse Gram matrix `GramM⁻¹`.  As a function
of `(t,x) ∈ [0,T) × (chart source)` it is `C^∞`: it is a finite sum of finite products of jointly
smooth factors (`gramInv_jointSmoothOn`, `rmChartExpr_joint_smooth`). -/
theorem rmNormSq_chart_jointSmoothOn {G : ℝ → SMet I M} {T : ℝ} (hJs : JointSmooth G (Ico 0 T))
    (x₀ : M) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ N4 (GramM (I := I) G x₀ p.1 p.2)
        (fun i j k l ↦ rmChartExpr (I := I) G x₀ i j k l p.1 p.2))
      (Ico 0 T ×ˢ (chartAt H x₀).source) := by
  have hG := metSmoothOn_chart (I := I) (M := M) hJs x₀
  have hR := rmChartExpr_joint_smooth (I := I) (M := M) hJs x₀
    (hder := fun hu hX => joint_deriv hu hX)
  intro p hp
  obtain ⟨t, y⟩ := p
  simp only [N4]
  refine ContMDiffWithinAt.sum (t := Finset.univ) (fun i _ => ?_)
  refine ContMDiffWithinAt.sum (t := Finset.univ) (fun j _ => ?_)
  refine ContMDiffWithinAt.sum (t := Finset.univ) (fun k _ => ?_)
  refine ContMDiffWithinAt.sum (t := Finset.univ) (fun l _ => ?_)
  refine ContMDiffWithinAt.sum (t := Finset.univ) (fun a _ => ?_)
  refine ContMDiffWithinAt.sum (t := Finset.univ) (fun b _ => ?_)
  refine ContMDiffWithinAt.sum (t := Finset.univ) (fun c _ => ?_)
  refine ContMDiffWithinAt.sum (t := Finset.univ) (fun d _ => ?_)
  have h1 : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ (GramM (I := I) G x₀ p.1 p.2)⁻¹ i a)
      (Ico 0 T ×ˢ (chartAt H x₀).source) (t, y) := by
    simpa only [GramInv] using gramInv_jointSmoothOn (I := I) (M := M) x₀ hG i a (t, y) hp
  have h2 : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ (GramM (I := I) G x₀ p.1 p.2)⁻¹ j b)
      (Ico 0 T ×ˢ (chartAt H x₀).source) (t, y) := by
    simpa only [GramInv] using gramInv_jointSmoothOn (I := I) (M := M) x₀ hG j b (t, y) hp
  have h3 : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ (GramM (I := I) G x₀ p.1 p.2)⁻¹ k c)
      (Ico 0 T ×ˢ (chartAt H x₀).source) (t, y) := by
    simpa only [GramInv] using gramInv_jointSmoothOn (I := I) (M := M) x₀ hG k c (t, y) hp
  have h4 : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ (GramM (I := I) G x₀ p.1 p.2)⁻¹ l d)
      (Ico 0 T ×ˢ (chartAt H x₀).source) (t, y) := by
    simpa only [GramInv] using gramInv_jointSmoothOn (I := I) (M := M) x₀ hG l d (t, y) hp
  have h5 := hR i j k l (t, y) hp
  have h6 := hR a b c d (t, y) hp
  exact (((((h1.mul h2).mul h3).mul h4).mul h5).mul h6)

/-- **The contraction step for `scal`.**  Same as `rmNormSq_chart_jointSmoothOn`, with the scalar
contraction `N2`. -/
theorem scalAt_chart_jointSmoothOn {G : ℝ → SMet I M} {T : ℝ} (hJs : JointSmooth G (Ico 0 T))
    (x₀ : M) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ N2 (GramM (I := I) G x₀ p.1 p.2)
        (fun i j k l ↦ rmChartExpr (I := I) G x₀ i j k l p.1 p.2))
      (Ico 0 T ×ˢ (chartAt H x₀).source) := by
  have hG := metSmoothOn_chart (I := I) (M := M) hJs x₀
  have hR := rmChartExpr_joint_smooth (I := I) (M := M) hJs x₀
    (hder := fun hu hX => joint_deriv hu hX)
  intro p hp
  obtain ⟨t, y⟩ := p
  simp only [N2]
  refine ContMDiffWithinAt.sum (t := Finset.univ) (fun i _ => ?_)
  refine ContMDiffWithinAt.sum (t := Finset.univ) (fun a _ => ?_)
  refine ContMDiffWithinAt.sum (t := Finset.univ) (fun j _ => ?_)
  refine ContMDiffWithinAt.sum (t := Finset.univ) (fun b _ => ?_)
  have h1 : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ (GramM (I := I) G x₀ p.1 p.2)⁻¹ i a)
      (Ico 0 T ×ˢ (chartAt H x₀).source) (t, y) := by
    simpa only [GramInv] using gramInv_jointSmoothOn (I := I) (M := M) x₀ hG i a (t, y) hp
  have h2 : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ (GramM (I := I) G x₀ p.1 p.2)⁻¹ j b)
      (Ico 0 T ×ˢ (chartAt H x₀).source) (t, y) := by
    simpa only [GramInv] using gramInv_jointSmoothOn (I := I) (M := M) x₀ hG j b (t, y) hp
  have h3 := hR i j a b (t, y) hp
  exact ((h1.mul h2).mul h3)

/-- **The contraction step for `|∇Rm|²`.**  Same, with the `(0,5)`-contraction `N5` of the
coordinate components `covRmChartExpr` of `∇Rm`. -/
theorem dRmNormSq_chart_jointSmoothOn {G : ℝ → SMet I M} {T : ℝ} (hJs : JointSmooth G (Ico 0 T))
    (x₀ : M) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ N5 (GramM (I := I) G x₀ p.1 p.2)
        (fun m i j k l ↦ covRmChartExpr (I := I) G x₀ m i j k l p.1 p.2))
      (Ico 0 T ×ˢ (chartAt H x₀).source) := by
  have hG := metSmoothOn_chart (I := I) (M := M) hJs x₀
  have hR := covRmChartExpr_joint_smooth (I := I) (M := M) hJs x₀
    (hder := fun hu hX => joint_deriv hu hX)
  intro p hp
  obtain ⟨t, y⟩ := p
  simp only [N5]
  refine ContMDiffWithinAt.sum (t := Finset.univ) (fun m _ => ?_)
  refine ContMDiffWithinAt.sum (t := Finset.univ) (fun i _ => ?_)
  refine ContMDiffWithinAt.sum (t := Finset.univ) (fun j _ => ?_)
  refine ContMDiffWithinAt.sum (t := Finset.univ) (fun k _ => ?_)
  refine ContMDiffWithinAt.sum (t := Finset.univ) (fun l _ => ?_)
  refine ContMDiffWithinAt.sum (t := Finset.univ) (fun a _ => ?_)
  refine ContMDiffWithinAt.sum (t := Finset.univ) (fun b _ => ?_)
  refine ContMDiffWithinAt.sum (t := Finset.univ) (fun c _ => ?_)
  refine ContMDiffWithinAt.sum (t := Finset.univ) (fun d _ => ?_)
  refine ContMDiffWithinAt.sum (t := Finset.univ) (fun e _ => ?_)
  have h1 : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ (GramM (I := I) G x₀ p.1 p.2)⁻¹ m a)
      (Ico 0 T ×ˢ (chartAt H x₀).source) (t, y) := by
    simpa only [GramInv] using gramInv_jointSmoothOn (I := I) (M := M) x₀ hG m a (t, y) hp
  have h2 : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ (GramM (I := I) G x₀ p.1 p.2)⁻¹ i b)
      (Ico 0 T ×ˢ (chartAt H x₀).source) (t, y) := by
    simpa only [GramInv] using gramInv_jointSmoothOn (I := I) (M := M) x₀ hG i b (t, y) hp
  have h3 : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ (GramM (I := I) G x₀ p.1 p.2)⁻¹ j c)
      (Ico 0 T ×ˢ (chartAt H x₀).source) (t, y) := by
    simpa only [GramInv] using gramInv_jointSmoothOn (I := I) (M := M) x₀ hG j c (t, y) hp
  have h4 : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ (GramM (I := I) G x₀ p.1 p.2)⁻¹ k d)
      (Ico 0 T ×ˢ (chartAt H x₀).source) (t, y) := by
    simpa only [GramInv] using gramInv_jointSmoothOn (I := I) (M := M) x₀ hG k d (t, y) hp
  have h5 : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ (GramM (I := I) G x₀ p.1 p.2)⁻¹ l e)
      (Ico 0 T ×ˢ (chartAt H x₀).source) (t, y) := by
    simpa only [GramInv] using gramInv_jointSmoothOn (I := I) (M := M) x₀ hG l e (t, y) hp
  have h6 := hR m i j k l (t, y) hp
  have h7 := hR a b c d e (t, y) hp
  exact ((((((h1.mul h2).mul h3).mul h4).mul h5).mul h6).mul h7)

/-- The chart-local set `[0,T) × (chartAt H x).source` is a neighbourhood of `(t,x)` inside
`[0,T) × M`.  This is what transfers chart-local smoothness to the ambient statement. -/
theorem chartLocal_mem_nhdsWithin (x : M) (t T : ℝ) :
    (Ico 0 T ×ˢ (chartAt H x).source) ∈ 𝓝[Ico 0 T ×ˢ (univ : Set M)] (t, x) := by
  have hmem1 : (univ : Set ℝ) ×ˢ (chartAt H x).source ∈ 𝓝 (t, x) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod Filter.univ_mem
      ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))
  refine Filter.mem_of_superset
    (Filter.inter_mem (nhdsWithin_le_nhds hmem1) self_mem_nhdsWithin) ?_
  rintro ⟨a, b⟩ ⟨⟨-, hb⟩, ha, -⟩
  exact ⟨ha, hb⟩

end Contraction

/-- **CONTRACT REG.**  The scalar curvature quantities `|Rm|²`, `|∇Rm|²` and `scal` of a Ricci flow
on `[0,T)` are jointly `C^∞` on `[0,T) × M`.

The proof is described in the module docstring: on the chart at each point the norms are the
contractions `N4`/`N2`/`N5` of the coordinate components of `Rm` (resp. `∇Rm`) with the inverse
Gram matrix of the coordinate frame, all of which are jointly smooth; the geometric functions agree
with these contractions on the chart, and the chart-local set is a neighbourhood of the point
inside `[0,T) × M`. -/
theorem norms_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : LCSmooth I M) :
    NormsSmooth I M := by
  intro G T hflow u hu
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G 0).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with rfl | rfl | rfl
  · -- `|Rm|²`
    intro p hp
    obtain ⟨t, x⟩ := p
    have hsrc : x ∈ (chartAt H x).source := mem_chart_source H x
    have hmem : (Ico 0 T ×ˢ (chartAt H x).source) ∈ 𝓝[Ico 0 T ×ˢ (univ : Set M)] (t, x) :=
      chartLocal_mem_nhdsWithin x t T
    refine ContMDiffWithinAt.mono_of_mem_nhdsWithin ?_ hmem
    refine (rmNormSq_chart_jointSmoothOn (I := I) (M := M) hflow.1 x (t, x)
      ⟨hp.1, hsrc⟩).congr_of_mem ?_ ⟨hp.1, hsrc⟩
    rintro ⟨t', y⟩ hq
    rw [rmNormSq_eq_N4 (I := I) hLC G t' hq.2]
    refine congrArg (fun R => N4 (GramM (I := I) G x t' y) R) ?_
    funext i j k l
    exact rmChartExpr_eq (I := I) hLC G x t' hq.2 i j k l
  · -- `|∇Rm|²`
    intro p hp
    obtain ⟨t, x⟩ := p
    have hsrc : x ∈ (chartAt H x).source := mem_chart_source H x
    have hmem : (Ico 0 T ×ˢ (chartAt H x).source) ∈ 𝓝[Ico 0 T ×ˢ (univ : Set M)] (t, x) :=
      chartLocal_mem_nhdsWithin x t T
    refine ContMDiffWithinAt.mono_of_mem_nhdsWithin ?_ hmem
    refine (dRmNormSq_chart_jointSmoothOn (I := I) (M := M) hflow.1 x (t, x)
      ⟨hp.1, hsrc⟩).congr_of_mem ?_ ⟨hp.1, hsrc⟩
    rintro ⟨t', y⟩ hq
    rw [dRmNormSq_eq_N5 (I := I) hLC G t' hq.2]
    refine congrArg (fun S => N5 (GramM (I := I) G x t' y) S) ?_
    funext m i j k l
    exact covRmChartExpr_eq (I := I) hLC G x t' hq.2 m i j k l
  · -- `scal`
    intro p hp
    obtain ⟨t, x⟩ := p
    have hsrc : x ∈ (chartAt H x).source := mem_chart_source H x
    have hmem : (Ico 0 T ×ˢ (chartAt H x).source) ∈ 𝓝[Ico 0 T ×ˢ (univ : Set M)] (t, x) :=
      chartLocal_mem_nhdsWithin x t T
    refine ContMDiffWithinAt.mono_of_mem_nhdsWithin ?_ hmem
    refine (scalAt_chart_jointSmoothOn (I := I) (M := M) hflow.1 x (t, x)
      ⟨hp.1, hsrc⟩).congr_of_mem ?_ ⟨hp.1, hsrc⟩
    rintro ⟨t', y⟩ hq
    rw [scalAt_eq_N2 (I := I) hLC G t' hq.2]
    refine congrArg (fun R => N2 (GramM (I := I) G x t' y) R) ?_
    funext i j k l
    exact rmChartExpr_eq (I := I) hLC G x t' hq.2 i j k l

end Work.Diff.GE
