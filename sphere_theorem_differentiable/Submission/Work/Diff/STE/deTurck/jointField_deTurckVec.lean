import Mathlib
import Submission.Work.Diff.STE.DeTurckField
import Submission.Work.Diff.EXT.curvDefs
import Submission.Work.Diff.T.lc_smooth
import Submission.Work.Diff.STE.deTurck.deTurckVec_eq_sum_chartComp
import Submission.Work.Diff.GE.gramInv_jointSmooth
import Submission.Work.Diff.GE.covRm_family_jointSmooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Joint smoothness of the DeTurck field of a family of metrics

`Work.Diff.STE.DeTurck.deTurckVec g gbar` is the geometric DeTurck field
`W(g) = tr_g (∇^g - ∇^gbar)` (`Submission.Work.Diff.STE.DeTurckField`), and
`Work.Diff.STE.deTurck.deTurckVec_eq_sum_chartComp` expands it in the coordinate frame of the chart
at `x₀` with coefficients `deTurckChartComp g gbar x₀ y k = ∑_{ab} γ^{ab}(Γ^k_{ab} - Γ̃^k_{ab})`.

Here we prove that for a *family* of metrics `G`, `Gbar` jointly `C^∞` on the open time set `J`
(`Work.Diff.EXT.JointMet`, i.e. `Submission.Diff.JointSmooth`), the family of DeTurck fields
`t ↦ deTurckVec (G t) (Gbar t)` is a *jointly* `C^∞` family of sections on `J ×ˢ univ`
(`Work.Diff.EXT.JointField`).

The proof is a chart computation at a point `p = (t₀, x₀)`:
* in the trivialisation of the tangent bundle at `x₀`, the coordinates of
  `deTurckVec (G s) (Gbar s) y` are `∑_k deTurckChartComp (G s) (Gbar s) x₀ y k • cBasis k`
  (`triv_deTurckVec_eq_sum`, from the chart-frame expansion of the DeTurck field and the fact that
  the chart frame has constant coordinates `cBasis`);
* `deTurckChartComp (G s) (Gbar s) x₀ y k = ∑_{ab} GramInv G x₀ s y a b *
  (chrCoord G x₀ k a b s y − chrCoord Gbar x₀ k a b s y)` is definitionally equal to a finite sum of
  products of the jointly smooth chart quantities `GramInv` and `chrCoord`
  (`deTurckChartComp_family`, `Work.Diff.GE.gramInv_jointSmooth`,
  `Work.Diff.GE.chrCoord_jointSmooth`), hence jointly smooth;
* the section criterion `Bundle.Trivialization.contMDiffWithinAt_iff` converts smoothness of the
  chart coordinates into smoothness of the section.
-/

namespace Work.Diff.STE.deTurck

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

section Helpers

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The chart components of the DeTurck field, with the metric family varying in the time slot.**
For a family of metrics `G`, the chart components of `deTurckVec (G s) (Gbar s)` are the same finite
sum of `GramInv`/`chrCoord` of the family, read at time `s` (definitional unfolding: the family slot
of `deTurckChartComp` is pinned to `0` but the metric itself is `G s`). -/
lemma deTurckChartComp_family (G Gbar : ℝ → SMet I M) (x₀ : M) (s : ℝ) (y : M)
    (k : Fin (Module.finrank ℝ E)) :
    Work.Diff.STE.DeTurck.deTurckChartComp (G s) (Gbar s) x₀ y k =
      ∑ a, ∑ b, Work.Diff.GE.GramInv G x₀ s y a b *
        (Work.Diff.GE.chrCoord G x₀ k a b s y
          - Work.Diff.GE.chrCoord Gbar x₀ k a b s y) := by
  rfl

/-- **The chart coordinates of the DeTurck field of a family of metrics.**  In the trivialisation of
the tangent bundle at `x₀`, the coordinates of `deTurckVec (G s) (Gbar s) y` are the chart
components `deTurckChartComp`. -/
lemma triv_deTurckVec_eq_sum [I.Boundaryless] [T2Space M]
    (G Gbar : ℝ → SMet I M) (x₀ : M) (s : ℝ) {y : M}
    (hy : y ∈ (chartAt H x₀).source) :
    ((trivializationAt E (TangentSpace I) x₀)
        (⟨y, Work.Diff.STE.DeTurck.deTurckVec (G s) (Gbar s) y⟩ : TangentBundle I M)).2
      = ∑ k : Fin (Module.finrank ℝ E),
          Work.Diff.STE.DeTurck.deTurckChartComp (G s) (Gbar s) x₀ y k
            • Work.Diff.GE.cBasis (E := E) k := by
  set triv := trivializationAt E (TangentSpace I) x₀ with htriv
  have hb : y ∈ triv.baseSet := by
    rw [htriv, TangentBundle.trivializationAt_baseSet]; exact hy
  rw [← Trivialization.continuousLinearMapAt_apply_of_mem ℝ triv hb]
  rw [deTurckVec_eq_sum_chartComp (I := I) (G s) (Gbar s) x₀ hy]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  congr 1
  rw [Work.Diff.GE.cFrame_apply]
  simp only [Submission.Geodesic.frameVector]
  exact Trivialization.continuousLinearMapAt_symmL triv hb _

/-- **Joint smoothness of the chart components of the DeTurck field of a family.**  If `G`, `Gbar`
are jointly `C^∞` on the open time set `J`, then `(t, y) ↦ deTurckChartComp (G t) (Gbar t) x₀ y k`
is jointly `C^∞` at `(t₀, x₀)` for every `t₀ ∈ J` and every chart index `k`. -/
lemma jointSmoothAt_deTurckChartComp {G Gbar : ℝ → SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : Submission.Diff.JointSmooth G J) (hGb : Submission.Diff.JointSmooth Gbar J)
    [T2Space M] {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x₀ : M) (k : Fin (Module.finrank ℝ E)) :
    Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M => Work.Diff.STE.DeTurck.deTurckChartComp (G p.1) (Gbar p.1) x₀ p.2 k)
      t₀ x₀ := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t₀).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hsum : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => ∑ a, ∑ b, Work.Diff.GE.GramInv G x₀ p.1 p.2 a b *
        (Work.Diff.GE.chrCoord G x₀ k a b p.1 p.2
          - Work.Diff.GE.chrCoord Gbar x₀ k a b p.1 p.2)) (t₀, x₀) := by
    refine ContMDiffAt.sum (fun a _ => ?_)
    refine ContMDiffAt.sum (fun b _ => ?_)
    refine (Work.Diff.GE.gramInv_jointSmooth (I := I) hJ hG ht₀ x₀ a b).mul ?_
    exact (Work.Diff.GE.chrCoord_jointSmooth (I := I) hJ hG ht₀ x₀ k a b).sub
      (Work.Diff.GE.chrCoord_jointSmooth (I := I) hJ hGb ht₀ x₀ k a b)
  simpa only [deTurckChartComp_family] using hsum

end Helpers

theorem jointField_deTurckVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] (hLC : Submission.Diff.LCSmooth I M)
    (G Gbar : ℝ → Submission.Diff.SMet I M) (J : Set ℝ) (hJ : IsOpen J)
    (hG : Work.Diff.EXT.JointMet G (Set.prod J Set.univ))
    (hGb : Work.Diff.EXT.JointMet Gbar (Set.prod J Set.univ)) :
    Work.Diff.EXT.JointField (fun t => Work.Diff.STE.DeTurck.deTurckVec (G t) (Gbar t))
      (Set.prod J Set.univ) := by
  intro p hp
  obtain ⟨hpJ, -⟩ := hp
  have hAt : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) I.tangent ∞
      (fun q : ℝ × M =>
        (⟨q.2, Work.Diff.STE.DeTurck.deTurckVec (G q.1) (Gbar q.1) q.2⟩ :
          TangentBundle I M)) p := by
    set triv := trivializationAt E (TangentSpace I) p.2 with htriv
    have hbase : p.2 ∈ triv.baseSet := by
      rw [htriv, TangentBundle.trivializationAt_baseSet]; exact mem_chart_source H p.2
    have he : (⟨p.2, Work.Diff.STE.DeTurck.deTurckVec (G p.1) (Gbar p.1) p.2⟩ :
        TangentBundle I M) ∈ triv.source := triv.mem_source.mpr hbase
    have hcoord : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, E) ∞
        (fun q : ℝ × M =>
          (triv ⟨q.2, Work.Diff.STE.DeTurck.deTurckVec (G q.1) (Gbar q.1) q.2⟩).2) p := by
      have hsum : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, E) ∞
          (fun q : ℝ × M => ∑ k : Fin (Module.finrank ℝ E),
            Work.Diff.STE.DeTurck.deTurckChartComp (G q.1) (Gbar q.1) p.2 q.2 k
              • Work.Diff.GE.cBasis (E := E) k) p := by
        refine ContMDiffAt.sum (fun k _ => ?_)
        exact (jointSmoothAt_deTurckChartComp (I := I) hJ hG hGb hpJ p.2 k).smul
          (contMDiffAt_const (c := Work.Diff.GE.cBasis (E := E) k))
      refine hsum.congr_of_eventuallyEq ?_
      have hsrc : (univ ×ˢ (chartAt H p.2).source) ∈ 𝓝 p :=
        (isOpen_univ.prod (chartAt H p.2).open_source).mem_nhds
          ⟨trivial, mem_chart_source H p.2⟩
      filter_upwards [hsrc] with q hq
      exact triv_deTurckVec_eq_sum (I := I) G Gbar p.2 q.1 hq.2
    exact ((Trivialization.contMDiffWithinAt_iff (e := triv) (f := fun q : ℝ × M =>
        (⟨q.2, Work.Diff.STE.DeTurck.deTurckVec (G q.1) (Gbar q.1) q.2⟩ : TangentBundle I M))
        (s := univ) (x₀ := p) he).mpr
      ⟨contMDiffAt_snd.contMDiffWithinAt, hcoord.contMDiffWithinAt⟩).contMDiffAt Filter.univ_mem
  exact hAt.contMDiffWithinAt.mono (Set.subset_univ _)

/-! ## The time-slice: smoothness of the DeTurck field of two fixed metrics

The case `G ≡ g`, `Gbar ≡ gbar` of the theorem above: the DeTurck field of a *pair of fixed* smooth
metrics is a `C^∞` section of the tangent bundle.  This is the smoothness in `x` that the pull-back
step of the DeTurck trick needs for a frozen time. -/

/-- **Smoothness of the DeTurck field of two fixed metrics.**  Obtained as the time slice `t = 0` of
`jointField_deTurckVec` applied to the (constant, hence jointly smooth) families
`fun _ : ℝ => g` and `fun _ : ℝ => gbar`. -/
theorem contMDiff_deTurckVec_of_joint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] (hLC : Submission.Diff.LCSmooth I M)
    (g gbar : Submission.Diff.SMet I M) :
    Work.Diff.EXT.SmoothTField (I := I) (M := M)
      (Work.Diff.STE.DeTurck.deTurckVec g gbar) := by
  have hmet : ∀ g' : Submission.Diff.SMet I M,
      Work.Diff.EXT.JointMet (fun _ : ℝ => g') (univ ×ˢ (univ : Set M)) := by
    intro g'
    have h : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        ((fun b : M => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) b (g'.inner b)) ∘
          (Prod.snd : ℝ × M → M)) :=
      g'.contMDiff.comp contMDiff_snd
    simpa only [Work.Diff.EXT.JointMet, Set.univ_prod_univ, Function.comp_def] using h.contMDiffOn
  have hJ := jointField_deTurckVec (I := I) (M := M) hLC (fun _ : ℝ => g) (fun _ : ℝ => gbar)
    univ isOpen_univ (hmet g) (hmet gbar)
  have hslice : ContMDiffOn I I.tangent ∞
      (T% (Work.Diff.STE.DeTurck.deTurckVec g gbar)) univ := by
    have h := hJ.comp (t := univ ×ˢ (univ : Set M))
      ((contMDiffOn_const (c := (0 : ℝ)) (s := (univ : Set M))).prodMk
        (contMDiffOn_id (I := I) (M := M) (s := univ)))
      (fun y _ => ⟨trivial, trivial⟩)
    simpa only [Function.comp_def, id_eq] using h
  rw [contMDiffOn_univ] at hslice
  exact hslice

end Work.Diff.STE.deTurck
