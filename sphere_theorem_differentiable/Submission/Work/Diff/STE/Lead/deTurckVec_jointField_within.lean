import Mathlib
import Submission.Work.Diff.STE.deTurck.jointField_deTurckVec
import Submission.Work.Diff.GE.covRmChartExpr_joint_smooth
import Submission.Work.Diff.GE.joint_deriv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Joint smoothness of the DeTurck field of a family of metrics on a *half-open* time slab

`Work.Diff.STE.deTurck.jointField_deTurckVec` proves that for a family `G` of metrics that is
jointly `C^∞` on an *open* time set `J`, the family `t ↦ deTurckVec (G t) gbar` is a jointly `C^∞`
family of sections on `J ×ˢ univ`.

The present module removes the openness hypothesis on the time set: for
`hG : JointMet G (Ico 0 τ ×ˢ univ)` — joint `C^∞`-ness *within* the half-open slab `[0, τ) × M` —
the DeTurck fields are jointly `C^∞` **within that slab**.

This is the form in which the short-time existence argument needs the result: the metric family is
only known (and only meaningful) for `t ≥ 0`.

The proof follows the chart computation of `jointField_deTurckVec` (expand the DeTurck field in the
coordinate frame of the chart at `x₀`, where its components are the finite sums
`deTurckChartComp = ∑ γ^{ab}(Γ^k_{ab} - Γ̃^k_{ab})`), but replaces the *pointwise* joint-smoothness
machinery (`gramInv_jointSmooth`, `chrCoord_jointSmooth`, which need `IsOpen J`) by the
*within-set* one, which is available for exactly this half-open slab:

* `Work.Diff.GE.gramInv_contMDiffOn` — joint smoothness of the inverse Gram matrix on
  `Ico 0 T ×ˢ (chartAt H x₀).source`;
* `Work.Diff.GE.chrCoord_contMDiffOn` — the same for the Christoffel symbols; the analytic input it
  needs is `Work.Diff.GE.joint_deriv`, which is exactly the within-slab derivative lemma.

Since the chart source of a point is a neighbourhood of that point *within* the slab (in the base
direction), joint smoothness on `Ico 0 T ×ˢ (chartAt H x₀).source` transports to joint smoothness on
the whole slab `Ico 0 T ×ˢ univ` by `ContMDiffWithinAt.mono_of_mem_nhdsWithin`, and the
trivialization criterion `Bundle.Trivialization.contMDiffWithinAt_iff` finishes the job.
-/

namespace Work.Diff.STE.Lead

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The chart source of a point is a neighbourhood of it within the space-time slab.**  If
`p.2` lies in the source of the chart at `x₀`, then `J ×ˢ (chartAt H x₀).source` is a neighbourhood
of `p` in the relative topology of the slab `J ×ˢ univ`. -/
private theorem chartSource_mem_nhdsWithin (J : Set ℝ) (x₀ : M) (p : ℝ × M)
    (hp : p.2 ∈ (chartAt H x₀).source) :
    J ×ˢ (chartAt H x₀).source ∈ 𝓝[J ×ˢ (univ : Set M)] p := by
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  exact ⟨univ ×ˢ (chartAt H x₀).source,
    (isOpen_univ.prod (chartAt H x₀).open_source).mem_nhds ⟨mem_univ _, hp⟩,
    fun y hy => ⟨hy.2.1, hy.1.2⟩⟩

end Helpers

theorem deTurckVec_jointField_within
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (gbar : Submission.Diff.SMet I M) (τ : ℝ)
    (hG : Work.Diff.EXT.JointMet G (Set.prod (Set.Ico (0 : ℝ) τ) (Set.univ : Set M))) :
    Work.Diff.EXT.JointField (fun t => Work.Diff.STE.DeTurck.deTurckVec (G t) gbar)
      (Set.prod (Set.Ico (0 : ℝ) τ) (Set.univ : Set M)) := by
  classical
  -- `JointMet G (Ico 0 τ ×ˢ univ)` is `JointSmooth G (Ico 0 τ)`, definitionally.
  have hJs : Submission.Diff.JointSmooth G (Set.Ico (0 : ℝ) τ) := hG
  -- The constant family of the background metric is jointly smooth on the slab.
  have hGb : Submission.Diff.JointSmooth (fun _ : ℝ => gbar) (Set.Ico (0 : ℝ) τ) := by
    have h : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ))
        (((⊤ : ℕ∞) : WithTop ℕ∞))
        ((fun b : M => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) b (gbar.inner b)) ∘
          (Prod.snd : ℝ × M → M)) :=
      gbar.contMDiff.comp contMDiff_snd
    have h2 : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ))
        (((⊤ : ℕ∞) : WithTop ℕ∞))
        (fun p : ℝ × M => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
          (((fun _ : ℝ => gbar) p.1).inner p.2))
        (Set.Ico (0 : ℝ) τ ×ˢ (univ : Set M)) := by
      simpa only [Set.univ_prod_univ, Function.comp_def] using
        h.contMDiffOn.mono (Set.prod_mono (Set.subset_univ _) (Subset.refl _))
    exact h2
  -- The analytic input of the chart computation: differentiating a jointly smooth family on the
  -- slab in a chart direction.  This is `Work.Diff.GE.joint_deriv`, verbatim.
  have hder : ∀ {u : ℝ → M → ℝ} {X : Π y : M, TangentSpace I y},
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M ↦ u p.1 p.2)
        (Set.Ico (0 : ℝ) τ ×ˢ (univ : Set M)) →
      CMDiff ∞ (T% X) →
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M ↦ mvfderiv I (u p.1) p.2 (X p.2))
        (Set.Ico (0 : ℝ) τ ×ˢ (univ : Set M)) :=
    fun hu hX => Work.Diff.GE.joint_deriv (I := I) (T := τ) hu hX
  intro p hp
  obtain ⟨t₀, x₀⟩ := p
  -- The chart components of the DeTurck field are jointly smooth on the slab.
  have hcomp : ∀ k : Fin (Module.finrank ℝ E),
      ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M =>
          Work.Diff.STE.DeTurck.deTurckChartComp (I := I) (G q.1) gbar x₀ q.2 k)
        (Set.Ico (0 : ℝ) τ ×ˢ (chartAt H x₀).source) (t₀, x₀) := by
    intro k
    have hpc : (t₀, x₀) ∈ Set.Ico (0 : ℝ) τ ×ˢ (chartAt H x₀).source :=
      ⟨hp.1, mem_chart_source H x₀⟩
    have hsum : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M => ∑ a, ∑ b,
          Work.Diff.GE.GramInv (I := I) G x₀ q.1 q.2 a b *
            (Work.Diff.GE.chrCoord (I := I) G x₀ k a b q.1 q.2
              - Work.Diff.GE.chrCoord (I := I) (fun _ : ℝ => gbar) x₀ k a b q.1 q.2))
        (Set.Ico (0 : ℝ) τ ×ˢ (chartAt H x₀).source) (t₀, x₀) := by
      refine ContMDiffWithinAt.sum (t := Finset.univ) (fun a _ => ?_)
      refine ContMDiffWithinAt.sum (t := Finset.univ) (fun b _ => ?_)
      exact ((Work.Diff.GE.gramInv_contMDiffOn (I := I) hJs x₀ a b) (t₀, x₀) hpc).mul
        (((Work.Diff.GE.chrCoord_contMDiffOn (I := I) hJs x₀ hder k a b) (t₀, x₀) hpc).sub
          ((Work.Diff.GE.chrCoord_contMDiffOn (I := I) hGb x₀ hder k a b) (t₀, x₀) hpc))
    refine hsum.congr_of_mem (fun q _ => ?_) hpc
    exact Work.Diff.STE.deTurck.deTurckChartComp_family (I := I) G (fun _ : ℝ => gbar)
      x₀ q.1 q.2 k
  -- The same, assembled in the model space.
  have hsumE : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => ∑ k : Fin (Module.finrank ℝ E),
        Work.Diff.STE.DeTurck.deTurckChartComp (I := I) (G q.1) gbar x₀ q.2 k
          • Work.Diff.GE.cBasis (E := E) k)
      (Set.Ico (0 : ℝ) τ ×ˢ (chartAt H x₀).source) (t₀, x₀) := by
    refine ContMDiffWithinAt.sum (t := Finset.univ) (fun k _ => ?_)
    exact (hcomp k).smul (contMDiffWithinAt_const (c := Work.Diff.GE.cBasis (E := E) k))
  -- Enlarge the base set: the chart source is a neighbourhood of `x₀` within `univ`.
  have hsumV : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => ∑ k : Fin (Module.finrank ℝ E),
        Work.Diff.STE.DeTurck.deTurckChartComp (I := I) (G q.1) gbar x₀ q.2 k
          • Work.Diff.GE.cBasis (E := E) k)
      (Set.Ico (0 : ℝ) τ ×ˢ (univ : Set M)) (t₀, x₀) :=
    hsumE.mono_of_mem_nhdsWithin
      (chartSource_mem_nhdsWithin (Set.Ico (0 : ℝ) τ) x₀ (t₀, x₀)
        (mem_chart_source H x₀))
  -- The chart coordinates of the DeTurck field are the same finite sum.
  set triv := trivializationAt E (TangentSpace I) x₀ with htriv
  have hbase : x₀ ∈ triv.baseSet := by
    rw [htriv, TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H x₀
  have he : (⟨x₀, Work.Diff.STE.DeTurck.deTurckVec (G t₀) gbar x₀⟩ : TangentBundle I M)
      ∈ triv.source :=
    triv.mem_source.mpr hbase
  have hcoord : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M =>
        (triv ⟨q.2, Work.Diff.STE.DeTurck.deTurckVec (G q.1) gbar q.2⟩).2)
      (Set.Ico (0 : ℝ) τ ×ˢ (univ : Set M)) (t₀, x₀) := by
    refine hsumV.congr_of_eventuallyEq_of_mem ?_ hp
    filter_upwards [chartSource_mem_nhdsWithin (Set.Ico (0 : ℝ) τ) x₀ (t₀, x₀)
      (mem_chart_source H x₀)] with q hq
    rw [htriv]
    exact Work.Diff.STE.deTurck.triv_deTurckVec_eq_sum (I := I) G (fun _ : ℝ => gbar) x₀ q.1
      hq.2
  -- The trivialization criterion converts the coordinate statement into the section statement.
  refine (Bundle.Trivialization.contMDiffWithinAt_iff (e := triv)
    (f := fun q : ℝ × M =>
      (⟨q.2, Work.Diff.STE.DeTurck.deTurckVec (G q.1) gbar q.2⟩ : TangentBundle I M))
    (s := Set.Ico (0 : ℝ) τ ×ˢ (univ : Set M)) (x₀ := (t₀, x₀)) he).mpr
    ⟨contMDiffAt_snd.contMDiffWithinAt, hcoord⟩

end Work.Diff.STE.Lead
