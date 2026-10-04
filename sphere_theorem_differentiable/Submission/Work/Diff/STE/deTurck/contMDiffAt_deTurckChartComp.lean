import Mathlib
import Submission.Work.Diff.STE.DeTurckField
import Submission.Work.Diff.GE.gramInv_jointSmooth
import Submission.Work.Diff.GE.covRm_family_jointSmooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE.deTurck

/-
Work.Diff.STE.DeTurck.deTurckChartComp g gbar x₀ p k is the k-th chart component
∑_{ab} γ^{ab}(Γ^k_{ab} - Γ̃^k_{ab}) of the DeTurck field of two fixed smooth metrics g, gbar
(coordinate frame of the chart at x₀; GramInv = inverse Gram matrix of that frame, chrCoord = upper
Christoffel symbol). The claim below says that, for fixed metrics, this component is a smooth
FUNCTION of the base point at the chart centre.

INGREDIENTS ALREADY PROVED (unfolding deTurckChartComp and chrCoord reduces the claim to finite sums
of products of the following):
* Work.Diff.GE.gramInv_jointSmooth : for a metric family G jointly smooth on an open J ∋ t₀,
  (s,y) ↦ GramInv G x₀ s y k m is C^∞ at (t₀,x₀).
* Work.Diff.GE.chrCoord_jointSmooth : same for (s,y) ↦ chrCoord G x₀ n a b s y.
Use them with the CONSTANT family G := fun _ : ℝ => g and time 0, on J = Set.univ; the constant
family is jointly smooth because ContMDiffRiemannianMetric.contMDiff composed with Prod.snd is
(Submission.Diff.JointSmooth (fun _ : ℝ => g) Set.univ; cf. jointSmooth_const in
Submission/Work/Diff/EXT/chartRic_partial_jet.lean). Then restrict the joint (s,y)-statement to
s = 0 by composing with fun y => (0, y).
Instances: gramInv_jointSmooth needs
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E _ := inferInstance
-/
theorem contMDiffAt_deTurckChartComp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (g gbar : Submission.Diff.SMet I M) (x₀ : M) (k : Fin (Module.finrank ℝ E)) :
    ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : M => Work.Diff.STE.DeTurck.deTurckChartComp g gbar x₀ y k) x₀ := by
  classical
  -- The constant metric family is jointly smooth on `Set.univ` (with time `0`).
  have hconst : ∀ g' : Submission.Diff.SMet I M,
      Submission.Diff.JointSmooth (fun _ : ℝ => g') Set.univ := by
    intro g'
    have h : ContMDiff (𝓘(ℝ,ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ))
        (((⊤ : ℕ∞) : WithTop ℕ∞))
        ((fun b : M => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) b (g'.inner b)) ∘
          (Prod.snd : ℝ × M → M)) :=
      g'.contMDiff.comp contMDiff_snd
    simpa only [Submission.Diff.JointSmooth, Set.univ_prod_univ, Function.comp_def] using
      h.contMDiffOn
  -- The instances needed by `gramInv_jointSmooth`, for the metric `g`.
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ((⊤ : ℕ∞) : WithTop ℕ∞) E
      (fun x : M ↦ TangentSpace I x) := inferInstance
  -- The map `y ↦ (0, y)` is smooth, so a jointly smooth function restricts to the slice `s = 0`.
  have hc : ContMDiffAt I (𝓘(ℝ,ℝ).prod I) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : M => ((0 : ℝ), y)) x₀ :=
    (contMDiffAt_const : ContMDiffAt I 𝓘(ℝ,ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun _ : M => (0 : ℝ)) x₀).prodMk contMDiffAt_id
  have hGram : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiffAt I 𝓘(ℝ,ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : M => Work.Diff.GE.GramInv (I := I) (fun _ : ℝ => g) x₀ 0 y a b) x₀ := by
    intro a b
    have h := (Work.Diff.GE.gramInv_jointSmooth (I := I) (G := fun _ : ℝ => g)
      (J := Set.univ) isOpen_univ (hconst g) (Set.mem_univ (0 : ℝ)) x₀ a b).comp x₀ hc
    simpa only [Function.comp_def] using h
  have hChr : ∀ (g' : Submission.Diff.SMet I M) (a b : Fin (Module.finrank ℝ E)),
      ContMDiffAt I 𝓘(ℝ,ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : M => Work.Diff.GE.chrCoord (I := I) (fun _ : ℝ => g') x₀ k a b 0 y) x₀ := by
    intro g' a b
    have h := (Work.Diff.GE.chrCoord_jointSmooth (I := I) (G := fun _ : ℝ => g')
      (J := Set.univ) isOpen_univ (hconst g') (Set.mem_univ (0 : ℝ)) x₀ k a b).comp x₀ hc
    simpa only [Function.comp_def] using h
  -- The finite sum of products is smooth.
  have hsum : ContMDiffAt I 𝓘(ℝ,ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : M => ∑ a, ∑ b,
        Work.Diff.GE.GramInv (I := I) (fun _ : ℝ => g) x₀ 0 y a b *
          (Work.Diff.GE.chrCoord (I := I) (fun _ : ℝ => g) x₀ k a b 0 y
            - Work.Diff.GE.chrCoord (I := I) (fun _ : ℝ => gbar) x₀ k a b 0 y)) x₀ := by
    refine ContMDiffAt.sum (fun a _ => ?_)
    refine ContMDiffAt.sum (fun b _ => ?_)
    exact (hGram a b).mul ((hChr g a b).sub (hChr gbar a b))
  simpa only [Work.Diff.STE.DeTurck.deTurckChartComp] using hsum

end Work.Diff.STE.deTurck
