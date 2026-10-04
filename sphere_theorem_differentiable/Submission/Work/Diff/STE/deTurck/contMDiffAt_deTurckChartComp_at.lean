import Mathlib
import Submission.Work.Diff.STE.LieMet
import Submission.Work.Diff.STE.deTurck.contMDiffAt_deTurckChartComp
import Submission.Work.Diff.GE.covRmChartExpr_joint_smooth
import Submission.Work.Diff.GE.joint_deriv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE.deTurck

set_option linter.unusedSectionVars false

theorem contMDiffAt_deTurckChartComp_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (g gbar : Submission.Diff.SMet I M) (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (c : Fin (Module.finrank ℝ E)) :
    ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M => Work.Diff.STE.DeTurck.deTurckChartComp g gbar x₀ q c)
      ((extChartAt I x₀).symm y) := by
  classical
  -- The constant metric family `fun _ => g'` is jointly smooth on all of `ℝ`.
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
  -- Restricting the time set to `Ico 0 1`.
  have hJs : ∀ g' : Submission.Diff.SMet I M,
      Submission.Diff.JointSmooth (fun _ : ℝ => g') (Set.Ico 0 1) := by
    intro g'
    refine (hconst g').mono ?_
    intro q _
    exact ⟨Set.mem_univ _, Set.mem_univ _⟩
  -- The analytic input: `mvfderiv` of a jointly smooth family along a smooth global field.
  have hder : ∀ {u : ℝ → M → ℝ} {X : Π y : M, TangentSpace I y},
      ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞ (fun p : ℝ × M ↦ u p.1 p.2)
        (Set.Ico 0 1 ×ˢ Set.univ) →
      ContMDiff I I.tangent ∞ (T% X) →
      ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
        (fun p : ℝ × M ↦ mvfderiv I (u p.1) p.2 (X p.2)) (Set.Ico 0 1 ×ˢ Set.univ) :=
    fun hu hX => Work.Diff.GE.joint_deriv (T := 1) hu hX
  -- The point at which we differentiate.
  set p : M := (extChartAt I x₀).symm y with hp_def
  have hp_ext : p ∈ (extChartAt I x₀).source := by
    rw [hp_def]
    exact PartialEquiv.map_target (extChartAt I x₀) hy
  have hp_src : p ∈ (chartAt H x₀).source := by
    rwa [extChartAt_source] at hp_ext
  have hnhds : (chartAt H x₀).source ∈ 𝓝 p :=
    (chartAt H x₀).open_source.mem_nhds hp_src
  have h0mem : ((0 : ℝ), p) ∈ Set.Ico 0 1 ×ˢ (chartAt H x₀).source :=
    ⟨⟨le_rfl, one_pos⟩, hp_src⟩
  -- The slice map `q ↦ (0, q)` is smooth.
  have hslice : ContMDiffAt I (𝓘(ℝ,ℝ).prod I) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M => ((0 : ℝ), q)) p :=
    (contMDiffAt_const : ContMDiffAt I 𝓘(ℝ,ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun _ : M => (0 : ℝ)) p).prodMk
      (contMDiffAt_id : ContMDiffAt I I ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : M => q) p)
  -- A jointly smooth function on `Ico 0 1 ×ˢ (chartAt H x₀).source` restricts to a smooth
  -- function of the base point at the centre of the slice.
  have key : ∀ {f : ℝ × M → ℝ},
      ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞ f
        (Set.Ico 0 1 ×ˢ (chartAt H x₀).source) →
      ContMDiffAt I 𝓘(ℝ,ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : M => f ((0 : ℝ), q)) p := by
    intro f hf
    have hmaps : MapsTo (fun q : M => ((0 : ℝ), q)) (chartAt H x₀).source
        (Set.Ico 0 1 ×ˢ (chartAt H x₀).source) :=
      fun q hq => ⟨⟨le_rfl, one_pos⟩, hq⟩
    have hw := hf ((0 : ℝ), p) h0mem
    have hcomp := ContMDiffWithinAt.comp p hw hslice.contMDiffWithinAt hmaps
    simpa only [Function.comp_def] using hcomp.contMDiffAt hnhds
  -- The inverse Gram matrix entries.
  have hGram : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiffAt I 𝓘(ℝ,ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M => Work.Diff.GE.GramInv (I := I) (fun _ : ℝ => g) x₀ 0 q a b) p := by
    intro a b
    exact key (f := fun z : ℝ × M =>
        Work.Diff.GE.GramInv (I := I) (fun _ : ℝ => g) x₀ z.1 z.2 a b)
      (Work.Diff.GE.gramInv_contMDiffOn (I := I) (G := fun _ : ℝ => g) (T := 1)
        (hJs g) x₀ a b)
  -- The Christoffel symbols, for either metric.
  have hChr : ∀ (g' : Submission.Diff.SMet I M) (a b : Fin (Module.finrank ℝ E)),
      ContMDiffAt I 𝓘(ℝ,ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M => Work.Diff.GE.chrCoord (I := I) (fun _ : ℝ => g') x₀ c a b 0 q) p := by
    intro g' a b
    exact key (f := fun z : ℝ × M =>
        Work.Diff.GE.chrCoord (I := I) (fun _ : ℝ => g') x₀ c a b z.1 z.2)
      (Work.Diff.GE.chrCoord_contMDiffOn (I := I) (G := fun _ : ℝ => g') (T := 1)
        (hJs g') x₀ hder c a b)
  -- The finite sum of products is smooth.
  have hsum : ContMDiffAt I 𝓘(ℝ,ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M => ∑ a, ∑ b,
        Work.Diff.GE.GramInv (I := I) (fun _ : ℝ => g) x₀ 0 q a b *
          (Work.Diff.GE.chrCoord (I := I) (fun _ : ℝ => g) x₀ c a b 0 q
            - Work.Diff.GE.chrCoord (I := I) (fun _ : ℝ => gbar) x₀ c a b 0 q)) p := by
    refine ContMDiffAt.sum (fun a _ => ?_)
    refine ContMDiffAt.sum (fun b _ => ?_)
    exact (hGram a b).mul ((hChr g a b).sub (hChr gbar a b))
  simpa only [Work.Diff.STE.DeTurck.deTurckChartComp] using hsum

end Work.Diff.STE.deTurck
