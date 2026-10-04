import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicTr.DT.HAuxDefs
import Submission.Work.Diff.EXT.ConnCov.RicTr.DT.HAuxKernel
import Submission.Work.Diff.EXT.ConnCov.RicTr.StepSelTermDT

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.ConnCov.DT.hAaux

theorem step_selTerm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    {c i j : ℕ} (hc : i + j = c) (F : Fin i → Fin c) (G' : Fin j → Fin c)
    (hf : Function.Injective F) (hg : Function.Injective G')
    (hdisj : Disjoint (Set.range F) (Set.range G'))
    (hcov : ∀ k : Fin c, k ∈ Set.range F ∪ Set.range G')
    (hadd : ∀ (d : Fin i → Work.Diff.EXT.ATower.TF (I := I) (M := M))
      (Y₁ Y₂ Z : Work.Diff.EXT.ATower.TF (I := I) (M := M)),
      (∀ p, Work.Diff.EXT.ATower.SmE I M (d p)) → Work.Diff.EXT.ATower.SmE I M Y₁ →
      Work.Diff.EXT.ATower.SmE I M Y₂ → Work.Diff.EXT.ATower.SmE I M Z →
      Work.Diff.EXT.ConnCov.DT.gtTower G t i d (Y₁ + Y₂) Z
        = Work.Diff.EXT.ConnCov.DT.gtTower G t i d Y₁ Z
          + Work.Diff.EXT.ConnCov.DT.gtTower G t i d Y₂ Z)
    (v : Fin (c + 1) → Work.Diff.EXT.ATower.TF (I := I) (M := M))
    (A B C : Work.Diff.EXT.ATower.TF (I := I) (M := M))
    (hv : ∀ k, Work.Diff.EXT.ATower.SmE I M (v k))
    (hA : Work.Diff.EXT.ATower.SmE I M A) (hB : Work.Diff.EXT.ATower.SmE I M B)
    (hC : Work.Diff.EXT.ATower.SmE I M C) (x : M) :
    Work.Diff.EXT.ATower.step (Submission.Diff.lcOf (G 0))
        (Work.Diff.EXT.ConnCov.DT.selTerm G t c i j F G') v A B C x
      = Work.Diff.EXT.ConnCov.DT.selTerm G t (c + 1) (i + 1) j
          (Work.Diff.EXT.ConnCov.DT.FTen F) (Work.Diff.EXT.ConnCov.DT.Gshift G') v A B C x
        + Work.Diff.EXT.ConnCov.DT.selTerm G t (c + 1) i (j + 1)
          (Work.Diff.EXT.ConnCov.DT.Fshift F) (Work.Diff.EXT.ConnCov.DT.GTen G') v A B C x :=
  Work.Diff.EXT.ConnCov.RicTr.StepSelTermDT (I := I) (M := M)
    hLC G t hc F G' hf hg hdisj hcov hadd v A B C hv hA hB hC x

end Work.Diff.EXT.ConnCov.DT.hAaux
