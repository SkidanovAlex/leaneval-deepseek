import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_FinalLeaves

theorem psiCan_C3_proved {α C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hEL : Work.FTS.FinalV2.EllLimOK3 α E)
    (hStar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' α C₀ Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 3 (fun q : ℝ × ℝ => Work.FTS.Nonlin.PsiCan Φs E g q.1 q.2 τ)
        Work.Construction.Qd := by
  intro τ hτ
  obtain ⟨gn, B, L, hC, hLip, hjet, hmu⟩ := hOK.2 (τ + 1) (by linarith)
  have hτT : τ ∈ Set.Icc (0 : ℝ) (τ + 1) := ⟨hτ, by linarith⟩
  have hE3 : ContDiffOn ℝ 3
      (Function.uncurry (E (Work.FTS.Galerkin.slice g τ))) Work.Construction.Qd :=
    (hEL (fun n => Work.FTS.Galerkin.slice (gn n) τ)
        (Work.FTS.Galerkin.slice g τ) B
        (fun n => (hC n τ hτT).1)
        (fun n => (hC n τ hτT).2.2)
        (hOK.1.1.c4 τ hτ)
        (fun j i hji z θ hzθ => hjet τ hτT j i hji z θ hzθ)).2.1
  have hΦs : ContDiffOn ℝ 3 (Function.uncurry Φs) Work.Construction.Qd :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Φs).mp hStar.smooth 3
  have h := hΦs.add hE3
  refine h.congr ?_
  intro q hq
  simp only [Function.uncurry, Work.FTS.Nonlin.PsiCan]

end Work.FTS_FinalLeaves
