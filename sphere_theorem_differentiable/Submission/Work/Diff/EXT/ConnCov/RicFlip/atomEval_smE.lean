import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicFlip.OSubKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.ConnCov.RicFlip

theorem atomEval_smE
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) {a ord : ℕ}
    (τ : Fin (ord + 2) → Fin a)
    (F : Fin a → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
    (hF : ∀ j, Work.Diff.EXT.ATower.SmE I M (F j)) :
    Work.Diff.EXT.ATower.SmE I M (Work.Diff.EXT.ConnCov.RicFlip.O.atomEval G t τ F) := by
  -- the level-`0` tensor `δ = covDiff G t = ∇^{G t} - ∇^{G 0}` sends smooth fields to smooth fields
  have hbase : ∀ (w : Fin 0 → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
      (X Y : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)),
      Work.Diff.EXT.ATower.SmE I M X → Work.Diff.EXT.ATower.SmE I M Y →
      Work.Diff.EXT.ATower.SmE I M (deltaBaseM G t w X Y) := by
    intro w X Y hX hY
    have h1 := Work.Diff.EXT.ATower.lcOf_apply_smE hLC (G t) X Y hX hY
    have h2 := Work.Diff.EXT.ATower.lcOf_apply_smE hLC (G 0) X Y hX hY
    exact h1.sub_section h2
  -- `atomEval` unfolds to the `ord`-th step of the `δ`-tower on the `τ`-indexed slots
  show Work.Diff.EXT.ATower.SmE I M
    (vtowerM (G t) (deltaBaseM G t) ord
      (fun l : Fin ord => F (τ (Fin.castAdd 2 l)))
      (F (τ (Fin.natAdd ord 0))) (F (τ (Fin.natAdd ord 1))))
  exact smE_vtowerM hLC (G t) (deltaBaseM G t) hbase ord
    (fun l : Fin ord => F (τ (Fin.castAdd 2 l)))
    (F (τ (Fin.natAdd ord 0))) (F (τ (Fin.natAdd ord 1)))
    (fun l => hF _) (hF _) (hF _)

end Work.Diff.EXT.ConnCov.RicFlip
