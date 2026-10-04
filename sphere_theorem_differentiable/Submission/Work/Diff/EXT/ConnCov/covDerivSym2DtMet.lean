import Mathlib
import Submission.Work.Diff.EXT.SmConnVar
import Submission.Work.Diff.Evol.covRic_eq_sum_covRm_fin

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.ConnCov

theorem covDerivSym2DtMet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (T : ℝ)
    (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (y : M) (a b c : TangentSpace I y) :
    Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G t)) (Submission.Diff.dtMet G t)
        (Submission.Diff.smoothExt y a) (Submission.Diff.smoothExt y b)
        (Submission.Diff.smoothExt y c) y
      = -2 * Work.Diff.Evol.covRic (G t) y a b c := by
  -- Along a Ricci flow, `∂ₜ g = -2 Ric` (two-sided at an interior time).
  have hdtfun : Submission.Diff.dtMet G t
      = fun z p q => (-2 : ℝ) * Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) z p q := by
    funext z p q
    exact Work.Diff.GE.Sm.dtMet_eq_ric_of_flow G T hflow t ht z p q
  rw [hdtfun]
  -- `covDerivSym2` is linear in the bilinear form, so the factor `-2` comes out.
  rw [Work.Diff.GE.Sm.covDerivSym2_const_mul (Submission.Diff.lcOf (G t)) (-2)
      (fun z p q => Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) z p q)
      (Submission.Diff.smoothExt y a) (Submission.Diff.smoothExt y b)
      (Submission.Diff.smoothExt y c) y]
  -- `covDerivSym2` with `h = Ric` is the `Ext` pattern `dRicPhi` of `∇Ric`.
  rw [Work.Diff.GE.Sm.covDerivSym2_ricAt_eq_dRicPhi (G t) y (Submission.Diff.smoothExt y a)
      (Submission.Diff.smoothExt y b) (Submission.Diff.smoothExt y c)]
  rw [Work.Diff.GE.smoothExt_apply y a, ← Work.Diff.Evol.covRic_eq_dRicPhi (G t) y a b c]

end Work.Diff.EXT.ConnCov
