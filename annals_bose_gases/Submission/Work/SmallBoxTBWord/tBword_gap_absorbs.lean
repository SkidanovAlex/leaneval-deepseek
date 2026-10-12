import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.SmallBoxTBWord.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxTBWord

theorem tBword_gap_absorbs {a s ε c μ av C' : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))} {volA : ℝ} {χ : EuclideanSpace ℝ (Fin 3) → ℝ} {N : ℕ} {Ψ : Submission.BoseGases.X N → ℝ} (ha : 0 ≤ a) (hgap : C' ^ 2 * μ * av ≤ Work.SmallBoxTBWord.tbGapCoeff s ε) : C' ^ 2 * μ * av * Work.SmallBoxTBWord.cnPlusBox a A volA Ψ ≤ Work.SmallBoxTBWord.tBword a A volA χ s ε c Ψ := by
  refine le_trans (mul_le_mul_of_nonneg_right hgap (cnPlusBox_nonneg a A volA Ψ)) ?_
  exact tBword_ge_gapPart (a:=a) (s:=s) (ε:=ε) (c:=c) (A:=A) (volA:=volA) (χ:=χ) (Ψ:=Ψ) ha

end Work.SmallBoxTBWord
