import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.SmallBoxTBWord.tBwordKin_le_kinWord
import Submission.Work.SmallBoxTBWord.winErrBox_le_cnPlus
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxTBWord

theorem tBwordKin_le_kinWord_cnPlus {a Cχ B c : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))} {volA : ℝ} {χ : EuclideanSpace ℝ (Fin 3) → ℝ} {n : ℕ} (ha : 0 < a) (hc : 0 ≤ c) (hCχ : 0 ≤ Cχ) (hB0 : 0 ≤ B) (hχ : ContDiff ℝ (⊤ : ENat) χ) (hcs : HasCompactSupport χ) (htsupp : tsupport χ ⊆ Submission.BoseGases.acube a) (hA : IsCompact A) (hsup : ∀ x, |χ x| ≤ Cχ) (hB : ∀ x : EuclideanSpace ℝ (Fin 3), (∑ k : Fin 3, (fderiv ℝ χ x (Submission.BoseGases.kcStdBasis k)) ^ 2) ≤ B) {Ψ : Submission.BoseGases.X (n + 1) → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ) : Work.SmallBoxTBWord.tBwordKin a A volA χ c Ψ ≤ 2 * Cχ ^ 2 * Submission.BoseGases.kinWord (n + 1) a Ψ + 2 * B * Work.SmallBoxTBWord.cnPlusBox a A volA Ψ := by
  have h1 := tBwordKin_le_kinWord (a := a) (Cχ := Cχ) (A := A) (volA := volA) (χ := χ)
    (n := n) (c := c) ha hc hCχ hχ hcs htsupp hA hsup hΨ
  have h2 := winErrBox_le_cnPlus (a := a) (A := A) (volA := volA) (B := B) (χ := χ) (N := n + 1)
    ha hA hB0 hB hΨ.continuous
  have h3 : 2 * winErrBox a A volA χ Ψ ≤ 2 * B * cnPlusBox a A volA Ψ := by
    nlinarith [h2]
  linarith [h1, h3]

end Work.SmallBoxTBWord
