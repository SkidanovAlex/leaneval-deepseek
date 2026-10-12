import ChallengeDeps
import Submission.Work.BoseRowQ2.Rows
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.HonParams` — the honest parameters in `(μa³)`

The honest environment's `d`, `K_ℓ`, `ε_T` and `ℓ` as powers of `t = μ a v³`
(`Work.BoseBox.fsParams`), plus the two combinations the arithmetic row of FS
l.3253–3257 needs:

    ε_T (d ℓ)^{-2} = (μ a v) · t^{-13/1292},      t = μ a v³.

These identities are what make the `b/400`-reserve comparison a *constant*
condition: the `t`-powers cancel exactly (`FINDING_rowQ2allcore.md`).
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseRowQ2

open Work.BoseB7 Work.BoseB7A Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open Work.BoseGateFS

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
variable {HM : ∀ μ : ℝ, HonestModes v μ} {μ : ℝ}

/-- The honest `ε_T` is `(μa³)^{23/1292}` (`Work.BoseRowsFS.honE_eT_eq`, reproved via
`fsParams` so that it composes with the others). -/
lemma honE_eT_eq' (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v) (fc fu : LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    (Work.BoseRowsFS.honE v h fc fu HM μ).eT = (μ * _root_.BoseGases.a v ^ 3) ^ (23 / 1292 : ℝ) :=
  Work.BoseRowsFS.honE_eT_eq v h fc fu HM μ

/-- `fsXp t (-(3/2)) = t^{-3/646}`. -/
lemma fsXp_neg_three_half (t : ℝ) :
    Work.BoseBox.fsXp t (-(3 / 2)) = t ^ (-(3 / 646) : ℝ) := by
  rw [Work.BoseBox.fsXp]
  congr 1
  norm_num

/-- The honest `d` is `(μa³)^{6/323}`. -/
lemma honE_d_eq (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v) (fc fu : LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    (Work.BoseRowsFS.honE v h fc fu HM μ).d = (μ * _root_.BoseGases.a v ^ 3) ^ (6 / 323 : ℝ) := by
  simp only [Work.BoseRowsFS.honE, Work.BoseBoxFock.HonestBoxFam, Work.BoseBoxFock.KzEnvHon,
    Work.BoseFixR.KzEnvFs, Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp]

/-- The honest `K_ℓ` is `(μa³)^{-3/646}`. -/
lemma honE_Kl_eq (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v) (fc fu : LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    (Work.BoseRowsFS.honE v h fc fu HM μ).Kl = (μ * _root_.BoseGases.a v ^ 3) ^ (-(3 / 646) : ℝ) := by
  simp only [Work.BoseRowsFS.honE, Work.BoseBoxFock.HonestBoxFam, Work.BoseBoxFock.KzEnvHon,
    Work.BoseFixR.KzEnvFs, Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
  exact fsXp_neg_three_half _

/-- The honest box side is `K_ℓ(μa)^{-1/2}` (in terms of `t = μa³`). -/
lemma honE_ell_eq (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v) (fc fu : LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) {μ : ℝ} (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v) :
    (Work.BoseRowsFS.honE v h fc fu HM μ).ell
      = (μ * _root_.BoseGases.a v ^ 3) ^ (-(3 / 646) : ℝ)
        * (μ * _root_.BoseGases.a v) ^ (-(1 / 2 : ℝ)) := by
  rw [Work.BoseRowsFS.honE_ell v h fc fu HM μ hμ hav, Work.BoseBoxFock.ellH,
    if_pos (Work.BoseBox.sideAt_pos hμ hav), Work.BoseBox.sideAt, Work.BoseBox.boxSide]
  simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
  rw [fsXp_neg_three_half]

end Work.BoseRowQ2
