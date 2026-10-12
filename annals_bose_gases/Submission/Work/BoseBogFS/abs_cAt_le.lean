import ChallengeDeps
import Submission.Work.BoseBogFS.CleanFunAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.abs_cAt_le` — the uniform bound for the pairing coefficient `c = ρŴ₁`

FS `eq:WSestimate`: `|Ŵ₁(k)| ≤ 16π·a v` for every `k` (proved, `Work.BoseB7AK.W1rows.W1hat_abs_le`,
under the dilute regime `R ≤ ℓ·chiR0`), together with `|ρ| ≤ cleanRhoB v μ` from the close
condition `|ρ − μ| ≤ μK_ℓ⁻²/(2¹⁴π)` of `CloseCondFS`.  Hence

`|cAt v h ρ μ k| = |ρ|·|Ŵ₁(k)| ≤ cleanCB v μ = cleanRhoB v μ · 16π (a v)`,

which is the upper-bound input of the sign row and of the oscillation estimates of the clean
Riemann row.  The regime `R ≤ ell v μ · chiR0` is obtained from `Adm` by
`Work.BoseBogFS.exists_adm_ell_ge` (the `∃ε₀` of the statement).
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem abs_cAt_le {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ ρ : ℝ,
      Work.BoseBoxFock.CloseCondFS v μ ρ → ∀ k : E3,
        |Work.BoseBogFS.cAt v h ρ μ k| ≤ Work.BoseBogFS.cleanCB v μ := by
  obtain ⟨ε, hε, hε'⟩ := exists_adm_ell_ge (v := v) hav
    (M := R / Submission.BoseGases.chiR0) (div_pos hR Submission.BoseGases.chiR0_pos)
  refine ⟨ε, hε, fun μ hμ ρ hρ k => ?_⟩
  have hMpos : 0 < R / Submission.BoseGases.chiR0 := div_pos hR Submission.BoseGases.chiR0_pos
  have hℓpos : 0 < ell v μ := lt_of_lt_of_le hMpos (hε' μ hμ)
  have hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0 := by
    have h := hε' μ hμ
    rw [div_le_iff₀ Submission.BoseGases.chiR0_pos] at h
    linarith [h]
  have hW := Work.BoseB7AK.W1rows.W1hat_abs_le (ℓ := ell v μ) hR hℓpos hv hvrad hv_supp h hRℓ k
  have hWAt : Work.BoseBogFS.W1At v h μ = Work.BoseFixR.W1fun v h (ell v μ) := rfl
  have hμpos : 0 < μ := hμ.1
  have hcl : |ρ - μ| ≤ μ * (paramsAt μ (a v)).Kl ^ (-(2 : ℝ)) / ((2 : ℝ) ^ 14 * Real.pi) := hρ
  have hKl : 0 < (paramsAt μ (a v)).Kl := by
    rw [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact Work.BoseBox.fsXp_pos (c := (-(3 / 2 : ℝ)))
      (mul_pos hμpos (pow_pos hav 3))
  have hthr : 0 ≤ μ * (paramsAt μ (a v)).Kl ^ (-(2 : ℝ)) / ((2 : ℝ) ^ 14 * Real.pi) := by
    have h1 : 0 < (paramsAt μ (a v)).Kl ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hKl _
    have h2 : (0 : ℝ) < (2 : ℝ) ^ 14 * Real.pi := by positivity
    positivity
  have hρb : |ρ| ≤ μ + μ * (paramsAt μ (a v)).Kl ^ (-(2 : ℝ)) / ((2 : ℝ) ^ 14 * Real.pi) := by
    have h := abs_le.mp hcl
    have hμabs : |μ| = μ := abs_of_pos hμpos
    rw [abs_le]
    constructor <;> linarith [h.1, h.2, hμabs, le_abs_self μ, neg_le_abs μ]
  have hρb' : |ρ| ≤ cleanRhoB v μ := by
    rw [cleanRhoB]
    exact hρb
  have hW' : |Work.BoseFixR.chat (Work.BoseBogFS.W1At v h μ) k| ≤ 16 * Real.pi * a v := by
    rw [hWAt]
    exact hW
  have hnn : 0 ≤ 16 * Real.pi * a v := by positivity
  calc |Work.BoseBogFS.cAt v h ρ μ k|
      = |ρ| * |Work.BoseFixR.chat (Work.BoseBogFS.W1At v h μ) k| := by
        rw [cAt, abs_mul]
    _ ≤ cleanRhoB v μ * (16 * Real.pi * a v) :=
        mul_le_mul hρb' hW' (abs_nonneg _) (le_trans (abs_nonneg _) hρb')
    _ = cleanCB v μ := rfl

end Work.BoseBogFS
