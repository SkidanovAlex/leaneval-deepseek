import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.varLapPow_cut_comm_pairing
import Submission.Work.Diff.STE.B3.VarCoef.sum_pairing_le
import Submission.Work.Diff.STE.B3.VarCoef.Assembly

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.VarCoef

theorem sum_commOp_pairing_le {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
    (k : ℕ) (hk : 1 ≤ k) (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρ1 : ρ 0 = 1)
    (ψ : κ → (ι → ℝ) → ℝ) (hψ : ∀ γ, ContDiff ℝ (⊤ : ℕ∞) (ψ γ))
    (hψp : ∀ γ, Work.Diff.STE.Periodic1 (ψ γ))
    (A : κ → ι → ι → (ι → ℝ) → ℝ) (hA : ∀ γ a b, ContDiff ℝ (⊤ : ℕ∞) (A γ a b))
    (hAp : ∀ γ a b, Work.Diff.STE.Periodic1 (A γ a b))
    (B : κ → ι → (ι → ℝ) → ℝ) (hB : ∀ γ a, ContDiff ℝ (⊤ : ℕ∞) (B γ a))
    (hBp : ∀ γ a, Work.Diff.STE.Periodic1 (B γ a))
    (c c' : κ → (ι → ℝ) → ℝ) (hc : ∀ γ, ContDiff ℝ (⊤ : ℕ∞) (c γ))
    (hcp : ∀ γ, Work.Diff.STE.Periodic1 (c γ))
    (hc' : ∀ γ, ContDiff ℝ (⊤ : ℕ∞) (c' γ))
    (hc'p : ∀ γ, Work.Diff.STE.Periodic1 (c' γ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ (F U : κ → (ι → ℝ) → ℂ),
        (∀ γ, Work.Diff.STE.B3.VarCoef.SmoothPer (F γ)) →
        (∀ γ, Work.Diff.STE.B3.VarCoef.SmoothPer (U γ)) →
        abs ((∑ γ : κ, Work.Diff.STE.L2re (F γ)
            (Work.Diff.STE.B3.VarCoef.XOp (ψ γ) (Work.Diff.STE.B3.VarCoef.cutOp ρ ε)
              (Work.Diff.STE.B3.VarCoef.POp (c γ) (c' γ)
                (Work.Diff.STE.B3.VarCoef.varLapOp (A γ) (B γ)) k (U γ))))
          - (∑ γ : κ, Work.Diff.STE.L2re (F γ)
            (Work.Diff.STE.B3.VarCoef.POp (c γ) (c' γ)
              (Work.Diff.STE.B3.VarCoef.varLapOp (A γ) (B γ)) k
                (Work.Diff.STE.B3.VarCoef.XOp (ψ γ) (Work.Diff.STE.B3.VarCoef.cutOp ρ ε)
                  (U γ)))))
        ≤ C * Real.sqrt (∑ γ : κ,
              Work.Diff.STE.CSq (k - 1) (Work.Diff.STE.fourierCoeff (F γ)))
            * Real.sqrt (∑ γ : κ, Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (U γ))) := by
  classical
  -- per-index commutator estimate, with a constant uniform in `ε ∈ (0,1]`
  choose Cγ hCγ using fun γ : κ =>
    varLapPow_cut_comm_pairing k hk ρ hρ hρ0 hρs hρ1 (A γ) (B γ) (c γ) (c' γ) (ψ γ)
      (hA γ) (hAp γ) (hB γ) (hBp γ) (hc γ) (hcp γ) (hc' γ) (hc'p γ) (hψ γ) (hψp γ)
  have hCγnn : ∀ γ : κ, 0 ≤ Cγ γ := fun γ => (hCγ γ).1
  refine ⟨∑ γ : κ, Cγ γ, Finset.sum_nonneg fun γ _ => hCγnn γ, ?_⟩
  intro ε hε hε1 F U hF hU
  have hx : ∀ γ : κ,
      |Work.Diff.STE.L2re (F γ)
          (Work.Diff.STE.B3.VarCoef.XOp (ψ γ) (Work.Diff.STE.B3.VarCoef.cutOp ρ ε)
            (Work.Diff.STE.B3.VarCoef.POp (c γ) (c' γ)
              (Work.Diff.STE.B3.VarCoef.varLapOp (A γ) (B γ)) k (U γ)))
        - Work.Diff.STE.L2re (F γ)
          (Work.Diff.STE.B3.VarCoef.POp (c γ) (c' γ)
            (Work.Diff.STE.B3.VarCoef.varLapOp (A γ) (B γ)) k
              (Work.Diff.STE.B3.VarCoef.XOp (ψ γ) (Work.Diff.STE.B3.VarCoef.cutOp ρ ε)
                (U γ)))| ≤
      Cγ γ * Real.sqrt (Work.Diff.STE.CSq (k - 1) (Work.Diff.STE.fourierCoeff (F γ)))
        * Real.sqrt (Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (U γ))) :=
    fun γ => (hCγ γ).2 ε hε hε1 (F γ) (U γ) (hF γ).1 (hF γ).2 (hU γ).1 (hU γ).2
  have hmain := abs_sum_le_sum_mul_sqrt
    (fun γ : κ =>
      Work.Diff.STE.L2re (F γ)
          (Work.Diff.STE.B3.VarCoef.XOp (ψ γ) (Work.Diff.STE.B3.VarCoef.cutOp ρ ε)
            (Work.Diff.STE.B3.VarCoef.POp (c γ) (c' γ)
              (Work.Diff.STE.B3.VarCoef.varLapOp (A γ) (B γ)) k (U γ)))
        - Work.Diff.STE.L2re (F γ)
          (Work.Diff.STE.B3.VarCoef.POp (c γ) (c' γ)
            (Work.Diff.STE.B3.VarCoef.varLapOp (A γ) (B γ)) k
              (Work.Diff.STE.B3.VarCoef.XOp (ψ γ) (Work.Diff.STE.B3.VarCoef.cutOp ρ ε)
                (U γ))))
    (fun γ : κ => Cγ γ)
    (fun γ : κ => Work.Diff.STE.CSq (k - 1) (Work.Diff.STE.fourierCoeff (F γ)))
    (fun γ : κ => Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (U γ)))
    hCγnn
    (fun γ => Work.Diff.STE.CSq_nonneg (k - 1) (Work.Diff.STE.fourierCoeff (F γ)))
    (fun γ => Work.Diff.STE.CSq_nonneg k (Work.Diff.STE.fourierCoeff (U γ)))
    hx
  rw [← Finset.sum_sub_distrib]
  exact hmain

end Work.Diff.STE.B3.VarCoef
