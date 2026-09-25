import Mathlib
import Submission.Work.NN.Final.Defs
import Submission.Work.NN.Final.twoCore

namespace Work.NN.Final

theorem flatTwoCore {n : ℕ} {α : ℝ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ (T2 : (Fin n → Fin n → (Fin n → ℂ) → ℂ) →ₗ[ℝ] (Fin n → (Fin n → ℂ) → ℂ))
      (C2 : ℕ → ℝ),
      (∀ k, 0 < C2 k) ∧
      (∀ η : Fin n → Fin n → (Fin n → ℂ) → ℂ,
        (∀ j l, ContDiffOn ℝ (1 : ℕ∞) (η j l) (Work.NN.Final.pd n ρ 4)) →
        (∀ j l z, η j l z = - η l j z) → Work.NN.Final.Clos2 n ρ 4 η →
        ∀ j l z, z ∈ Work.NN.Final.pd n ρ 2 →
          Work.CR.Flat.dbarCoord j (T2 η l) z - Work.CR.Flat.dbarCoord l (T2 η j) z = η j l z) ∧
      (∀ (k : ℕ) (η : Fin n → Fin n → (Fin n → ℂ) → ℂ),
        (∀ j l, ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞) (η j l) (Work.NN.Final.pd n ρ 4)) →
        (∀ j l z, η j l z = - η l j z) → Work.NN.Final.Clos2 n ρ 4 η → ∀ j : Fin n,
          Work.CR.Flat.holderNorm (k + 1) α (T2 η j) (Work.NN.Final.pd n ρ 2)
            ≤ ENNReal.ofReal (C2 k) * ∑ j, ∑ l, Work.CR.Flat.holderNorm k α (η j l) (Work.NN.Final.pd n ρ 4)) ∧
      (∀ η : Fin n → Fin n → (Fin n → ℂ) → ℂ,
        (∀ j l, ContDiffOn ℝ (⊤ : ℕ∞) (η j l) (Work.NN.Final.pd n ρ 4)) →
        (∀ j l z, η j l z = - η l j z) → Work.NN.Final.Clos2 n ρ 4 η →
        ∀ j : Fin n, ContDiffOn ℝ (⊤ : ℕ∞) (T2 η j) (Work.NN.Final.pd n ρ 2)) :=
  twoCore hρ hα0 hα1

end Work.NN.Final
