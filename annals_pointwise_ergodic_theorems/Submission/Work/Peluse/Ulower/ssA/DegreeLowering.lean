import Mathlib
import Submission.Work.Peluse.Ulower.ssA.Step
import Submission.Work.Peluse.Ulower.StepLe.levelTwoExtract
import Submission.Work.Peluse.Ulower.lemma74_doubling
import Submission.Work.Peluse.Pairing.boxSumPow_neg_directions
import Submission.Work.Peluse.Ulower.StepLe.blindConvertK2
import Submission.Work.Peluse.Ulower.boxNormPow_le_mass

namespace Work.Peluse.Ulower

theorem ssDegreeLoweringA {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree)
    (h1 : Work.Peluse.PeluseU2Inverse) (h2 : Work.Peluse.PeluseMajorArc P) :
    ∀ A : ℕ, 1 ≤ A → ∀ s : ℕ, 2 ≤ s → ∃ K : ℕ, 1 ≤ K ∧
      ∀ (Ns N D : ℕ) (f₀ f₁ : ℤ → ℂ) (δ : ℝ),
        2 ≤ P.natDegree → 1 ≤ N → 1 ≤ Ns → 1 ≤ D →
        (N : ℝ) ≤ (Ns : ℝ) →
        (N : ℝ) ^ P.natDegree ≤ (A : ℝ) * (Ns : ℝ) →
        (Ns : ℝ) ≤ (A : ℝ) * (N : ℝ) ^ P.natDegree →
        (D : ℝ) ≤ (Ns : ℝ) →
        Work.Peluse.SupportIn f₀ Ns → Work.Peluse.SupportIn f₁ Ns →
        (∀ x : ℤ, ‖f₀ x‖ ≤ 1) → (∀ x : ℤ, ‖f₁ x‖ ≤ 1) →
        0 < δ → δ ≤ 1 →
        δ ≤ Work.Peluse.uNormPow s (Work.Peluse.arithIcc P.leadingCoeff D)
          (Work.Peluse.symIcc (Work.Peluse.dSup P Ns N)) (Work.Peluse.dualFn N P f₀ f₁) →
        (δ * ((D : ℝ) / (Ns : ℝ))) ^ K ≤
          Work.Peluse.uNormPow 2 (Work.Peluse.arithIcc P.leadingCoeff D)
            (Work.Peluse.symIcc (Work.Peluse.dSup P Ns N)) (Work.Peluse.dualFn N P f₀ f₁) := by
  intro A hA s hs
  exact Work.Peluse.UlowerA.degree_lowering_A_of_step hd
    (Work.Peluse.UlowerA.ssStepA hd h1 h2) A hA s hs

end Work.Peluse.Ulower
