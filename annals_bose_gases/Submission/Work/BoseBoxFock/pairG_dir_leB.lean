import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pairGSliceIdent
import Submission.Work.BoseBoxFock.pairGc13_core
import Submission.Work.BoseBoxFock.pairGc21_core
import Submission.Work.BoseBoxFock.pairGc23_core
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairG_dir_leB` — the D2 (S2) estimate for the three `Q₂` row fibres

For `Θ = 1_{Λ(ℓ)^n}·Θ₀` in the box and bounded kernel factors `A`, `B`, the Dirichlet energy
`pairEnergy ℓ (pairG₁₃ p Θ A B)` of the block I/III.1 fibre is bounded by
`C·cA²cB²·‖Θ₀‖²·(‖Θ₀‖² + Dirichlet content of Θ₀)`, and similarly for the fibres `pairG23`
(the two-slot kernel `A⊗B`) and `pairG21` (`A⊗A`).

The proof is the per-fibre assembly of `pairGFibre`
(`pairEnergy_pairGc{13,23,21}_le`) applied to the analytic cores `pairGc{13,23,21}_core`
(box identity, continuity, parametric differentiability, Cauchy–Schwarz mass and Dirichlet
bounds for the clean representatives) with the slice identities of `pairGSliceIdent`.

`sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

theorem pairG_dir_leB {n : ℕ} {l : ℝ} (hl : 0 < l) :
    ∃ C : ℝ, 0 ≤ C ∧
    (∀ (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {Θ Θ₀ : Work.BoseDict.Xn n → ℂ}
        {A B : EuclideanSpace ℝ (Fin 3) → ℂ} {cA cB : ℝ},
      ContDiff ℝ (⊤ : ℕ∞) Θ₀ →
      (∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n l) Θ₀ x) →
      Measurable A → Measurable B →
      (∀ x, ‖A x‖ ≤ cA) → (∀ x, ‖B x‖ ≤ cB) → 0 ≤ cA → 0 ≤ cB →
      Work.BoseBoxFock.L1Tails.pairEnergy l (Work.BoseBoxFock.pairG13 p Θ A B)
        ≤ C * cA ^ 2 * cB ^ 2 * Work.BoseBoxFock.pinL2 l Θ₀
            * (Work.BoseBoxFock.pinDir l Θ₀ + Work.BoseBoxFock.pinL2 l Θ₀))
    ∧
    (∀ (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {Θ Θ₀ : Work.BoseDict.Xn n → ℂ}
        {A B : EuclideanSpace ℝ (Fin 3) → ℂ} {cA cB : ℝ},
      ContDiff ℝ (⊤ : ℕ∞) Θ₀ →
      (∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n l) Θ₀ x) →
      Measurable A → Measurable B →
      (∀ x, ‖A x‖ ≤ cA) → (∀ x, ‖B x‖ ≤ cB) → 0 ≤ cA → 0 ≤ cB →
      Work.BoseBoxFock.L1Tails.pairEnergy l (Work.BoseBoxFock.pairG23 p Θ A B)
        ≤ C * cA ^ 2 * cB ^ 2 * Work.BoseBoxFock.pinL2 l Θ₀
            * (Work.BoseBoxFock.pinDir l Θ₀ + Work.BoseBoxFock.pinL2 l Θ₀))
    ∧
    (∀ (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {Θ Θ₀ : Work.BoseDict.Xn n → ℂ}
        {A : EuclideanSpace ℝ (Fin 3) → ℂ} {cA : ℝ},
      ContDiff ℝ (⊤ : ℕ∞) Θ₀ →
      (∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n l) Θ₀ x) →
      Measurable A →
      (∀ x, ‖A x‖ ≤ cA) → 0 ≤ cA →
      Work.BoseBoxFock.L1Tails.pairEnergy l (Work.BoseBoxFock.pairG21 p Θ A)
        ≤ C * cA ^ 4 * Work.BoseBoxFock.pinL2 l Θ₀
            * (Work.BoseBoxFock.pinDir l Θ₀ + Work.BoseBoxFock.pinL2 l Θ₀)) := by
  obtain ⟨C13, hC13₀, hC13⟩ := pairEnergy_pairGc13_le (ℓ := l) hl
  obtain ⟨C23, hC23₀, hC23⟩ := pairEnergy_pairGc23_le (ℓ := l) hl
  obtain ⟨C21, hC21₀, hC21⟩ := pairEnergy_pairGc21_le (ℓ := l) hl
  refine ⟨max C13 (max C23 C21), le_trans hC13₀ (le_max_left _ _), ?_, ?_, ?_⟩
  · intro p hp Θ Θ₀ A B cA cB hΘ₀ hΘ hA hB hAb hBb hcA hcB
    obtain ⟨hEq, hcont, hder, hval, hdb⟩ :=
      pairGc13_core (ℓ := l) hl p hp hΘ₀ hΘ hA hB hAb hBb hcA hcB
    have hmain := hC13 p hp hΘ₀ hcA hcB hval hder hdb hcont
      (setIntegral_memX13 hl p hΘ₀) (setIntegral_memY13 hl p hp hΘ₀)
      (setIntegral_dirX13_le hl p hΘ₀)
    rw [pairEnergy_congr_box hl hEq]
    refine hmain.trans ?_
    have hpin0 : 0 ≤ pinL2 l Θ₀ := integral_nonneg fun x => by positivity
    have hpinD0 : 0 ≤ pinDir l Θ₀ := integral_nonneg fun x => by positivity
    refine mul_le_mul_of_nonneg_right ?_ (add_nonneg hpinD0 hpin0)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg cA))
      (sq_nonneg cB)) hpin0
  · intro p hp Θ Θ₀ A B cA cB hΘ₀ hΘ hA hB hAb hBb hcA hcB
    obtain ⟨hEq, hcont, hder, hval, hdb⟩ :=
      pairGc23_core (ℓ := l) hl p hp hΘ₀ hΘ hA hB hAb hBb hcA hcB
    have hmain := hC23 p hp hΘ₀ hcA hcB hval hder hdb hcont
      (setIntegral_memX23 hl p hp hΘ₀) (setIntegral_dirX23_le hl p hp hΘ₀)
    rw [pairEnergy_congr_box hl hEq]
    refine hmain.trans ?_
    have hpin0 : 0 ≤ pinL2 l Θ₀ := integral_nonneg fun x => by positivity
    have hpinD0 : 0 ≤ pinDir l Θ₀ := integral_nonneg fun x => by positivity
    refine mul_le_mul_of_nonneg_right ?_ (add_nonneg hpinD0 hpin0)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (le_trans (le_max_left C23 C21) (le_max_right C13 (max C23 C21)))
        (sq_nonneg cA)) (sq_nonneg cB)) hpin0
  · intro p hp Θ Θ₀ A cA hΘ₀ hΘ hA hAb hcA
    obtain ⟨hEq, hcont, hder, hval, hdb⟩ :=
      pairGc21_core (ℓ := l) hl p hp hΘ₀ hΘ hA hAb hcA
    have hmain := hC21 p hp hΘ₀ hcA hval hder hdb hcont
      (setIntegral_memY21 hl p hp hΘ₀) (setIntegral_dirY21_le hl p hp hΘ₀)
    rw [pairEnergy_congr_box hl hEq]
    refine hmain.trans ?_
    have hpin0 : 0 ≤ pinL2 l Θ₀ := integral_nonneg fun x => by positivity
    have hpinD0 : 0 ≤ pinDir l Θ₀ := integral_nonneg fun x => by positivity
    refine mul_le_mul_of_nonneg_right ?_ (add_nonneg hpinD0 hpin0)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (le_trans (le_max_right C23 C21) (le_max_right C13 (max C23 C21)))
      (pow_nonneg hcA 4)) hpin0

end Work.BoseBoxFock
