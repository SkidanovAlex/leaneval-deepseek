import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Submission.Work.BoseBoxFock.pairGc23DirV2
import Submission.Work.BoseBoxFock.pairGc23NormSqLeV2
import Submission.Work.BoseBoxFock.pairGc23_continuous
import Submission.Work.BoseBoxFock.pairGc23_eq_on_box
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairGc23_core` — the five analytic conjuncts of the clean `pairGc23` fibre

Assembled from the proved pieces `pairGc23_eq_on_box` (the box identity), `pairGc23_continuous`,
`pairGc23NormSqLeV2` (the Cauchy–Schwarz mass bound) and `pairGc23DirV2` (parametric
differentiability together with the Dirichlet bound).

`sorry`-free.
-/

noncomputable section

namespace Work.BoseBoxFock

theorem pairGc23_core {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ Θ₀ : Work.BoseDict.Xn n → ℂ}
    {A B : EuclideanSpace ℝ (Fin 3) → ℂ} {cA cB : ℝ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀)
    (hΘ : ∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n ℓ) Θ₀ x)
    (hA : Measurable A) (hB : Measurable B)
    (hAb : ∀ x, ‖A x‖ ≤ cA) (hBb : ∀ x, ‖B x‖ ≤ cB) (hcA : 0 ≤ cA) (hcB : 0 ≤ cB) :
    (∀ w y : EuclideanSpace ℝ (Fin 3), w ∈ Work.BoseK15.corpusBox.boxL ℓ →
        y ∈ Work.BoseK15.corpusBox.boxL ℓ → pairG23 p Θ A B w y = pairGc23 ℓ p hp Θ₀ A B w y)
    ∧ Continuous (Function.uncurry (pairGc23 ℓ p hp Θ₀ A B))
    ∧ (∀ z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        DifferentiableAt ℝ (fun w' => pairGc23 ℓ p hp Θ₀ A B w' z.2) z.1)
    ∧ (∀ w y : EuclideanSpace ℝ (Fin 3), ‖pairGc23 ℓ p hp Θ₀ A B w y‖ ^ 2
          ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 6 * memX23 ℓ p Θ₀ w y * pinL2 ℓ Θ₀)
    ∧ (∀ z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3), ∑ j : Fin 3,
          ‖fderiv ℝ (fun w' => pairGc23 ℓ p hp Θ₀ A B w' z.2) z.1
            (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
          ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 6 * dirX23 ℓ p Θ₀ z.1 z.2 * pinL2 ℓ Θ₀) := by
  obtain ⟨hdir, hdb⟩ := pairGc23DirV2 hℓ p hp hΘ₀ hA hB hAb hBb hcA hcB
  exact ⟨pairGc23_eq_on_box hℓ p hp hΘ₀ hΘ hA hB hAb hBb hcA hcB,
    pairGc23_continuous hℓ p hp hΘ₀ hA hB hAb hBb hcA hcB,
    hdir,
    pairGc23NormSqLeV2 hℓ p hp hΘ₀ hA hB hAb hBb hcA hcB,
    hdb⟩

end Work.BoseBoxFock
