import Mathlib
import Submission.Work.BMF.good_bike_aux
import Submission.Work.BMF.adi_count
import Submission.Work.BMF.bikeSetAll_bridge
import Submission.Work.BMF.primesIn_half_card_le_all

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Finset Real

/-- **Sum of the not-very-good bicycles over the primes.**  Each bicycle of the full graph
which is not `δ`-very good is counted only by the at most `δ π₀(P₂)` primes supporting it
(`sum_notVeryGoodBikes_le`), and the total number of bicycles of the full graph is
`≪ (π₀(P₁)²)^{2ℓ+1}/(X/L)` (`bikeSetAll_card_le`).  Multiplying the two bounds gives the
stated estimate. -/
theorem notVeryGood_bikes_sum_le (k ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    ∃ C P₀ : ℝ, 0 < C ∧ 0 < P₀ ∧ ∀ (f : ℕ → ℂ) (c Cq X L P₁ P₂ δ : ℝ)
      (D : Work.BMF.QuadData k f c Cq X L P₁ P₂),
      P₀ ≤ P₁ → 0 < P₁ → 2 ≤ P₂ → 0 < L → 0 < X → 8000 * P₁ ^ 2 < X / L →
      3 ≤ X / L → X / L ≤ P₁ ^ (ℓ - 1) → 0 ≤ δ →
      ∑ q ∈ Work.BMF.primesIn (P₂ / 2) P₂, ((Work.BMF.notVeryGoodBikes D ℓ δ q).card : ℝ)
        ≤ C * δ * Work.BMF.pi0 P₂ * (Work.BMF.pi0 P₁ ^ 2) ^ (2 * ℓ + 1) / (X / L) := by
  classical
  obtain ⟨C₁, P₁₀, hC₁, hP₁₀, hbike⟩ := bikeSetAll_card_le k ℓ hℓ
  refine ⟨C₁, max P₁₀ 3, hC₁, lt_max_of_lt_right (by norm_num), ?_⟩
  intro f c Cq X L P₁ P₂ δ D hP₀ hP hP₂ hL hX hbig hN3 hNle hδ
  have hP₁₀' : P₁₀ ≤ P₁ := le_trans (le_max_left _ _) hP₀
  have hb := hbike f c Cq X L P₁ P₂ D hP₁₀' hP hL hX hbig hN3 hNle
  have hs := sum_notVeryGoodBikes_le D ℓ δ hP₂ hδ
  have hnn : 0 ≤ δ * pi0 P₂ := mul_nonneg hδ (pi0_pos hP₂).le
  calc ∑ q ∈ primesIn (P₂ / 2) P₂, ((notVeryGoodBikes D ℓ δ q).card : ℝ)
      ≤ δ * pi0 P₂ * ((bikeSetAll D ℓ).card : ℝ) := hs
    _ ≤ δ * pi0 P₂ * (C₁ * (pi0 P₁ ^ 2) ^ (2 * ℓ + 1) / (X / L)) :=
        mul_le_mul_of_nonneg_left hb hnn
    _ = C₁ * δ * pi0 P₂ * (pi0 P₁ ^ 2) ^ (2 * ℓ + 1) / (X / L) := by ring

end Work.BMF
