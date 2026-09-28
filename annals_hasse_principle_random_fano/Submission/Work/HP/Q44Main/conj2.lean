import Mathlib
import Submission.Work.HP.MDEstimates.ell44_56_bound
import Submission.Work.HP.MDEstimates.q44_perlat_56
import Submission.Work.HP.Q44Main.q44_layer_sum

set_option autoImplicit false
noncomputable section
namespace Work.HP.Q44Main
open Work.HP

/-- **Second half of `quartic44`.** `ℓ^{(56)}(Z;Δ,J) ≪ Z⁴ Δ²⁴ J¹⁵`. -/
theorem conj2_56 :
    ∃ K : ℝ, 0 < K ∧ ∀ Z Δ J : ℝ, 1 ≤ Z → 1 ≤ Δ → 1 ≤ J →
      (ell44 56 Z Δ J : ℝ) ≤ K * Z ^ 4 * Δ ^ 24 * J ^ 15 := by
  obtain ⟨K1, hK1pos, hK1⟩ := MDEstimates.q44_perlat_56
  obtain ⟨K2, hK2pos, hK2⟩ := q44_layer_sum
  refine ⟨K1 * K2, by positivity, ?_⟩
  intro Z Δ J hZ hΔ hJ
  obtain ⟨T, hT, hsum⟩ := MDEstimates.ell44_le_sum Z Δ J hZ
  have hfac : (∑ L ∈ T, (({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) |
        p.1 ∈ L ∧ p.2 ∈ L ∧ eNorm p.1 ≤ Z ∧ eNorm p.2 ≤ Z ∧
        LinearIndependent ℤ ![p.1, p.2] ∧ lam (Gam 4 4 p.1 p.2) 56 ≤ J} :
      Set ((Fin 5 → ℤ) × (Fin 5 → ℤ))).ncard : ℝ))
      ≤ K1 * Z ^ 4 * J ^ 15 * (∑ L ∈ T, lam L 1 ^ 18 * lam L 2 ^ 18 * lam L 3 ^ 20) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun L hL => ?_)
    obtain ⟨-, hrk, -, hl1, hl2⟩ := hT L hL
    refine le_trans (hK1 L hrk Z J hZ hJ hl1 hl2) (le_of_eq ?_)
    ring
  calc (ell44 56 Z Δ J : ℝ)
      ≤ ∑ L ∈ T, (({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) |
          p.1 ∈ L ∧ p.2 ∈ L ∧ eNorm p.1 ≤ Z ∧ eNorm p.2 ≤ Z ∧
          LinearIndependent ℤ ![p.1, p.2] ∧ lam (Gam 4 4 p.1 p.2) 56 ≤ J} :
        Set ((Fin 5 → ℤ) × (Fin 5 → ℤ))).ncard : ℝ) := hsum
    _ ≤ K1 * Z ^ 4 * J ^ 15 * (∑ L ∈ T, lam L 1 ^ 18 * lam L 2 ^ 18 * lam L 3 ^ 20) := hfac
    _ ≤ K1 * Z ^ 4 * J ^ 15 * (K2 * Δ ^ 24) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact hK2 T Δ hΔ (fun L hL => ⟨(hT L hL).1, (hT L hL).2.1, (hT L hL).2.2.1⟩)
    _ = (K1 * K2) * Z ^ 4 * Δ ^ 24 * J ^ 15 := by ring

end Work.HP.Q44Main
