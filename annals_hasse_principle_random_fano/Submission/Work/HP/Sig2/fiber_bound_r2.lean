import Mathlib
import Submission.Work.HP.WinR2Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.Defs

namespace Work.HP.Sig2

theorem fiber_bound_r2 (n : ℕ) (hn : 2 ≤ n)
    (Knum : ℝ) (hKnum : 0 < Knum)
    (hnum : ∀ (s : Fin 2 → ℝ) (F : Finset (Submodule ℤ (Fin (n + 1) → ℤ))), (∀ j, 1 ≤ s j) →
      (∀ L ∈ F, IsPrimLat L ∧ rk L = 2 ∧ ∀ j : Fin 2, lam L (j.1 + 1) ≤ s j) →
      ((F.card : ℝ) ≤ Knum * ∏ j : Fin 2, s j ^ (n + 1 + 2 + 1 - 2 * (j.1 + 1))))
    (Ksmall : ℝ) (hKsmall : 0 < Ksmall)
    (hbp : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)) (k : Fin 2 → ℕ) (X Y : ℝ), rk L = 2 →
      (∀ j : Fin 2, (2 : ℝ) ^ (k j) ≤ 2 * lam L (j.1 + 1)) → 1 ≤ X → 1 ≤ Y → X ≤ Y →
      lam L 1 ≤ X → lam L 2 ≤ Y →
      (ballCount L X : ℝ) * (ballCount L Y : ℝ) ≤ winBp Ksmall X Y k)
    (X Y Δ : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hXY : X ≤ Y)
    (T : Finset (Submodule ℤ (Fin (n + 1) → ℤ))) (k : Fin 2 → ℕ)
    (hT : ∀ L ∈ T, IsPrimLat L ∧ rk L = 2 ∧ detL L ≤ Δ + 1 ∧ lam L 1 ≤ X ∧ lam L 2 ≤ Y)
    (hwin1 : ∀ L ∈ T, ∀ j : Fin 2, lam L (j.1 + 1) ≤ (2 : ℝ) ^ (kwin 2 L j))
    (hwin2 : ∀ L ∈ T, ∀ j : Fin 2, (2 : ℝ) ^ (kwin 2 L j) ≤ 2 * lam L (j.1 + 1))
    (hk : ∀ L ∈ T, kwin 2 L = k) :
    (∑ L ∈ T, (ballCount L X : ℝ) * (ballCount L Y : ℝ)) ≤
      Knum * (2 : ℝ) ^ (∑ j : Fin 2, k j * winE n j) * winBp Ksmall X Y k := by
  -- Nonnegativity of the window bound `winBp`.
  have hX0 : (0 : ℝ) < X := by linarith
  have hY0 : (0 : ℝ) < Y := by linarith
  have hCnn : 0 ≤ winBp Ksmall X Y k := by
    rw [winBp]; positivity
  -- The per-lattice bound from `hbp`, with the window exponent fixed.
  have hper : ∀ L ∈ T, (ballCount L X : ℝ) * (ballCount L Y : ℝ) ≤ winBp Ksmall X Y k := by
    intro L hL
    obtain ⟨_, hrk, _, hlam1, hlam2⟩ := hT L hL
    refine hbp L k X Y hrk ?_ hX hY hXY hlam1 hlam2
    intro j
    have := hwin2 L hL j
    rwa [hk L hL] at this
  -- The number of lattices in the window, at scale `2 ^ k`.
  have hcard : (T.card : ℝ) ≤ Knum * (2 : ℝ) ^ (∑ j : Fin 2, k j * winE n j) := by
    have hnum' := hnum (fun j => (2 : ℝ) ^ (k j)) T
      (fun j => one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
      (fun L hL => ⟨(hT L hL).1, (hT L hL).2.1,
        fun j => by have := hwin1 L hL j; rwa [hk L hL] at this⟩)
    have hprod : (∏ j : Fin 2, ((2 : ℝ) ^ (k j)) ^ (n + 1 + 2 + 1 - 2 * (j.1 + 1)))
        = (2 : ℝ) ^ (∑ j : Fin 2, k j * winE n j) := by
      have h1 : (∏ j : Fin 2, ((2 : ℝ) ^ (k j)) ^ (n + 1 + 2 + 1 - 2 * (j.1 + 1)))
          = ∏ j : Fin 2, (2 : ℝ) ^ (k j * winE n j) := by
        refine Finset.prod_congr rfl (fun j _ => ?_)
        rw [← pow_mul, winE]
      rw [h1, Finset.prod_pow_eq_pow_sum]
    rwa [hprod] at hnum'
  calc (∑ L ∈ T, (ballCount L X : ℝ) * (ballCount L Y : ℝ))
      ≤ ∑ _L ∈ T, winBp Ksmall X Y k := Finset.sum_le_sum hper
    _ = (T.card : ℝ) * winBp Ksmall X Y k := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Knum * (2 : ℝ) ^ (∑ j : Fin 2, k j * winE n j)) * winBp Ksmall X Y k :=
        mul_le_mul_of_nonneg_right hcard hCnn

end Work.HP.Sig2
