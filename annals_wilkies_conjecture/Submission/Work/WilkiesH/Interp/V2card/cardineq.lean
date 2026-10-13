import Mathlib
import Submission.Work.WilkiesH.Interp.V2Params
import Submission.Work.WilkiesH.Interp.V2Lemmas

namespace Work.WilkiesH.Interp.V2card

open Work.WilkiesH.Interp

/-- `K = 2μ + 4` is at least `1` (indeed at least `4`). -/
lemma one_le_Kr (μ : ℕ) : (1 : ℝ) ≤ Kr μ := by
  simp only [Kr]
  exact_mod_cast (by simp only [KK]; omega : (1 : ℕ) ≤ KK μ)

/-- `ρ^{-b} = (1/K)^{-b} = K^b`. -/
lemma rhoV_zpow_eq (μ g H : ℕ) :
    (rhoV μ) ^ (-(bV μ g H : ℤ)) = (Kr μ) ^ (bV μ g H) := by
  rw [Kr, rhoV]; simp only [KK]; rw [zpow_neg, inv_zpow, inv_inv, zpow_natCast]

/-- First Siegel ingredient: `⌈ρ^{-b}⌉ ≤ 2 K^b`. -/
lemma rpbX_le (μ g H : ℕ) :
    ((rpbX μ g H : ℕ) : ℝ) ≤ 2 * (Kr μ) ^ (bX μ g H) := by
  have hK1 := one_le_Kr μ
  have hw : (1 : ℝ) ≤ (Kr μ) ^ (bV μ g H) := one_le_pow₀ hK1
  simp only [rpbX, bX]
  rw [rhoV_zpow_eq μ g H]
  have h0 : (0 : ℝ) ≤ (Kr μ) ^ (bV μ g H) := le_trans zero_le_one hw
  have hlt := Nat.ceil_lt_add_one h0
  linarith

/-- Second Siegel ingredient: `4 N₁ exp (b log K / λ) ≤ Q`, from
`QV = 4 N₁ ⌈exp (b log K / λ)⌉ + 2`. -/
lemma QX_ge (μ g H : ℕ) :
    4 * ((N1X μ g H : ℕ) : ℝ) *
      Real.exp (((bX μ g H : ℕ) : ℝ) * Real.log (Kr μ) / ((lamX μ g H : ℕ) : ℝ))
    ≤ ((QX μ g H : ℕ) : ℝ) := by
  have hle := le_ceilQV μ g H
  have hN : (0 : ℝ) ≤ ((N1V μ g H : ℕ) : ℝ) := Nat.cast_nonneg _
  have hC : (0 : ℝ) ≤ ((ceilQV μ g H : ℕ) : ℝ) := Nat.cast_nonneg _
  have hQe : QX μ g H = 4 * N1V μ g H * ceilQV μ g H + 2 := by
    simp only [QX, QV]; rfl
  rw [hQe]
  simp only [bX, lamX, N1X]
  push_cast
  nlinarith [hle, hN, hC]

-- The Siegel cardinality condition for the explicit parameters.
-- `V2Lemmas.cardineq_abstract` reduces it to: `⌈ρ^(-b)⌉ ≤ 2 K^b`, `4 N₁ exp (b log K / λ) ≤ Q`
-- (from `QV = 4 N₁ ⌈exp (b log K / λ)⌉ + 2`, see `V2Params.le_ceilQV` and `QV_eq_four`),
-- and `λ + 1 = N₁/m` (`V2Lemmas.lamX_eq`).
theorem cardineq (μ g H : ℕ) (hlam : 8 * g + 8 ≤ Work.WilkiesH.Interp.lamX μ g H) :
    (Work.WilkiesH.Interp.QX μ g H + 1) ^ (Work.WilkiesH.Interp.N1X μ g H) >
      (2 * (Work.WilkiesH.Interp.N1X μ g H * Work.WilkiesH.Interp.rpbX μ g H *
        Work.WilkiesH.Interp.QX μ g H) + 1) ^ (Work.WilkiesH.Interp.mX μ g H) := by
  have hK1 : (1 : ℝ) ≤ Kr μ := one_le_Kr μ
  have hQ1 : 1 ≤ QX μ g H := one_le_QV μ g H
  have hN1 : 1 ≤ N1X μ g H := one_le_N1V μ g H
  have hm : 1 ≤ mX μ g H := one_le_mV μ g H
  have hlam1 : 1 ≤ lamX μ g H := by omega
  have hce : ((rpbX μ g H : ℕ) : ℝ) ≤ 2 * (Kr μ) ^ (bX μ g H) := rpbX_le μ g H
  have hQV : 4 * ((N1X μ g H : ℕ) : ℝ) *
      Real.exp (((bX μ g H : ℕ) : ℝ) * Real.log (Kr μ) / ((lamX μ g H : ℕ) : ℝ))
      ≤ ((QX μ g H : ℕ) : ℝ) := QX_ge μ g H
  have hleq : lamX μ g H + 1 = N1X μ g H / mX μ g H := lamX_eq μ g H hlam
  exact cardineq_abstract (Kr μ) hK1 (lamX μ g H) (bX μ g H) (N1X μ g H) (mX μ g H)
    (rpbX μ g H) (QX μ g H) hQ1 hN1 hm hlam1 hce hQV hleq

end Work.WilkiesH.Interp.V2card
