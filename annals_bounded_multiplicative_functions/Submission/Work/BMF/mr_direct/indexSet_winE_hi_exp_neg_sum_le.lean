import Mathlib
import Submission.Work.BMF.mr_direct.goodSet_bound_range_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The weighted high-frequency energy sum over `indexSet`

`Work.BMF.mr_direct.indexSet_winE_hi_exp_neg_sum_le`: the sum
`Σ_{j ∈ indexSet K P Q} (X₂ e^{-j/K}) · (e^{-2αj/K} · winE_j)`
of the `j`-th Buchstab window energies `winE_j`, weighted by the high end `X₂ e^{-j/K}` of the
window and by the exponential factor `e^{-2αj/K}`, is at most
`36 (K log (Q/P) + 2) (X₂/X₁) P^{-2α}`.

The proof is a term-by-term application of the elementary bound `winE_le_exp`
(`winE_j ≤ 2 e^{(j+1)/K}/X₁`) followed by the geometric sum estimate
`indexSet_exp_neg_sum_le` (`Σ_j e^{-2αj/K} ≤ 3 P^{-2α} (K log (Q/P) + 2)`).
-/

namespace Work.BMF.mr_direct

theorem indexSet_winE_hi_exp_neg_sum_le (b : ℕ → ℂ) (K P Q X₁ X₂ α : ℝ)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hX : 0 < X₁) (hX₂ : 0 < X₂) (hK : 3 ≤ K) (hP : 2 ≤ P)
    (hPQ : P ≤ Q) (hα0 : 0 < α) (hα1 : α ≤ 1 / 4) :
    (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
        (X₂ * Real.exp (-(j : ℝ) / K)) *
          (Real.exp (-(2 * α * (j : ℝ) / K)) * Work.BMF.mr_direct.winE b P Q K X₁ X₂ j))
      ≤ 36 * (K * Real.log (Q / P) + 2) * ((X₂ / X₁) * P ^ (-(2 * α))) := by
  have hKpos : 0 < K := by linarith
  have hPpos : 0 < P := by linarith
  have hlogQ : 0 ≤ Real.log (Q / P) :=
    Real.log_nonneg (by rw [le_div_iff₀ hPpos]; linarith)
  -- term-by-term: `winE_j ≤ 2 e^{(j+1)/K}/X₁`, and `e^{-j/K} · e^{(j+1)/K} = e^{1/K}`
  have hterm : ∀ j ∈ Work.BMF.mrDirect.indexSet K P Q,
      (X₂ * Real.exp (-(j : ℝ) / K)) *
          (Real.exp (-(2 * α * (j : ℝ) / K)) * Work.BMF.mr_direct.winE b P Q K X₁ X₂ j)
        ≤ (2 * (X₂ / X₁) * Real.exp (1 / K)) * Real.exp (-(2 * α * (j : ℝ) / K)) := by
    intro j _
    have hE : Work.BMF.mr_direct.winE b P Q K X₁ X₂ j
        ≤ 2 * Real.exp (((j : ℝ) + 1) / K) / X₁ :=
      winE_le_exp b P Q K X₁ X₂ j hb hX
    have he2 : 0 < Real.exp (-(2 * α * (j : ℝ) / K)) := Real.exp_pos _
    have hfac : 0 ≤ X₂ * Real.exp (-(j : ℝ) / K) :=
      mul_nonneg hX₂.le (Real.exp_pos _).le
    refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE he2.le) hfac) ?_
    have hexp : Real.exp (-(j : ℝ) / K) * Real.exp (((j : ℝ) + 1) / K) = Real.exp (1 / K) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [show (X₂ * Real.exp (-(j : ℝ) / K)) *
          (Real.exp (-(2 * α * (j : ℝ) / K)) * (2 * Real.exp (((j : ℝ) + 1) / K) / X₁))
        = 2 * (X₂ / X₁) * (Real.exp (-(j : ℝ) / K) * Real.exp (((j : ℝ) + 1) / K)) *
            Real.exp (-(2 * α * (j : ℝ) / K)) from by ring,
      hexp]
  have hfacnn : 0 ≤ 2 * (X₂ / X₁) * Real.exp (1 / K) := by
    have h : 0 ≤ X₂ / X₁ := div_nonneg hX₂.le hX.le
    positivity
  have hsum_eq : (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
        (2 * (X₂ / X₁) * Real.exp (1 / K)) * Real.exp (-(2 * α * (j : ℝ) / K)))
      = (2 * (X₂ / X₁) * Real.exp (1 / K)) *
        ∑ j ∈ Work.BMF.mrDirect.indexSet K P Q, Real.exp (-(2 * α * (j : ℝ) / K)) := by
    rw [Finset.mul_sum]
  have hbound : (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
        (X₂ * Real.exp (-(j : ℝ) / K)) *
          (Real.exp (-(2 * α * (j : ℝ) / K)) * Work.BMF.mr_direct.winE b P Q K X₁ X₂ j))
      ≤ (2 * (X₂ / X₁) * Real.exp (1 / K)) *
        (3 * P ^ (-(2 * α)) * (K * Real.log (Q / P) + 2)) := by
    calc (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
            (X₂ * Real.exp (-(j : ℝ) / K)) *
              (Real.exp (-(2 * α * (j : ℝ) / K)) * Work.BMF.mr_direct.winE b P Q K X₁ X₂ j))
        ≤ ∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
            (2 * (X₂ / X₁) * Real.exp (1 / K)) * Real.exp (-(2 * α * (j : ℝ) / K)) :=
          Finset.sum_le_sum hterm
      _ = (2 * (X₂ / X₁) * Real.exp (1 / K)) *
            ∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
              Real.exp (-(2 * α * (j : ℝ) / K)) := hsum_eq
      _ ≤ (2 * (X₂ / X₁) * Real.exp (1 / K)) *
            (3 * P ^ (-(2 * α)) * (K * Real.log (Q / P) + 2)) :=
          mul_le_mul_of_nonneg_left
            (indexSet_exp_neg_sum_le K P Q α hK hP hPQ hα0 hα1) hfacnn
  have h6 : 6 * Real.exp (1 / K) ≤ 36 := by
    have h1 : 1 / K ≤ 1 := by
      rw [div_le_one hKpos]
      linarith
    have h2 : Real.exp (1 / K) ≤ Real.exp 1 := Real.exp_le_exp.mpr h1
    nlinarith [h2, Real.exp_one_lt_three]
  have hv : 0 ≤ K * Real.log (Q / P) + 2 := by nlinarith [hKpos, hlogQ]
  have hnn : 0 ≤ (X₂ / X₁) * P ^ (-(2 * α)) * (K * Real.log (Q / P) + 2) := by
    have ha : 0 ≤ X₂ / X₁ := div_nonneg hX₂.le hX.le
    have hb' : 0 ≤ P ^ (-(2 * α)) := (Real.rpow_pos_of_pos hPpos _).le
    exact mul_nonneg (mul_nonneg ha hb') hv
  calc (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
        (X₂ * Real.exp (-(j : ℝ) / K)) *
          (Real.exp (-(2 * α * (j : ℝ) / K)) * Work.BMF.mr_direct.winE b P Q K X₁ X₂ j))
      ≤ (2 * (X₂ / X₁) * Real.exp (1 / K)) *
          (3 * P ^ (-(2 * α)) * (K * Real.log (Q / P) + 2)) := hbound
    _ = (6 * Real.exp (1 / K)) *
          ((X₂ / X₁) * P ^ (-(2 * α)) * (K * Real.log (Q / P) + 2)) := by ring
    _ ≤ 36 * ((X₂ / X₁) * P ^ (-(2 * α)) * (K * Real.log (Q / P) + 2)) :=
        mul_le_mul_of_nonneg_right h6 hnn
    _ = 36 * (K * Real.log (Q / P) + 2) * ((X₂ / X₁) * P ^ (-(2 * α))) := by ring

end Work.BMF.mr_direct
