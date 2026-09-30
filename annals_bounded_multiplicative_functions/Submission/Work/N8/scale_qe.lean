import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.adi_const
import Submission.Work.N8.scale_qe_ineq5
import Submission.Work.N8.scale_qe_ineq6
import Submission.Work.N8.scale_qe_ineq7

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

/-- Positivity of `Y ^ (ε^2/2)` for `Y ≠ 0`, when `0 < ε < 1`. -/
private lemma rpow_sq_half_pos (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) {Y : ℝ}
    (hY : Y ≠ 0) : 0 < Y ^ (ε ^ 2 / 2) := by
  have hε2 : ε ^ 2 / 2 < 1 / 2 := by nlinarith
  rcases lt_trichotomy Y 0 with h | h | h
  · rw [Real.rpow_def_of_neg h]
    refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
    · nlinarith [sq_nonneg ε, Real.pi_pos]
    · nlinarith [Real.pi_pos]
  · exact absurd h hY
  · exact Real.rpow_pos_of_pos h _

theorem scale_qe (k : ℕ) (θ ε c : ℝ) (ℓ : ℕ) (C₀C : ℝ) (δ : ℝ)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1 / 2) (hε : 0 < ε) (hεθ : ε ≤ θ / 100)
    (hc : 0 < c) (hC₀C : 10 ≤ C₀C) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδc : 2 * δ ≤ c)
    (hδinv : Work.BMF.C1c k C₀C ≤ δ⁻¹)
    (hδbig : 1 + 3 * (Work.BMF.K0c k : ℝ) * ((2 * (ℓ : ℝ) + 2) * (Real.log 2 + ε) + 2) ≤ δ⁻¹) :
    ∃ X₀ : ℝ, ∀ X H P₁ P₂ : ℝ, X₀ ≤ X / (P₁ * P₂) → X ^ θ ≤ H → H ≤ X ^ (1 - θ) →
      X ^ (ε ^ 2 / 2) ≤ P₁ → P₁ ≤ X ^ ε → X ^ (ε ^ 2 / 2) ≤ P₂ → P₂ ≤ X ^ ε →
      2 ≤ H / (P₁ * P₂) ∧ H / (P₁ * P₂) ≤ X / (P₁ * P₂) ∧ 4 ≤ P₂ ∧
      100 * C₀C ^ 4 ≤ X / H ∧
      2 * (Work.BMF.K0c k : ℝ) *
          ((2 * (ℓ : ℝ) + 2) * Real.log (2 * P₁) + Real.log (X / (P₁ * P₂)) + 1)
        ≤ (1 / δ) * Real.log (X / (P₁ * P₂)) ∧
      (Work.BMF.K0c k : ℝ) *
          ((2 * (ℓ : ℝ) + 2) * Real.log (2 * P₁) + Real.log (X / (P₁ * P₂)) + 1)
          / Real.log (P₂ / 2) ≤ (c - δ) * Work.BMF.pi0 P₂ ∧
      ((2 * P₁) ^ (2 * ℓ + 2) * (X / (P₁ * P₂))) ^ (max (Work.BMF.Kc k) 1)
        ≤ (P₂ / 2) ^ ⌈c * Work.BMF.pi0 P₂⌉₊ := by
  have hε1 : ε < 1 := by nlinarith [hεθ, hθ₁]
  have hθ2pos : 0 < θ / 2 := by linarith
  have hρ : 0 < ε ^ 2 / 2 := by positivity
  -- the three asymptotic conjuncts, with their own thresholds
  obtain ⟨N5, h5⟩ := scale_qe_ineq5 k θ ε ℓ δ hθ₀ hθ₁ hε hεθ hδ hδbig
  obtain ⟨N6, h6⟩ := scale_qe_ineq6 k θ ε c ℓ δ hθ₀ hθ₁ hε hεθ hc hδ hδ1 hδc
  obtain ⟨N7, h7⟩ := scale_qe_ineq7 k θ ε c ℓ hθ₀ hθ₁ hε hεθ hc
  -- a threshold forcing `X` large enough for the trivial conjuncts
  have hev : ∀ᶠ X : ℝ in Filter.atTop,
      1 ≤ X ∧ 4 ≤ X ^ (ε ^ 2 / 2) ∧ max 2 (100 * C₀C ^ 4) ≤ X ^ (θ / 2) :=
    (Filter.eventually_ge_atTop (1 : ℝ)).and <|
      ((tendsto_rpow_atTop hρ).eventually (Filter.eventually_ge_atTop 4)).and
        ((tendsto_rpow_atTop hθ2pos).eventually
          (Filter.eventually_ge_atTop (max 2 (100 * C₀C ^ 4))))
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hev
  set N : ℝ := max 1 (max N0 (max N5 (max N6 N7))) with hNdef
  have hN1 : 1 ≤ N := le_max_left _ _
  have hN0le : N0 ≤ N := by
    rw [hNdef]
    exact le_trans (le_max_left N0 (max N5 (max N6 N7)))
      (le_max_right 1 (max N0 (max N5 (max N6 N7))))
  have hN5le : N5 ≤ N := by
    rw [hNdef]
    exact le_trans (le_trans (le_max_left N5 (max N6 N7))
        (le_max_right N0 (max N5 (max N6 N7))))
      (le_max_right 1 (max N0 (max N5 (max N6 N7))))
  have hN6le : N6 ≤ N := by
    rw [hNdef]
    exact le_trans (le_trans (le_trans (le_max_left N6 N7) (le_max_right N5 (max N6 N7)))
        (le_max_right N0 (max N5 (max N6 N7))))
      (le_max_right 1 (max N0 (max N5 (max N6 N7))))
  have hN7le : N7 ≤ N := by
    rw [hNdef]
    exact le_trans (le_trans (le_trans (le_max_right N6 N7) (le_max_right N5 (max N6 N7)))
        (le_max_right N0 (max N5 (max N6 N7))))
      (le_max_right 1 (max N0 (max N5 (max N6 N7))))
  refine ⟨N ^ 2, ?_⟩
  intro X H P₁ P₂ hX0 hHl hHu hP1l hP1u hP2l hP2u
  -- derive `N ≤ X` from the hypothesis `N^2 ≤ X/(P₁*P₂)`
  have hNX : N ≤ X := by
    have hN2ge1 : (1 : ℝ) ≤ N ^ 2 := one_le_pow₀ hN1
    have hXpos : 0 < X := by
      rcases lt_trichotomy X 0 with h | h | h
      · have hP1pos : 0 < P₁ := lt_of_lt_of_le (rpow_sq_half_pos ε hε hε1 (ne_of_lt h)) hP1l
        have hP2pos : 0 < P₂ := lt_of_lt_of_le (rpow_sq_half_pos ε hε hε1 (ne_of_lt h)) hP2l
        have hlt : X / (P₁ * P₂) < 0 := div_neg_of_neg_of_pos h (mul_pos hP1pos hP2pos)
        linarith [le_trans hN2ge1 hX0]
      · subst h
        simp only [zero_div] at hX0
        linarith [hN2ge1]
      · exact h
    have hP1pos : 0 < P₁ := lt_of_lt_of_le (Real.rpow_pos_of_pos hXpos _) hP1l
    have hPPpos : 0 < P₁ * P₂ :=
      mul_pos hP1pos (lt_of_lt_of_le (Real.rpow_pos_of_pos hXpos _) hP2l)
    have hPPge : X ^ (ε ^ 2) ≤ P₁ * P₂ := by
      have h1 := Real.rpow_add hXpos (ε ^ 2 / 2) (ε ^ 2 / 2)
      calc X ^ (ε ^ 2) = X ^ (ε ^ 2 / 2 + ε ^ 2 / 2) := by ring_nf
        _ = X ^ (ε ^ 2 / 2) * X ^ (ε ^ 2 / 2) := h1
        _ ≤ P₁ * P₂ := mul_le_mul hP1l hP2l (Real.rpow_nonneg hXpos.le _) hP1pos.le
    have hA_le : X / (P₁ * P₂) ≤ X ^ (1 - ε ^ 2) := by
      have hh := Real.rpow_sub hXpos (1 : ℝ) (ε ^ 2)
      rw [Real.rpow_one] at hh
      rw [hh]
      exact div_le_div_of_nonneg_left hXpos.le (Real.rpow_pos_of_pos hXpos _) hPPge
    have h1 : N ^ 2 ≤ X ^ (1 - ε ^ 2) := le_trans hX0 hA_le
    have ht : 0 < 1 - ε ^ 2 := by nlinarith
    have h2 : (N ^ 2) ^ (1 / (1 - ε ^ 2)) ≤ (X ^ (1 - ε ^ 2)) ^ (1 / (1 - ε ^ 2)) :=
      Real.rpow_le_rpow (sq_nonneg N) h1 (by positivity)
    have h3 : (X ^ (1 - ε ^ 2)) ^ (1 / (1 - ε ^ 2)) = X := by
      rw [← Real.rpow_mul hXpos.le (1 - ε ^ 2) (1 / (1 - ε ^ 2))]
      rw [show (1 - ε ^ 2) * (1 / (1 - ε ^ 2)) = 1 by field_simp, Real.rpow_one]
    have h4 : N ≤ (N ^ 2) ^ (1 / (1 - ε ^ 2)) := by
      have hy : 1 ≤ 1 / (1 - ε ^ 2) := by rw [le_div_iff₀ ht]; nlinarith [sq_nonneg ε]
      calc N ≤ N ^ 2 := by nlinarith [hN1]
        _ = (N ^ 2) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (N ^ 2) ^ (1 / (1 - ε ^ 2)) := Real.rpow_le_rpow_of_exponent_le hN2ge1 hy
    linarith [h2, h3, h4]
  obtain ⟨hX1, hXρ, hXθ2⟩ := hN0 X (le_trans hN0le hNX)
  have hXpos : 0 < X := lt_of_lt_of_le one_pos hX1
  have h2le : 2 ≤ X ^ (θ / 2) := le_trans (le_max_left 2 (100 * C₀C ^ 4)) hXθ2
  have h100le : 100 * C₀C ^ 4 ≤ X ^ (θ / 2) := le_trans (le_max_right 2 (100 * C₀C ^ 4)) hXθ2
  have hP1pos : 0 < P₁ := lt_of_lt_of_le (Real.rpow_pos_of_pos hXpos _) hP1l
  have hP2pos : 0 < P₂ := lt_of_lt_of_le (Real.rpow_pos_of_pos hXpos _) hP2l
  have hPPpos : 0 < P₁ * P₂ := mul_pos hP1pos hP2pos
  have hPPle : P₁ * P₂ ≤ X ^ (2 * ε) := by
    calc P₁ * P₂ ≤ X ^ ε * X ^ ε := mul_le_mul hP1u hP2u hP2pos.le (Real.rpow_nonneg hXpos.le _)
      _ = X ^ (ε + ε) := (Real.rpow_add hXpos ε ε).symm
      _ = X ^ (2 * ε) := by ring_nf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 2 ≤ H/(P₁*P₂)
    have hHnonneg : 0 ≤ H := le_trans (Real.rpow_nonneg hXpos.le θ) hHl
    have h1 : X ^ (θ - 2 * ε) ≤ H / (P₁ * P₂) := by
      rw [Real.rpow_sub hXpos θ (2 * ε)]
      exact div_le_div₀ hHnonneg hHl hPPpos hPPle
    have hsub : θ / 2 ≤ θ - 2 * ε := by nlinarith [hεθ, hθ₀]
    have h2 : X ^ (θ / 2) ≤ X ^ (θ - 2 * ε) := Real.rpow_le_rpow_of_exponent_le hX1 hsub
    linarith
  · -- H/(P₁*P₂) ≤ X/(P₁*P₂)
    have hHX : H ≤ X := by
      calc H ≤ X ^ (1 - θ) := hHu
        _ ≤ X ^ 1 := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
        _ = X := Real.rpow_one X
    exact div_le_div_of_nonneg_right hHX hPPpos.le
  · -- 4 ≤ P₂
    exact le_trans hXρ hP2l
  · -- 100*C₀C^4 ≤ X/H
    have hHpos : 0 < H := lt_of_lt_of_le (Real.rpow_pos_of_pos hXpos θ) hHl
    have h1 : X / X ^ (1 - θ) ≤ X / H := div_le_div_of_nonneg_left hXpos.le hHpos hHu
    have h2 : X / X ^ (1 - θ) = X ^ θ := by
      have hh := Real.rpow_sub hXpos (1 : ℝ) (1 - θ)
      rw [Real.rpow_one] at hh
      rw [← hh]; congr 1; ring
    rw [h2] at h1
    have h3 : X ^ (θ / 2) ≤ X ^ θ := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    linarith
  · exact h5 X H P₁ P₂ (le_trans hN5le hNX) hHl hHu hP1l hP1u hP2l hP2u
  · exact h6 X H P₁ P₂ (le_trans hN6le hNX) hHl hHu hP1l hP1u hP2l hP2u
  · exact h7 X H P₁ P₂ (le_trans hN7le hNX) hHl hHu hP1l hP1u hP2l hP2u

end Work.N8
