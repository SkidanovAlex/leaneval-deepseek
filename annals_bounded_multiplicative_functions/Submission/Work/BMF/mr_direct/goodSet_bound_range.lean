import Mathlib
import Submission.Work.BMF.mr_direct_range_defs
import Submission.Work.BMF.mr_direct.goodSet_E1_bound
import Submission.Work.BMF.mr_direct.goodSet_bound_range_defs
import Submission.Work.BMF.mr_direct.goodSet_range_perj_bound
import Submission.Work.BMF.mr_direct.indexSet_winE_exp_neg_sum_le
import Submission.Work.BMF.mr_direct.indexSet_winE_hi_exp_neg_sum_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1600000

namespace Work.BMF.mr_direct

open MeasureTheory intervalIntegral Finset
open scoped BigOperators

noncomputable section

/-- Auxiliary: the `exp(-2αj/K)`-weighted sum of the window energies over the index set is at
most `6 (K log(Q/P) + 2) P^{-2α}`.  Each summand is bounded by `2 exp(-2αj/K)` (since
`winE ≤ 2`) and the index set contributes a factor `K log(Q/P) + 2`. -/
lemma winE_exp_neg_sum_le_small (b : ℕ → ℂ) (K P Q X₁ X₂ α : ℝ)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hX : 0 < X₁) (hK : 3 ≤ K) (hP : 2 ≤ P) (hPQ : P ≤ Q)
    (hα0 : 0 < α) (hα1 : α ≤ 1 / 4) :
    (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
        Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j)
      ≤ 6 * (K * Real.log (Q / P) + 2) * P ^ (-(2 * α)) := by
  have hterm : ∀ j ∈ Work.BMF.mrDirect.indexSet K P Q,
      Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j
        ≤ Real.exp (-(2 * α * (j : ℝ) / K)) * 2 := fun j _ =>
    mul_le_mul_of_nonneg_left (winE_le_two b P Q K X₁ X₂ j hb hX) (Real.exp_pos _).le
  calc (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
        Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j)
      ≤ ∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
          Real.exp (-(2 * α * (j : ℝ) / K)) * 2 := Finset.sum_le_sum hterm
    _ = 2 * (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
          Real.exp (-(2 * α * (j : ℝ) / K))) := by rw [← Finset.sum_mul, mul_comm]
    _ ≤ 2 * (3 * P ^ (-(2 * α)) * (K * Real.log (Q / P) + 2)) :=
        mul_le_mul_of_nonneg_left (indexSet_exp_neg_sum_le K P Q α hK hP hPQ hα0 hα1)
          (by norm_num)
    _ = 6 * (K * Real.log (Q / P) + 2) * P ^ (-(2 * α)) := by ring

theorem goodSet_bound_range :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X₁ X₂ K P Q S α : ℝ) (b c : ℕ → ℂ) (u : Set ℝ),
        1 ≤ X₁ → X₁ ≤ X₂ → X₂ ≤ 4 * X₁ → 3 ≤ K → 2 ≤ P → P ≤ Q → 0 ≤ S →
        0 < α → α ≤ 1 / 4 →
        (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
        u ⊆ Set.Icc (-S) S →
        (∀ t ∈ u, ∀ j ∈ Work.BMF.mrDirect.indexSet K P Q,
          ‖Work.BMF.mrDirect.primePoly c K j t‖ ≤ Real.exp (-(α * (j : ℝ) / K))) →
        K * Real.log (Q / P) *
          (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
            ∫ t in u, ‖Work.BMF.mrDirect.primePoly c K j t *
                Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2)
        ≤ C * (1 + 1 / α) * (K + 1) ^ 4 * (Real.log (Q / P) + 1) ^ 2 *
            (S / X₁ * Q ^ (1 - 2 * α) + X₂ / X₁ * P ^ (-(2 * α))) := by
  obtain ⟨C_W, hCWpos, hperj_hyp⟩ := goodSet_range_perj_bound
  refine ⟨200 * (C_W + 1), by positivity, ?_⟩
  intro X₁ X₂ K P Q S α b c u hX1 hX12 hX24 hK hP hPQ hS hα0 hα1 hb hc hu hgood
  have hX1pos : 0 < X₁ := by linarith
  have hX2pos : 0 < X₂ := by linarith
  have hKpos : 0 < K := by linarith
  have hPpos : 0 < P := by linarith
  have hQpos : 0 < Q := by linarith
  have hLnn : 0 ≤ Real.log (Q / P) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hPpos]; linarith
  have hQnn : 0 ≤ Q ^ (1 - 2 * α) := (Real.rpow_pos_of_pos hQpos _).le
  have hPnn : 0 ≤ P ^ (-(2 * α)) := (Real.rpow_pos_of_pos hPpos _).le
  have hratio : 1 ≤ X₂ / X₁ := (one_le_div hX1pos).mpr hX12
  -- the per-j bound
  have hperj : ∀ j ∈ Work.BMF.mrDirect.indexSet K P Q,
      (∫ t in u, ‖Work.BMF.mrDirect.primePoly c K j t *
            Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2)
        ≤ C_W * (2 * S + (winHi K X₂ j + 1)) *
            (Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j) := by
    intro j hj
    exact hperj_hyp X₁ X₂ K P Q S α b c u j hX1pos hS hα0 hu (fun t ht => hgood t ht j hj)
  -- the three estimates
  have hS1 := indexSet_winE_exp_neg_sum_le b K P Q X₁ X₂ α hb hX1pos hK hP hPQ hα0 hα1
  have hS2 := indexSet_winE_hi_exp_neg_sum_le b K P Q X₁ X₂ α hb hX1pos hX2pos hK hP hPQ hα0 hα1
  have hS3 := winE_exp_neg_sum_le_small b K P Q X₁ X₂ α hb hX1pos hK hP hPQ hα0 hα1
  set L : ℝ := Real.log (Q / P) with hL
  set U1 : ℝ := S / X₁ * Q ^ (1 - 2 * α) with hU1
  set U2 : ℝ := X₂ / X₁ * P ^ (-(2 * α)) with hU2
  have hLnn' : 0 ≤ L := by rw [hL]; exact hLnn
  have hU1nn : 0 ≤ U1 := by
    rw [hU1]; exact mul_nonneg (div_nonneg hS hX1pos.le) hQnn
  have hU2nn : 0 ≤ U2 := by
    rw [hU2]; exact mul_nonneg (div_nonneg hX2pos.le hX1pos.le) hPnn
  have hKL2nn : 0 ≤ K * L + 2 := by nlinarith [hKpos, hLnn']
  -- the split of the sum
  have hsplit : (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
        C_W * (2 * S + (winHi K X₂ j + 1)) *
          (Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j))
      = C_W * (2 * S * (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
            Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j)
        + ((∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
              (X₂ * Real.exp (-(j : ℝ) / K)) *
                (Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j))
          + (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
              Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j))) := by
    have hpt : ∀ j ∈ Work.BMF.mrDirect.indexSet K P Q,
        C_W * (2 * S + (winHi K X₂ j + 1)) *
          (Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j)
        = C_W * (2 * S * (Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j)
            + ((X₂ * Real.exp (-(j : ℝ) / K)) *
                  (Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j)
              + Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j)) := by
      intro j hj
      rw [winHi]; ring
    rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum]
  -- bound the three pieces
  have hA : 2 * S * (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
        Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j)
      ≤ 40 * (K * L + 2) * U1 := by
    have h1 := mul_le_mul_of_nonneg_left hS1 (by linarith : (0:ℝ) ≤ 2 * S)
    have heq : 2 * S * (20 * (K * L + 2) * (Q ^ (1 - 2 * α) / X₁))
        = 40 * (K * L + 2) * U1 := by rw [hU1]; ring
    exact le_trans h1 (le_of_eq heq)
  have h6 : 6 * (K * L + 2) * P ^ (-(2 * α)) ≤ 6 * (K * L + 2) * U2 := by
    rw [hU2]
    have hthis : P ^ (-(2 * α)) ≤ (X₂ / X₁) * P ^ (-(2 * α)) := by
      nlinarith [hPnn, hratio]
    exact mul_le_mul_of_nonneg_left hthis (by linarith : (0:ℝ) ≤ 6 * (K * L + 2))
  have hcomb : 2 * S * (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
          Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j)
        + ((∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
              (X₂ * Real.exp (-(j : ℝ) / K)) *
                (Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j))
          + (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
              Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j))
      ≤ 42 * (K * L + 2) * (U1 + U2) := by
    have h40 : 40 * (K * L + 2) * U1 ≤ 42 * (K * L + 2) * U1 := by
      nlinarith [mul_nonneg hKL2nn hU1nn]
    have h42 : 36 * (K * L + 2) * U2 + 6 * (K * L + 2) * U2
        = 42 * (K * L + 2) * U2 := by ring
    nlinarith [hA, hS2, hS3, h6, h40, h42, mul_nonneg hKL2nn hU2nn]
  have hsum : (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
        ∫ t in u, ‖Work.BMF.mrDirect.primePoly c K j t *
            Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2)
      ≤ C_W * (42 * (K * L + 2) * (U1 + U2)) := by
    have h1 : (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
          ∫ t in u, ‖Work.BMF.mrDirect.primePoly c K j t *
              Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2)
        ≤ C_W * (2 * S * (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
              Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j)
            + ((∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
                  (X₂ * Real.exp (-(j : ℝ) / K)) *
                    (Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j))
              + (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
                  Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j))) := by
      calc (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
            ∫ t in u, ‖Work.BMF.mrDirect.primePoly c K j t *
                Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2)
          ≤ ∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
              C_W * (2 * S + (winHi K X₂ j + 1)) *
                (Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j) :=
            Finset.sum_le_sum hperj
        _ = C_W * (2 * S * (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
              Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j)
            + ((∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
                  (X₂ * Real.exp (-(j : ℝ) / K)) *
                    (Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j))
              + (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
                  Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j))) := hsplit
    exact le_trans h1 (mul_le_mul_of_nonneg_left hcomb hCWpos.le)
  -- multiply out and do the final arithmetic
  have hKL : 0 ≤ K * L := mul_nonneg hKpos.le hLnn'
  have hstep : K * L * (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
        ∫ t in u, ‖Work.BMF.mrDirect.primePoly c K j t *
            Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2)
      ≤ K * L * (C_W * (42 * (K * L + 2) * (U1 + U2))) :=
    mul_le_mul_of_nonneg_left hsum hKL
  have harith : K * L * (C_W * (42 * (K * L + 2) * (U1 + U2)))
      ≤ 200 * (C_W + 1) * (1 + 1 / α) * (K + 1) ^ 4 * (L + 1) ^ 2 * (U1 + U2) := by
    have hUU : 0 ≤ U1 + U2 := by linarith
    have hKLK : K * L * (K * L + 2) ≤ 2 * ((K + 1) ^ 4 * (L + 1) ^ 2) := by
      have h1 : K * L * (K * L + 2) ≤ 2 * K ^ 2 * (L + 1) ^ 2 := by
        nlinarith [hK, hLnn', mul_nonneg hKpos.le hLnn', sq_nonneg (K * L), sq_nonneg L]
      have h2 : K ^ 2 ≤ (K + 1) ^ 4 := by
        nlinarith [hK, sq_nonneg (K - 1), sq_nonneg K, sq_nonneg (K + 1)]
      have h2' : K ^ 2 * (L + 1) ^ 2 ≤ (K + 1) ^ 4 * (L + 1) ^ 2 :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
      have h1' : K * L * (K * L + 2) ≤ 2 * (K ^ 2 * (L + 1) ^ 2) := by
        have e : 2 * (K ^ 2 * (L + 1) ^ 2) = 2 * K ^ 2 * (L + 1) ^ 2 := by ring
        linarith [h1, e]
      have h2'' : 2 * (K ^ 2 * (L + 1) ^ 2) ≤ 2 * ((K + 1) ^ 4 * (L + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left h2' (by norm_num : (0:ℝ) ≤ 2)
      linarith [h1', h2'']
    have h4 : 84 * C_W ≤ 200 * (C_W + 1) * (1 + 1 / α) := by
      have h3 : (1:ℝ) ≤ 1 + 1 / α := by
        have : 0 < 1 / α := by positivity
        linarith
      have hA : 200 * (C_W + 1) ≤ 200 * (C_W + 1) * (1 + 1 / α) :=
        le_mul_of_one_le_right (by linarith [hCWpos]) h3
      linarith [hA, hCWpos]
    have hA0 : 0 ≤ (K + 1) ^ 4 * (L + 1) ^ 2 * (U1 + U2) :=
      mul_nonneg (mul_nonneg (by positivity) (by positivity)) hUU
    have hmain : 42 * C_W * (U1 + U2) * (2 * ((K + 1) ^ 4 * (L + 1) ^ 2))
        ≤ 200 * (C_W + 1) * (1 + 1 / α) * (K + 1) ^ 4 * (L + 1) ^ 2 * (U1 + U2) := by
      have h5 := mul_le_mul_of_nonneg_right h4 hA0
      have e1 : (84 * C_W) * ((K + 1) ^ 4 * (L + 1) ^ 2 * (U1 + U2))
          = 42 * C_W * (U1 + U2) * (2 * ((K + 1) ^ 4 * (L + 1) ^ 2)) := by ring
      have e2 : (200 * (C_W + 1) * (1 + 1 / α)) * ((K + 1) ^ 4 * (L + 1) ^ 2 * (U1 + U2))
          = 200 * (C_W + 1) * (1 + 1 / α) * (K + 1) ^ 4 * (L + 1) ^ 2 * (U1 + U2) := by ring
      linarith [h5, e1, e2]
    calc K * L * (C_W * (42 * (K * L + 2) * (U1 + U2)))
        = 42 * C_W * (U1 + U2) * (K * L * (K * L + 2)) := by ring
      _ ≤ 42 * C_W * (U1 + U2) * (2 * ((K + 1) ^ 4 * (L + 1) ^ 2)) :=
          mul_le_mul_of_nonneg_left hKLK (by nlinarith [hCWpos, hUU])
      _ ≤ 200 * (C_W + 1) * (1 + 1 / α) * (K + 1) ^ 4 * (L + 1) ^ 2 * (U1 + U2) := hmain
  exact le_trans hstep harith


end

end Work.BMF.mr_direct
