import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FlatP

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The finite-sum bookkeeping of the Leibniz expansion.**  For `a + b ≤ 6`, the total mass
of the binomial coefficients of the two-operator Leibniz rule is at most `2^a·2^b ≤ 2^6 = 64`,
against a constant per-term bound `T ≥ 0`. -/
theorem sum_choose_mul_le (a b : ℕ) (hab : a + b ≤ 6) (T : ℝ) (hT : 0 ≤ T) :
    ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
      ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ)) * T ≤ 64 * T := by
  have hsum_a : ∑ a₁ ∈ Finset.range (a + 1), ((a.choose a₁ : ℝ)) = (2 : ℝ) ^ a := by
    rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
    norm_num
  have hsum_b : ∑ b₁ ∈ Finset.range (b + 1), ((b.choose b₁ : ℝ)) = (2 : ℝ) ^ b := by
    rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
    norm_num
  have key : ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
        ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ)) * T
      = ((2 : ℝ) ^ a * (2 : ℝ) ^ b) * T := by
    have step1 : (∑ a₁ ∈ Finset.range (a + 1), (a.choose a₁ : ℝ))
          * (∑ b₁ ∈ Finset.range (b + 1), ((b.choose b₁ : ℝ) * T))
        = ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            (a.choose a₁ : ℝ) * ((b.choose b₁ : ℝ) * T) :=
      Finset.sum_mul_sum _ _ _ _
    have step2 : (∑ b₁ ∈ Finset.range (b + 1), ((b.choose b₁ : ℝ) * T))
        = (∑ b₁ ∈ Finset.range (b + 1), (b.choose b₁ : ℝ)) * T :=
      (Finset.sum_mul _ _ _).symm
    calc ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ)) * T
        = ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            (a.choose a₁ : ℝ) * ((b.choose b₁ : ℝ) * T) := by
          refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun b₁ _ => ?_
          ring
      _ = (∑ a₁ ∈ Finset.range (a + 1), (a.choose a₁ : ℝ))
            * (∑ b₁ ∈ Finset.range (b + 1), ((b.choose b₁ : ℝ) * T)) := step1.symm
      _ = (∑ a₁ ∈ Finset.range (a + 1), (a.choose a₁ : ℝ))
            * ((∑ b₁ ∈ Finset.range (b + 1), (b.choose b₁ : ℝ)) * T) := by rw [step2]
      _ = ((2 : ℝ) ^ a * (2 : ℝ) ^ b) * T := by rw [hsum_a, hsum_b]; ring
  rw [key]
  have h2 : (2 : ℝ) ^ a * (2 : ℝ) ^ b ≤ 64 := by
    rw [← pow_add]
    calc (2 : ℝ) ^ (a + b) ≤ (2 : ℝ) ^ 6 := pow_le_pow_right₀ (by norm_num) hab
      _ = 64 := by norm_num
  exact mul_le_mul_of_nonneg_right h2 hT

theorem abs_mixed_mul_le {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    {A Q : ℝ → ℝ → ℝ} {KA KQ : ℝ}
    (hA : Work.FTS.EllipticEst.SmoothOpen A) (hQ : Work.FTS.EllipticEst.SmoothOpen Q)
    (hAdec : ∀ j i : ℕ, j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i A z θ| ≤ KA * (z / (1 + z)) *
          (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1))
    (hQdec : ∀ j i : ℕ, j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i Q z θ| ≤ KQ * (z / (1 + z) ^ 2) *
          (if 1 ≤ i then (Real.sin (2 * θ)) ^ (α / 3) else 1))
    {a b : ℕ} (hab : a + b ≤ 6) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) z θ|
        ≤ KA * KQ * (z / (1 + z)) * (z / (1 + z) ^ 2) *
            (if 1 ≤ a then 8192 * (Real.sin (2 * θ)) ^ (α / 5) else 8192) := by
  intro z θ hz hθ0 hθ1
  -- ## Elementary angular and radial facts
  have hspos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hsnn : 0 ≤ Real.sin (2 * θ) := le_of_lt hspos
  have hsle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hznn : 0 ≤ z := le_of_lt hz
  have hd1 : 0 ≤ z / (1 + z) := div_nonneg hznn (by linarith)
  have hd2 : 0 ≤ z / (1 + z) ^ 2 := div_nonneg hznn (by positivity)
  have hsp : 0 ≤ (Real.sin (2 * θ)) ^ (α / 5) := Real.rpow_nonneg hsnn _
  have hs3 : 0 ≤ (Real.sin (2 * θ)) ^ (α / 3) := Real.rpow_nonneg hsnn _
  -- ## The two decay constants are nonnegative
  have hKA : 0 ≤ KA := by
    by_contra hlt
    push_neg at hlt
    have h1 := hAdec 0 1 (by norm_num) z θ hz hθ0 hθ1
    rw [if_pos (le_refl 1)] at h1
    have h2 : KA * (z / (1 + z))
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) < 0 :=
      mul_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos hlt (div_pos hz (by linarith)))
        (mul_pos (by linarith) (Real.rpow_pos_of_pos hspos _))
    linarith [abs_nonneg (Work.Spaces.mixed 0 1 A z θ)]
  have hKQ : 0 ≤ KQ := by
    by_contra hlt
    push_neg at hlt
    have h1 := hQdec 0 0 (by norm_num) z θ hz hθ0 hθ1
    rw [if_neg (by norm_num : ¬ (1 : ℕ) ≤ 0)] at h1
    simp only [mul_one] at h1
    have h2 : KQ * (z / (1 + z) ^ 2) < 0 :=
      mul_neg_of_neg_of_pos hlt (div_pos hz (by positivity))
    linarith [abs_nonneg (Work.Spaces.mixed 0 0 Q z θ)]
  -- ## The two composite constants
  set W : ℝ := KA * KQ * (z / (1 + z)) * (z / (1 + z) ^ 2) with hW
  have hWnn : 0 ≤ W := by
    rw [hW]
    exact mul_nonneg (mul_nonneg (mul_nonneg hKA hKQ) hd1) hd2
  set T : ℝ := (if 1 ≤ a then 2 * W * (Real.sin (2 * θ)) ^ (α / 5) else W) with hT
  have hTnn : 0 ≤ T := by
    rw [hT]
    by_cases ha : 1 ≤ a
    · rw [if_pos ha]
      exact mul_nonneg (mul_nonneg (by norm_num) hWnn) hsp
    · rw [if_neg ha]; exact hWnn
  -- ## The per-term bound
  have hper : ∀ a₁ ≤ a, ∀ b₁ ≤ b,
      |Work.Spaces.mixed b₁ a₁ A z θ| * |Work.Spaces.mixed (b - b₁) (a - a₁) Q z θ| ≤ T := by
    intro a₁ ha₁ b₁ hb₁
    have hA₁ := hAdec b₁ a₁ (by omega) z θ hz hθ0 hθ1
    by_cases ha₁' : 1 ≤ a₁
    · -- ### the first block carries an angular derivative
      rw [if_pos ha₁'] at hA₁
      have hAp : 0 ≤ KA * (z / (1 + z))
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
        mul_nonneg (mul_nonneg hKA hd1) (mul_nonneg (by linarith) hsp)
      have hQb : |Work.Spaces.mixed (b - b₁) (a - a₁) Q z θ| ≤ KQ * (z / (1 + z) ^ 2) := by
        have hQ₁ := hQdec (b - b₁) (a - a₁) (by omega) z θ hz hθ0 hθ1
        by_cases h2 : 1 ≤ a - a₁
        · rw [if_pos h2] at hQ₁
          refine le_trans hQ₁ ?_
          calc KQ * (z / (1 + z) ^ 2) * (Real.sin (2 * θ)) ^ (α / 3)
              ≤ KQ * (z / (1 + z) ^ 2) * 1 :=
                mul_le_mul_of_nonneg_left (Real.rpow_le_one hsnn hsle (by positivity))
                  (mul_nonneg hKQ hd2)
            _ = KQ * (z / (1 + z) ^ 2) := by ring
        · rw [if_neg h2] at hQ₁
          simpa using hQ₁
      refine le_trans (mul_le_mul hA₁ hQb (abs_nonneg _) hAp) ?_
      have hW1 : W * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
          = (KA * (z / (1 + z))
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
            * (KQ * (z / (1 + z) ^ 2)) := by
        rw [hW]; ring
      rw [← hW1]
      by_cases ha : 1 ≤ a
      · rw [hT]; simp only [if_pos ha]
        have h1 : α + Real.sin (2 * θ) ≤ 2 := by linarith
        have hstep : W * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
            ≤ W * (2 * (Real.sin (2 * θ)) ^ (α / 5)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hsp) hWnn
        calc W * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
            ≤ W * (2 * (Real.sin (2 * θ)) ^ (α / 5)) := hstep
          _ = 2 * W * (Real.sin (2 * θ)) ^ (α / 5) := by ring
      · exfalso; omega
    · -- ### the first block has no angular derivative: then `a₁ = 0`
      obtain rfl : a₁ = 0 := by omega
      rw [if_neg (by norm_num : ¬ (1 : ℕ) ≤ 0)] at hA₁
      simp only [mul_one] at hA₁
      have hAp : 0 ≤ KA * (z / (1 + z)) := mul_nonneg hKA hd1
      by_cases ha : 1 ≤ a
      · -- the angular derivative has moved entirely to `Q`
        have hQ₁ := hQdec (b - b₁) (a - 0) (by omega) z θ hz hθ0 hθ1
        have h2 : 1 ≤ a - 0 := by omega
        rw [if_pos h2] at hQ₁
        have hQp2 : 0 ≤ KQ * (z / (1 + z) ^ 2) := mul_nonneg hKQ hd2
        have hexp : (Real.sin (2 * θ)) ^ (α / 3) ≤ (Real.sin (2 * θ)) ^ (α / 5) :=
          Real.rpow_le_rpow_of_exponent_ge hspos hsle (by linarith)
        have hW1 : W * (Real.sin (2 * θ)) ^ (α / 5)
            = (KA * (z / (1 + z)))
              * (KQ * (z / (1 + z) ^ 2) * (Real.sin (2 * θ)) ^ (α / 5)) := by
          rw [hW]; ring
        refine le_trans (mul_le_mul hA₁ hQ₁ (abs_nonneg _) hAp) ?_
        refine le_trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hexp hQp2) hAp) ?_
        rw [← hW1]
        rw [hT]; simp only [if_pos ha]
        nlinarith [mul_nonneg hWnn hsp]
      · -- no angular derivative anywhere
        have h2 : ¬ (1 ≤ a - 0) := by omega
        have hQ₁ := hQdec (b - b₁) (a - 0) (by omega) z θ hz hθ0 hθ1
        rw [if_neg h2] at hQ₁
        simp only [mul_one] at hQ₁
        refine le_trans (mul_le_mul hA₁ hQ₁ (abs_nonneg _) hAp) ?_
        have hW1 : W = (KA * (z / (1 + z))) * (KQ * (z / (1 + z) ^ 2)) := by
          rw [hW]; ring
        rw [← hW1, hT]; simp only [if_neg ha]
        rfl
  -- ## The Leibniz expansion and the sum bound
  have hleib := Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed b a A Q hA hQ z θ hz hθ0 hθ1
  rw [hleib]
  have hsum : |∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
        ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
          * (Work.Spaces.mixed b₁ a₁ A z θ * Work.Spaces.mixed (b - b₁) (a - a₁) Q z θ)|
      ≤ 64 * T := by
    calc |∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (Work.Spaces.mixed b₁ a₁ A z θ * Work.Spaces.mixed (b - b₁) (a - a₁) Q z θ)|
        ≤ ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            |((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (Work.Spaces.mixed b₁ a₁ A z θ * Work.Spaces.mixed (b - b₁) (a - a₁) Q z θ)| := by
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          exact Finset.sum_le_sum fun a₁ _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ)) * T := by
          refine Finset.sum_le_sum fun a₁ ha₁ => Finset.sum_le_sum fun b₁ hb₁ => ?_
          have ha₁le : a₁ ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha₁)
          have hb₁le : b₁ ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb₁)
          have hX : |Work.Spaces.mixed b₁ a₁ A z θ
              * Work.Spaces.mixed (b - b₁) (a - a₁) Q z θ| ≤ T := by
            rw [abs_mul]
            exact hper a₁ ha₁le b₁ hb₁le
          have hC : 0 ≤ (a.choose a₁ : ℝ) * (b.choose b₁ : ℝ) := by positivity
          calc |((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
                * (Work.Spaces.mixed b₁ a₁ A z θ * Work.Spaces.mixed (b - b₁) (a - a₁) Q z θ)|
              = ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
                * |Work.Spaces.mixed b₁ a₁ A z θ
                    * Work.Spaces.mixed (b - b₁) (a - a₁) Q z θ| := by
                rw [abs_mul, abs_of_nonneg hC]
            _ ≤ ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ)) * T :=
                mul_le_mul_of_nonneg_left hX hC
      _ ≤ 64 * T := sum_choose_mul_le a b hab T hTnn
  refine le_trans hsum ?_
  by_cases ha : 1 ≤ a
  · simp only [hT, if_pos ha]
    have hWs : 0 ≤ W * (Real.sin (2 * θ)) ^ (α / 5) := mul_nonneg hWnn hsp
    calc 64 * (2 * W * (Real.sin (2 * θ)) ^ (α / 5))
        = 128 * (W * (Real.sin (2 * θ)) ^ (α / 5)) := by ring
      _ ≤ 8192 * (W * (Real.sin (2 * θ)) ^ (α / 5)) :=
          mul_le_mul_of_nonneg_right (by norm_num) hWs
      _ = W * (8192 * (Real.sin (2 * θ)) ^ (α / 5)) := by ring
  · simp only [hT, if_neg ha]
    calc 64 * W ≤ 8192 * W := mul_le_mul_of_nonneg_right (by norm_num) hWnn
      _ = W * 8192 := by ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FlatP
