import Mathlib
import Submission.Work.KMTAreas.A7.randSymb_coeff_aux

namespace Work.KMTAreas.A7

theorem randSymb_coeff_data (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ)
    (ε : ℕ → ℂ) (hε : ∀ n, ‖ε n‖ ≤ 1) (ha : Monotone a) (K : ℕ) :
    (Work.KMTAreas.A7.randSymb (Work.KMTAreas.A7.smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K
        = fun ξ : ℝ => ∑ m ∈ Finset.range (K + 1),
            Work.KMTAreas.A7.randCoeff ρ C₀ a l₁ l₂ k₁ k₂ ε K m
              * Work.KMTAreas.A7.varphiNt (Nat.floor (a m)) k₁ t ξ)
    ∧ (∀ m : ℕ, ‖Work.KMTAreas.A7.randCoeff ρ C₀ a l₁ l₂ k₁ k₂ ε K m‖ ≤ 2)
    ∧ (∀ c e : ℕ,
        ‖∑ m ∈ Finset.Icc c e, Work.KMTAreas.A7.randCoeff ρ C₀ a l₁ l₂ k₁ k₂ ε K m‖ ≤ 4) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · -- ### 1. the randomised symbol is the finite linear combination of the bumps
    funext ξ
    let A : ℕ → Prop := fun m => randAct ρ C₀ a l₁ l₂ k₁ k₂ m
    let φ : ℕ → ℂ := fun m => varphiNt (Nat.floor (a m)) k₁ t ξ
    have hA0 : ¬ A 0 := by simp [A, randAct]
    have hsmall : ∀ m : ℕ, smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t m ξ = (if A m then φ m else 0) := by
      intro m
      rw [smallSymbF_apply, ite_apply, Pi.zero_apply]
    -- the two shifted sums
    have h1 : ∑ x ∈ Finset.range K, ε x * (if A (x + 1) then φ (x + 1) else 0)
        = ∑ m ∈ Finset.range (K + 1), ε (m - 1) * (if A m then φ m else 0) := by
      have hsum := Finset.sum_range_succ' (fun m => ε (m - 1) * (if A m then φ m else 0)) K
      have h0 : ε (0 - 1) * (if A 0 then φ 0 else 0) = 0 := by simp [hA0]
      rw [hsum, h0, add_zero]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      show ε k * (if A (k + 1) then φ (k + 1) else 0)
        = ε ((k + 1) - 1) * (if A (k + 1) then φ (k + 1) else 0)
      rw [Nat.add_sub_cancel]
    have h2 : ∑ x ∈ Finset.range K, ε x * (if A x then φ x else 0)
        = ∑ m ∈ Finset.range (K + 1),
            ε m * (if A m then φ m else 0) * (if m < K then (1 : ℂ) else 0) := by
      rw [Finset.sum_range_succ
        (fun m => ε m * (if A m then φ m else 0) * (if m < K then (1 : ℂ) else 0)) K]
      have hK : ε K * (if A K then φ K else 0) * (if K < K then (1 : ℂ) else 0) = 0 := by simp
      rw [hK, add_zero]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [Finset.mem_range] at hm
      rw [if_pos hm, mul_one]
    -- the coefficient of the `m`-th bump, on the range of summation
    have h3 : ∀ m ∈ Finset.range (K + 1),
        randCoeff ρ C₀ a l₁ l₂ k₁ k₂ ε K m * φ m
          = ε (m - 1) * (if A m then φ m else 0)
            - ε m * (if A m then φ m else 0) * (if m < K then (1 : ℂ) else 0) := by
      intro m hm
      rw [Finset.mem_range] at hm
      have hmK : m ≤ K := by omega
      rw [show randCoeff ρ C₀ a l₁ l₂ k₁ k₂ ε K m
          = (if randAct ρ C₀ a l₁ l₂ k₁ k₂ m then
              (ε (m - 1) * (if m ≤ K then (1 : ℂ) else 0)
                - ε m * (if m < K then (1 : ℂ) else 0)) else 0) from rfl]
      by_cases hAm : A m
      · rw [if_pos hAm, if_pos hAm, if_pos hmK, mul_one]
        ring
      · rw [if_neg hAm, if_neg hAm]
        ring
    rw [randSymb]
    simp only [hsmall]
    refine Eq.trans (b := ∑ x ∈ Finset.range K,
      ε x * (if A (x + 1) then φ (x + 1) else 0)
        - ∑ x ∈ Finset.range K, ε x * (if A x then φ x else 0)) ?_ ?_
    · rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun x _ => mul_sub _ _ _)
    · rw [h1, h2, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun m hm => (h3 m hm).symm)
  · -- ### 2. the coefficients are bounded by `2`
    intro m
    rw [show randCoeff ρ C₀ a l₁ l₂ k₁ k₂ ε K m
        = (if randAct ρ C₀ a l₁ l₂ k₁ k₂ m then
            (ε (m - 1) * (if m ≤ K then (1 : ℂ) else 0)
              - ε m * (if m < K then (1 : ℂ) else 0)) else 0) from rfl]
    by_cases h : randAct ρ C₀ a l₁ l₂ k₁ k₂ m
    · rw [if_pos h]
      refine le_trans (norm_sub_le _ _) ?_
      rw [norm_mul, norm_mul]
      have e1 : ‖ε (m - 1)‖ ≤ 1 := hε (m - 1)
      have e2 : ‖ε m‖ ≤ 1 := hε m
      have c1 : ‖(if m ≤ K then (1 : ℂ) else 0)‖ ≤ 1 := by
        by_cases h : m ≤ K
        · rw [if_pos h]; simp
        · rw [if_neg h]; simp
      have c2 : ‖(if m < K then (1 : ℂ) else 0)‖ ≤ 1 := by
        by_cases h : m < K
        · rw [if_pos h]; simp
        · rw [if_neg h]; simp
      have p1 : ‖ε (m - 1)‖ * ‖(if m ≤ K then (1 : ℂ) else 0)‖ ≤ 1 :=
        le_trans (mul_le_mul e1 c1 (norm_nonneg _) (by norm_num)) (by norm_num)
      have p2 : ‖ε m‖ * ‖(if m < K then (1 : ℂ) else 0)‖ ≤ 1 :=
        le_trans (mul_le_mul e2 c2 (norm_nonneg _) (by norm_num)) (by norm_num)
      linarith
    · rw [if_neg h]
      norm_num
  · -- ### 3. the partial sums of the coefficients over an interval are bounded by `4`
    intro c e
    by_cases hce : c ≤ e
    · let u : ℕ → ℂ := fun m => if randAct ρ C₀ a l₁ l₂ k₁ k₂ m then (1 : ℂ) else 0
      let G : ℕ → ℂ := fun m => ε m * (if m < K then (1 : ℂ) else 0)
      have huap : ∀ m, u m = (if randAct ρ C₀ a l₁ l₂ k₁ k₂ m then (1 : ℂ) else 0) :=
        fun m => rfl
      have hGap : ∀ m, G m = ε m * (if m < K then (1 : ℂ) else 0) := fun m => rfl
      have hP : ∀ {j m k : ℕ}, j ≤ m → m ≤ k →
          randAct ρ C₀ a l₁ l₂ k₁ k₂ j → randAct ρ C₀ a l₁ l₂ k₁ k₂ k →
          randAct ρ C₀ a l₁ l₂ k₁ k₂ m :=
        fun {j m k} h1 h2 h3 h4 => randAct_interval ha h1 h2 h3 h4
      -- the coefficient is the difference of a telescoping sequence
      have hcoef : ∀ m, randCoeff ρ C₀ a l₁ l₂ k₁ k₂ ε K m = u m * (G (m - 1) - G m) := by
        intro m
        rw [show randCoeff ρ C₀ a l₁ l₂ k₁ k₂ ε K m
            = (if randAct ρ C₀ a l₁ l₂ k₁ k₂ m then
                (ε (m - 1) * (if m ≤ K then (1 : ℂ) else 0)
                  - ε m * (if m < K then (1 : ℂ) else 0)) else 0) from rfl]
        rw [huap, hGap, hGap]
        by_cases hAm : randAct ρ C₀ a l₁ l₂ k₁ k₂ m
        · rw [if_pos hAm, if_pos hAm]
          have hm0 : m ≠ 0 := hAm.1
          have hd : (if m - 1 < K then (1 : ℂ) else 0) = (if m ≤ K then (1 : ℂ) else 0) := by
            by_cases h : m ≤ K
            · rw [if_pos h, if_pos (by omega)]
            · rw [if_neg h, if_neg (by omega)]
          rw [hd]
          ring
        · rw [if_neg hAm, if_neg hAm]
          ring
      have hu1 : ∀ m, ‖u m‖ ≤ 1 := by
        intro m
        rw [huap]
        by_cases h : randAct ρ C₀ a l₁ l₂ k₁ k₂ m
        · rw [if_pos h]; simp
        · rw [if_neg h]; simp
      have hG1 : ∀ m, ‖G m‖ ≤ 1 := by
        intro m
        rw [hGap, norm_mul]
        have hc : ‖(if m < K then (1 : ℂ) else 0)‖ ≤ 1 := by
          by_cases h : m < K
          · rw [if_pos h]; simp
          · rw [if_neg h]; simp
        calc ‖ε m‖ * ‖(if m < K then (1 : ℂ) else 0)‖ ≤ 1 * 1 :=
              mul_le_mul (hε m) hc (norm_nonneg _) (by norm_num)
          _ = 1 := by norm_num
      -- telescoping
      have htelescope :
          ∑ m ∈ Finset.Icc c e, (u (m - 1) * G (m - 1) - u m * G m)
            = u (c - 1) * G (c - 1) - u e * G e :=
        sum_Icc_sub_succ_sub (fun m => u m * G m) c e hce
      have hsplit : ∑ m ∈ Finset.Icc c e, u m * (G (m - 1) - G m)
          = (u (c - 1) * G (c - 1) - u e * G e)
            + ∑ m ∈ Finset.Icc c e, (u m - u (m - 1)) * G (m - 1) := by
        rw [← htelescope, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun m _ => by ring)
      have hbd : ‖u (c - 1) * G (c - 1) - u e * G e‖ ≤ 2 := by
        have p1 : ‖u (c - 1) * G (c - 1)‖ ≤ 1 := by
          rw [norm_mul]
          refine le_trans (mul_le_mul_of_nonneg_left (hG1 (c - 1)) (norm_nonneg _)) ?_
          rw [mul_one]
          exact hu1 (c - 1)
        have p2 : ‖u e * G e‖ ≤ 1 := by
          rw [norm_mul]
          refine le_trans (mul_le_mul_of_nonneg_left (hG1 e) (norm_nonneg _)) ?_
          rw [mul_one]
          exact hu1 e
        linarith [norm_sub_le (u (c - 1) * G (c - 1)) (u e * G e)]
      have hst : ‖∑ m ∈ Finset.Icc c e, (u m - u (m - 1)) * G (m - 1)‖ ≤ 2 := by
        have hterm : ∀ m ∈ Finset.Icc c e,
            ‖(u m - u (m - 1)) * G (m - 1)‖ ≤ ‖u m - u (m - 1)‖ := by
          intro m _
          rw [norm_mul]
          exact le_trans (mul_le_mul_of_nonneg_left (hG1 (m - 1)) (norm_nonneg _))
            (le_of_eq (mul_one _))
        calc ‖∑ m ∈ Finset.Icc c e, (u m - u (m - 1)) * G (m - 1)‖
            ≤ ∑ m ∈ Finset.Icc c e, ‖(u m - u (m - 1)) * G (m - 1)‖ := norm_sum_le _ _
          _ ≤ ∑ m ∈ Finset.Icc c e, ‖u m - u (m - 1)‖ := Finset.sum_le_sum hterm
          _ ≤ 2 := sum_Icc_unit_step_le_two
                (fun m => randAct ρ C₀ a l₁ l₂ k₁ k₂ m) hP c e
      calc ‖∑ m ∈ Finset.Icc c e, randCoeff ρ C₀ a l₁ l₂ k₁ k₂ ε K m‖
          = ‖∑ m ∈ Finset.Icc c e, u m * (G (m - 1) - G m)‖ := by
            congr 1
            exact Finset.sum_congr rfl (fun m _ => hcoef m)
        _ = ‖(u (c - 1) * G (c - 1) - u e * G e)
              + ∑ m ∈ Finset.Icc c e, (u m - u (m - 1)) * G (m - 1)‖ := by rw [hsplit]
        _ ≤ ‖u (c - 1) * G (c - 1) - u e * G e‖
              + ‖∑ m ∈ Finset.Icc c e, (u m - u (m - 1)) * G (m - 1)‖ := norm_add_le _ _
        _ ≤ 2 + 2 := add_le_add hbd hst
        _ = 4 := by norm_num
    · have hempty : Finset.Icc c e = ∅ := by
        rw [Finset.Icc_eq_empty_iff]
        exact hce
      rw [hempty, Finset.sum_empty, norm_zero]
      norm_num

end Work.KMTAreas.A7
