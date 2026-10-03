import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.Assembly

namespace Work.FIArea4.L14

open scoped BigOperators

/-! ## Elementary `oddPart` facts -/

/-- For odd `n`, the odd part of `n` is `n` itself. -/
private lemma oddPart_eq_self_of_odd {n : ℕ} (hn : Odd n) : Work.FIPlan.oddPart n = n := by
  have h2 : ¬ (2 ∣ n) := by
    rintro ⟨c, rfl⟩
    rcases hn with ⟨d, hd⟩
    omega
  rw [Work.FIPlan.oddPart, Nat.factorization_eq_zero_of_not_dvd h2, pow_zero, Nat.div_one]

/-- The odd part is insensitive to multiplying by `2`. -/
private lemma oddPart_two_mul (n : ℕ) : Work.FIPlan.oddPart (2 * n) = Work.FIPlan.oddPart n := by
  have h := Nat.ordCompl_self_pow_mul n 1 Nat.prime_two
  simpa [Work.FIPlan.oddPart, pow_one] using h

/-- Reindex the even numbers of `[1,D]` as `2k`, `k ∈ [1, D/2]`. -/
private lemma sum_Icc_filter_even (D : ℕ) (g : ℕ → ℝ) :
    ∑ b ∈ (Finset.Icc 1 D).filter Even, g b = ∑ k ∈ Finset.Icc 1 (D / 2), g (2 * k) := by
  refine Finset.sum_bij (fun b _ => b / 2) ?_ ?_ ?_ ?_
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_Icc] at hb
    obtain ⟨⟨h1, h2⟩, hev⟩ := hb
    refine Finset.mem_Icc.mpr ⟨?_, Nat.div_le_div_right h2⟩
    have h2b : 2 ≤ b := by rcases hev with ⟨c, hc⟩; omega
    exact Nat.div_pos h2b (by norm_num)
  · intro b1 hb1 b2 hb2 heq
    simp only [Finset.mem_filter, Finset.mem_Icc] at hb1 hb2
    have e1 := Nat.two_mul_div_two_of_even hb1.2
    have e2 := Nat.two_mul_div_two_of_even hb2.2
    rw [← e1, ← e2, heq]
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    refine ⟨2 * k, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, ?_⟩, ⟨k, by ring⟩⟩
      have : k * 2 ≤ D := (Nat.le_div_iff_mul_le (by norm_num)).mp hk.2
      omega
    · exact Nat.mul_div_cancel_left k (by norm_num)
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_Icc] at hb
    congr 1
    exact (Nat.two_mul_div_two_of_even hb.2).symm

/-- The recursion identity behind the bound: split the full sum into its odd and even parts,
and reindex the even part as `(1/2)` times the same sum up to `D/2`. -/
private lemma sum_oddPart_decomp (G : ℕ → ℝ) (D : ℕ) :
    ∑ b ∈ Finset.Icc 1 D, ((b : ℝ))⁻¹ * G (Work.FIPlan.oddPart b)
      = (∑ b ∈ (Finset.Icc 1 D).filter Odd, ((b : ℝ))⁻¹ * G b)
        + (2 : ℝ)⁻¹ * ∑ b ∈ Finset.Icc 1 (D / 2),
            ((b : ℝ))⁻¹ * G (Work.FIPlan.oddPart b) := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 D) (fun b => Odd b)
        (fun b => ((b : ℝ))⁻¹ * G (Work.FIPlan.oddPart b))]
  rw [show (Finset.Icc 1 D).filter (fun b => ¬ Odd b) = (Finset.Icc 1 D).filter Even from
      Finset.filter_congr (fun b _ => Nat.not_odd_iff_even)]
  congr 1
  · apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mem_filter] at hb
    rw [oddPart_eq_self_of_odd hb.2]
  · rw [sum_Icc_filter_even D (fun b => ((b : ℝ))⁻¹ * G (Work.FIPlan.oddPart b))]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [oddPart_two_mul]
    have hcast : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
    rw [hcast, mul_inv_rev]
    ring

/-- Main induction: the full sum is dominated by twice the odd-part sum. -/
private theorem main_bound (G : ℕ → ℝ) (hG : ∀ e, 0 ≤ G e) :
    ∀ D : ℕ, ∑ b ∈ Finset.Icc 1 D, ((b : ℝ))⁻¹ * G (Work.FIPlan.oddPart b)
      ≤ 2 * ∑ e ∈ (Finset.Icc 1 D).filter Odd, ((e : ℝ))⁻¹ * G e := by
  intro D
  induction D using Nat.strong_induction_on with
  | h D ih =>
    rcases Nat.eq_zero_or_pos D with hD0 | hDpos
    · subst hD0
      simp
    · have hdiv : D / 2 < D := Nat.div_lt_self hDpos (by norm_num)
      have hih := ih (D / 2) hdiv
      rw [sum_oddPart_decomp G D]
      have hT2 : (∑ e ∈ (Finset.Icc 1 (D / 2)).filter Odd, ((e : ℝ))⁻¹ * G e)
          ≤ (∑ e ∈ (Finset.Icc 1 D).filter Odd, ((e : ℝ))⁻¹ * G e) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro e he
          simp only [Finset.mem_filter, Finset.mem_Icc] at he ⊢
          exact ⟨⟨he.1.1, le_trans he.1.2 (Nat.div_le_self D 2)⟩, he.2⟩
        · intro e _ _
          exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg e)) (hG e)
      have hstep : (2 : ℝ)⁻¹ * (∑ b ∈ Finset.Icc 1 (D / 2),
            ((b : ℝ))⁻¹ * G (Work.FIPlan.oddPart b))
          ≤ (∑ e ∈ (Finset.Icc 1 (D / 2)).filter Odd, ((e : ℝ))⁻¹ * G e) := by
        have h := mul_le_mul_of_nonneg_left hih (show (0 : ℝ) ≤ (2 : ℝ)⁻¹ by norm_num)
        have heq : (2 : ℝ)⁻¹ * (2 * (∑ e ∈ (Finset.Icc 1 (D / 2)).filter Odd,
              ((e : ℝ))⁻¹ * G e))
            = (∑ e ∈ (Finset.Icc 1 (D / 2)).filter Odd, ((e : ℝ))⁻¹ * G e) := by
          rw [← mul_assoc, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_mul]
        linarith [h, heq]
      linarith [hstep, hT2]

theorem sum_inv_oddPart_le (D : ℕ) (G : ℕ → ℝ) (hG : ∀ e, 0 ≤ G e) : ∑ b ∈ Finset.Icc 1 D, ((b : ℝ))⁻¹ * G (Work.FIPlan.oddPart b) ≤ 2 * ∑ e ∈ (Finset.Icc 1 D).filter Odd, ((e : ℝ))⁻¹ * G e :=
  main_bound G hG D

end Work.FIArea4.L14
