import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ArcCRT

namespace Work.BourgainPlan.IonescuWainger

open Finset
open scoped BigOperators

/-- If every element of `A` lies in `S` and is at most `qmax`, then `Q_A ≤ qmax^{|A|}`. -/
lemma QA_le_pow_card {S : Finset ℕ} {qmax : ℕ} (hmax : ∀ q ∈ S, q ≤ qmax)
    {A : Finset ℕ} (hA : A ⊆ S) : QA A ≤ qmax ^ A.card := by
  rw [QA]
  calc ∏ q ∈ A, q ≤ ∏ q ∈ A, qmax := by
        apply Finset.prod_le_prod₀
        · intro q _
          exact Nat.zero_le _
        · intro q hq
          exact hmax q (hA hq)
    _ = qmax ^ A.card := by rw [Finset.prod_const]

/-- The nonce smallness hypothesis of `khintchine_majorArc_real` follows from `(r,c)`-goodness:
on a nonce tuple of `2r` subsets of `S` of cardinality at most `k`, one has
`∏_j Q_{A_j} ≤ q_max^{2rk}`, so `2r·ε < c/q_max^{2rk}` gives `2r·ε < 1/∏_j Q_{A_j}`. -/
theorem nonce_smallness_of_good {S : Finset ℕ} {r k qmax : ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hqmax : 1 ≤ qmax) (hmax : ∀ q ∈ S, q ≤ qmax) {c ε : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (hgood : ε < c / (2 * (r : ℝ) * (qmax : ℝ) ^ (2 * r * k)))
    {A : Fin r ⊕ Fin r → Finset ℕ} (hA : ∀ j, A j ⊆ S) (hcard : ∀ j, (A j).card ≤ k) :
    2 * (r : ℝ) * ε < 1 / ((∏ j, QA (A j) : ℕ) : ℝ) := by
  have hqmaxpos : 0 < qmax := lt_of_lt_of_le Nat.zero_lt_one hqmax
  -- each `Q_{A_j} ≤ qmax^k`
  have hAj_le : ∀ j, QA (A j) ≤ qmax ^ k := by
    intro j
    exact le_trans (QA_le_pow_card (hmax := hmax) (hA j))
      (Nat.pow_le_pow_right hqmaxpos (hcard j))
  -- the product is at most `qmax^{2rk}`
  have hprod_le : (∏ j, QA (A j)) ≤ qmax ^ (2 * r * k) := by
    have h1 : (∏ j : Fin r ⊕ Fin r, QA (A j))
        ≤ (∏ _j : Fin r ⊕ Fin r, qmax ^ k) := by
      apply Finset.prod_le_prod₀
      · intro j _
        exact Nat.zero_le _
      · intro j _
        exact hAj_le j
    have h2' : (∏ _j : Fin r ⊕ Fin r, qmax ^ k) = qmax ^ (2 * r * k) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin,
        ← pow_mul]
      congr 1
      ring
    rwa [h2'] at h1
  -- the product is at least `1`
  have hprod_ge1 : 1 ≤ ∏ j, QA (A j) := by
    apply Finset.one_le_prod₀
    intro j _
    rw [QA]
    apply Finset.one_le_prod₀
    intro q hq
    have hq' : 2 ≤ q := h2 q (hA j hq)
    omega
  have hMpos : (0 : ℝ) < (qmax : ℝ) ^ (2 * r * k) := by
    have hq : (1 : ℝ) ≤ (qmax : ℝ) := by exact_mod_cast hqmax
    exact pow_pos (lt_of_lt_of_le zero_lt_one hq) _
  -- step 1: `2r·ε < c / qmax^{2rk}`
  have hstep1 : 2 * (r : ℝ) * ε < c / ((qmax : ℝ) ^ (2 * r * k)) := by
    set d : ℝ := 2 * (r : ℝ) with hd
    have hdnn : 0 ≤ d := by rw [hd]; positivity
    rcases eq_or_lt_of_le hdnn with h | h
    · rw [← h, zero_mul]
      exact div_pos hc hMpos
    · have hlt := mul_lt_mul_of_pos_left hgood h
      have heq : d * (c / (d * (qmax : ℝ) ^ (2 * r * k)))
          = c / ((qmax : ℝ) ^ (2 * r * k)) := by
        field_simp
      rw [heq] at hlt
      exact hlt
  -- step 2: `c / qmax^{2rk} < 1 / qmax^{2rk}`
  have hstep2 : c / ((qmax : ℝ) ^ (2 * r * k)) < 1 / ((qmax : ℝ) ^ (2 * r * k)) :=
    div_lt_div_of_pos_right hc1 hMpos
  -- step 3: `1 / qmax^{2rk} ≤ 1 / ∏_j Q_{A_j}`
  have hstep3 : 1 / ((qmax : ℝ) ^ (2 * r * k))
      ≤ 1 / ((∏ j, QA (A j) : ℕ) : ℝ) := by
    apply one_div_le_one_div_of_le
    · exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hprod_ge1)
    · exact_mod_cast hprod_le
  linarith

end Work.BourgainPlan.IonescuWainger
