import Mathlib
import Submission.Work.FIArea7.sum_inv_sq_filter_le
import Submission.Work.FIArea7.sum_inv_Icc_le_two_log

namespace Work.FIArea7

/-- Arithmetic normalization: with `u = N^{δ₁}/(4s)`,
`X·(A·N/(2u)) = 2·A·X·s·N^{1-δ₁}`. -/
private lemma arith_u_slack (X A N s : ℝ) (δ₁ : ℝ) (hNpos : 0 < N) (hs : s ≠ 0) :
    X * (A * N / (2 * (N ^ δ₁ / (4 * s))))
      = 2 * A * (X * s * N ^ (1 - δ₁)) := by
  rw [show N ^ (1 - δ₁) = N / N ^ δ₁ from by rw [Real.rpow_sub hNpos, Real.rpow_one]]
  have h2 : N ^ δ₁ ≠ 0 := (Real.rpow_pos_of_pos hNpos δ₁).ne'
  field_simp
  ring

/-- Generalisation of `Work.FIArea7.regionHigh_inner_le` to an arbitrary positive threshold
factor `s` (instead of `2K+1`): for `1 ≤ e`, the `b`-sum restricted to `4be·s > N^{δ₁}` is at
most `A·N/(2u)` with `u = N^{δ₁}/(4s)`. -/
private lemma regionSlack_inner_le (B : ℕ) (N δ₁ A s u : ℝ)
    (hN : 1 ≤ N) (hδ : 0 < δ₁) (hA : 0 ≤ A) (hs : 0 < s)
    (hu : u = N ^ δ₁ / (4 * s)) (e : ℕ) (he : 1 ≤ e) :
    (∑ b ∈ Finset.Icc 1 B,
        (if ¬ (4 * (b : ℝ) * (e : ℝ) * s ≤ N ^ δ₁)
          then (1 / (b : ℝ)) * (A * N / (4 * (b : ℝ) * (e : ℝ))) else 0))
      ≤ A * N / (2 * u) := by
  classical
  have hNpos : (0 : ℝ) < N := by linarith
  have h4q : (0 : ℝ) < 4 * s := by linarith
  have hPpos : (0 : ℝ) < N ^ δ₁ := Real.rpow_pos_of_pos hNpos δ₁
  have hupos : (0 : ℝ) < u := by rw [hu]; exact div_pos hPpos h4q
  have hepos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hiff : ∀ b : ℕ,
      (¬ (4 * (b : ℝ) * (e : ℝ) * s ≤ N ^ δ₁)) ↔ u < (b : ℝ) * (e : ℝ) := by
    intro b
    have hcast : 4 * (b : ℝ) * (e : ℝ) * s = (b : ℝ) * (e : ℝ) * (4 * s) := by ring
    rw [hcast, not_le, hu, div_lt_iff₀ h4q]
  have hsum_eq : (∑ b ∈ Finset.Icc 1 B,
        (if ¬ (4 * (b : ℝ) * (e : ℝ) * s ≤ N ^ δ₁)
          then (1 / (b : ℝ)) * (A * N / (4 * (b : ℝ) * (e : ℝ))) else 0))
      = ∑ b ∈ Finset.Icc 1 B,
        (if u < (b : ℝ) * (e : ℝ)
          then (1 / (b : ℝ)) * (A * N / (4 * (b : ℝ) * (e : ℝ))) else 0) :=
    Finset.sum_congr rfl (fun b _ => if_congr (hiff b) rfl rfl)
  rw [hsum_eq, ← Finset.sum_filter]
  have hT : ((Finset.Icc 1 B).filter (fun b : ℕ => u < (b : ℝ) * (e : ℝ)))
      = (Finset.Icc 1 B).filter (fun b : ℕ => u / e < (b : ℝ)) := by
    refine Finset.filter_congr (fun b _ => ?_)
    exact (div_lt_iff₀ hepos).symm
  rw [hT]
  have hfac : (∑ b ∈ (Finset.Icc 1 B).filter (fun b : ℕ => u / e < (b : ℝ)),
        (1 / (b : ℝ)) * (A * N / (4 * (b : ℝ) * (e : ℝ))))
      = (A * N / (4 * (e : ℝ)))
        * (∑ b ∈ (Finset.Icc 1 B).filter (fun b : ℕ => u / e < (b : ℝ)),
            (1 : ℝ) / ((b : ℝ) ^ 2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
    have hb1R : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb1
    have hbne : (b : ℝ) ≠ 0 := by linarith
    have hene : (e : ℝ) ≠ 0 := ne_of_gt hepos
    field_simp
  rw [hfac]
  have hSbound :
      (∑ b ∈ (Finset.Icc 1 B).filter (fun b : ℕ => u / e < (b : ℝ)),
          (1 : ℝ) / ((b : ℝ) ^ 2)) ≤ 2 * e / u := by
    have hc : 0 < u / e := div_pos hupos hepos
    have hle := sum_inv_sq_filter_le B (u / e) hc
    have h2 : 2 / (u / e) = 2 * e / u := by
      have hune : u ≠ 0 := ne_of_gt hupos
      have hene : (e : ℝ) ≠ 0 := ne_of_gt hepos
      field_simp
    linarith
  have hANnn : 0 ≤ A * N / (4 * (e : ℝ)) := by
    apply div_nonneg
    · exact mul_nonneg hA (le_of_lt hNpos)
    · positivity
  have hfinal : (A * N / (4 * (e : ℝ))) * (2 * e / u) = A * N / (2 * u) := by
    have hune : u ≠ 0 := ne_of_gt hupos
    have hene : (e : ℝ) ≠ 0 := ne_of_gt hepos
    field_simp
    ring
  exact le_trans (mul_le_mul_of_nonneg_left hSbound hANnn) (le_of_eq hfinal)

/-- ***FI* (17.13)-type elementary estimate for the angular slack region**: the `(b,e)`-pairs
with `4be(2K + L₀ + 2) > N^{δ₁}` carry the weight `(1/b)(100·N/(4be) + 1)` and their total is at
most `1200·X·(2K+L₀+2)·N^{1-δ₁} + 2X·log(B+2)`. -/
theorem regionSlackSum_le (B X K L₀ : ℕ) (N δ₁ : ℝ)
    (hN : 1 ≤ N) (hδ : 0 < δ₁) (hδ1 : δ₁ ≤ 1) :
    (∑ p ∈ ((Finset.Icc 1 B).product (Finset.Icc 1 X)).filter
        (fun p => ¬ (4 * (p.1 : ℝ) * (p.2 : ℝ) * (2 * (K : ℝ) + (L₀ : ℝ) + 2) ≤ N ^ δ₁)),
        (1 / (p.1 : ℝ)) * (100 * N / (4 * (p.1 : ℝ) * (p.2 : ℝ)) + 1))
      ≤ 1200 * ((X : ℝ) * (2 * (K : ℝ) + (L₀ : ℝ) + 2) * N ^ (1 - δ₁))
          + 2 * ((X : ℝ) * Real.log ((B : ℝ) + 2)) := by
  have hNpos : (0 : ℝ) < N := by linarith
  set s : ℝ := 2 * (K : ℝ) + (L₀ : ℝ) + 2 with hsdef
  have hspos : (0 : ℝ) < s := by rw [hsdef]; positivity
  have hNδpos : (0 : ℝ) < N ^ δ₁ := Real.rpow_pos_of_pos hNpos δ₁
  have hNpow : (0 : ℝ) < N ^ (1 - δ₁) := Real.rpow_pos_of_pos hNpos (1 - δ₁)
  have hXnn : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  set u : ℝ := N ^ δ₁ / (4 * s) with hu
  have hu_pos : 0 < u := by rw [hu]; exact div_pos hNδpos (by positivity)
  set P1 : ℝ := ∑ e ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 B,
      (if ¬ (4 * (b : ℝ) * (e : ℝ) * s ≤ N ^ δ₁)
        then (1 / (b : ℝ)) * (100 * N / (4 * (b : ℝ) * (e : ℝ))) else 0) with hP1
  set P2 : ℝ := ∑ e ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 B,
      (if ¬ (4 * (b : ℝ) * (e : ℝ) * s ≤ N ^ δ₁)
        then (1 : ℝ) / (b : ℝ) else 0) with hP2
  have hsplit : (∑ p ∈ ((Finset.Icc 1 B).product (Finset.Icc 1 X)).filter
        (fun p => ¬ (4 * (p.1 : ℝ) * (p.2 : ℝ) * s ≤ N ^ δ₁)),
        (1 / (p.1 : ℝ)) * (100 * N / (4 * (p.1 : ℝ) * (p.2 : ℝ)) + 1)) = P1 + P2 := by
    rw [hP1, hP2]
    rw [Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product, Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun e he => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    by_cases hQ : ¬ (4 * (b : ℝ) * (e : ℝ) * s ≤ N ^ δ₁)
    · rw [if_pos hQ, if_pos hQ, if_pos hQ]; ring
    · rw [if_neg hQ, if_neg hQ, if_neg hQ]; ring
  have hP1_le : P1 ≤ 2 * 100 * ((X : ℝ) * s * N ^ (1 - δ₁)) := by
    rw [hP1]
    have hstep : ∀ e ∈ Finset.Icc 1 X,
        (∑ b ∈ Finset.Icc 1 B,
          (if ¬ (4 * (b : ℝ) * (e : ℝ) * s ≤ N ^ δ₁)
            then (1 / (b : ℝ)) * (100 * N / (4 * (b : ℝ) * (e : ℝ))) else 0))
          ≤ 100 * N / (2 * u) := by
      intro e he
      exact regionSlack_inner_le B N δ₁ 100 s u hN hδ (by norm_num) hspos hu e
        (Finset.mem_Icc.mp he).1
    calc (∑ e ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 B,
            (if ¬ (4 * (b : ℝ) * (e : ℝ) * s ≤ N ^ δ₁)
              then (1 / (b : ℝ)) * (100 * N / (4 * (b : ℝ) * (e : ℝ))) else 0))
        ≤ ∑ e ∈ Finset.Icc 1 X, (100 * N / (2 * u)) := Finset.sum_le_sum hstep
      _ = (X : ℝ) * (100 * N / (2 * u)) := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
      _ = 2 * 100 * ((X : ℝ) * s * N ^ (1 - δ₁)) := by
          rw [hu]
          exact arith_u_slack (X : ℝ) 100 N s δ₁ hNpos (ne_of_gt hspos)
  have hP2_le : P2 ≤ 2 * ((X : ℝ) * Real.log ((B : ℝ) + 2)) := by
    rw [hP2]
    calc (∑ e ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 B,
            (if ¬ (4 * (b : ℝ) * (e : ℝ) * s ≤ N ^ δ₁)
              then (1 : ℝ) / (b : ℝ) else 0))
        ≤ ∑ e ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 B, (1 : ℝ) / (b : ℝ) := by
          refine Finset.sum_le_sum (fun e he => Finset.sum_le_sum (fun b hb => ?_))
          by_cases hQ : ¬ (4 * (b : ℝ) * (e : ℝ) * s ≤ N ^ δ₁)
          · rw [if_pos hQ]
          · rw [if_neg hQ]
            have hb1 : (1 : ℝ) ≤ (b : ℝ) := by
              exact_mod_cast (Finset.mem_Icc.mp hb).1
            have hbpos : (0 : ℝ) < (b : ℝ) := by linarith
            positivity
      _ = (X : ℝ) * (∑ b ∈ Finset.Icc 1 B, (1 : ℝ) / (b : ℝ)) := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
      _ ≤ (X : ℝ) * (2 * Real.log ((B : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_left (sum_inv_Icc_le_two_log B) hXnn
      _ = 2 * ((X : ℝ) * Real.log ((B : ℝ) + 2)) := by ring
  have hnn : 0 ≤ (X : ℝ) * s * N ^ (1 - δ₁) :=
    mul_nonneg (mul_nonneg hXnn (le_of_lt hspos)) (le_of_lt hNpow)
  rw [hsplit]
  nlinarith [hP1_le, hP2_le, hnn]

end Work.FIArea7
