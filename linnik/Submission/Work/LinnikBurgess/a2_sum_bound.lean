import Mathlib
import Submission.Work.LinnikBurgess.a2_gcdmul
import Submission.Work.LinnikBurgess.a2_dist_le_two_Icc
import Submission.Work.LinnikBurgess.a2_sum_gcd_mul_gcd_Icc_le
import Submission.Commons.NumberTheory.Divisors.sum_gcd_le_of_pos

namespace Work.LinnikBurgess

/-- The `a2`-sum (weight form).  For `0 < m`, `gcd(m,d) = 1`, `0 < d`, and a pivot `x ∈ [1,H]`, the sum over `y ∈ [1,H]`, `y ≠ x`, of `gcd(m,|x-y|)·(H/d·gcd(d,|x-y|) + 1)` is at most `2·(H^2·τ(d)/d + H)·τ(m)`. -/
theorem a2_sum_bound {m d H : ℕ} (hm : 0 < m) (hmd : Nat.Coprime m d) (hd : 0 < d)
    (x : ℕ) (hx : x ∈ Finset.Icc 1 H) :
    (∑ y ∈ (Finset.Icc 1 H).filter (fun y => y ≠ x),
        ((Nat.gcd m (((x : ℤ) - (y : ℤ)).natAbs) : ℝ)
          * ((H : ℝ) * (Nat.gcd d (((x : ℤ) - (y : ℤ)).natAbs) : ℝ) / (d : ℝ) + 1)))
      ≤ 2 * (((H : ℝ) ^ 2 * ((d.divisors.card : ℝ)) / (d : ℝ)) + (H : ℝ))
          * ((m.divisors.card : ℝ)) := by
  obtain ⟨hx1, hxH⟩ := Finset.mem_Icc.mp hx
  -- the weight as a function of the distance
  set F : ℕ → ℝ := fun n => (Nat.gcd m n : ℝ) * ((H : ℝ) * (Nat.gcd d n : ℝ) / (d : ℝ) + 1)
    with hF
  have hFnn : ∀ n, 0 ≤ F n := by
    intro n
    rw [hF]
    positivity
  -- step 1: replace the sum over the window by twice the sum over the distances `1 … H-1`
  have hstep1 : (∑ y ∈ (Finset.Icc 1 H).filter (fun y => y ≠ x), F (((x : ℤ) - (y : ℤ)).natAbs))
      ≤ 2 * ∑ c ∈ Finset.Icc 1 (H - 1), F c := a2_dist_le_two_Icc hx1 hxH hFnn
  -- split the weight
  have hFs : ∀ c : ℕ, F c
      = (H : ℝ) / (d : ℝ) * ((Nat.gcd m c : ℝ) * (Nat.gcd d c : ℝ)) + (Nat.gcd m c : ℝ) := by
    intro c
    rw [hF]
    ring
  have hsplit : (∑ c ∈ Finset.Icc 1 (H - 1), F c)
      = (H : ℝ) / (d : ℝ)
          * (∑ c ∈ Finset.Icc 1 (H - 1), (Nat.gcd m c : ℝ) * (Nat.gcd d c : ℝ))
        + ∑ c ∈ Finset.Icc 1 (H - 1), (Nat.gcd m c : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun c _ => hFs c)
  -- the two divisor-counting bounds
  have hA := a2_sum_gcd_mul_gcd_Icc_le hm hd hmd (H - 1)
  have hB : (∑ c ∈ Finset.Icc 1 (H - 1), (Nat.gcd m c : ℝ))
      ≤ (((H - 1 : ℕ)) : ℝ) * (m.divisors.card : ℝ) := by
    have hnat : ∑ c ∈ Finset.Icc 1 (H - 1), Nat.gcd m c ≤ (H - 1) * m.divisors.card := by
      calc ∑ c ∈ Finset.Icc 1 (H - 1), Nat.gcd m c
          = ∑ c ∈ Finset.Icc 1 (H - 1), Nat.gcd c m :=
            Finset.sum_congr rfl (fun c _ => Nat.gcd_comm _ _)
        _ ≤ (H - 1) * m.divisors.card :=
            Commons.NumberTheory.Divisors.sum_gcd_le_of_pos (H - 1) m hm
    calc (∑ c ∈ Finset.Icc 1 (H - 1), (Nat.gcd m c : ℝ))
        = ((∑ c ∈ Finset.Icc 1 (H - 1), Nat.gcd m c : ℕ) : ℝ) := (Nat.cast_sum _ _).symm
      _ ≤ (((H - 1) * m.divisors.card : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = (((H - 1 : ℕ)) : ℝ) * (m.divisors.card : ℝ) := by push_cast; ring
  have hsum : (∑ c ∈ Finset.Icc 1 (H - 1), F c)
      ≤ (H : ℝ) / (d : ℝ)
          * ((((H - 1 : ℕ)) : ℝ) * ((m.divisors.card : ℝ) * (d.divisors.card : ℝ)))
        + (((H - 1 : ℕ)) : ℝ) * (m.divisors.card : ℝ) := by
    rw [hsplit]
    exact add_le_add (mul_le_mul_of_nonneg_left hA (by positivity)) hB
  -- the final arithmetic
  have hNle : (((H - 1 : ℕ)) : ℝ) ≤ (H : ℝ) := by exact_mod_cast Nat.sub_le H 1
  have hτm : (0 : ℝ) ≤ (m.divisors.card : ℝ) := by positivity
  have hτd : (0 : ℝ) ≤ (d.divisors.card : ℝ) := by positivity
  have hkey : (H : ℝ) / (d : ℝ)
        * ((((H - 1 : ℕ)) : ℝ) * ((m.divisors.card : ℝ) * (d.divisors.card : ℝ)))
        + (((H - 1 : ℕ)) : ℝ) * (m.divisors.card : ℝ)
      ≤ (((H : ℝ) ^ 2 * (d.divisors.card : ℝ) / (d : ℝ)) + (H : ℝ))
          * (m.divisors.card : ℝ) := by
    have h1 : (H : ℝ) / (d : ℝ)
          * ((((H - 1 : ℕ)) : ℝ) * ((m.divisors.card : ℝ) * (d.divisors.card : ℝ)))
        ≤ (H : ℝ) / (d : ℝ)
          * ((H : ℝ) * ((m.divisors.card : ℝ) * (d.divisors.card : ℝ))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_right hNle (by positivity)
    have h2 : (((H - 1 : ℕ)) : ℝ) * (m.divisors.card : ℝ) ≤ (H : ℝ) * (m.divisors.card : ℝ) :=
      mul_le_mul_of_nonneg_right hNle hτm
    have h3 : (H : ℝ) / (d : ℝ)
          * ((H : ℝ) * ((m.divisors.card : ℝ) * (d.divisors.card : ℝ)))
        = ((H : ℝ) ^ 2 * (d.divisors.card : ℝ) / (d : ℝ)) * (m.divisors.card : ℝ) := by
      field_simp
    linarith [h1, h2, h3]
  -- reassemble
  have hgoal : (∑ y ∈ (Finset.Icc 1 H).filter (fun y => y ≠ x),
        F (((x : ℤ) - (y : ℤ)).natAbs))
      = ∑ y ∈ (Finset.Icc 1 H).filter (fun y => y ≠ x),
        ((Nat.gcd m (((x : ℤ) - (y : ℤ)).natAbs) : ℝ)
          * ((H : ℝ) * (Nat.gcd d (((x : ℤ) - (y : ℤ)).natAbs) : ℝ) / (d : ℝ) + 1)) := by
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [hF]
  rw [← hgoal]
  calc (∑ y ∈ (Finset.Icc 1 H).filter (fun y => y ≠ x), F (((x : ℤ) - (y : ℤ)).natAbs))
      ≤ 2 * ∑ c ∈ Finset.Icc 1 (H - 1), F c := hstep1
    _ ≤ 2 * ((((H : ℝ) ^ 2 * (d.divisors.card : ℝ) / (d : ℝ)) + (H : ℝ))
          * (m.divisors.card : ℝ)) := by linarith [hsum, hkey]
    _ = 2 * (((H : ℝ) ^ 2 * (d.divisors.card : ℝ) / (d : ℝ)) + (H : ℝ))
          * (m.divisors.card : ℝ) := by ring

end Work.LinnikBurgess
